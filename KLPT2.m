KLPT2_VERBOSE := false;
procedure SetKLPT2Verbose(flag)
    KLPT2_VERBOSE := flag;
end procedure;

procedure KLPT2VPrint(msg)
    if KLPT2_VERBOSE then
        print msg;
    end if;
end procedure;

function TwoAdicPart(N)
    M := N;
    while N mod 2 eq 0 do
        N div:= 2;
    end while;
    return M div N;
end function;

function QuaternionInverse(a)
    return Conjugate(a) / Norm(a);
end function;

function ConjugateTransposeQ(M)
    K := BaseRing(M);
    return Transpose(Matrix(K, Nrows(M), Ncols(M), [Conjugate(x) : x in Eltseq(M)]));
end function;

function ReducedNorm2x2(u)
    a := u[1][1]; b := u[1][2];
    c := u[2][1]; d := u[2][2];
    return Norm(a) * Norm(d) + Norm(b) * Norm(c) - Trace(Conjugate(a) * b * Conjugate(d) * c);
end function;

function MatInverseQ2(u)
    a := u[1][1]; b := u[1][2];
    c := u[2][1]; d := u[2][2];

    unorm := Norm(a) * Norm(d) + Norm(b) * Norm(c) - Trace(Conjugate(a) * b * Conjugate(d) * c);
    M := u * ConjugateTransposeQ(u);
    x := M[1][1];
    y := M[1][2];
    z := M[2][2];

    B := BaseRing(u);
    return ConjugateTransposeQ(u) * Matrix(B, 2, 2, [z, -y, -Conjugate(y), x]) / unorm;
end function;

function LeftIdealRightMul(I, beta)
    O := LeftOrder(I);
    return LeftIdeal(O, [x * beta : x in Basis(I)]);
end function;

function QFValue(q, x, y)
    return x^2 + q * y^2;
end function;

function SolveBinaryQF(q, M)
    if M lt 0 then
        return false, 0, 0;
    end if;
    K<w> := QuadraticField(-q);
    ok, sols := NormEquation(K, M);
    if (not ok) or (#sols eq 0) then
        return false, 0, 0;
    end if;
    coeffs := Eltseq(sols[1]);
    return true, Integers()!coeffs[1], Integers()!coeffs[2];
end function;

function CornacchiaFriendly(n : B := 2^20)
    if n lt 0 then
        return false;
    end if;
    if n lt 2^160 then
        return true;
    end if;
    return IsProbablyPrime(n);
end function;

function DecompAlphaN(I)
    N := Integers()!Norm(I);
    basis := Basis(I);
    for _ in [1 .. 10000] do
        a := &+[basis[t] * Random(0, 50) : t in [1 .. #basis]];
        if GCD(Integers()!Norm(a), N^2) eq N then
            return a;
        end if;
    end for;
    error "DecompAlphaN failed to find a decomposition element";
end function;

KLPTContextRF := recformat< B, i, j, k, p, q >;

function NewKLPTContext(B)
    i := B.1;
    j := B.2;
    k := B.3;
    p := Integers()!(-j^2);
    q := Integers()!(-i^2);
    return rec<KLPTContextRF | B := B, i := i, j := j, k := k, p := p, q := q>;
end function;

function KLPT_MatrixToGens(ctx, M)
    basisB := Basis(ctx`B);
    return [&+[M[r][c] * basisB[c] : c in [1 .. #basisB]] : r in [1 .. Nrows(M)]];
end function;

function KLPT_ReducedBasis(ctx, I)
    M := BasisMatrix(I);
    S := 2^Ceiling(Log(2, ctx`p * ctx`q));
    basisB := Basis(ctx`B);
    scale := [Max(1, Round(S * Sqrt(RealField()!Norm(g)))) : g in basisB];
    D := DiagonalMatrix(Integers(), scale);
    L := LLL(M * D);
    Dinv := DiagonalMatrix(Rationals(), [1 / (Rationals()!d) : d in scale]);
    return KLPT_MatrixToGens(ctx, ChangeRing(L, Rationals()) * Dinv);
end function;

function KLPT_EquivalentPrimeIdeal(ctx, I, bannedIdeals)
    Ibasis := KLPT_ReducedBasis(ctx, I);
    N := Integers()!Norm(I);
    // I think this is better. 
    m := Max(Floor(Log(RealField()!ctx`p) / 5), 15);

    found := false;
    bestNorm := 0;
    bestDelta := ctx`B!0;
    bestIdeal := I;

    for a1 in [0 .. m] do
        for a2 in [-m .. m] do
            for a3 in [-m .. m] do
                for a4 in [-m .. m] do
                    delta := a1 * Ibasis[1] + a2 * Ibasis[2] + a3 * Ibasis[3] + a4 * Ibasis[4];
                    qdnorm := Norm(delta) / N;
                    if Denominator(qdnorm) ne 1 then
                        continue;
                    end if;
                    dnorm := Integers()!qdnorm;
                    if dnorm le 2 then
                        continue;
                    end if;
                    if (not found) or (dnorm lt bestNorm) then
                        if GCD(dnorm, 2 * ctx`q) ne 1 then
                            continue;
                        end if;
                        if not IsProbablyPrime(dnorm) then
                            continue;
                        end if;
                        cand := LeftIdealRightMul(I, Conjugate(delta) / N);
                        if cand in bannedIdeals then
                            continue;
                        end if;
                        found := true;
                        bestNorm := dnorm;
                        bestDelta := delta;
                        bestIdeal := cand;
                    end if;
                end for;
            end for;
        end for;
    end for;

    if not found then
        // Fallback so we get wider search. 
        for _ in [1 .. 20000] do
            a1 := Random(0, 3 * m);
            a2 := Random(-3 * m, 3 * m);
            a3 := Random(-3 * m, 3 * m);
            a4 := Random(-3 * m, 3 * m);
            delta := a1 * Ibasis[1] + a2 * Ibasis[2] + a3 * Ibasis[3] + a4 * Ibasis[4];
            qdnorm := Norm(delta) / N;
            if Denominator(qdnorm) ne 1 then
                continue;
            end if;
            dnorm := Integers()!qdnorm;
            if dnorm le 2 then
                continue;
            end if;
            if GCD(dnorm, 2 * ctx`q) ne 1 then
                continue;
            end if;
            if not IsProbablyPrime(dnorm) then
                continue;
            end if;
            cand := LeftIdealRightMul(I, Conjugate(delta) / N);
            if cand in bannedIdeals then
                continue;
            end if;
            found := true;
            bestNorm := dnorm;
            bestDelta := delta;
            bestIdeal := cand;
            break;
        end for;
    end if;

    if not found then
        error "KLPT_EquivalentPrimeIdeal failed to find a prime norm equivalent ideal";
    end if;
    return bestIdeal, bestDelta;
end function;

function KLPT_RepresentInteger(ctx, M)
    if M lt 0 then
        return false, ctx`B!0;
    end if;

    q := ctx`q;
    p := ctx`p;
    B := ctx`B;
    i := ctx`i; j := ctx`j; k := ctx`k;
    m := Max(Floor(Sqrt(RealField()!(M / ((1 + q) * p)))), 3);

    for z in [1 .. m - 1] do
        for t in [0 .. m - 1] do
            Mm := M - p * QFValue(q, z, t);
            if Mm lt 0 then
                continue;
            end if;
            if CornacchiaFriendly(Mm) then
                ok, x, y := SolveBinaryQF(q, Mm);
                if ok then
                    return true, B!(x + y * i + z * j - t * k);
                end if;
            end if;
        end for;
    end for;
    return false, B!0;
end function;

function ModQuaternion(ctx, x, A, F)
    c := Eltseq(x);
    return A![F!c[1], F!c[2], F!c[3], F!c[4]];
end function;

function KLPT_IdealModConstraint(ctx, I, gamma, alpha)
    N := Integers()!Norm(I);
    F := GF(N);

    A<ii, jj, kk> := QuaternionAlgebra(F, -ctx`q, -ctx`p);
    okSplit, _, phi := IsMatrixRing(A);
    if not okSplit then
        error "Quaternion algebra modulo N did not split";
    end if;

    basisB := Basis(ctx`B);
    els := [gamma * ctx`j, gamma * (-ctx`k)] cat [basisB[t] * alpha : t in [1 .. #basisB]];
    mats := [phi(ModQuaternion(ctx, e, A, F)) : e in els];

    cols := [Vector(F, Eltseq(m)) : m in mats];
    eqs := Transpose(Matrix(cols));     // 4 x 6
    ker := Nullspace(Transpose(eqs));   // right kernel of eqs

    for sol in Basis(ker) do
        seq := Eltseq(sol);
        if (#seq ne 6) then
            continue;
        end if;
        if (seq[1] eq 0 and seq[2] eq 0) then
            continue;
        end if;
        C := Integers()!seq[1];
        D := Integers()!seq[2];

        cand := LeftIdeal(LeftOrder(I), [N, gamma * ctx`j * (C + ctx`i * D)]);
        if cand eq I then
            return true, C, D;
        end if;
    end for;

    return false, 0, 0;
end function;

function KLPT_StrongApproximation(ctx, N, facT, C, D)
    p := ctx`p;
    q := ctx`q;
    i := ctx`i; j := ctx`j; k := ctx`k;

    T := &*[t[1]^t[2] : t in facT];
    F := GF(N);
    qfCD := QFValue(q, C, D);
    if (qfCD mod N) eq 0 then
        return false, ctx`B!0;
    end if;

    lamsq := (F!T) / ((F!p) * (F!qfCD));
    if KroneckerSymbol(Integers()!lamsq, N) eq -1 then
        nonsq := 1;
        for t in facT do
            pri := t[1];
            if KroneckerSymbol(pri, N) eq -1 then
                nonsq := pri;
                break;
            end if;
        end for;
        if nonsq eq 1 then
            return false, ctx`B!0;
        end if;
        T div:= nonsq;
        lamsq := (F!T) / ((F!p) * (F!qfCD));
    end if;

    isSq, lamF := IsSquare(lamsq);
    if not isSq then
        return false, ctx`B!0;
    end if;
    lam := Integers()!lamF;

    Acoef := F!(2 * p * lam * C);
    Bcoef := F!(2 * q * p * lam * D);
    rhsNum := T - p * QFValue(q, lam * C, lam * D);
    if rhsNum mod N ne 0 then
        return false, ctx`B!0;
    end if;
    rhs := F!(rhsNum div N);

    if (Acoef eq 0) and (Bcoef eq 0) then
        if rhs ne 0 then
            return false, ctx`B!0;
        end if;
        aF := F!0;
        bF := F!0;
        ker0F := F!1;
        ker1F := F!0;
    elif Acoef ne 0 then
        aF := rhs / Acoef;
        bF := F!0;
        ker0F := -Bcoef / Acoef;
        ker1F := F!1;
    else
        aF := F!0;
        bF := rhs / Bcoef;
        ker0F := F!1;
        ker1F := F!0;
    end if;

    a := Integers()!aF;
    b := Integers()!bF;
    ker0 := Integers()!ker0F;
    ker1 := Integers()!ker1F;

    Lat := Matrix(Integers(), 4, 3, [
        N * ker0, N * ker1, 0,
        N^2, 0, 0,
        0, N^2, 0,
        -lam * C - N * a, -lam * D - N * b, N^2
    ]);
    Red := LLL(Lat);

    for vec in RowSequence(Red) do
        if Abs(vec[3]) ne N^2 then
            continue;
        end if;
        x1 := -vec[1];
        y1 := -vec[2];
        M := T - p * QFValue(q, x1, y1);
        if M mod (N^2) ne 0 then
            continue;
        end if;
        M div:= N^2;
        if not CornacchiaFriendly(M) then
            continue;
        end if;

        ok, s1, s2 := SolveBinaryQF(q, M);
        if not ok then
            continue;
        end if;

        zNum := x1 - lam * C;
        tNum := y1 - lam * D;
        if (zNum mod N ne 0) or (tNum mod N ne 0) then
            continue;
        end if;
        z := zNum div N;
        t := tNum div N;

        nu := lam * j * (C + D * i) + N * (s1 + i * s2 + j * z - k * t);
        return true, nu;
    end for;

    return false, ctx`B!0;
end function;

function KLPT_FindExtra(ctx, N, facT)
    ex := 1;
    fac := [<t[1], t[2]> : t in facT];
    while (N * ex lt 30 * ctx`p) and (#fac gt 0) do
        idx := Random([1 .. #fac]);
        l := fac[idx][1];
        e := fac[idx][2];
        ex *:= l;
        Remove(~fac, idx);
        if e gt 1 then
            Append(~fac, <l, e - 1>);
        end if;
    end while;
    return ex, fac;
end function;

function RationalListGCD(values)
    if #values eq 0 then
        return Rationals()!1;
    end if;
    denLcm := LCM([Denominator(v) : v in values]);
    ints := [Integers()!(v * denLcm) : v in values];
    g := 0;
    for z in ints do
        g := GCD(g, Abs(z));
    end for;
    if g eq 0 then
        return Rationals()!1;
    end if;
    return Rationals()!g / denLcm;
end function;

function KLPT_WithTarget(ctx, I, T)
    B := ctx`B;
    q := ctx`q;
    p := ctx`p;

    O0 := LeftOrder(I);
    origN := Integers()!Norm(I);
    banned := [];

    nuFound := false;
    gamma := B!0;
    nu := B!0;
    II := I;
    alpha_marked := B!0;
    N := 0;

    outerIter := 0;
    maxOuter := 50;
    while (not nuFound) and (outerIter lt maxOuter) do
        outerIter +:= 1;
        if (origN gt 2) and (origN lt Floor(Sqrt(RealField()!p))) and (GCD(origN, 2 * q) eq 1) and IsProbablyPrime(origN) and not (I in banned) then
            KLPT2VPrint("KLPT: original ideal is already prime and small enough");
            II := I;
            alpha_marked := B!origN;
        else
            KLPT2VPrint("KLPT: searching equivalent prime ideal");
            try
                II, alpha_marked := KLPT_EquivalentPrimeIdeal(ctx, I, banned);
            catch err
                KLPT2VPrint("KLPT: falling back to the original ideal");
                II := I;
                alpha_marked := B!origN;
            end try;
        end if;

        N := Integers()!Norm(II);
        fac := Factorization(T);
        tries := Min(Max(N div 100000, 5), 2000);

        for _ in [1 .. tries] do
            ex, facupdated := KLPT_FindExtra(ctx, N, fac);
            okGamma, gamma0 := KLPT_RepresentInteger(ctx, N * ex);
            if not okGamma then
                continue;
            end if;
            gamma := gamma0;

            alpha := DecompAlphaN(II);
            okCD, C, D := KLPT_IdealModConstraint(ctx, II, gamma, alpha);
            if not okCD then
                continue;
            end if;

            if ((p * QFValue(q, C mod N, D mod N)) mod N ne 0) and ((D mod N) ne 0) then
                nuFound, nu := KLPT_StrongApproximation(ctx, N, facupdated, C, D);
                if nuFound then
                    break;
                end if;
            end if;
        end for;

        if not nuFound then
            Append(~banned, II);
        end if;
    end while;

    if not nuFound then
        error "KLPT_WithTarget failed to find a strong approximation solution";
    end if;

    beta := gamma * nu;

    Jtmp := LeftIdealRightMul(II, Conjugate(beta) / N);
    denom := RationalListGCD(Eltseq(BasisMatrix(Jtmp)));
    return_alpha := (beta / denom) * alpha_marked / N;
    J := LeftIdealRightMul(I, Conjugate(return_alpha) / origN);

    return return_alpha, J;
end function;

function RandomReduced(O : SBound := 0.8, StartExp := 130, MaxExp := 1000)
    B := QuaternionAlgebra(O);
    ctx := NewKLPTContext(B);
    p := ctx`p;

    boundS := Floor((RealField()!p)^SBound);
    s := Random(0, boundS);
    while (not IsPrime(s)) or (s mod 4 ne 1) do
        s := Random(0, boundS);
    end while;

    boundT := Floor((RealField()!p)^(3 * SBound));
    t := Random(0, boundT);
    while t mod 4 ne 2 do
        t := Random(0, boundT);
    end while;

    for ind in [StartExp .. MaxExp] do
        ok, r := KLPT_RepresentInteger(ctx, s * t - 2^ind);
        if ok then
            return Matrix(B, 2, 2, [B!s, r, Conjugate(r), B!t]);
        end if;
    end for;

    error "RandomReduced failed to construct a reduced matrix";
end function;

function ComputeAC(O, g : L := 2, E := 0)
    B := QuaternionAlgebra(O);
    i := B.1; j := B.2; k := B.3;
    p := Integers()!(-j^2);

    s := Integers()!g[1][1];
    r := g[1][2];
    t := Integers()!g[2][2];

    if E eq 0 then
        E := Floor((Log(RealField()!p) / Log(RealField()!2)) * 7);
    end if;
    Le := L^E;

    F := GF(s);
    u := F!(t * p * Integers()!Norm(r));
    if u eq 0 then
        error "ComputeAC failed: zero inverse in GF(s)";
    end if;
    uInv := u^-1;

    found := false;
    a1 := 0;
    a2 := 0;
    c := B!0;
    trials := 0;
    maxTrials := 5000000;

    while (not found) and (trials lt maxTrials) do
        trials +:= 1;
        c20 := Random(F);
        isSq, c10 := IsSquare((F!Le) * uInv - c20^2);
        if not isSq then
            continue;
        end if;

        c2 := Integers()!c20;
        c1 := Integers()!c10;
        if ((c1 - c2) mod 2) ne 1 then
            continue;
        end if;

        c := c1 * Conjugate(r) * j + c2 * Conjugate(r) * k;
        A0 := Le - t * Integers()!Norm(c);
        if A0 mod s ne 0 then
            continue;
        end if;
        A1 := A0 div s;
        A := A1 div TwoAdicPart(A1);
        if (A gt 0) and IsPrime(A) and (A mod 4 eq 1) then
            okTS, x, y := SolveBinaryQF(1, A);
            if okTS then
                found := true;
                a1 := x;
                a2 := y;
            end if;
        end if;
    end while;

    if not found then
        error "ComputeAC failed to find (a,c)";
    end if;
    a := B!(a1 + a2 * i);
    return a, c, E;
end function;

function ComputeO1O2(O, alpha, a, c)
    B := QuaternionAlgebra(O);
    i := B.1; j := B.2; k := B.3;
    p := Integers()!(-j^2);

    alphaCoeff := Eltseq(alpha);
    nc := Integers()!Norm(c);
    R := Integers(nc);
    gamma := c * Conjugate(a);
    gCoeff := Eltseq(gamma);

    M := Matrix(R, 4, 4, [
        R!gCoeff[1], R!(-gCoeff[2]), R!(-gCoeff[3] * p), R!(-gCoeff[4] * p),
        R!gCoeff[2], R!( gCoeff[1]), R!( gCoeff[4] * p), R!(-gCoeff[3] * p),
        R!gCoeff[3], R!(-gCoeff[4]), R!( gCoeff[1]),     R!( gCoeff[2]),
        R!gCoeff[4], R!( gCoeff[3]), R!(-gCoeff[2]),     R!( gCoeff[1])
    ]);
    V := Vector(R, [R!alphaCoeff[t] : t in [1 .. 4]]);
    o2vec := Solution(M, V);
    o2 := B!(Integers()!o2vec[1] + Integers()!o2vec[2] * i + Integers()!o2vec[3] * j + Integers()!o2vec[4] * k);

    oca := o2 * gamma;
    ocaCoeff := Eltseq(oca);
    denomAlpha := LCM([Denominator(x) : x in alphaCoeff]);
    if denomAlpha eq 2 then
        beta := alpha - (1 + i + j + k) / 2;
    else
        beta := alpha;
    end if;
    betaCoeff := Eltseq(beta);

    q1, r1 := Quotrem(Integers()!(betaCoeff[1] - ocaCoeff[1]), nc);
    q2, r2 := Quotrem(Integers()!(betaCoeff[2] - ocaCoeff[2]), nc);
    q3, r3 := Quotrem(Integers()!(betaCoeff[3] - ocaCoeff[3]), nc);
    q4, r4 := Quotrem(Integers()!(betaCxoeff[4] - ocaCoeff[4]), nc);
    if not ((r1 eq 0) and (r2 eq 0) and (r3 eq 0) and (r4 eq 0)) then
        error "ComputeO1O2 failed: o2 does not satisfy modular constraints";
    end if;

    if denomAlpha eq 2 then
        o1 := B!(q1 + q2 * i + q3 * j + q4 * k) + (1 + i + j + k) / (2 * nc);
    else
        o1 := B!(q1 + q2 * i + q3 * j + q4 * k);
    end if;

    if not (o1 * Norm(c) + o2 * c * Conjugate(a) eq alpha) then
        error "ComputeO1O2 failed: output does not satisfy the defining equation";
    end if;

    return o1, o2;
end function;

function ComputeBD_KLPT(O, a, c : L := 2, E := 300)
    B := QuaternionAlgebra(O);
    ctx := NewKLPTContext(B);

    I := LeftIdeal(O, [Integers()!Norm(c), c * Conjugate(a)]);
    alpha, J := KLPT_WithTarget(ctx, I, L^E);

    o1, o2 := ComputeO1O2(O, alpha, a, c);
    g, aa, cc := XGCD(Integers()!Norm(a), Integers()!Norm(c));
    if g ne 1 then
        error "ComputeBD_KLPT requires gcd(Norm(a), Norm(c)) = 1";
    end if;

    b := cc * (Norm(c) * Conjugate(o1) + a * Conjugate(c) * Conjugate(o2));
    d := -aa * (c * Conjugate(a) * Conjugate(o1) + Norm(a) * Conjugate(o2));

    facJ := Factorization(Integers()!Norm(J));
    if #facJ gt 0 then
        eOut := facJ[1][2];
    else
        eOut := 0;
    end if;

    return b, d, eOut;
end function;

function FindAlpha(g, O)
    B := QuaternionAlgebra(O);

    s := Integers()!g[1][1];
    r := g[1][2];
    t := g[2][2];
    rc := Eltseq(r);

    alpha1, r1new := Quotrem(Integers()!rc[1], s);
    alpha2, r2new := Quotrem(Integers()!rc[2], s);
    alpha3, r3new := Quotrem(Integers()!rc[3], s);
    alpha4, r4new := Quotrem(Integers()!rc[4], s);

    alpha := B![alpha1, alpha2, alpha3, alpha4];
    rnew := B![r1new, r2new, r3new, r4new];
    if rnew ne (r - alpha * s) then
        error "FindAlpha produced inconsistent r-entry";
    end if;

    tnew := Norm(alpha) * s + Trace(Conjugate(alpha) * r) + t;

    gnew := Matrix(B, 2, 2, [B!s, rnew, Conjugate(rnew), B!tnew]);
    ualpha := Matrix(B, 2, 2, [B!1, alpha, B!0, B!1]);
    return gnew, ualpha;
end function;

function ChoosePolarisationPrimePowerReduced(g, O : L := 2, E := 0)
    a, c, eAC := ComputeAC(O, g : L := L, E := E);
    b, d, eBD := ComputeBD_KLPT(O, a, c : L := L, E := eAC);
    B := QuaternionAlgebra(O);

    u := Matrix(B, 2, 2, [a, b, c, d]);
    h := ConjugateTransposeQ(u) * g * u;
    return h, u, eAC, eBD;
end function;

function ConnectMatricesReduced(g1, g2, O : L := 2, E := 0)
    if Conjugate(g1[1][2]) ne g1[2][1] then
        error "ConnectMatricesReduced: g1 must be Hermitian";
    end if;
    if Conjugate(g2[1][2]) ne g2[2][1] then
        error "ConnectMatricesReduced: g2 must be Hermitian";
    end if;

    h1, u1, e1, f1 := ChoosePolarisationPrimePowerReduced(g1, O : L := L, E := E);
    h2, u2, e2, f2 := ChoosePolarisationPrimePowerReduced(g2, O : L := L, E := e1);

    D := Integers()!h1[1][1];
    if D ne Integers()!h2[1][1] then
        error "ConnectMatricesReduced: top-left entries did not match";
    end if;
    okD, _, _ := IsPrimePower(D);
    if not okD then
        error "ConnectMatricesReduced: top-left entry is not a prime power";
    end if;

    B := QuaternionAlgebra(O);
    r1 := h1[1][2];
    r2 := h2[1][2];
    tau := Matrix(B, 2, 2, [B!D, r1 - r2, B!0, B!D]);

    gamma := u2 * tau * MatInverseQ2(u1) * ReducedNorm2x2(u1);
    ellPow := D^2 * ReducedNorm2x2(u1);
    return gamma, ellPow, h1, h2, u1, u2, <e1, f1, e2, f2>;
end function;

////////////////////////////////////////////////////////////////////////
// Sage style wrapper
////////////////////////////////////////////////////////////////////////

function ConjugateTranspose(M)
    return ConjugateTransposeQ(M);
end function;

function ReducedNorm(u)
    return ReducedNorm2x2(u);
end function;

function MatInverse(u)
    return MatInverseQ2(u);
end function;

function Compute_ac(O, g : L := 2, e := 0)
    return ComputeAC(O, g : L := L, E := e);
end function;

function Compute_bd_KLPT(O, a, c : L := 2, e := 300)
    return ComputeBD_KLPT(O, a, c : L := L, E := e);
end function;

function ChoosePolarisationPrimePower_Reduced(g, O, t2 : L := 2)
    // `t2` is accepted for signature 
    return ChoosePolarisationPrimePowerReduced(g, O : L := L, E := 0);
end function;

function ConnectMatrices_Reduced(D, g1, g2, O : L := 2)
    // `D` is accepted for signature 
    return ConnectMatricesReduced(g1, g2, O : L := L, E := 0);
end function;

function FastExampleData()
    p := 3 * 2^43 - 1;
    B<i,j,k> := QuaternionAlgebra(Rationals(), -1, -p);
    O := QuaternionOrder([1, i, (i + j) / 2, (1 + k) / 2]);

    g1 := Matrix(B, 2, 2, [
        B!50890016657,
        B!(-863067848249479309881 + 1137349014214088243244 * i + j - k),
        B!(-863067848249479309881 - 1137349014214088243244 * i - j + k),
        B!40082714730313402201920563137231
    ]);
    g2 := Matrix(B, 2, 2, [
        B!9649191169,
        B!(-923954084130295985514 + 159836740039816258651 * i + j - 15 * k),
        B!(-923954084130295985514 - 159836740039816258651 * i - j + 15 * k),
        B!91261541728430194367609532073051
    ]);

    return p, B, O, g1, g2;
end function;

function FastExampleConnect(: L := 2, E := 0, Attempts := 10)
    _, _, O, g1, g2 := FastExampleData();

    for t in [1 .. Attempts] do
        KLPT2VPrint(Sprintf("FastExampleConnect: attempt %o/%o", t, Attempts));
        try
            gamma, ellPow, h1, h2, u1, u2, metrics := ConnectMatricesReduced(g1, g2, O : L := L, E := E);
            ok := ConjugateTransposeQ(gamma) * g2 * gamma eq ellPow * g1;
            if ok then
                return gamma, ellPow, h1, h2, u1, u2, metrics, g1, g2;
            end if;
        catch err
            KLPT2VPrint("FastExampleConnect: attempt failed; retrying");
        end try;
    end for;

    error "FastExampleConnect failed to produce a valid connecting matrix within Attempts";
end function;

// Tests 

procedure VerifyFastExampleMagma(: L := 2, E := 0, Attempts := 10)
    gamma, ellPow, _, _, _, _, metrics, g1, g2 := FastExampleConnect(: L := L, E := E, Attempts := Attempts);
    ok := ConjugateTransposeQ(gamma) * g2 * gamma eq ellPow * g1;
    print "Verification (gamma^* g2 gamma == ellPow * g1):", ok;
    print "ellPow:", ellPow;
    print "metrics <e1,f1,e2,f2>:", metrics;
    print "gamma:", gamma;
end procedure;

procedure FastExampleMagma()
    _, _, _, g1, g2 := FastExampleData();
    print "FastExampleMagma loaded matrices g1 and g2.";
    print "g1:", g1;
    print "g2:", g2;
    print "Use FastExampleConnect() or VerifyFastExampleMagma() for a full connection attempt.";
end procedure;
