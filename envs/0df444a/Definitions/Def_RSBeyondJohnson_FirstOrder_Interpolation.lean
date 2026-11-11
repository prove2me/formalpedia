-- Prove2me | Definitions.Def_RSBeyondJohnson_FirstOrder_Interpolation
-- name    : RSBeyondJohnson_FirstOrder_Interpolation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:31:16.356219+00:00
-- url     : https://prove2.me/theorems/c0b0b2be-f46d-4572-b31b-a6eaf3052105
-- title:
--   Local hidden-derivative constraints $\Phi^{d,m}_{\alpha,y}$, explainers and the first-order support (Definitions 3.6, 3.8, 3.10, (19))
-- statement:
--   Polynomials $Q\in F[X,Y_0,\dots,Y_d]$ are interpolation equations; $Q(X,P,P^{[1]},\dots,P^{[d]})$ substitutes a candidate $P$ and its **Hasse derivatives** $P^{[j]}=\sum_{i\ge j}\binom ij p_iX^{i-j}$ (valid in every characteristic). A polynomial in $F[X,Z,Y_0,\dots,Y_d]$ is a polynomial in the challenge $Z$ with coefficients in $F[X,Y_0,\dots,Y_d]$; $Q(X,z,Y)$ is its specialization at $Z=z$.
--
--   **Definition 3.6.** With $B_d(T,Y)=\sum_{j=1}^d(-1)^{j+1}T^jY_j$,
--   $$\Phi^{d,m}_{\alpha,y}(Q)=Q\big(\alpha+T,\ y+B_d(T,Y)+T^{d+1}V,\ Y_1,\dots,Y_d\big)\pmod{T^m}$$
--   in $F[T,V,Y_1,\dots,Y_d]/(T^m)$; the local constraints are $\Phi^{d,m}_{\alpha,y}(Q)=0$. It is a linear map, recorded by the coefficients of $T^0,\dots,T^{m-1}$.
--
--   **Definition 3.8.** A nonzero $Q$ is an **explainer** for $y\in F^n$ at threshold $A$ and degree bound $K$ if every $P$ with $\deg P<K$ and $|\{i:P(\alpha_i)=y_i\}|\ge A$ satisfies $Q(X,P,P^{[1]},\dots,P^{[d]})\equiv0$.
--
--   **Definition 3.10.** A nonzero $Q\in F[X,Z,Y_0,\dots,Y_d]$ is a **symbolic explainer** for the received curve $w(Z)$ if for every $z\in F$ and $\deg P<K$, $|S_z(P)|\ge A$ implies $Q(X,z,P,P^{[1]},\dots,P^{[d]})\equiv0$.
--
--   **First-order support (19).**
--   $$\mathcal V_{m,B_\partial,B_{\mathrm{jet}}}=\mathrm{span}_F\{X^xY_0^aY_1^b:\ b\le B_\partial,\ a+b\le B_{\mathrm{jet}},\ x+D(a+b)<mA\}.$$
--   The *total jet degree* of $Q$ is its total degree in $Y_0,\dots,Y_d$; *translations in $X$ and $Y_0$* are $Q\mapsto Q(X+a,Y_0+b,Y_1,\dots)$.
--
--   **Formalization Note.** Variables of $F[X,Y_0,\dots,Y_d]$ are `Option (Fin (d+1))` (`none` $=X$), the convention of the reused `RSListDecodingCapacity.AllRates.hasseJetEval`. $D$ and $A$ are explicit arguments of `firstOrderSupport`.
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), pp. 17–21, Definitions 3.4, 3.6, 3.8, 3.10 and (19)

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Decoding
import Definitions.Def_RSBeyondJohnson_FirstOrder_Agreement

open Polynomial

namespace RSBeyondJohnson.FirstOrder

/-!
# Hidden-derivative interpolation: local constraints, explainers, the first-order support

Dao, Kominers, Thaler, *Reed–Solomon Codes Beyond Johnson*, STOC 2027 submission (manuscript of
November 2, 2026), §3.2–3.4, pp. 17–21: Definition 3.4 (Hasse derivative), Definition 3.6 ((10)–(11)),
Definition 3.8, Definition 3.10, the first-order support (19).

**Variables.** `F[X, Y₀, …, Y_d]` is `MvPolynomial (Option (Fin (d + 1))) F`: `none` is `X` and
`some j` is `Y_j` (the convention of the reused definition
`RSListDecodingCapacity.AllRates.hasseJetEval`, whose `hasseJetEval d Q P` is
`Q(X, P, P^[1], …, P^[d])` with Mathlib's Hasse derivatives `Polynomial.hasseDeriv`, valid in
every characteristic). A polynomial in `F[X, Z, Y₀, …, Y_d]` is a polynomial in the challenge
variable `Z` with coefficients in `F[X, Y₀, …, Y_d]`, i.e. an element of
`(MvPolynomial (Option (Fin (d + 1))) F)[X]` (the outer `Polynomial.X` is `Z`). Its
specialization `Q(X, z, Y)` at `z ∈ F` is `Q.eval (MvPolynomial.C z)`. "Q ∈ F[Z] ⊗_F 𝒬" for a
subspace `𝒬 ⊆ F[X, Y]` means every `Z`-coefficient of `Q` lies in `𝒬`.

**Degrees.** The total jet degree of `Q ∈ F[X, Y₀, …, Y_d]` is its total degree in
`Y₀, …, Y_d` (`X` has weight `0`); the `Y₁`-degree is `MvPolynomial.degreeOf (some 1)`; the
challenge degree of a polynomial in `Z` is `Polynomial.natDegree`.
-/

/-- The specialization `Q(X, z, Y₀, …, Y_d)` of `Q ∈ F[X, Z, Y₀, …, Y_d]` at the challenge `z`. -/
noncomputable def specZ {F : Type*} [Field F] {d : ℕ}
    (Q : (MvPolynomial (Option (Fin (d + 1))) F)[X]) (z : F) :
    MvPolynomial (Option (Fin (d + 1))) F :=
  Q.eval (MvPolynomial.C z)

/-- The total jet degree of `Q ∈ F[X, Y₀, …, Y_d]`: its total degree in `Y₀, …, Y_d`. -/
noncomputable def jetDegree {F : Type*} [Field F] {d : ℕ} (Q : MvPolynomial (Option (Fin (d + 1))) F) : ℕ :=
  Q.weightedTotalDegree (fun v : Option (Fin (d + 1)) => if v = none then 0 else 1)

/-- The substitution of Definition 3.6 ((10), p. 18), into `F[T, V, Y₁, …, Y_d]`, written as
polynomials in `T` (`Polynomial.X`) over `MvPolynomial (Option (Fin d)) F`, where `none` is `V`
and `some j` is `Y_{j+1}`:
`X ↦ α + T`, `Y₀ ↦ y + B_d(T, Y) + T^{d+1} V` with `B_d(T, Y) = ∑_{j=1}^{d} (−1)^{j+1} T^j Y_j`
(an empty sum is zero), and `Y_j ↦ Y_j` for `1 ≤ j ≤ d`. -/
noncomputable def localSubst {F : Type*} [Field F] (d : ℕ) (α y : F) :
    Option (Fin (d + 1)) → (MvPolynomial (Option (Fin d)) F)[X] :=
  fun v => match v with
    | none => Polynomial.C (MvPolynomial.C α) + Polynomial.X
    | some j =>
      if h : (j : ℕ) = 0 then
        Polynomial.C (MvPolynomial.C y) +
          (∑ i : Fin d, Polynomial.C ((-1 : MvPolynomial (Option (Fin d)) F) ^ ((i : ℕ) + 2) *
              MvPolynomial.X (some i)) * Polynomial.X ^ ((i : ℕ) + 1)) +
          Polynomial.X ^ (d + 1) * Polynomial.C (MvPolynomial.X none)
      else Polynomial.C (MvPolynomial.X (some ⟨(j : ℕ) - 1, by omega⟩))

/-- **Definition 3.6 (Local hidden-derivative constraints)**, (10), p. 18, as a linear map:
`Φ^{d,m}_{α,y}(Q) = Q(α + T, y + B_d(T, Y) + T^{d+1} V, Y₁, …, Y_d) (mod T^m)`, recorded by its
coefficients of `T^0, …, T^{m−1}` (each a polynomial in `V, Y₁, …, Y_d`); this is the image in
`F[T, V, Y₁, …, Y_d]/(T^m)`. The constraints (11) are `Φ^{d,m}_{α,y}(Q) = 0`. -/
noncomputable def localConstraintMap {F : Type*} [Field F] (d m : ℕ) (α y : F) :
    MvPolynomial (Option (Fin (d + 1))) F →ₗ[F] (Fin m → MvPolynomial (Option (Fin d)) F) :=
  LinearMap.pi fun i : Fin m =>
    ((Polynomial.lcoeff (MvPolynomial (Option (Fin d)) F) (i : ℕ)).restrictScalars F).comp
      (MvPolynomial.aeval (localSubst d α y)).toLinearMap

/-- **Definition 3.8 (Hidden-derivative explainer)**, p. 18: a nonzero `Q ∈ F[X, Y₀, …, Y_d]`
such that every `P ∈ F[X]` with `deg P < K` and `|{i : P(α_i) = y_i}| ≥ A` satisfies
`Q(X, P, P^[1], …, P^[d]) ≡ 0`. (The definition's context fixes distinct points, `K ≥ 1` and
`1 ≤ A ≤ n`; these are hypotheses of the theorems that use it.) -/
def IsExplainer {F : Type*} [Field F] {n : ℕ} (α y : Fin n → F) (K A d : ℕ)
    (Q : MvPolynomial (Option (Fin (d + 1))) F) : Prop :=
  Q ≠ 0 ∧ ∀ P : F[X], P.degree < (K : WithBot ℕ) →
    A ≤ RSListDecodingCapacity.AllRates.agreement α y P →
      RSListDecodingCapacity.AllRates.hasseJetEval d Q P = 0

/-- **Definition 3.10 (Symbolic explainer for a received curve)**, p. 19: a nonzero
`Q ∈ F[X, Z, Y₀, …, Y_d]` such that for every `z ∈ F` and every `P ∈ F[X]` with `deg P < K`,
`|S_z(P)| ≥ A` implies `Q(X, z, P, P^[1], …, P^[d]) ≡ 0`. The line `f + Z g` is
`w = lineCurve f g`. -/
def IsSymbolicExplainer {F : Type*} [Field F] {n ℓ : ℕ} (α : Fin n → F)
    (w : Fin (ℓ + 1) → Fin n → F) (K A d : ℕ) (Q : (MvPolynomial (Option (Fin (d + 1))) F)[X]) :
    Prop :=
  Q ≠ 0 ∧ ∀ z : F, ∀ P : F[X], P.degree < (K : WithBot ℕ) → A ≤ (agrSet α w z P).card →
    RSListDecodingCapacity.AllRates.hasseJetEval d (specZ Q z) P = 0

/-- The translation `Q(X, Y₀, Y₁, …, Y_d) ↦ Q(X + a, Y₀ + b, Y₁, …, Y_d)` ("translations in `X` and
`Y₀`", Proposition 3.13 and Lemma 3.14). -/
noncomputable def translateXY0 {F : Type*} [Field F] (d : ℕ) (a b : F) :
    MvPolynomial (Option (Fin (d + 1))) F →ₐ[F] MvPolynomial (Option (Fin (d + 1))) F :=
  MvPolynomial.aeval fun v => match v with
    | none => MvPolynomial.X none + MvPolynomial.C a
    | some j => if (j : ℕ) = 0 then MvPolynomial.X (some j) + MvPolynomial.C b
                else MvPolynomial.X (some j)

/-- The exponent set of the first-order support (19), p. 21: monomials `X^x Y₀^a Y₁^b`
(`x = s none`, `a = s (some 0)`, `b = s (some 1)`) with `b ≤ B∂`, `a + b ≤ B_jet` and
`x + D(a + b) < mA`. -/
def firstOrderExponents (m Bd Bjet D A : ℕ) : Set (Option (Fin 2) →₀ ℕ) :=
  {s | s (some 1) ≤ Bd ∧ s (some 0) + s (some 1) ≤ Bjet ∧
    s none + D * (s (some 0) + s (some 1)) < m * A}

/-- **The first-order support** (19), p. 21:
`V_{m,B∂,B_jet} = span_F {X^x Y₀^a Y₁^b : b ≤ B∂, a + b ≤ B_jet, x + D(a + b) < mA}` in
`F[X, Y₀, Y₁]`. In the paper `D = K − 1` with `K = max{k, 2}`; `D` and `A` are explicit
arguments here. -/
noncomputable def firstOrderSupport (F : Type*) [Field F] (m Bd Bjet D A : ℕ) :
    Submodule F (MvPolynomial (Option (Fin 2)) F) :=
  MvPolynomial.restrictSupport F (firstOrderExponents m Bd Bjet D A)

end RSBeyondJohnson.FirstOrder


