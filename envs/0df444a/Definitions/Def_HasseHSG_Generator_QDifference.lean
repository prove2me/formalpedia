-- Prove2me | Definitions.Def_HasseHSG_Generator_QDifference
-- name    : HasseHSG_Generator_QDifference
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:34:55.281888+00:00
-- url     : https://prove2.me/theorems/11d136a1-5718-4aad-8380-feeb2079e8e6
-- title:
--   The difference field $(L,\sigma_q)$, the shifts $c_i$, $Q_d$ and the operator $D_{q,d}$ (§4, §5.3, Eqs. (4)–(11))
-- statement:
--   Let $F$ be a field, $a_1,\dots,a_n\in F$, and let $q$ be transcendental over $F$. Consider the chain (Eq. (4))
--
--   $$F(q)\subset F(q)(t)\subset B:=F(q)(t)[x_1,\dots,x_n]\subset L:=\operatorname{Frac}(B).$$
--
--   1. The **$q$-integer** is $[m]_q=1+q+\dots+q^{m-1}$.
--   2. The substitution $g(t)\mapsto g(qt)$ acts on $F(q)(t)$.
--   3. The **shifts** are $c_i(t)=(q-1)t\,\dfrac{a_i}{1-a_it}\in F(q)(t)$ (Eq. (6)).
--   4. The map $\sigma_q:B\to B$ is $f(t,x_1,\dots,x_n)\mapsto f(qt,\,x_1+c_1(t),\dots,x_n+c_n(t))$ (Eq. (7)). It is an $F(q)$-algebra automorphism of $B$ and extends to $L$ by $\sigma_q(u/v)=\sigma_q(u)/\sigma_q(v)$.
--   5. With $Q_d(t)=\prod_{i=1}^n(1-a_it)^d$, the operator is
--   $$D_{q,d}=Q_d(t)\,\tilde D_q,\qquad \tilde D_q=\frac{\sigma_q-\mathrm{id}}{qt-t}$$
--   (Eqs. (8), (11)). It is defined on $B$ and, by the same formula, on $L$ (Remark 5.1).
--   6. On $F(q)[t,x]$, $D_{q,d}(f)$ is the polynomial equal to $Q_d\tilde D_q f$ (Lemma 5.2 shows it is a polynomial when $\deg_x f\le d$).
--   7. The degrees used later: $\deg_t f$ is the largest $t$-degree of a coefficient of $f\in R[t][x]$; $\deg_q f$ is the largest $q$-degree of a coefficient of $f\in F[q][t][x]$.
--
--   The operator $D_{q,d}$ replaces the derivation of the characteristic-zero construction. Unlike a derivation, it does not kill $p$-th powers in characteristic $p$.
--
--   **Formalization Note.** $F(q)$ is `RatFunc F` with $q$ = `RatFunc.X`, and $F(q)(t)$ is `RatFunc (RatFunc F)` with $t$ = `RatFunc.X`. $B$ is `MvPolynomial (Fin n) (F(q)(t))` and $L$ is `FractionRing B`. $F(q)[t,x]$ is `MvPolynomial (Fin n) (Polynomial (RatFunc F))`, and $F[q][t,x]$ is `MvPolynomial (Fin n) (Polynomial (Polynomial F))`, with outer variable $t$ and inner variable $q$.
--
--   - `sigmaT` evaluates the reduced numerator and denominator at $qt$.
--   - `sigmaB` substitutes into each monomial.
--   - `sigmaL` applies `sigmaB` to a chosen representative $u/v$ (`IsLocalization.sec`). The value does not depend on the representative, because $\sigma_q$ is an injective ring endomorphism of $B$.
--   - `DqdPoly` is the polynomial $g$ with $g=Q_d\tilde D_q f$ in $B$ when one exists. If no polynomial representative exists, it takes the placeholder value $0$. A polynomial representative can also exist outside the degree-bounded domain; in that case it is returned.
--   - `embFqL`, `embFxL`, `embFqxL`, `embFqTL`, `embFQTL` are the inclusions of $F(q)$, $F[x]$, $F(q)[x]$, $F(q)[t]$ and $F[q][t]$ into $L$.
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), p. 15 (§4: q-integers, fixed field); pp. 19–21, §5.3, Eqs. (4)–(11), Remark 5.1

import Mathlib

open MvPolynomial

namespace HasseHSG.Generator

/-!
Bal, Ghosh, *Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary
Characteristic Fields*, §4 (p. 15) and §5.3 (pp. 19–21), Eqs. (4)–(11), Remark 5.1.

Notation (Eq. (4)): `F(q) = RatFunc F` with `q = RatFunc.X` transcendental over `F`;
`F(q)(t) = RatFunc (RatFunc F)` with `t = RatFunc.X`; `B = F(q)(t)[x₁, …, xₙ]`;
`L = Frac(B)`. The ring `F(q)[t, x]` is `MvPolynomial (Fin n) (F(q)[t])` and `F[q][t, x]` is
`MvPolynomial (Fin n) ((F[q])[t])` (outer polynomial variable `t`, inner `q`). The points
`a₁, …, aₙ ∈ F` are a function `a : Fin n → F`.
-/

/-- The `q`-integer `[m]_q = 1 + q + ⋯ + q^{m-1}` (p. 15), in any semiring. -/
def qInt {R : Type*} [Semiring R] (q : R) (m : ℕ) : R :=
  ∑ i ∈ Finset.range m, q ^ i

/-- `F(q)`: rational functions in a transcendental `q` over `F`. -/
abbrev Fq (F : Type*) [Field F] := RatFunc F

/-- `F(q)(t)`. -/
abbrev Fqt (F : Type*) [Field F] := RatFunc (RatFunc F)

/-- `B = F(q)(t)[x₁, …, xₙ]` (Eq. (4)). -/
abbrev BRing (F : Type*) [Field F] (n : ℕ) := MvPolynomial (Fin n) (Fqt F)

/-- `L = Frac(B)` (Eq. (4)). -/
abbrev LField (F : Type*) [Field F] (n : ℕ) := FractionRing (BRing F n)

/-- `F(q)[t, x₁, …, xₙ]`. -/
abbrev PolyQT (F : Type*) [Field F] (n : ℕ) := MvPolynomial (Fin n) (Polynomial (Fq F))

/-- `F[q][t, x₁, …, xₙ]` (outer polynomial variable `t`, inner `q`). -/
abbrev PolyQTInt (F : Type*) [Field F] (n : ℕ) := MvPolynomial (Fin n) (Polynomial (Polynomial F))

/-- The transcendental `q ∈ F(q)`. -/
noncomputable abbrev qVar (F : Type*) [Field F] : Fq F := RatFunc.X

/-- The variable `t ∈ F(q)(t)`. -/
noncomputable abbrev tVar (F : Type*) [Field F] : Fqt F := RatFunc.X

/-- An element of `F(q)` viewed as a constant of `F(q)(t)`. -/
noncomputable abbrev cK {F : Type*} [Field F] (x : Fq F) : Fqt F := algebraMap (Fq F) (Fqt F) x

/-- An element of `F` viewed in `F(q)`. -/
noncomputable abbrev cF {F : Type*} [Field F] (x : F) : Fq F := algebraMap F (Fq F) x

/-- The substitution `g(t) ↦ g(qt)` on `F(q)(t)` (p. 19): numerator and denominator are evaluated
at `q·t`. -/
noncomputable def sigmaT {F : Type*} [Field F] (g : Fqt F) : Fqt F :=
  RatFunc.eval (algebraMap (Fq F) (Fqt F)) (cK (qVar F) * tVar F) g

/-- The shift `cᵢ(t) = (q − 1) t · aᵢ / (1 − aᵢ t) ∈ F(q)(t)` (Eq. (6)). -/
noncomputable def cShift {F : Type*} [Field F] {n : ℕ} (a : Fin n → F) (i : Fin n) : Fqt F :=
  (cK (qVar F) - 1) * tVar F * cK (cF (a i)) / (1 - cK (cF (a i)) * tVar F)

/-- `σ_q : B → B`, `f(t, x₁, …, xₙ) ↦ f(qt, x₁ + c₁(t), …, xₙ + cₙ(t))` (Eq. (7)): the
coefficients (elements of `F(q)(t)`) are mapped by `t ↦ qt` and `xᵢ` is replaced by `xᵢ + cᵢ(t)`. -/
noncomputable def sigmaB {F : Type*} [Field F] {n : ℕ} (a : Fin n → F) (f : BRing F n) :
    BRing F n :=
  ∑ m ∈ f.support, C (sigmaT (f.coeff m)) * ∏ i, (X i + C (cShift a i)) ^ (m i)

/-- `Q_d(t) = ∏ᵢ (1 − aᵢ t)^d` as a polynomial in `t` over `F(q)` (Eq. (11)). -/
noncomputable def QdPoly {F : Type*} [Field F] {n : ℕ} (a : Fin n → F) (d : ℕ) :
    Polynomial (Fq F) :=
  ∏ i, (1 - Polynomial.C (cF (a i)) * Polynomial.X) ^ d

/-- `Q_d(t) ∈ F(q)(t)`. -/
noncomputable def Qd {F : Type*} [Field F] {n : ℕ} (a : Fin n → F) (d : ℕ) : Fqt F :=
  algebraMap (Polynomial (Fq F)) (Fqt F) (QdPoly a d)

/-- `D_{q,d} = Q_d(t) · D̃_q` on `B`, where `D̃_q f = (σ_q f − f) / (qt − t)` (Eqs. (8), (9), (11)). -/
noncomputable def DqdB {F : Type*} [Field F] {n : ℕ} (a : Fin n → F) (d : ℕ) (f : BRing F n) :
    BRing F n :=
  C (Qd a d / ((cK (qVar F) - 1) * tVar F)) * (sigmaB a f - f)

/-- The inclusion `F(q)[t, x] ⊆ B`. -/
noncomputable def embedPoly {F : Type*} [Field F] {n : ℕ} : PolyQT F n →+* BRing F n :=
  MvPolynomial.map (algebraMap (Polynomial (Fq F)) (Fqt F))

/-- The inclusion `F[q][t, x] ⊆ F(q)[t, x]`. -/
noncomputable def embedInt {F : Type*} [Field F] {n : ℕ} : PolyQTInt F n →+* PolyQT F n :=
  MvPolynomial.map (Polynomial.mapRingHom (algebraMap (Polynomial F) (Fq F)))

/-- `D_{q,d}` on `F(q)[t, x]` (Eq. (11)): the polynomial `g` with `g = Q_d(t) D̃_q(f)` in `B`.
Lemma 5.2 states that it exists whenever `deg_x f ≤ d` (the domain of Eq. (11)).
If no polynomial representative exists, the value is `0`; when a representative exists even
outside that domain, it is returned. Uniqueness follows from injectivity of `F(q)[t, x] → B`. -/
noncomputable def DqdPoly {F : Type*} [Field F] {n : ℕ} (a : Fin n → F) (d : ℕ)
    (f : PolyQT F n) : PolyQT F n :=
  open Classical in
  if h : ∃ g : PolyQT F n, embedPoly g = DqdB a d (embedPoly f) then h.choose else 0

/-- `deg_t f` for `f ∈ R[t][x₁, …, xₙ]`: the largest `t`-degree of a coefficient (`0` for `f = 0`). -/
noncomputable def degT {R : Type*} [CommSemiring R] {n : ℕ} (f : MvPolynomial (Fin n) (Polynomial R)) :
    ℕ :=
  f.support.sup fun m => (f.coeff m).natDegree

/-- `deg_q f` for `f ∈ F[q][t][x₁, …, xₙ]`: the largest `q`-degree of a coefficient of a monomial
`t^j x^m` (`0` for `f = 0`). -/
noncomputable def degQ {F : Type*} [Field F] {n : ℕ} (f : PolyQTInt F n) : ℕ :=
  f.support.sup fun m => (f.coeff m).support.sup fun j => ((f.coeff m).coeff j).natDegree

/-- `σ_q` extended to `L = Frac(B)` (p. 20): `σ_q(u / v) = σ_q(u) / σ_q(v)`, computed on a chosen
representative `h = u / v` (`IsLocalization.sec`); `σ_q` is an injective ring endomorphism of `B`,
so the value does not depend on the representative. -/
noncomputable def sigmaL {F : Type*} [Field F] {n : ℕ} (a : Fin n → F) (h : LField F n) :
    LField F n :=
  algebraMap (BRing F n) (LField F n)
      (sigmaB a (IsLocalization.sec (nonZeroDivisors (BRing F n)) h).1) /
    algebraMap (BRing F n) (LField F n)
      (sigmaB a ((IsLocalization.sec (nonZeroDivisors (BRing F n)) h).2 : BRing F n))

/-- `F(q)(t) ⊆ L`. -/
noncomputable def embFqtL {F : Type*} [Field F] {n : ℕ} : Fqt F →+* LField F n :=
  (algebraMap (BRing F n) (LField F n)).comp MvPolynomial.C

/-- `F(q) ⊆ L`. -/
noncomputable def embFqL {F : Type*} [Field F] {n : ℕ} : Fq F →+* LField F n :=
  embFqtL.comp (algebraMap (Fq F) (Fqt F))

/-- `D_{q,d} = Q_d(t) (σ_q − id) / ((q − 1) t)` on `L` (Remark 5.1). -/
noncomputable def DqdL {F : Type*} [Field F] {n : ℕ} (a : Fin n → F) (d : ℕ) (h : LField F n) :
    LField F n :=
  embFqtL (Qd a d / ((cK (qVar F) - 1) * tVar F)) * (sigmaL a h - h)

/-- `F(q)[x₁, …, xₙ] ⊆ B` (coefficients as constants in `t`). -/
noncomputable def embFqxB {F : Type*} [Field F] {n : ℕ} :
    MvPolynomial (Fin n) (Fq F) →+* BRing F n :=
  MvPolynomial.map (algebraMap (Fq F) (Fqt F))

/-- `F(q)[x₁, …, xₙ] ⊆ L`. -/
noncomputable def embFqxL {F : Type*} [Field F] {n : ℕ} :
    MvPolynomial (Fin n) (Fq F) →+* LField F n :=
  (algebraMap (BRing F n) (LField F n)).comp embFqxB

/-- `F[x₁, …, xₙ] ⊆ L`. -/
noncomputable def embFxL {F : Type*} [Field F] {n : ℕ} : MvPolynomial (Fin n) F →+* LField F n :=
  embFqxL.comp (MvPolynomial.map (algebraMap F (Fq F)))

/-- `F(q)[t] ⊆ L`. -/
noncomputable def embFqTL {F : Type*} [Field F] {n : ℕ} : Polynomial (Fq F) →+* LField F n :=
  embFqtL.comp (algebraMap (Polynomial (Fq F)) (Fqt F))

/-- `F[q][t] ⊆ L` (outer polynomial variable `t`, inner `q`). -/
noncomputable def embFQTL {F : Type*} [Field F] {n : ℕ} :
    Polynomial (Polynomial F) →+* LField F n :=
  embFqTL.comp (Polynomial.mapRingHom (algebraMap (Polynomial F) (Fq F)))

end HasseHSG.Generator


