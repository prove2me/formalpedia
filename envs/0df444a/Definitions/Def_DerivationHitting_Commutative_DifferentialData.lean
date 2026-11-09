-- Prove2me | Definitions.Def_DerivationHitting_Commutative_DifferentialData
-- name    : DerivationHitting_Commutative_DifferentialData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:00.430236+00:00
-- url     : https://prove2.me/theorems/4103ee9e-d284-4815-af2e-c99aabc4802f
-- title:
--   Rational derivations, associated evaluation, and the D-Wronskian
-- statement:
--   Let $F$ be a field, $R=F(t)[x_1,\ldots,x_n]$, and $b_1,\ldots,b_n\in F(t)$. Differentiate rational functions by the quotient rule on their canonical numerator and nonzero denominator, and apply that derivative coefficientwise to elements of $R$. Define
--   $$
--    D_b h=\partial_t h+\sum_{i=1}^n b_i(t)\partial_{x_i}h,\qquad b_i^{\log}(t)=\frac{i}{1+it}.
--   $$
--   Trivial constants means $D_bh=0$ if and only if $h$ is the image of a scalar in $F$.
--
--   For a tuple $P_i\in F[[t]]$, the associated evaluation $\Phi_P:R\to F((t))$ uses the canonical rational-function embedding on coefficients and substitutes $P_i$ for $x_i$. The compatibility condition says that $P_i'=b_i$ inside $F((t))$; it does not assume injectivity.
--
--   For $t$-free polynomials $g_1,\ldots,g_q\in F[x_1,\ldots,x_n]$, first extend their coefficients to $F(t)$ and define the determinant
--   $$
--    W_{D_b}(g_1,\ldots,g_q)=\det\bigl(D_b^m g_j\bigr)_{0\le m<q,\ 1\le j\le q}.
--   $$
--   These are the concrete operators and maps used by §§2–4. The operator is $F$-linear, not $F(t)$-linear. No property to be proved in a milestone is bundled into the data.
--
--   **Formalization Note** An empty Wronskian has determinant $1$. Canonical rational denominators are nonzero; none of the definitions evaluates a rational function at a pole.
-- source:
--   Shubham Bhardwaj, Foram Lakhani, Partha Mukhopadhyay, Ramprasad Saptharishi, Pratik Shastri, Amit Sinhababu, STOC 2027 submission #577 (October 2026), pp. 10–12, Definition 2.1, associated map (2.2), §2.1 concrete derivation, and §3 displayed D-Wronskian; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/577.pdf

import Definitions.Def_DerivationHitting_Commutative_PolynomialData
open scoped RatFunc

namespace DerivationHitting.Commutative
noncomputable section

/-- Formal rational derivative by the quotient rule on canonical numerator and denominator.
`RatFunc.denom_ne_zero` guarantees that this denominator never vanishes as a polynomial. -/
def rationalDerivative {F : Type*} [Field F] (a : RatFunc F) : RatFunc F :=
  algebraMap (Polynomial F) (RatFunc F)
    (a.num.derivative * a.denom - a.num * a.denom.derivative) /
      (algebraMap (Polynomial F) (RatFunc F) a.denom) ^ 2

/-- Differentiate each rational coefficient, holding all x variables fixed. -/
def timeDerivative {F : Type*} [Field F] {n : ℕ}
    (h : MvPolynomial (Fin n) (RatFunc F)) : MvPolynomial (Fin n) (RatFunc F) :=
  ∑ m ∈ h.support, MvPolynomial.monomial m (rationalDerivative (MvPolynomial.coeff m h))

/-- Definition 2.1: an F-linear operator; it is not F(t)-linear. -/
def linearDerivation {F : Type*} [Field F] {n : ℕ}
    (b : Fin n → RatFunc F) (h : MvPolynomial (Fin n) (RatFunc F)) :
    MvPolynomial (Fin n) (RatFunc F) :=
  timeDerivative h + ∑ i, MvPolynomial.C (b i) * MvPolynomial.pderiv i h

/-- The concrete kernels i/(1+it) with the paper's one-based indices. -/
def logarithmKernel {F : Type*} [Field F] {n : ℕ} (i : Fin n) : RatFunc F :=
  algebraMap F (RatFunc F) ((i.val + 1 : ℕ) : F) /
    (1 + algebraMap F (RatFunc F) ((i.val + 1 : ℕ) : F) * RatFunc.X)

/-- Trivial ring of constants means exactly the embedded base field, in both directions. -/
def hasTrivialConstants {F : Type*} [Field F] {n : ℕ}
    (b : Fin n → RatFunc F) : Prop :=
  ∀ h : MvPolynomial (Fin n) (RatFunc F),
    linearDerivation b h = 0 ↔ ∃ c : F, h = MvPolynomial.C (algebraMap F (RatFunc F) c)

/-- The actual associated evaluation, with the canonical F(t) → F((t)) embedding. -/
def associatedEvaluation {F : Type*} [Field F] {n : ℕ}
    (P : Fin n → PowerSeries F) :
    MvPolynomial (Fin n) (RatFunc F) →+* LaurentSeries F :=
  MvPolynomial.eval₂Hom (algebraMap (RatFunc F) (LaurentSeries F))
    (fun i => algebraMap (PowerSeries F) (LaurentSeries F) (P i))

/-- The primitive compatibility required in §2, interpreted inside Laurent series. -/
def arePrimitives {F : Type*} [Field F] {n : ℕ}
    (b : Fin n → RatFunc F) (P : Fin n → PowerSeries F) : Prop :=
  ∀ i, algebraMap (PowerSeries F) (LaurentSeries F) (PowerSeries.derivative F (P i)) =
    algebraMap (RatFunc F) (LaurentSeries F) (b i)

/-- Embed the t-free polynomials into F(t)[x]. -/
def rationalPolynomial {F : Type*} [Field F] {n : ℕ}
    (f : MvPolynomial (Fin n) F) : MvPolynomial (Fin n) (RatFunc F) :=
  MvPolynomial.map (algebraMap F (RatFunc F)) f

/-- Rows 0,…,q−1 are successive applications of D; this object is a determinant. -/
def derivationWronskian {F : Type*} [Field F] {n q : ℕ}
    (b : Fin n → RatFunc F) (g : Fin q → MvPolynomial (Fin n) F) :
    MvPolynomial (Fin n) (RatFunc F) :=
  Matrix.det (fun m j : Fin q =>
    (linearDerivation b)^[m.val] (rationalPolynomial (g j)))

end
end DerivationHitting.Commutative


