-- Prove2me | Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression
-- name    : PrivateAgnosticHalfspace_Gaussian_Regression
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T11:23:43.462351+00:00
-- url     : https://prove2.me/theorems/044e114c-9f8c-4854-87e6-721f965f3fb1
-- title:
--   Absolute-loss regression, convex oracles and polynomial spaces
-- statement:
--   Let $\phi:X\to\mathbb R^D$ be a measurable feature map, let $P$ be a law of examples $(X,Y)$ with $Y\in\{-1,1\}$, and let $S$ be a sample of size $n$. The absolute regression risks and one-sided uniform deviation are
--   $$
--   L_P(v)=\mathbb E_P|\langle v,\phi(X)\rangle-Y|,\qquad
--   \widehat L_S(v)=\frac1n\sum_i|\langle v,\phi(X_i)\rangle-Y_i|,\qquad
--   \Delta(S)=\sup_{\|v\|_2\le R}(L_P(v)-\widehat L_S(v)).
--   $$
--   For a general public convex loss $\ell(v;z)$, the empirical minimum is the infimum of its empirical average over the specified compact nonempty feasible set. A subgradient oracle satisfies the defining supporting inequality for every evaluation point; a projection oracle returns a nearest feasible point. Their validity is asserted by the ERM theorem, not stored as assumed optimization or privacy guarantees.
--
--   The degree-$p$ polynomial space consists of actual multivariate real polynomial functions of total degree at most $p$. Its Hermite-coordinate predictor is $q_v(x)=\langle v,\psi_p(x)\rangle$.
--
--   These interfaces isolate the general regression objects from the clipped Gaussian learner. Finite moments, bounded suprema and attained compact minima are verified in theorem conclusions wherever a total real integral or extremum is used.
-- source:
--   Giorgio Racca, Amartya Sanyal, Vikrant Singhal, STOC 2027 submission #1006 (October 2026), p. 21–23, 26, Lemmas B.4, B.7, B.8, B.10 and Eq. (15); canonical PDF sha256 f0122a33e29daa624b530bdd0b071998d8e44197b30449b0cb3213289645cec7

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Computation

open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option autoImplicit false

namespace PrivateAgnosticHalfspace.Gaussian

noncomputable def risk {X : Type*} [MeasurableSpace X] (D : ℕ)
    (φ : X → Vec D) (P : Measure (X × Bool)) (v : Vec D) : ℝ :=
  ∫ z, |inner ℝ v (φ z.1) - label z.2| ∂P
noncomputable def empiricalRisk {X : Type*} (D : ℕ) {n : ℕ}
    (φ : X → Vec D) (S : Fin n → X × Bool) (v : Vec D) : ℝ :=
  (∑ i, |inner ℝ v (φ (S i).1) - label (S i).2|) / n
noncomputable def deviation {X : Type*} [MeasurableSpace X] (D : ℕ) {n : ℕ}
    (φ : X → Vec D) (P : Measure (X × Bool)) (R : ℝ) (S : Fin n → X × Bool) : ℝ :=
  sSup ((fun v => risk D φ P v - empiricalRisk D φ S v) '' Metric.closedBall 0 R)
noncomputable def generalEmpiricalLoss {Z : Type*} (D : ℕ) {n : ℕ}
    (ℓ : Vec D → Z → ℝ) (S : Fin n → Z) (v : Vec D) : ℝ :=
  (∑ i, ℓ v (S i)) / n
noncomputable def empiricalMinimum {Z : Type*} (D : ℕ) {n : ℕ}
    (ℓ : Vec D → Z → ℝ) (S : Fin n → Z) (Ω : Set (Vec D)) : ℝ :=
  sInf (generalEmpiricalLoss D ℓ S '' Ω)

def IsSubgradient {Z : Type*} (D : ℕ) (ℓ : Vec D → Z → ℝ)
    (g : Z → Vec D → Vec D) : Prop :=
  ∀ z v w, ℓ v z + inner ℝ (g z v) (w - v) ≤ ℓ w z

def IsProjection (D : ℕ) (Ω : Set (Vec D)) (π : Vec D → Vec D) : Prop :=
  ∀ v, π v ∈ Ω ∧ ∀ w ∈ Ω, ‖π v - v‖ ≤ ‖w - v‖

/-- Public optimizer input; raw sample values enter only through indexed subgradient calls. -/
noncomputable def ermInput (D n : ℕ) (ε δ R T : ℝ) (x₀ : Vec D) (i : ℕ) : ℝ :=
  if h : i < 6 then (![ (D : ℝ), n, ε, δ, R, T ] : Fin 6 → ℝ) ⟨i, h⟩
  else if h : i - 6 < D then x₀ ⟨i - 6, h⟩ else 0
noncomputable def sampleOracle {Z : Type*} (D : ℕ) {n : ℕ}
    (g : Z → Vec D → Vec D) (π : Vec D → Vec D) (S : Fin n → Z) : Oracle D :=
  ⟨fun i v => if h : i < n then g (S ⟨i, h⟩) v else 0, π⟩

/-- Source polynomial space, as actual pointwise real functions, rather than a hypothesis
asserting that a supplied feature map is already a basis. -/
def polynomialFunctions (d p : ℕ) : Set (Vec d → ℝ) :=
  {f | ∃ Q : MvPolynomial (Fin d) ℝ, Q.totalDegree ≤ p ∧
    ∀ x, f x = MvPolynomial.eval (fun i => x i) Q}
noncomputable def polynomialPredictor (d p : ℕ) (w : Coeff d p) (x : Vec d) : ℝ :=
  inner ℝ w (features d p x)

end PrivateAgnosticHalfspace.Gaussian


