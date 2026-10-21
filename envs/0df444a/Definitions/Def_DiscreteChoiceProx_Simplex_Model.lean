-- Prove2me | Definitions.Def_DiscreteChoiceProx_Simplex_Model
-- name    : DiscreteChoiceProx_Simplex_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:42.987955+00:00
-- url     : https://prove2.me/theorems/a922e670-8fb8-42cf-be79-66efb52b58df
-- title:
--   ARUM surplus, conjugate, simplex, norms, densities and matrix class
-- statement:
--   The model has $n\ge1$ alternatives, deterministic utilities $u\in\mathbb R^n$, and a probability law $\mu$ for the shock vector $\epsilon\in\mathbb R^n$. Assumption 1 means that every shock coordinate is integrable, the joint law is absolutely continuous with respect to Lebesgue measure, and every nonempty open set has positive probability.
--
--   The surplus and its unrestricted convex conjugate are
--
--   $$
--   E(u)=\mathbb E_\mu\bigl[\max_i(u_i+\epsilon_i)\bigr],\qquad E^*(p)=\sup_{u\in\mathbb R^n}\{\langle p,u\rangle-E(u)\}.
--   $$
--
--   The file also defines the simplex $\Delta$, the choice probability $P_i(u)$, coordinate gradient and Hessian, strong convexity in $\ell_1$, strong smoothness in $\ell_\infty$, the induced matrix norm $\|A\|_{\infty,1}$, the symmetric matrix class $\mathcal A$ with nonnegative diagonal, nonpositive off-diagonal and zero row sums, density versions $g_{ij}$ of $\epsilon_j-\epsilon_i$, and Theorem 2's ordered-pair parameter $\beta$.
--
--   These definitions fix the common model used by every target theorem.
--
--   **Formalization Note** The conjugate is extended-real valued. The choice event includes ties, null under Assumption 1. $\ell_1$ is an explicit coordinate sum; the default norm on coordinate functions is $\ell_\infty$.
-- source:
--   Müller, Nesterov, Shikhman, Discrete choice prox-functions on the simplex, arXiv:1909.05591v1, pp. 2–11, Definitions 1–3, Assumption 1, and §2.2.2

import Mathlib

open MeasureTheory

namespace DiscreteChoiceProx.Simplex

/-- The ordinary coordinate pairing on utility and probability vectors. -/
def pair {n : ℕ} (p u : Fin n → ℝ) : ℝ := ∑ i, p i * u i

/-- The `ℓ₁` norm, distinct from the default sup norm on `Fin n → ℝ`. -/
def norm1 {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, |x i|

/-- The probability simplex of alternatives. -/
abbrev simplex (n : ℕ) : Set (Fin n → ℝ) := stdSimplex ℝ (Fin n)

/-- Assumption 1: finite coordinate means, absolute continuity, and full support. -/
structure Assumption1 {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] : Prop where
  integrable : ∀ i, Integrable (fun e : Fin n → ℝ => e i) μ
  absCont : μ ≪ (volume : Measure (Fin n → ℝ))
  fullSupp : ∀ U : Set (Fin n → ℝ), IsOpen U → U.Nonempty → 0 < μ U

/-- `E(u)`, the expected maximum utility. -/
noncomputable def surplus {n : ℕ} [NeZero n] (μ : Measure (Fin n → ℝ))
    (u : Fin n → ℝ) : ℝ :=
  ∫ e, Finset.univ.sup' Finset.univ_nonempty (fun i => u i + e i) ∂μ

/-- `E*(p)`, the unrestricted Fenchel conjugate of the surplus. -/
noncomputable def conj {n : ℕ} [NeZero n] (μ : Measure (Fin n → ℝ))
    (p : Fin n → ℝ) : EReal :=
  ⨆ u : Fin n → ℝ, ((pair p u - surplus μ u : ℝ) : EReal)

/-- Probability that alternative `i` attains the maximum, including ties. -/
noncomputable def choiceProb {n : ℕ} (μ : Measure (Fin n → ℝ))
    (u : Fin n → ℝ) (i : Fin n) : ℝ :=
  (μ {e | ∀ k, u k + e k ≤ u i + e i}).toReal

/-- Coordinate partial derivative, formed from the Fréchet derivative. -/
noncomputable def grad {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (u : Fin n → ℝ) (i : Fin n) : ℝ :=
  fderiv ℝ f u (Pi.single i 1)

/-- The matrix of second coordinate partials. -/
noncomputable def hess {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ (fun w => grad f w j) u (Pi.single i 1)

/-- Definition 2: strong convexity on the simplex in the `ℓ₁` norm. -/
def IsStronglyConvexL1 {n : ℕ} (d : (Fin n → ℝ) → ℝ) (β : ℝ) : Prop :=
  ∀ p ∈ simplex n, ∀ q ∈ simplex n, ∀ a ∈ Set.Icc (0 : ℝ) 1,
    d (a • p + (1 - a) • q) ≤
      a * d p + (1 - a) * d q - β / 2 * a * (1 - a) * norm1 (p - q) ^ 2

/-- Definition 3: strong smoothness in the sup norm. -/
def IsStronglySmoothSup {n : ℕ} (f : (Fin n → ℝ) → ℝ) (L : ℝ) : Prop :=
  ∀ u v, f (u + v) ≤ f u + pair (grad f u) v + L / 2 * ‖v‖ ^ 2

/-- The induced matrix norm from `ℓ∞` to `ℓ₁`. -/
noncomputable def normInfOne {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup ((fun z => norm1 (A.mulVec z)) '' {z | ∀ i, |z i| ≤ 1})

/-- The symmetric matrix class `𝒜` from page 8. -/
def ClassA {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A.IsSymm ∧ (∀ i, 0 ≤ A i i) ∧ (∀ i j, i ≠ j → A i j ≤ 0) ∧
    (∀ i, ∑ j, A i j = 0)

/-- A fixed nonnegative measurable version of the density of `εⱼ − εᵢ`. -/
def IsDiffDensity {n : ℕ} (μ : Measure (Fin n → ℝ)) (i j : Fin n)
    (g : ℝ → ℝ) : Prop :=
  Measurable g ∧ (∀ z, 0 ≤ g z) ∧
    μ.map (fun e => e j - e i) = volume.withDensity (fun z => ENNReal.ofReal (g z))

/-- Theorem 2's parameter, summed over ordered distinct pairs. -/
noncomputable def beta {n : ℕ} (g : Fin n → Fin n → ℝ → ℝ)
    (zbar : Fin n → Fin n → ℝ) : ℝ :=
  1 / (2 * ∑ i, ∑ j ∈ Finset.univ.erase i, g i j (zbar i j))

end DiscreteChoiceProx.Simplex


