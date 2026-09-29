-- Prove2me | Definitions.Def_LinearOptimization_FinitelyGeneratedSet
-- name    : LinearOptimization_FinitelyGeneratedSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-05T20:47:43.999962+00:00
-- url     : https://prove2.me/theorems/9a93b178-d673-42d2-bc6d-44d96da91be4
-- title:
--   Finitely generated set
-- statement:
--   **(Eq. (4.6), p. 182)** A set $Q$ is said to be *finitely generated* if it is specified in the form
--
--   $$Q = \left\{\sum_{i=1}^{k} \lambda_i x^i + \sum_{j=1}^{r} \theta_j w^j \;\middle|\; \lambda_i \ge 0,\ \theta_j \ge 0,\ \sum_{i=1}^{k} \lambda_i = 1\right\},$$
--
--   where $x^1, \dots, x^k$ and $w^1, \dots, w^r$ are some given elements of $\mathbb{R}^n$.
--
--   (Equivalently, $Q$ is the image of the polyhedron $H = \{(\lambda_1, \dots, \lambda_k, \theta_1, \dots, \theta_r) \mid \sum_i \lambda_i = 1, \lambda_i \ge 0, \theta_j \ge 0\}$ under the linear mapping $(\lambda, \theta) \mapsto \sum_i \lambda_i x^i + \sum_j \theta_j w^j$, pp. 181-183.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Eq. (4.6), p. 182 (converse to the resolution theorem)

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
Finitely generated sets.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, **Eq. (4.6), p. 182** (converse to the resolution
theorem): "A set `Q` is said to be *finitely generated* if it is specified
in the form
`Q = {Σᵢ λᵢ xⁱ + Σⱼ θⱼ wʲ | λᵢ ≥ 0, θⱼ ≥ 0, Σᵢ λᵢ = 1}`,
where `x¹, …, xᵏ` and `w¹, …, wʳ` are some given elements of `ℝⁿ`."
(Equivalently — pp. 181–183 — `Q` is the image of the polyhedron
`H = {(λ, θ) | Σᵢ λᵢ = 1, λ ≥ 0, θ ≥ 0}` under the linear map
`(λ, θ) ↦ Σᵢ λᵢ xⁱ + Σⱼ θⱼ wʲ`.)
-/

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, Eq. (4.6) (p. 182).** The finitely generated set with generators
`x : Fin k → ℝⁿ` (convex-combination part) and `w : Fin r → ℝⁿ`
(conic part): all points `Σᵢ λᵢ • x i + Σⱼ θⱼ • w j` with `λ ≥ 0`,
`θ ≥ 0`, `Σᵢ λᵢ = 1`. -/
def finitelyGeneratedSet {n k r : ℕ} (x : Fin k → (Fin n → ℝ))
    (w : Fin r → (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y | ∃ (lam : Fin k → ℝ) (theta : Fin r → ℝ),
    (∀ i, 0 ≤ lam i) ∧ (∀ j, 0 ≤ theta j) ∧ (∑ i, lam i) = 1 ∧
    y = ∑ i, lam i • x i + ∑ j, theta j • w j}

/-- A set is finitely generated if it can be specified in the form of
Bertsimas & Tsitsiklis, Eq. (4.6) for some finite generator families. -/
def IsFinitelyGenerated {n : ℕ} (Q : Set (Fin n → ℝ)) : Prop :=
  ∃ (k r : ℕ) (x : Fin k → (Fin n → ℝ)) (w : Fin r → (Fin n → ℝ)),
    Q = finitelyGeneratedSet x w

end LinearOptimization


