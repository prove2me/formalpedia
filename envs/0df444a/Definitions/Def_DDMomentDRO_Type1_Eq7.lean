-- Prove2me | Definitions.Def_DDMomentDRO_Type1_Eq7
-- name    : DDMomentDRO_Type1_Eq7
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:45:53.890868+00:00
-- url     : https://prove2.me/theorems/8a41caff-f193-4d9c-8c3a-a488becb9c32
-- title:
--   (6), (7), pp. 8–9 — the 2J+1 moment-constraint ambiguity set and the values of the joint program (7)
-- statement:
--   This file fixes the special Type 1 ambiguity set (6) of Yu and Shen and the joint program (7), on top of the stage data of `DDMomentDRO.Type1.Setting`.
--
--   For each uncertain parameter $j\in[J]$ let $\bar\mu_j,\bar\sigma_j$ be its empirical mean and standard deviation, $\epsilon^\mu_j$, $\underline\epsilon^S_j$, $\bar\epsilon^S_j$ the moment tolerances, and $\lambda^\mu_{ji},\lambda^S_{ji}$ the decision-dependence rates. The empirical moments depend affinely on the state $x$:
--   $$\mu_j(x)=\bar\mu_j\Big(1+\sum_{i=1}^I\lambda^\mu_{ji}x_i\Big),\qquad S_j(x)=(\bar\mu_j^2+\bar\sigma_j^2)\Big(1+\sum_{i=1}^I\lambda^S_{ji}x_i\Big).$$
--
--   **The ambiguity set (6).** $\mathcal P(x)$ is the set of $p\in\mathbb R^K_+$ with
--   $$\sum_{k=1}^K p_k=1,\qquad \mu_j(x)-\epsilon^\mu_j\le\sum_{k=1}^K p_k\xi^k_j\le\mu_j(x)+\epsilon^\mu_j,\qquad S_j(x)\underline\epsilon^S_j\le\sum_{k=1}^K p_k(\xi^k_j)^2\le S_j(x)\bar\epsilon^S_j$$
--   for every $j$.
--
--   **The joint program (7).** Its variables are $(x,y)\in S$ and $\alpha=(\alpha_1,\alpha_2,\alpha_3)$, $\beta=(\beta_1,\beta_2,\beta_3)$ with $\alpha_1,\beta_1\in\mathbb R$ and $\alpha_2,\alpha_3,\beta_2,\beta_3\in\mathbb R^J$, all nonnegative, subject to
--   $$-\alpha_1+\beta_1+\sum_{j}\xi^k_j(-\alpha_{2j}+\beta_{2j})+\sum_j(\xi^k_j)^2(-\alpha_{3j}+\beta_{3j})\ \ge\ Q^k(x)\qquad\forall k.\tag{7b}$$
--   Its objective (7a) is $g(x,y)$ plus
--   $$\begin{aligned}&-\alpha_1-\sum_j\alpha_{2j}(\bar\mu_j-\epsilon^\mu_j)-\sum_j\sum_i\lambda^\mu_{ji}\bar\mu_j\alpha_{2j}x_i-\sum_j\alpha_{3j}(\bar\mu_j^2+\bar\sigma_j^2)\underline\epsilon^S_j-\sum_j\sum_i\lambda^S_{ji}\underline\epsilon^S_j(\bar\mu_j^2+\bar\sigma_j^2)\alpha_{3j}x_i\\&+\beta_1+\sum_j\beta_{2j}(\bar\mu_j+\epsilon^\mu_j)+\sum_j\sum_i\lambda^\mu_{ji}\bar\mu_j\beta_{2j}x_i+\sum_j\beta_{3j}(\bar\mu_j^2+\bar\sigma_j^2)\bar\epsilon^S_j+\sum_j\sum_i\lambda^S_{ji}\bar\epsilon^S_j(\bar\mu_j^2+\bar\sigma_j^2)\beta_{3j}x_i.\end{aligned}$$
--   The dual values of (7) are these objective values at its feasible points.
--
--   These objects state (7), the computable specialisation of Theorem 1 used by the paper's algorithm.
--
--   **Formalization Note** The $\lambda$'s are named `lamμ`, `lamS` (λ is a Lean keyword). The multipliers of the normalisation row are the scalars $\alpha_1,\beta_1$; those of the mean and second-moment rows are vectors in $\mathbb R^J$. The objective (7a) is transcribed term by term, without simplification.
-- source:
--   Yu & Shen, Multistage distributionally robust mixed-integer programming with decision-dependent moment-based ambiguity sets, arXiv:2002.12518v3, pp. 8–9, (5), (6), (7)

import Mathlib
import Definitions.Def_DDMomentDRO_Type1_Setting

namespace DDMomentDRO.Type1

/-- The empirical first moment of p. 8: `μⱼ(x) = μ̄ⱼ (1 + ∑ᵢ λ^μ_{ji} xᵢ)`. -/
def muFn {I J : ℕ} (μbar : Fin J → ℝ) (lamμ : Fin J → Fin I → ℝ) (x : Fin I → ℝ) (j : Fin J) :
    ℝ :=
  μbar j * (1 + ∑ i, lamμ j i * x i)

/-- The empirical second moment of p. 8: `Sⱼ(x) = (μ̄ⱼ² + σ̄ⱼ²)(1 + ∑ᵢ λ^S_{ji} xᵢ)`. -/
def SFn {I J : ℕ} (μbar σbar : Fin J → ℝ) (lamS : Fin J → Fin I → ℝ) (x : Fin I → ℝ)
    (j : Fin J) : ℝ :=
  (μbar j ^ 2 + σbar j ^ 2) * (1 + ∑ i, lamS j i * x i)

/-- The ambiguity set (6) at the state `x`: `p ∈ ℝ^K_+` with `∑ₖ pₖ = 1` (6a),
`μⱼ(x) − ε^μⱼ ≤ ∑ₖ pₖ ξᵏⱼ ≤ μⱼ(x) + ε^μⱼ` (6b) and
`Sⱼ(x) ε̲^Sⱼ ≤ ∑ₖ pₖ (ξᵏⱼ)² ≤ Sⱼ(x) ε̄^Sⱼ` (6c), for every `j`. -/
def amb6 {I J K : ℕ} (ξ : Fin K → Fin J → ℝ) (μbar σbar εμ εSl εSu : Fin J → ℝ)
    (lamμ lamS : Fin J → Fin I → ℝ) (x : Fin I → ℝ) : Set (Fin K → ℝ) :=
  {p | (∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1 ∧
    (∀ j, muFn μbar lamμ x j - εμ j ≤ ∑ k, p k * ξ k j ∧
      ∑ k, p k * ξ k j ≤ muFn μbar lamμ x j + εμ j) ∧
    (∀ j, SFn μbar σbar lamS x j * εSl j ≤ ∑ k, p k * ξ k j ^ 2 ∧
      ∑ k, p k * ξ k j ^ 2 ≤ SFn μbar σbar lamS x j * εSu j)}

/-- The dual part of the objective (7a), term by term as printed on p. 9. -/
def obj7 {I J : ℕ} (μbar σbar εμ εSl εSu : Fin J → ℝ) (lamμ lamS : Fin J → Fin I → ℝ)
    (x : Fin I → ℝ) (α1 : ℝ) (α2 α3 : Fin J → ℝ) (β1 : ℝ) (β2 β3 : Fin J → ℝ) : ℝ :=
  -α1 - ∑ j, α2 j * (μbar j - εμ j) - ∑ j, ∑ i, lamμ j i * μbar j * α2 j * x i
    - ∑ j, α3 j * (μbar j ^ 2 + σbar j ^ 2) * εSl j
    - ∑ j, ∑ i, lamS j i * εSl j * (μbar j ^ 2 + σbar j ^ 2) * α3 j * x i
    + β1 + ∑ j, β2 j * (μbar j + εμ j) + ∑ j, ∑ i, lamμ j i * μbar j * β2 j * x i
    + ∑ j, β3 j * (μbar j ^ 2 + σbar j ^ 2) * εSu j
    + ∑ j, ∑ i, lamS j i * εSu j * (μbar j ^ 2 + σbar j ^ 2) * β3 j * x i

/-- Dual feasibility (7b) and `α, β ≥ 0` at the state `x`. -/
def Feas7 {I J K : ℕ} (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ)
    (x : Fin I → ℝ) (α1 : ℝ) (α2 α3 : Fin J → ℝ) (β1 : ℝ) (β2 β3 : Fin J → ℝ) : Prop :=
  0 ≤ α1 ∧ 0 ≤ α2 ∧ 0 ≤ α3 ∧ 0 ≤ β1 ∧ 0 ≤ β2 ∧ 0 ≤ β3 ∧
    ∀ k, Qn x k ≤ -α1 + β1 + ∑ j, ξ k j * (-α2 j + β2 j) + ∑ j, ξ k j ^ 2 * (-α3 j + β3 j)

/-- The objective values (7a) of the joint program (7) at its feasible points (7b), (7c),
`α, β ≥ 0`. -/
def dualVals7 {I J K : ℕ} (S : Set ((Fin I → ℝ) × (Fin I → Fin J → ℝ)))
    (g : (Fin I → ℝ) → (Fin I → Fin J → ℝ) → ℝ) (Qn : (Fin I → ℝ) → Fin K → ℝ)
    (ξ : Fin K → Fin J → ℝ) (μbar σbar εμ εSl εSu : Fin J → ℝ)
    (lamμ lamS : Fin J → Fin I → ℝ) : Set ℝ :=
  {v | ∃ x y α1 α2 α3 β1 β2 β3, (x, y) ∈ S ∧ Feas7 Qn ξ x α1 α2 α3 β1 β2 β3 ∧
    v = g x y + obj7 μbar σbar εμ εSl εSu lamμ lamS x α1 α2 α3 β1 β2 β3}

end DDMomentDRO.Type1


