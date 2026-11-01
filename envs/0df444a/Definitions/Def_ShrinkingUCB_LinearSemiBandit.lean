-- Prove2me | Definitions.Def_ShrinkingUCB_LinearSemiBandit
-- name    : ShrinkingUCB_LinearSemiBandit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:35.296956+00:00
-- url     : https://prove2.me/theorems/970af81b-4115-4677-bbf6-2de285f9d9f6
-- title:
--   Semi-bandit instance with linear generalization, $\mu(i)=x_i^\top\theta^*$
-- statement:
--   There are $N$ products and a dimension $d$. Each product $i\in[N]$ has a known feature vector $x_i\in\mathbb R^d$, and $\theta^*\in\mathbb R^d$ is an unknown parameter. The probability of positive sales of product $i$ in any period is
--
--   $$
--   \mu(i)=x_i^\top\theta^*.
--   $$
--
--   The instance satisfies the standing assumptions $\|\theta^*\|\le1$, and $\|x_i\|\le1$ and $\mu(i)\in[0,1]$ for every $i\in[N]$.
--
--   This is the general data of a stochastic linear semi-bandit, on which the reward model and every algorithm of the mission are built.
--
--   **Formalization Note** Vectors are functions `Fin d → ℝ` and the Euclidean norm is written out as $\sqrt{v\cdot v}$. Feature vectors need not be distinct: distinct products may share a feature vector.
-- source:
--   Jin, Simchi-Levi, Wang, Wang, Yang, Shrinking the Upper Confidence Bound: A Dynamic Product Selection Problem for Urban Warehouses, arXiv:1903.07844v2, §2, p.9

import Mathlib

open Matrix

namespace ShrinkingUCB

/-- A semi-bandit instance with linear generalization (Jin, Simchi-Levi, Wang, Wang, Yang,
*Shrinking the Upper Confidence Bound*, arXiv:1903.07844v2, §2, p.9): `N` products with known
feature vectors `x i ∈ ℝ^d` and an unknown parameter `θ* ∈ ℝ^d`, subject to the paper's standing
assumptions `‖θ*‖ ≤ 1`, `‖x_i‖ ≤ 1` and `µ(i) = x_iᵀθ* ∈ [0, 1]`.

**Formalization Note.** Vectors are `Fin d → ℝ`, and the Euclidean norm is written out as
`√(v ⬝ᵥ v)`. The map `x` need not be injective: "distinct products" does not mean distinct
features. -/
structure LinearSemiBandit (d N : ℕ) where
  /-- The feature vector `x_i` of product `i`. -/
  x : Fin N → Fin d → ℝ
  /-- The unknown parameter `θ*`. -/
  θstar : Fin d → ℝ
  θstar_norm_le : √(θstar ⬝ᵥ θstar) ≤ 1
  x_norm_le : ∀ i, √(x i ⬝ᵥ x i) ≤ 1
  mean_nonneg : ∀ i, 0 ≤ x i ⬝ᵥ θstar
  mean_le_one : ∀ i, x i ⬝ᵥ θstar ≤ 1

/-- The probability of positive sales `µ(i) = x_iᵀθ*` (arXiv:1903.07844v2, p.9). -/
def LinearSemiBandit.μ {d N : ℕ} (I : LinearSemiBandit d N) (i : Fin N) : ℝ :=
  I.x i ⬝ᵥ I.θstar

end ShrinkingUCB


