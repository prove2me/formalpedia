-- Prove2me | Definitions.Def_BoydADMM_Constrained_Geometry
-- name    : BoydADMM_Constrained_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:55:05.834492+00:00
-- url     : https://prove2.me/theorems/fc174627-7eab-4061-85b4-addead135e6c
-- title:
--   Product and consensus geometry for parallel projections
-- statement:
--   Let $N\ge 1$ and let $\mathcal A_i\subseteq\mathbb R^n$ be the sets used by the parallel projection method. A block vector $x=(x_i)_{i=1}^N$ belongs to the product $\mathcal C=\prod_i\mathcal A_i$ when each $x_i\in\mathcal A_i$. The consensus set is $\mathcal D=\{(z,\ldots,z):z\in\mathbb R^n\}$. Define the block average and squared stacked Euclidean distance by
--
--   $$\bar x=\frac1N\sum_{i=1}^N x_i,\qquad d_2(x,y)^2=\sum_{i=1}^N\|x_i-y_i\|_2^2.$$
--
--   A block projection is a point in a specified set that minimizes this squared distance. These definitions give the geometry used throughout the parallel projection chapter.
--
--   **Formalization Note** Blocks are functions on `Fin N`. Their ordinary function-space norm is not used as the norm of the stacked vector; `blockSqDist` is the displayed Euclidean sum. Averaging is used only when $N\ge1$.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 35, §5.1.2; https://doi.org/10.1561/2200000016

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection

namespace BoydADMM.Constrained

/-- The vector space used for each of the `N` feasibility constraints. -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A point of the stacked space `ℝ^(nN)`, indexed by its `N` blocks. -/
abbrev Blocks (N n : ℕ) := Fin N → Vec n

/-- The Cartesian product `𝒜₁ × ⋯ × 𝒜_N` of §5.1.2. -/
def productSet {N n : ℕ} (A : Fin N → Set (Vec n)) : Set (Blocks N n) :=
  {x | ∀ i, x i ∈ A i}

/-- The diagonal consensus set `𝒟` of §5.1.2. -/
def consensusSet (N n : ℕ) : Set (Blocks N n) :=
  {x | ∃ z : Vec n, ∀ i, x i = z}

/-- The block average `x̄ = (1/N) ∑ᵢ xᵢ`; used only with `0 < N`. -/
noncomputable def avg {N n : ℕ} (x : Blocks N n) : Vec n :=
  (1 / (N : ℝ)) • ∑ i : Fin N, x i

/-- Squared Euclidean distance in the stacked space, rather than the function type's norm. -/
noncomputable def blockSqDist {N n : ℕ} (v w : Blocks N n) : ℝ :=
  ∑ i : Fin N, ‖v i - w i‖ ^ 2

/-- Euclidean projection in `ℝ^(nN)`, expressed through its squared distance. -/
def IsBlockProjection {N n : ℕ} (C : Set (Blocks N n)) (v p : Blocks N n) : Prop :=
  p ∈ C ∧ ∀ w ∈ C, blockSqDist v p ≤ blockSqDist v w

end BoydADMM.Constrained


