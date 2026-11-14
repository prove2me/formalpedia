-- Prove2me | Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_Minimax
-- name    : ConsistentSubmodular_Randomized_AdaptivityGap_Minimax
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:07:26.233673+00:00
-- url     : https://prove2.me/theorems/5bee2142-aca4-4f4d-a8f4-b5a620674002
-- title:
--   Minimax quantities of a payoff matrix: guarantee, row sums, largest row sum
-- statement:
--   Fix $m \in \mathbb{N}$ and a real matrix $w = (w_{i,j})_{0 \le i,j \le m}$; in the application $w_{i,j} = f(O_i \cup R_j)/f(O_j \cup R_j)$ is the normalized payoff of candidate $i$ at stage $j$. Write $\Delta$ for the simplex of probability vectors on $\{0,\dots,m\}$ (type `Point m`, vectors in $\mathbb{R}^{m+1}$).
--
--   - `guarantee w a` is the guarantee of the maximizing distribution $a$:
--   $$\min_{0\le j\le m} \sum_{i=0}^{m} a_i\, w_{i,j}.$$
--   - `rowSums w` is the $\mathbb{R}$-linear map $\mathbb{R}^{m+1} \to \mathbb{R}^{m+1}$ sending $b$ to the vector $\big(\sum_{j=0}^{m} b_j\, w_{i,j}\big)_{i}$, i.e. multiplication of $b$ by the matrix $w$.
--   - `rowMax w b` is the largest row sum against $b$:
--   $$\max_{0\le i\le m} \sum_{j=0}^{m} b_j\, w_{i,j}.$$
--
--   The two quantities are the payoffs of the two players in the finite zero-sum game with matrix $w$, and no simplex condition is built into the definitions; they are meaningful for any vectors.
--
--   These definitions are the objects of the finite minimax duality used in the analysis of the addition-robustness linear program in the adaptivity-gap argument of the randomized bound (Appendix A.4): the value $\rho^\star$ of the program equals both $\max_{a\in\Delta}$ of the guarantee and $\min_{b\in\Delta}$ of the largest row sum.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/Minimax.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Minimax

variable {m : ℕ}

/-- The guarantee `min_j Σ_i a_i w_{i,j}` of the maximizing distribution `a`. -/
def guarantee (w : Fin (m + 1) → Fin (m + 1) → ℝ) (a : Point m) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun j => ∑ i, a i * w i j

/-- The row sums `(Σ_j b_j w_{i,j})_i` of a distribution `b`, as a linear map. -/
def rowSums (w : Fin (m + 1) → Fin (m + 1) → ℝ) : Point m →ₗ[ℝ] Point m where
  toFun b i := ∑ j, b j * w i j
  map_add' b c := by
    ext i
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' r b := by
    ext i
    simp [Finset.mul_sum, mul_assoc]

/-- The largest row sum `max_i Σ_j b_j w_{i,j}` against the distribution `b`. -/
def rowMax (w : Fin (m + 1) → Fin (m + 1) → ℝ) (b : Point m) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => ∑ j, b j * w i j

end ConsistentSubmodular.Minimax

end


