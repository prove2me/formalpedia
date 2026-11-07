-- Prove2me | Definitions.Def_SparseHistComm_levelSucc
-- name    : SparseHistComm_levelSucc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:37:26.961205+00:00
-- url     : https://prove2.me/theorems/4248af4c-037d-4513-a54a-dbab3bf6b013
-- title:
--   Success probability $\Pr_{J_i \text{ i.i.d.}\sim p}\{\sum_i J_i \ge nk - \lfloor nD\rfloor\}$ of a level law
-- statement:
--   For a probability vector $p = (p_0,\dots,p_k)$ on the covering levels $\{0,\dots,k\}$, let $J_1,\dots,J_n$ be i.i.d. with law $p$. This is the probability
--   $$
--   \Pr_{J_1,\dots,J_n \text{ i.i.d.} \sim p}\Big\{ \sum_{i=1}^n J_i \ge nk - \lfloor nD\rfloor \Big\} = \sum_{\substack{(j_1,\dots,j_n) \in \{0,\dots,k\}^n \\ j_1 + \dots + j_n \ge nk - \lfloor nD\rfloor}} \prod_{i=1}^n p_{j_i}
--   $$
--   that the total level reaches the required threshold.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (12), p.7 (the constraint)

import Mathlib
import Definitions.Def_SparseHistComm_threshold

namespace SparseHistComm

/-- For a law `p = (p₀, …, p_k)` on the covering levels `{0, …, k}`, the probability
`Pr_{J₁,…,Jₙ i.i.d. ∼ p}{∑ᵢ Jᵢ ≥ nk − ⌊nD⌋}` (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), the constraint of (12), p.7):
`∑_{J ∈ {0,…,k}ⁿ, ∑ᵢ Jᵢ ≥ t} ∏ᵢ p(Jᵢ)`. -/
noncomputable def levelSucc (n k : ℕ) (D : ℝ) (p : Fin (k + 1) → ℝ) : ℝ :=
  ∑ J ∈ (Finset.univ : Finset (Fin n → Fin (k + 1))).filter
      (fun J => threshold n k D ≤ ∑ i, ((J i : ℕ) : ℤ)), ∏ i, p (J i)

end SparseHistComm


