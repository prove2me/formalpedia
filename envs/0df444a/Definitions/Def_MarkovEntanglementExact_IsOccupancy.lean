-- Prove2me | Definitions.Def_MarkovEntanglementExact_IsOccupancy
-- name    : MarkovEntanglementExact_IsOccupancy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:25.584842+00:00
-- url     : https://prove2.me/theorems/23f962b9-840b-4438-bd64-1eba873094e6
-- title:
--   Distribution on joint pairs with positive agent marginals
-- statement:
--   A function $\mu$ on $S_A\times S_B$ is an **occupancy** if it is a probability distribution whose two agent marginals are positive at every pair:
--   $$\mu\ge0,\qquad\sum_{p}\mu(p)=1,\qquad \mu(s_A,a_A)=\sum_{s_B,a_B}\mu(s_A,a_A,s_B,a_B)>0,\qquad \mu(s_B,a_B)>0.$$
--
--   These are the conditions of footnote 1 of the paper, under which the conditional $\mu(s_B,a_B\mid s_A,a_A)$ of Eq. (2) is defined. Footnote 1 removes pairs of zero marginal from the index sets by restricting the feasible action set.
--
--   **Formalization Note** Positivity is required of the marginals only. Example 1 of the paper has joint pairs of occupancy zero, and the published `IsPositiveDist` would exclude it. Stationarity is not required, since Theorem 1 does not use it.
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, §2, p.8, Eq. (2) and footnote 1

import Mathlib
import Definitions.Def_markov_entanglement

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact

variable {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]

/-- A probability distribution `μ` on joint pairs whose agent marginals are positive at every
pair: `μ ≥ 0`, `Σ μ = 1`, and `μ(s_A, a_A) > 0`, `μ(s_B, a_B) > 0`. These are the conditions of
footnote 1 under which the conditional `μ(s_B, a_B | s_A, a_A)` in Eq. (2) is well defined.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, §2, p.8, Eq. (2) and
footnote 1.

**Formalization Note.** Positivity is on the two agent marginals, not on joint pairs: Example 1
(pp.9–10) has joint pairs of occupancy zero and positive marginals, so the published
`IsPositiveDist` would exclude it. Stationarity of `μ` and uniqueness are not part of this
definition, since Theorem 1 never uses them. Footnote 1 removes the pairs of zero marginal from
the index sets by restricting the feasible action sets, so "positive at every pair" is the
paper's situation. -/
def IsOccupancy (μ : SA × SB → ℝ) : Prop :=
  (∀ p, 0 ≤ μ p) ∧ (∑ p, μ p = 1) ∧ (∀ a, 0 < marginalA μ a) ∧ ∀ b, 0 < marginalB μ b

end MarkovEntanglementExact


