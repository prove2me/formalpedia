-- Prove2me | Definitions.Def_SecondBestMatch_Supplement_activityBound
-- name    : SecondBestMatch_Supplement_activityBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:41:10.970191+00:00
-- url     : https://prove2.me/theorems/a216bbdf-3e78-4d83-89a4-541bda3aa56f
-- title:
--   Activity indicator $d_k$
-- statement:
--   An agent $k\in K=B\sqcup S$ is **active** if some matching in $\mathcal F$ contains an edge incident to $k$. Its activity indicator is
--
--   $$
--   d_k=\begin{cases}1,& k\text{ is active},\\ 0,& k\text{ is inactive.}\end{cases}
--   $$
--
--   The service probability of every agent lies in $[0,d_k]$, and $d_k$ is the Lipschitz constant imposed on the agent's utility potential in Definition A.1.
--
--   **Formalization Note** The value is a nonnegative real (`NNReal`) so that it serves directly as a Lipschitz constant.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea7cce1bbfc7757c56937ec4ac13847b6d0025758a63fa8d6a25314385), Appendix A.1, p.27

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch.Supplement

open Classical in
/-- The activity indicator `d_k` of an agent `k ∈ K = B ⊔ S` (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Appendix A.1, p.27):
agent `k` is **active** if some matching in `ℱ` contains an edge incident to `k`, and
`d_k = 1` if `k` is active, `d_k = 0` otherwise.

**Formalization Note** The agent set `K` is the disjoint union `B ⊕ S` (buyers `Sum.inl i`,
sellers `Sum.inr j`). The value is a nonnegative real (`ℝ≥0`) so that it can serve directly as a
Lipschitz constant (`LipschitzOnWith`). -/
noncomputable def activityBound {B S : Type*} (m : Market B S) (k : B ⊕ S) : NNReal :=
  if ∃ M ∈ m.family, ∃ e ∈ M, (Sum.inl e.1 : B ⊕ S) = k ∨ (Sum.inr e.2 : B ⊕ S) = k then 1 else 0

end SecondBestMatch.Supplement


