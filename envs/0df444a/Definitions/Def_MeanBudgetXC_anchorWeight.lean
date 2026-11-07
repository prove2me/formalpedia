-- Prove2me | Definitions.Def_MeanBudgetXC_anchorWeight
-- name    : MeanBudgetXC_anchorWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:42:03.353962+00:00
-- url     : https://prove2.me/theorems/ebb12e52-c4d0-4919-b272-00a726e50afa
-- title:
--   The anchor weight $\alpha_{\mathrm{anc}}$
-- statement:
--   For a common heavy weight $L=L_{\mathrm{heavy}}$, the **anchor weight** $\alpha_{\mathrm{anc}}$ on the edges of the host graph gives weight $L$ to each heavy edge (path, padding and marker edges) and weight one to each interaction edge.
--
--   **Formalization Note** An interaction edge is recognized as an edge both of whose ends are path endpoints.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 4.3, p.19, display (16)

import Mathlib
import Definitions.Def_MeanBudgetXC_hostGraph
import Definitions.Def_MeanBudgetXC_isEndpoint

namespace MeanBudgetXC

/-- The **anchor weight** `α_anc` (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 4.3, (16), p.19): weight `1` on every interaction edge
(an edge both of whose ends are path endpoints) and the common heavy weight `L = L_heavy` on every
heavy edge (path, padding and marker edges). -/
def anchorWeight (n₀ t ℓ c niso : ℕ) (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] (L : ℝ) :
    (hostGraph n₀ t ℓ c niso T).edgeSet → ℝ :=
  fun e => if ∀ x ∈ e.1.toFinset, isEndpoint x = true then 1 else L

end MeanBudgetXC


