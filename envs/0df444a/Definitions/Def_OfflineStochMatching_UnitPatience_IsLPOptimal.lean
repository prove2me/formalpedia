-- Prove2me | Definitions.Def_OfflineStochMatching_UnitPatience_IsLPOptimal
-- name    : OfflineStochMatching_UnitPatience_IsLPOptimal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:31:18.393+00:00
-- url     : https://prove2.me/theorems/213a2e1e-6efc-4b47-b610-05d3fc9cbf6e
-- title:
--   Optimal solution of the LP relaxation (3)
-- statement:
--   A vector $y$ is an **optimal solution of the LP relaxation (3)** if it is feasible for (3) and maximizes the objective
--
--   $$
--   \mathrm{LP}=\max\ \sum_{e\in E} w_e z_e,\qquad z_e=y_ep_e,
--   $$
--
--   over all feasible solutions. Its value upper-bounds every probing algorithm (Lemma 1), and it is the starting point of the algorithm of Section 4.
--
--   **Formalization Note** Optimality is stated as attainment (feasible and at least the objective of every feasible $y'$), not through a supremum. An optimum always exists: $y=0$ is feasible and the feasible set is a compact polytope.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §2, p. 7, LP (3)

import Mathlib
import Definitions.Def_OfflineStochMatching_UnitPatience_IsLPFeasible

namespace OfflineStochMatching.UnitPatience

/-- **Optimal solution of the LP relaxation (3).**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, §2, p. 7, LP (3):
`LP := max Σ_{e∈E} w_e z_e` subject to (3a)–(3d), with `z_e = y_e p_e`.

`IsLPOptimal G y` says that `y` is feasible for (3) and attains the maximum of the objective
`Σ_e w_e (y_e p_e)` over all feasible solutions.

**Formalization Note.** The optimum is stated as attainment, not as an `sSup`; an optimum always
exists (`y = 0` is feasible and the feasible set is a compact polytope). -/
def IsLPOptimal {V E : Type*} [Fintype E] [DecidableEq V] (G : StochGraph V E) (y : E → ℝ) :
    Prop :=
  IsLPFeasible G y ∧
    ∀ y', IsLPFeasible G y' → ∑ e, G.w e * (y' e * G.p e) ≤ ∑ e, G.w e * (y e * G.p e)

end OfflineStochMatching.UnitPatience


