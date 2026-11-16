-- Prove2me | Definitions.Def_FeedbackSwitching_Supplement_appleTasting
-- name    : FeedbackSwitching_Supplement_appleTasting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:19:33.878451+00:00
-- url     : https://prove2.me/theorems/1364d0c7-f076-4e72-99eb-e959ac8d98f9
-- title:
--   The apple-tasting feedback graph (two actions, one revealing and one blind)
-- statement:
--   **Apple tasting** is the feedback graph on two actions in which action $1$, the **revealing** action, observes the losses of both actions, and action $2$, the **blind** action, yields no feedback at all. As a directed graph on $\{1,2\}$ its edge set is
--   $$
--   E=\{(1,1),\,(1,2)\}.
--   $$
--   It is the smallest strongly revealing graph: for the only pair of distinct actions, the endpoint $1$ observes both losses. Its regret with switching costs is therefore of order $\sqrt T$, which Theorem 5 achieves with explicit constants.
--
--   **Formalization Note** Actions are `Fin 2`, 0-based as in the base mission: Lean action `0` is the paper's revealing action $1$ and Lean action `1` is the blind action $2$; `appleTasting i j` holds exactly when `i = 0`.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Appendix A, p.42 (PDF p.44)

import Mathlib
import Definitions.Def_FeedbackSwitching_FeedbackGraph

namespace FeedbackSwitching.Supplement

/-- **Apple tasting** (App. A, p.42 = PDF p.44). Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco,
Koren, *The Price of Partial Information with Switching Costs: A Complete Characterization for
Feedback Graphs*, arXiv:2606.03851 (held version, sha256 ded8f8bc…).

"In apple tasting, action 1, which we call revealing, observes both losses, and the other, the
blind action 2, yields no feedback." As a feedback graph on two actions: `G i j` holds exactly
when `i` is the revealing action.

**Formalization Note.** Actions are `Fin 2`, 0-based as in the base mission: Lean action `0` is
the paper's revealing action 1 (edges `0 → 0` and `0 → 1`), Lean action `1` is the paper's blind
action 2 (no out-edges, not even a self-loop). -/
def appleTasting : FeedbackGraph 2 := fun i _ => i = 0

end FeedbackSwitching.Supplement


