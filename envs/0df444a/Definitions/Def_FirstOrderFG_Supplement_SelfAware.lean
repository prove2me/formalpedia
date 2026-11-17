-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_SelfAware
-- name    : FirstOrderFG_Supplement_SelfAware
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:37:35.232221+00:00
-- url     : https://prove2.me/theorems/b9f7a0b9-7e95-44c5-b077-c0d80fd28001
-- title:
--   Self-aware feedback graph
-- statement:
--   A directed feedback graph is **self-aware** when every arm has a self-loop. Thus playing any arm always reveals that arm's own loss, and the self-loop vertex set is the whole arm set.
--
--   This is the graph regime of Algorithms 1 and 3 and Theorems 3.2 and A.2.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3

import Mathlib

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **A self-aware feedback graph.** Zhang–Zhang–Luo–Mineiro,
*Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861,
§2, p.3: `G` is self-aware when every vertex has a self-loop, equivalently `V_self = V`.

**Formalization Note.** `E i j` means that playing `i` reveals the loss of `j`. -/
def SelfAware {K : ℕ} (E : Fin K → Fin K → Prop) : Prop :=
  ∀ i, E i i

end FirstOrderFG.Supplement


