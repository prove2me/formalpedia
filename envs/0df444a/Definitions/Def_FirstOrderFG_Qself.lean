-- Prove2me | Definitions.Def_FirstOrderFG_Qself
-- name    : FirstOrderFG_Qself
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:36.578726+00:00
-- url     : https://prove2.me/theorems/67b19f37-3615-4e41-a546-03cead6d1e40
-- title:
--   Observation probability in the self-loop subgraph $Q_i^{G_{\mathrm{self}}}(q)$
-- statement:
--   Throughout, $G=(V,E)$ is a directed graph on the arms $V=[K]$; the edge $i\to j$ means that playing arm $i$ reveals the loss of arm $j$.
--
--   For a distribution $q$ on $V_{\mathrm{self}}$, the observation probability of $i$ in the induced subgraph $G_{\mathrm{self}}$ is
--   $$
--   Q_i^{G_{\mathrm{self}}}(q)=\sum_{j\in V_{\mathrm{self}}:\ j\to i} q_j .
--   $$
--
--   **Formalization Note** Distributions on $V_{\mathrm{self}}$ are functions on all arms of which only the coordinates in $V_{\mathrm{self}}$ are read.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3; §4.1, Eqs. (21)–(22), p.9

import Mathlib
import Definitions.Def_FirstOrderFG_Vself

namespace FirstOrderFG

/-- **Observation probability in `G_self`, `Q_i^{G_self}(q)`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §2, p.3 (`G_self` is
"the subgraph induced by" `V_self`) and §4.1, p.9 (Eq. (21)–(22)):
`Q_i^{G_self}(q) = ∑_{j ∈ V_self : j → i} q_j`.

**Formalization Note.** Base distributions `q ∈ ∆(V_self)` are functions `Fin K → ℝ` of which
only the coordinates in `V_self` are read. -/
def Qself {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (q : Fin K → ℝ) (i : Fin K) : ℝ :=
  ∑ j ∈ (Vself E).filter (fun j => E j i), q j

end FirstOrderFG


