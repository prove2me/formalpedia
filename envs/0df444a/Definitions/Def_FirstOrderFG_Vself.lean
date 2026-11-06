-- Prove2me | Definitions.Def_FirstOrderFG_Vself
-- name    : FirstOrderFG_Vself
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:25.83286+00:00
-- url     : https://prove2.me/theorems/38dc9cca-7a17-46ed-a4c8-fad4e0b6c9dd
-- title:
--   The self-loop vertices $V_{\mathrm{self}}$
-- statement:
--   Throughout, $G=(V,E)$ is a directed graph on the arms $V=[K]$; the edge $i\to j$ means that playing arm $i$ reveals the loss of arm $j$.
--
--   The set of vertices with a self-loop is
--   $$
--   V_{\mathrm{self}}=\{i\in V:\ i\to i\},\qquad s=|V_{\mathrm{self}}| .
--   $$
--   Playing such a vertex reveals its own loss. The subgraph $G_{\mathrm{self}}$ induced by $V_{\mathrm{self}}$ is handled by the self-aware base learner.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3

import Mathlib

namespace FirstOrderFG

/-- **The self-loop vertices `V_self`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §2, p.3:
`V_self ≜ {i ∈ V : i → i}`; `s ≜ |V_self|` is `(Vself E).card`.

**Formalization Note.** `E i j` is the edge `i → j`. -/
def Vself {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] : Finset (Fin K) :=
  Finset.univ.filter (fun i => E i i)

end FirstOrderFG


