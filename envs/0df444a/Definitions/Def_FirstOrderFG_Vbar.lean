-- Prove2me | Definitions.Def_FirstOrderFG_Vbar
-- name    : FirstOrderFG_Vbar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:29.146297+00:00
-- url     : https://prove2.me/theorems/4bebc1f2-31df-45af-b2cc-260a6594d870
-- title:
--   The vertices without self-loops $\bar V_{\mathrm{self}}$
-- statement:
--   Throughout, $G=(V,E)$ is a directed graph on the arms $V=[K]$; the edge $i\to j$ means that playing arm $i$ reveals the loss of arm $j$.
--
--   The complement $\bar V_{\mathrm{self}}=V\setminus V_{\mathrm{self}}$ is the set of vertices without a self-loop. Under strong observability each of them is observed by every other vertex.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3

import Mathlib
import Definitions.Def_FirstOrderFG_Vself

namespace FirstOrderFG

/-- **The vertices without self-loops `V̄_self = V ∖ V_self`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §2, p.3. -/
def Vbar {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] : Finset (Fin K) :=
  Finset.univ.filter (fun i => i ∉ Vself E)

end FirstOrderFG


