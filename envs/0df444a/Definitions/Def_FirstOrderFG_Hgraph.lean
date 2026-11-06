-- Prove2me | Definitions.Def_FirstOrderFG_Hgraph
-- name    : FirstOrderFG_Hgraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:39.021502+00:00
-- url     : https://prove2.me/theorems/8b75f097-6531-4a6f-a44f-dc5adc0c5223
-- title:
--   Decision-observation ratio sum $\mathcal H^G(q)$
-- statement:
--   Throughout, $G=(V,E)$ is a directed graph on the arms $V=[K]$; the edge $i\to j$ means that playing arm $i$ reveals the loss of arm $j$.
--
--   For a distribution $q$ on the arms and a horizon $T$, the **decision-observation ratio sum** over the self-loop vertices, with fixed offset $1/(KT)$, is
--   $$
--   \mathcal H^G(q)=\sum_{i\in V_{\mathrm{self}}}\frac{q_i}{Q_i^G(q)+1/(KT)} .
--   $$
--   It measures the cost of loss estimation and is bounded by $O(\alpha\ln(KT))$ (Lemma 2.1).
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3

import Mathlib
import Definitions.Def_FirstOrderFG_Vself
import Definitions.Def_FirstOrderFG_Qobs

namespace FirstOrderFG

/-- **The decision-observation ratio sum `H^G(q)`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §2, p.3:
`H^G(q) ≜ ∑_{i ∈ V_self} q_i / (Q_i^G(q) + 1/(KT))`, "the decision-observation ratio sum over the
vertices with self-loops, with fixed offset `1/(KT)`".

**Formalization Note.** `K` is the number of arms (the length of `Fin K`) and `T : ℕ` the
horizon; the offset is `1/(K·T)` computed in `ℝ`. -/
noncomputable def Hgraph {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ)
    (q : Fin K → ℝ) : ℝ :=
  ∑ i ∈ Vself E, q i / (Qobs E q i + 1 / ((K : ℝ) * T))

end FirstOrderFG


