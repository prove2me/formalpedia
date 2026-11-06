-- Prove2me | Definitions.Def_FirstOrderFG_Hself
-- name    : FirstOrderFG_Hself
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:46:41.045625+00:00
-- url     : https://prove2.me/theorems/8b3a0c62-83a0-4957-be01-a2e8221d2fe5
-- title:
--   Ratio sum in the self-loop subgraph $\mathcal H^{G_{\mathrm{self}}}(q)$
-- statement:
--   Throughout, $G=(V,E)$ is a directed graph on the arms $V=[K]$; the edge $i\to j$ means that playing arm $i$ reveals the loss of arm $j$.
--
--   For a distribution $q$ on $V_{\mathrm{self}}$,
--   $$
--   \mathcal H^{G_{\mathrm{self}}}(q)=\sum_{i\in V_{\mathrm{self}}}\frac{q_i}{Q_i^{G_{\mathrm{self}}}(q)+1/(KT)} ,
--   $$
--   with the offset $1/(KT)$ of the whole graph ($K$ arms), kept unchanged when passing to $G_{\mathrm{self}}$. Algorithm 4 doubles its guess $A$ whenever $\mathcal H^{G_{\mathrm{self}}}(q_t)>A$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Lemma 4.1, p.11; Algorithm 4, line 6, p.32; App. A.3, p.20

import Mathlib
import Definitions.Def_FirstOrderFG_Vself
import Definitions.Def_FirstOrderFG_Qself

namespace FirstOrderFG

/-- **`H^{G_self}(q)`, the ratio sum in the self-loop subgraph.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §4 (Lemma 4.1, p.11;
Algorithm 4, line 6, p.32), with the original offset kept ("keeping the original offset
`1/(KT)`", App. A.3, p.20): `H^{G_self}(q) = ∑_{i ∈ V_self} q_i / (Q_i^{G_self}(q) + 1/(KT))`.

**Formalization Note.** `K` is the number of arms of the whole graph `G`, not `|V_self|`. -/
noncomputable def Hself {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ)
    (q : Fin K → ℝ) : ℝ :=
  ∑ i ∈ Vself E, q i / (Qself E q i + 1 / ((K : ℝ) * T))

end FirstOrderFG


