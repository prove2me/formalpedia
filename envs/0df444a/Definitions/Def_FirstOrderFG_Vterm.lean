-- Prove2me | Definitions.Def_FirstOrderFG_Vterm
-- name    : FirstOrderFG_Vterm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:46:22.004169+00:00
-- url     : https://prove2.me/theorems/fec6bce5-38ba-448f-acd3-282783870a18
-- title:
--   The local-norm term $\mathcal V_t$
-- statement:
--   For the master distribution $x$ and estimate $\tilde g$,
--   $$
--   \mathcal V_t=\mathbb I\{0\in\mathcal B\}\,x_{0}^2\tilde g_{0}^2+\sum_{i\in\bar V_{\mathrm{self}}}\min\{x_{i},(1-x_{i})^2\}\,\tilde g_{i}^2 .
--   $$
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Lemma B.3, p.27

import Mathlib
import Definitions.Def_FirstOrderFG_Vself
import Definitions.Def_FirstOrderFG_Vbar

namespace FirstOrderFG

/-- **The local-norm term `V_t` of Lemma B.3.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Lemma B.3, p.27:
`V_t ≜ 𝕀{0 ∈ B} x_{t,0}² g̃_{t,0}² + ∑_{i ∈ V̄_self} min{x_{t,i}, (1 − x_{t,i})²} g̃_{t,i}²`. -/
noncomputable def Vterm {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (x g : Option (Fin K) → ℝ) : ℝ :=
  (if (Vself E).Nonempty then x none ^ 2 * g none ^ 2 else 0)
    + ∑ i ∈ Vbar E, min (x (some i)) ((1 - x (some i)) ^ 2) * g (some i) ^ 2

end FirstOrderFG


