-- Prove2me | Definitions.Def_FirstOrderFG_Bset
-- name    : FirstOrderFG_Bset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:46:20.425205+00:00
-- url     : https://prove2.me/theorems/21dbd735-ce20-4645-9c5c-7389f4991e05
-- title:
--   The master action set $\mathcal B$
-- statement:
--   The **master action set** $\mathcal B$ has one action for each vertex $i\in\bar V_{\mathrm{self}}$ (a vertex without self-loop) and, when $s=|V_{\mathrm{self}}|>0$, one **meta-action** $0$ standing for the self-aware learner on $G_{\mathrm{self}}$. Its size is $M=|\mathcal B|$, so $M=|\bar V_{\mathrm{self}}|+\mathbb I\{s>0\}$.
--
--   **Formalization Note** Master actions are elements of `Option (Fin K)`: `some i` is the action of the vertex $i\in\bar V_{\mathrm{self}}$ and `none` is the meta-action $0$, present exactly when $V_{\mathrm{self}}\neq\emptyset$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §4.1, p.8

import Mathlib
import Definitions.Def_FirstOrderFG_Vself
import Definitions.Def_FirstOrderFG_Vbar

namespace FirstOrderFG

/-- **The master action set `B`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §4.1, p.8: "Denote by `B` the master action set,
consisting of one action for each vertex in `V̄_self` and, when `s > 0`, a meta-action `0`
representing `G_self`. Denote by `M ≜ |B|` its size."

**Formalization Note.** Master actions are `Option (Fin K)`: `some i` is the action of the vertex
`i ∈ V̄_self`, and `none` is the meta-action `0`, present exactly when `V_self` is nonempty.
`M` is `(Bset E).card`. -/
def Bset {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] : Finset (Option (Fin K)) :=
  (if (Vself E).Nonempty then {none} else ∅) ∪ (Vbar E).image some

end FirstOrderFG


