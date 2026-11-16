-- Prove2me | Definitions.Def_MSetBandit_Supplement_History
-- name    : MSetBandit_Supplement_History
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:44:58.376194+00:00
-- url     : https://prove2.me/theorems/169a6d23-c0b7-48de-a5c0-bdb8aa4517c3
-- title:
--   Interaction history $H_t=(X_1,Y_1,\dots,X_t,Y_t)$
-- statement:
--   For a round count $t$, a **history of length $t$** is a sequence
--   $$
--   H_t=(X_1,Y_1,\dots,X_t,Y_t)\in(\mathcal X_{d,m}\times\mathbb R)^t,
--   $$
--   recording at each round the action $X_\tau$ played and the scalar feedback $Y_\tau=X_\tau^\top\ell_\tau$ observed; $H_0=\emptyset$ is the empty history.
--
--   Histories are the information on which both the learner's decisions and an adaptive adversary's losses depend in the lower-bound model. The learner never observes the loss vectors $\ell_\tau$ themselves.
--
--   **Formalization Note** Rounds are indexed from $0$: a history of length $t$ is a function from $\{0,\dots,t-1\}$ to pairs (action, feedback).
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Appendix E, p.40 (definition of $H_t$)

import Mathlib
import Definitions.Def_MSetBandit_Action

namespace MSetBandit.Supplement

/-- **Interaction history `H_t`.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Appendix E, p.40:
"`H_t := (X_1, Y_1, …, X_t, Y_t)` the history of actions and observed feedback up to round `t`,
where `Y_t := X_t^⊤ ℓ_t`. We set `H_0 := ∅`."

`History d m t` is the type of histories of length `t`: entry `τ` is the pair (action played at
round `τ`, scalar feedback observed at round `τ`).

**Formalization Note.** Rounds are 0-based (`τ = 0, …, t − 1`); `History d m 0` is the empty
history. The learner sees only the scalar feedback, never the loss vector. -/
abbrev History (d m t : ℕ) : Type := Fin t → Action d m × ℝ

end MSetBandit.Supplement


