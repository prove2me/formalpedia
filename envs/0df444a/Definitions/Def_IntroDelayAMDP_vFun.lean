-- Prove2me | Definitions.Def_IntroDelayAMDP_vFun
-- name    : IntroDelayAMDP_vFun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:09.229008+00:00
-- url     : https://prove2.me/theorems/99f72dd1-8236-4a6a-a133-0d4d866e1bd7
-- title:
--   V-function, Eq. (12)
-- statement:
--   $V^\pi(s)$ is the expected cost of following $\pi$ from $s$ to the end of the episode under transition $P$: the backward iteration run for the $H-h(s)$ remaining steps. For the loss $\ell_k$ of an episode it is the paper's $V^\pi_k$; for a bonus it is the value of (3).
--
--   Since $P(s'\mid s,a)\neq0$ only for $s'$ in the next layer, the function satisfies the Bellman equations (12), with $V=0$ beyond the last layer.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (12), p.13

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_valueIter

namespace IntroDelayAMDP

/-- **V-function** (Eq. (12), p.13). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed pp.12–13: "we let `V^π_k(s) ≜ 0` for all
terminal states `s ∈ S_H`, and define the Q- and V-functions backward from the last layer via the
Bellman equations: `Q^π_k(s, a) ≜ ℓ_k(s, a) + E_{s′∼P(·|s,a)}[V^π_k(s′)]`,
`V^π_k(s) ≜ E_{a∼π(·|s)}[Q^π_k(s, a)]`".

`vFun L P c π s` is `V^π(s)` under transition `P` for the per-pair cost `c` (the loss `ℓ_k` of an
episode in Eq. (12), or the bonus `b_k` in Eq. (3)): it is the backward iteration run for the
`H − layer(s)` remaining steps.

**Formalization Note.** Because `P(s' | s, a) ≠ 0` only for `s'` in the next layer, the
iteration depth `H − layer(s) − 1` used for the successors equals `H − layer(s')`, so `vFun`
satisfies the Bellman equations of (12), with `V = 0` beyond the last layer (no terminal layer is
modelled; see `LayeredSpace`). -/
noncomputable def vFun {St A : Type} [Fintype St] [Fintype A] {H : ℕ} (L : LayeredSpace St H)
    (P : St → A → St → ℝ) (c : St → A → ℝ) (π : St → A → ℝ) (s : St) : ℝ :=
  valueIter P c π (H - L.layer s) s

end IntroDelayAMDP


