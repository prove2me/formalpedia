-- Prove2me | Definitions.Def_IntroDelayAMDP_qFun
-- name    : IntroDelayAMDP_qFun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:15.002552+00:00
-- url     : https://prove2.me/theorems/c881fb18-7a88-43af-90cb-44a49da26560
-- title:
--   Q-function, Eq. (12)
-- statement:
--   The Q-function of a policy $\pi$ for the per-pair cost $c$ is
--   $$Q^\pi(s,a)=c(s,a)+\sum_{s'}P(s'\mid s,a)V^\pi(s').$$
--   For a last-layer pair the sum is empty, which is the convention $V=0$ on $\mathcal S_H$.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (12), p.13

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_vFun

namespace IntroDelayAMDP

/-- **Q-function** (Eq. (12), p.13). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed p.13: "`Q^π_k(s, a) ≜ ℓ_k(s, a) +
E_{s′∼P(·|s,a)}[V^π_k(s′)]`".

`qFun L P c π s a = c(s, a) + ∑_{s'} P(s' | s, a) V^π(s')`, with `V^π = vFun L P c π`. For a
last-layer pair the sum is empty (the row of `P` vanishes), which is `V = 0` on `S_H`. -/
noncomputable def qFun {St A : Type} [Fintype St] [Fintype A] {H : ℕ} (L : LayeredSpace St H)
    (P : St → A → St → ℝ) (c : St → A → ℝ) (π : St → A → ℝ) (s : St) (a : A) : ℝ :=
  c s a + ∑ s', P s a s' * vFun L P c π s'

end IntroDelayAMDP


