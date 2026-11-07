-- Prove2me | Definitions.Def_IntroDelayAMDP_bonusQ
-- name    : IntroDelayAMDP_bonusQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:14.654257+00:00
-- url     : https://prove2.me/theorems/0d812ed6-6df7-49ef-826c-1e9a570a63e6
-- title:
--   Optimistic bonus Q-function, Eq. (18)
-- statement:
--   $B(s,a)$ runs the optimistic iteration for the $H-h(s)$ remaining layers, so that
--   $$B(s,a)=b(s)+\max_{P'\in\mathcal P}\sum_{s'\in\mathcal S_{h+1}}P'(s'\mid s,a)\sum_{a'}\pi(a'\mid s')B(s',a'),$$
--   with $B=0$ on $\mathcal S_H$.
--
--   **Formalization Note** The maximum is over the whole $P'\in\mathcal P$, as printed. For the confidence sets, which are products over pairs, this is the per-pair maximum.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (18), Algorithm 1 line 5, p.16

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_bonusIter

namespace IntroDelayAMDP

/-- **Optimistic bonus Q-function** `B_κ` (Eq. (18), Algorithm 1 line 5, p.16). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed p.16:
"Compute the bonus Q-function backward from the last layer, with `B_κ = 0` on `S_H`:
`B_κ(s, a) ≜ b_κ(s) + max_{P′∈P_κ} ∑_{s′∈S_{h+1}} P′(s′ | s, a) ∑_{a′} π_κ(a′ | s′)B_κ(s′, a′),
∀ s ∈ S_h, a ∈ A`. (18)"

`bonusQ L cs π b s a` runs `bonusIter` for the `H − layer(s)` remaining layers. For a last-layer
pair it is `b(s)` (`B = 0` on `S_H`).

**Formalization Note.** The maximum is taken over the whole `P′ ∈ cs`, as printed; for the
confidence sets, which are products over pairs, this is the per-pair maximum. Rows of `P′` vanish
outside the next layer, so the sum over all `s′` is the sum over `S_{h+1}`. -/
noncomputable def bonusQ {St A : Type} [Fintype St] [Fintype A] {H : ℕ} (L : LayeredSpace St H)
    (cs : Set (St → A → St → ℝ)) (π : St → A → ℝ) (b : St → ℝ) (s : St) (a : A) : ℝ :=
  bonusIter cs π b (H - L.layer s) s a

end IntroDelayAMDP


