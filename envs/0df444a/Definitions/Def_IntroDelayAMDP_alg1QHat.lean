-- Prove2me | Definitions.Def_IntroDelayAMDP_alg1QHat
-- name    : IntroDelayAMDP_alg1QHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:52:24.659095+00:00
-- url     : https://prove2.me/theorems/8cc3322a-c9cd-47a0-9ae1-31bb0538ec89
-- title:
--   The GRR estimate
-- statement:
--   $\hat Q_k(s,a)=\mathbf 1[(s_{k,h},a_{k,h})=(s,a)]L_{k,h}\hat w_k(s,a)/2$, Eq. (5) in the form of Section 3. The stored piece of a started estimate is $L_{k,h}/2$ and that of any other key is $0$, so this is the piece times the attempt count.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (5), p.6; Section 3, p.15

import Mathlib
import Definitions.Def_IntroDelayAMDP_alg1WHat

namespace IntroDelayAMDP

/-- **The GRR estimate `Q̂_k(s, a)`** (Eq. (5), printed p.6, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530):
"`Q̂_k(s, a) ≜ 1[(s_{k,h}, a_{k,h}) = (s, a)] L_{k,h} ŵ_k(s, a)/2`"). The stored piece of a started
estimate is `L_{k,h}/2` and that of any other key is `0`, so this is `piece · ŵ_k(s, a)`; it is `0`
when `(s, a)` is not visited in episode `k` or its estimate does not start (then `ŵ_k(s, a) = 0`). -/
noncomputable def alg1QHat {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] {H K : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams)
    (ω : Tape St A K H) (k : ℕ) (s : St) (a : A) : ℝ :=
  (runState L P ℓ p ω K).piece k s a * alg1WHat L P ℓ p ω k s a

end IntroDelayAMDP


