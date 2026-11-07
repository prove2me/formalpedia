-- Prove2me | Definitions.Def_IntroDelayAMDP_pFinish
-- name    : IntroDelayAMDP_pFinish
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:50.100487+00:00
-- url     : https://prove2.me/theorems/808d68f8-6458-4bb0-afe9-25017a3e2af7
-- title:
--   The finishing probability of an attempt, Eq. (27)
-- statement:
--   $p_k(s,a)=\gamma+(1-\gamma)q^{\pi_k}(s,a)/2$, for a stop probability $\gamma$ and the policy of the estimate's episode. By Lemma A.6 it is the probability that an attempt has $I_{k,\kappa}(s,a)=1$.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (27), p.29

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_occ

namespace IntroDelayAMDP

/-- **The finishing probability `p_k(s, a)` of an attempt** (Eq. (27), printed p.29, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530):
"`p_k(s, a) ≜ γ + (1 − γ)q^{π_k}(s, a)/2`"), for a stop probability `γ` and the policy `π_k` of the
estimate's episode, with `q^{π_k}` the occupancy under the true transition `P`. -/
noncomputable def pFinish {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] {H : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (γ : ℝ) (πk : St → A → ℝ) (s : St) (a : A) : ℝ :=
  γ + (1 - γ) * occ L P πk s a / 2

end IntroDelayAMDP


