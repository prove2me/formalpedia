-- Prove2me | Definitions.Def_IntroDelayAMDP_alg1Conf
-- name    : IntroDelayAMDP_alg1Conf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:51:14.072195+00:00
-- url     : https://prove2.me/theorems/56011934-7582-4709-acd4-adf7abe08b9b
-- title:
--   The confidence set used by Algorithm 1
-- statement:
--   $\mathcal P_k$ on a sample point: the set (16) built from the transitions observed before episode $k$.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (16), pp.14–15; Algorithm 1, line 17, p.16

import Mathlib
import Definitions.Def_IntroDelayAMDP_runState
import Definitions.Def_IntroDelayAMDP_confSet

namespace IntroDelayAMDP

/-- **The confidence set `P_k` used by Algorithm 1 in episode `k`** (Eq. (16), printed pp.14–15,
and line 17, printed p.16, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): the set (16) built from the transitions observed in the
episodes before `k` (0-based), with `β = p.beta`. -/
noncomputable def alg1Conf {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] {H K : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams)
    (ω : Tape St A K H) (k : ℕ) : Set (St → A → St → ℝ) :=
  confSet L p.beta (runState L P ℓ p ω k).obs

end IntroDelayAMDP


