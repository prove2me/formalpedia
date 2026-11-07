-- Prove2me | Definitions.Def_IntroDelayAMDP_alg1Visits
-- name    : IntroDelayAMDP_alg1Visits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:51:05.130208+00:00
-- url     : https://prove2.me/theorems/ca64daf4-b2f1-4c5d-ace0-31d87b75b5eb
-- title:
--   The visit count
-- statement:
--   $N_k(s,a)$: the number of visits to $(s,a)$ before episode $k$.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Section 3, p.14

import Mathlib
import Definitions.Def_IntroDelayAMDP_runState

namespace IntroDelayAMDP

/-- **The visit count `N_k(s, a)`** (Section 3, printed p.14, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530): "let `N_k(s, a)` be the
number of visits to `(s, a)` before episode `k`"), for the 0-based episode `k`. -/
noncomputable def alg1Visits {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] {H K : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams)
    (ω : Tape St A K H) (k : ℕ) (s : St) (a : A) : ℕ :=
  (runState L P ℓ p ω k).visits s a

end IntroDelayAMDP


