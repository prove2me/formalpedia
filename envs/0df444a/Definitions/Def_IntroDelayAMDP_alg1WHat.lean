-- Prove2me | Definitions.Def_IntroDelayAMDP_alg1WHat
-- name    : IntroDelayAMDP_alg1WHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:51:16.035506+00:00
-- url     : https://prove2.me/theorems/0cbc5400-7cc4-4928-a647-64c5eecfe94e
-- title:
--   The number of attempts of an estimate
-- statement:
--   $\hat w_k(s,a)$: the total number of attempts of the estimate $(k,s,a)$, read after all $K$ episodes of the run, and $0$ if it does not start.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), App. A, p.29

import Mathlib
import Definitions.Def_IntroDelayAMDP_runState

namespace IntroDelayAMDP

/-- **The number of attempts `ŵ_k(s, a)` of the estimate `(k, s, a)`** (App. A, printed p.29, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530): "We write `ŵ_k(s, a) ≤ M` for the total number of attempts of the estimate `(k, s, a)` (`0`
if it does not start)"): its count after all `K` episodes of the run. -/
noncomputable def alg1WHat {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] {H K : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams)
    (ω : Tape St A K H) (k : ℕ) (s : St) (a : A) : ℕ :=
  (runState L P ℓ p ω K).w k s a

end IntroDelayAMDP


