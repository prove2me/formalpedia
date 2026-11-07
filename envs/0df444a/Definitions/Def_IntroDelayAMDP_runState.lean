-- Prove2me | Definitions.Def_IntroDelayAMDP_runState
-- name    : IntroDelayAMDP_runState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:49:22.327203+00:00
-- url     : https://prove2.me/theorems/b6cb055f-e537-4e40-9841-5106aa3a0de6
-- title:
--   The run of Algorithm 1 on the tape
-- statement:
--   The state of Algorithm 1 before the 0-based episode $\kappa$ on a sample point, for fixed oblivious losses and given parameters: the initial state at $\kappa=0$, and one more application of the episode step for each later episode.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 1, p.16

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_AlgParams
import Definitions.Def_IntroDelayAMDP_Tape
import Definitions.Def_IntroDelayAMDP_coins
import Definitions.Def_IntroDelayAMDP_initState
import Definitions.Def_IntroDelayAMDP_algStep

namespace IntroDelayAMDP

/-- **The run of Algorithm 1 on the tape** (Algorithm 1, printed p.16, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)). For the layered
space `L`, the true transition `P`, the oblivious losses `ℓ` (fixed in advance), the parameters
`p` and a sample point `ω` of the tape, `runState L P ℓ p ω κ` is the state of Algorithm 1 before
the 0-based episode `κ` (the paper's episode `κ + 1`): `runState … 0` is the initial state of
line 1, and `runState … (κ + 1)` applies `algStep` with the coins of episode `κ`.

**Formalization Note.** Episodes are 0-based; the paper's episodes `1, …, K` are `0, …, K − 1`. The
action fixed by `Classical.arbitrary` is a default of the sampler, reached only on a null set. -/
noncomputable def runState {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A]
    {H K : ℕ} (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams)
    (ω : Tape St A K H) : ℕ → AlgState St A
  | 0 => initState L (Classical.arbitrary A)
  | κ + 1 => algStep L P ℓ p (Classical.arbitrary A) (runState L P ℓ p ω κ) κ (coins ω κ)

end IntroDelayAMDP


