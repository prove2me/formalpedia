-- Prove2me | Definitions.Def_IntroDelayAMDP_alg1Ind
-- name    : IntroDelayAMDP_alg1Ind
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:51:58.799199+00:00
-- url     : https://prove2.me/theorems/c0030493-a311-409c-acd0-2236a5ae0a0b
-- title:
--   The indicator $I_{k,\kappa}(s,a)$
-- statement:
--   $I_{k,\kappa}(s,a)$: the attempt of the estimate $(k,s,a)$ in episode $\kappa$ succeeds or randomly stops it. It is false if the estimate does not attempt in $\kappa$.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), App. A, p.29

import Mathlib
import Definitions.Def_IntroDelayAMDP_runState

namespace IntroDelayAMDP

/-- **The indicator `I_{k,κ}(s, a)`** (App. A, printed p.29, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530): "`I_{k,κ}(s, a)` for the
indicator that its attempt with episode `κ` succeeds or randomly stops it"), as recorded by the run
after all `K` episodes (0-based `k`, `κ`); it is false if the estimate does not attempt in `κ`. -/
noncomputable def alg1Ind {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] {H K : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams)
    (ω : Tape St A K H) (k κ : ℕ) (s : St) (a : A) : Prop :=
  (runState L P ℓ p ω K).ind k κ s a

end IntroDelayAMDP


