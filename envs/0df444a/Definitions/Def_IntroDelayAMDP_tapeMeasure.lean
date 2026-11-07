-- Prove2me | Definitions.Def_IntroDelayAMDP_tapeMeasure
-- name    : IntroDelayAMDP_tapeMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:51.504304+00:00
-- url     : https://prove2.me/theorems/caa0cf0d-365e-47dd-b7be-aecc13d29b62
-- title:
--   The law of the tape
-- statement:
--   The product over all coordinates of the uniform probability measure on $[0,1]$, so the coordinates are independent and uniform.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Section 2.1, p.12

import Mathlib
import Definitions.Def_IntroDelayAMDP_Tape

namespace IntroDelayAMDP

open MeasureTheory

/-- **The law of the tape** (Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Section 2.1, printed p.12): the product over all coordinates
of the uniform (Lebesgue) probability measure on `[0, 1]`, so the coordinates are independent
and uniform. It is a probability measure. -/
noncomputable def tapeMeasure (St A : Type) [Fintype St] [Fintype A] (K H : ℕ) :
    Measure (Tape St A K H) :=
  Measure.pi fun _ => volume

end IntroDelayAMDP


