-- Prove2me | Definitions.Def_actuarial_annualDeathMass
-- name    : actuarial_annualDeathMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:06:35.217093+00:00
-- url     : https://prove2.me/theorems/3ca2bb7e-eec3-4c70-9fe8-4ba9cc475ec6
-- title:
--   Probability of death during the next policy year
-- statement:
--   The probability that curtate lifetime equals t, and the death benefit is due at the end of policy year t.
--
--   **Mathematical statement**
--
--   $$
--   D_t=\Pr(K=t)
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Ch.6 §6.3, equations (6.3.4)-(6.3.10); Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Ch.7 §7.3.3, https://doi.org/10.1017/CBO9780511800146.008

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def annualDeathMass {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) (K : Ω → ℕ) (t : ℕ) : ℝ :=
  (P {ω | K ω = t}).toReal

end ActuarialValuation


