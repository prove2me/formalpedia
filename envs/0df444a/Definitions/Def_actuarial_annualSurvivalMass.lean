-- Prove2me | Definitions.Def_actuarial_annualSurvivalMass
-- name    : actuarial_annualSurvivalMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:06:17.638737+00:00
-- url     : https://prove2.me/theorems/e79166c2-0343-4bf0-ae85-b601352cfe10
-- title:
--   In-force survival probability at duration t
-- statement:
--   The probability that curtate future lifetime is at least t, represented as a real number.
--
--   **Mathematical statement**
--
--   $$
--   S_t=\Pr(K\ge t)
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Ch.6 §6.3, equations (6.3.4)-(6.3.10); Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Ch.7 §7.3.3, https://doi.org/10.1017/CBO9780511800146.008

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def annualSurvivalMass {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) (K : Ω → ℕ) (t : ℕ) : ℝ :=
  (P {ω | t ≤ K ω}).toReal

end ActuarialValuation


