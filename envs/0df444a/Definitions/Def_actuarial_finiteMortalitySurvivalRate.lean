-- Prove2me | Definitions.Def_actuarial_finiteMortalitySurvivalRate
-- name    : actuarial_finiteMortalitySurvivalRate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T07:04:25.381906+00:00
-- url     : https://prove2.me/theorems/ed597357-6fb4-4f8c-8815-995dc0f9a67e
-- title:
--   Conditional one-year survival probability
-- statement:
--   Following-year survival mass divided by current mass, with positive denominator for a conditional probability.
--
--   **Mathematical statement**
--
--   $$
--   p_t=S_{t+1}/S_t,\quad S_t>0
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteMortalitySurvivalRate {Ω : Type*} [Fintype Ω]
  (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ) : ℝ :=
  finiteMortalitySurvivalMass w K (t + 1) /
    finiteMortalitySurvivalMass w K t

end ActuarialValuation


