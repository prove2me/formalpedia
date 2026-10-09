-- Prove2me | Definitions.Def_actuarial_finiteMortalityDeathRate
-- name    : actuarial_finiteMortalityDeathRate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T07:03:18.675117+00:00
-- url     : https://prove2.me/theorems/6a06d8e1-bb8a-4cdb-a649-dd154210de9c
-- title:
--   Conditional one-year mortality probability
-- statement:
--   Death mass divided by the current survival mass. Its probability interpretation requires positive survival mass.
--
--   **Mathematical statement**
--
--   $$
--   q_t=D_t/S_t,\quad S_t>0
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDeathMass
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteMortalityDeathRate {Ω : Type*} [Fintype Ω]
  (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ) : ℝ :=
  finiteMortalityDeathMass w K t / finiteMortalitySurvivalMass w K t

end ActuarialValuation


