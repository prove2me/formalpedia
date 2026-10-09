-- Prove2me | Definitions.Def_actuarial_finiteMortalitySurvivalMass
-- name    : actuarial_finiteMortalitySurvivalMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T07:02:22.563925+00:00
-- url     : https://prove2.me/theorems/9297238f-251c-4592-9c68-0ead318e73e1
-- title:
--   Finite-scenario probability of survival to year t
-- statement:
--   Total finite-scenario weight assigned to survival through the start of policy year t.
--
--   **Mathematical statement**
--
--   $$
--   S_t=\sum_\omega w_\omega\mathbf1_{\{K_\omega\ge t\}}
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteMortalitySurvivalMass {Ω : Type*} [Fintype Ω]
  (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ) : ℝ :=
  ∑ ω : Ω, if t ≤ K ω then w ω else 0

end ActuarialValuation


