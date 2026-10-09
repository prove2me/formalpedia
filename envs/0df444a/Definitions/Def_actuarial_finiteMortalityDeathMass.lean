-- Prove2me | Definitions.Def_actuarial_finiteMortalityDeathMass
-- name    : actuarial_finiteMortalityDeathMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T07:02:48.486983+00:00
-- url     : https://prove2.me/theorems/e580d698-8201-4068-ad65-88433ae60a6d
-- title:
--   Finite-scenario death-year probability mass
-- statement:
--   Total scenario weight for death during policy year t, with death benefit due at time t+1.
--
--   **Mathematical statement**
--
--   $$
--   D_t=\sum_\omega w_\omega\mathbf1_{\{K_\omega=t\}}
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteMortalityDeathMass {Ω : Type*} [Fintype Ω]
  (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ) : ℝ :=
  ∑ ω : Ω, if K ω = t then w ω else 0

end ActuarialValuation


