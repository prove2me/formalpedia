-- Prove2me | Definitions.Def_actuarial_finiteMortalityInnovation
-- name    : actuarial_finiteMortalityInnovation
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T07:05:11.822218+00:00
-- url     : https://prove2.me/theorems/a3178c46-26a0-4d51-8682-70accac745fa
-- title:
--   Annual death-year martingale-difference candidate
-- statement:
--   Realised death-year indicator minus the conditional death rate multiplied by the indicator that the policy is still in force.
--
--   **Mathematical statement**
--
--   $$
--   I_t=\mathbf1_{\{K=t\}}-q_t\mathbf1_{\{K\ge t\}}
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDeathRate
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteMortalityInnovation {Ω : Type*} [Fintype Ω]
  (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ) (ω : Ω) : ℝ :=
  (if K ω = t then 1 else 0) -
  finiteMortalityDeathRate w K t * (if t ≤ K ω then 1 else 0)

end ActuarialValuation


