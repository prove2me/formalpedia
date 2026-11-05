-- Prove2me | Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
-- name    : AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-03T23:31:27.11456+00:00
-- url     : https://prove2.me/theorems/66a113ed-6260-42ea-862c-576aa1e2b0cb
-- title:
--   Original source intrinsic finite-band compensated negative small jumps
-- statement:
--   For original X on the original Omega, define Jsmall^(n)(t,omega) as the literal intrinsic marked jump integral over times (0,t] and marks (-1,-1/(n+1)], minus t times the corresponding source X.nu signed mark integral. The cutoff endpoint is included, -1 excluded; no Brownian process, isometry or martingale is assumed.
-- source:
--   Actual original SpectrallyNegativeLevy X.X left-limit jump-counting measure and X.nu; supported by Proved original finite-mark source finiteness 3537a106, P4-H signed source band integrability 1fa1d6da (currently proof pending) and Proved negative truncation ν integrability 16a2d301.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- The genuine original source X compensated small-negative-jump finite-band
process, with strict -1 and inclusive cutoff -(n+1)⁻¹. Pathwise and ν-side
integrability are separate P4-H theorems; no martingale property is asserted. -/
noncomputable def avram_p4_h_gaussian_intrinsic_small_band_compensated
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  (∫ p in (Ioc (0 : ℝ≥0) t ×ˢ
      Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))),
      p.2 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) -
    (t : ℝ) * (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))),
      z ∂X.ν)

end AvramDividend.Classical


