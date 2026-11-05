-- Prove2me | Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
-- name    : AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-04T00:04:29.104406+00:00
-- url     : https://prove2.me/theorems/33b0fa2b-3cba-4ea7-b17c-5b323c4d5edb
-- title:
--   Actual original Levy process minus drift, finite-band compensated small jumps and uncompensated large jumps
-- statement:
--   Define for every actual original spectrally negative Levy X and finite small-jump cutoff n the raw finite-cutoff Gaussian residual candidate R^n_t = X.X_t - t X.c - Jsmall^n_t - Jlarge_t, using only the already published same-source intrinsic jump integrals on the original Omega and X.nu. This is a genuine source process definition. Continuity, martingale, L2 limit, bracket and Gaussianity remain proof obligations.
-- source:
--   Published P4-H source Definitions 66a113ed-6260-42ea-862c-576aa1e2b0cb and 4c0b840b-c1d8-4087-81ff-ad3ec077ddde; exact source drift X.c. The finite-band source integral-to-jump sum theorem 79505e86 is a separately submitted proof, not assumed here.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- At each fixed cutoff, subtract the exact original process drift and the
original intrinsic compensated finite-band small jumps and large jumps.
No continuity, Gaussian law, or L2-limit is asserted for this cutoff. -/
noncomputable def avram_p4_h_gaussian_intrinsic_truncated_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  X.X t ω - (t : ℝ) * X.c -
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
    avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω

end AvramDividend.Classical


