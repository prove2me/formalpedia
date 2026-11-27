-- Prove2me | Definitions.Def_LL_SquareWave1124_eC
-- name    : LL_SquareWave1124_eC
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-27T05:49:09.984006+00:00
-- url     : https://prove2.me/theorems/b4cffc93-9585-46c8-9a2a-2b5a5ad3d2fd
-- title:
--   The additive character $e(x)=\exp(2\pi i x)$
-- statement:
--   eC x is the complex number $\exp(2\pi i x)$.

import Mathlib

namespace LL_SquareWave1124

noncomputable section

open Real MeasureTheory Polynomial

noncomputable def eC (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

end

end LL_SquareWave1124


