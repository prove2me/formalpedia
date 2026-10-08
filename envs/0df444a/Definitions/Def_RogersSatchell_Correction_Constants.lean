-- Prove2me | Definitions.Def_RogersSatchell_Correction_Constants
-- name    : RogersSatchell_Correction_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:43:10.640525+00:00
-- url     : https://prove2.me/theorems/5e3b5298-4897-4e50-88df-c2660f566702
-- title:
--   Section 3, p. 507 — the constants a = √(2π)[1/4 − (√2 − 1)/6] and b = (1 + 3π/4)/12
-- statement:
--   The two numerical constants of Section 3 of Rogers and Satchell are
--
--   $$a \;=\; \sqrt{2\pi}\,\Big[\tfrac14 - \tfrac{\sqrt2 - 1}{6}\Big]\approx 0.4536,\qquad b \;=\; \frac{1 + 3\pi/4}{12}\approx 0.2797 .$$
--
--   The paper introduces them on p. 507 as the coefficients in $E\Delta \approx a\sigma\sqrt h$ and $E\Delta^2 \approx b\sigma^2 h$, where $\Delta$ is the amount by which the maximum of a random walk sampled at mesh $h$ underestimates the maximum of the continuous log-price path. They enter the corrected estimator (5).
--
--   **Formalization Note.** Both constants are stated symbolically with `Real.sqrt` and `Real.pi`; the decimal values above are for orientation only. The print's "$\sqrt{2\pi}$" has its radical over $2\pi$, as Eq. (11) confirms.
-- source:
--   Rogers and Satchell, Estimating variance from high, low and closing prices, Ann. Appl. Probab. 1 (1991), p. 507, Section 3 (definitions of a and b)

import Mathlib

namespace RogersSatchell.Correction

/-- The constant `a = √(2π) [1/4 − (√2 − 1)/6]` of §3, p. 507 (Rogers–Satchell 1991). -/
noncomputable def constA : ℝ := Real.sqrt (2 * Real.pi) * (1 / 4 - (Real.sqrt 2 - 1) / 6)

/-- The constant `b = (1 + 3π/4)/12` of §3, p. 507 (Rogers–Satchell 1991). -/
noncomputable def constB : ℝ := (1 + 3 * Real.pi / 4) / 12

end RogersSatchell.Correction


