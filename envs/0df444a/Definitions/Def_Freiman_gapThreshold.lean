-- Prove2me | Definitions.Def_Freiman_gapThreshold
-- name    : Freiman_gapThreshold
-- status  : Definition
-- author  : @tp
-- created : 2026-09-08T23:21:34.800357+00:00
-- url     : https://prove2.me/theorems/2722dead-a15a-47ad-bcc6-55d375b08d96
-- title:
--   Constants for the interval and gap constructions
-- statement:
--   Define
--   $$
--   c_0=\frac{90556591}{20000000},\qquad
--   h=\frac{21+\sqrt{21}}5,
--   $$
--   and
--   $$
--   \mu_*=4+\frac{19033619-2\sqrt{462}}{72101381}
--           +\frac{37252-\sqrt{243542}}{139318}.
--   $$
--   Every square root is nonnegative. The constant $h$ is used in the upper ray construction. The constants $c_0$ and $\mu_*$ are used in the gap statements below Freiman's constant. Their ordering and spectral properties are asserted in separate theorems.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Theorem 19.3, p. 64; §20, p. 65, including equation (20.1); and Theorem 21.1, p. 71.

import Mathlib.Analysis.Real.Sqrt

namespace Freiman

noncomputable def gapThreshold : ℝ := 90556591 / 20000000

noncomputable def upperRayStart : ℝ := (21 + Real.sqrt 21) / 5

noncomputable def gapLeft : ℝ :=
  4 + (19033619 - 2 * Real.sqrt 462) / 72101381 +
    (37252 - Real.sqrt 243542) / 139318

end Freiman


