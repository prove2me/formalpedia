-- Prove2me | Definitions.Def_LL_Burst9MatrixR2_sigma
-- name    : LL_Burst9MatrixR2_sigma
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-21T04:33:57.822613+00:00
-- url     : https://prove2.me/theorems/ecc4eb16-331f-4d4c-aa72-be08c5ece044
-- title:
--   Wu's logarithmic integral $\sigma(a,b,c)$
-- statement:
--   $\sigma(a,b,c)$ is the oriented interval integral $\int_a^b \log\frac{c}{t-1}\,\frac{dt}{t}$, so it changes sign when $a>b$, and as a Bochner integral it is 0 if the integrand is not integrable. Real log and division follow the conventions $\log 0=0$, $\log x=\log|x|$ for $x<0$ and $x/0=0$.

import Mathlib

namespace LL_Burst9MatrixR2

noncomputable section

open Real Finset Set MeasureTheory intervalIntegral

def sigma (a b c : ℝ) : ℝ := ∫ t in a..b, log (c / (t - 1)) / t

end

end LL_Burst9MatrixR2


