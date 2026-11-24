-- Prove2me | Definitions.Def_LL_Decomp119bLeavesA2_fhat
-- name    : LL_Decomp119bLeavesA2_fhat
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T15:22:52.429949+00:00
-- url     : https://prove2.me/theorems/38564394-f683-44b9-980f-e5785c39a644
-- title:
--   The Fourier transform $\widehat f(t)=\int e(-yt)f(y)\,dy$
-- statement:
--   For a real function $f$ and real $t$, $\widehat f(t)$ is the integral over the real line of $e(-yt)f(y)$, a complex number; the integral is the Lebesgue integral, equal to $0$ when the integrand is not integrable.

import Mathlib
import Definitions.Def_LL_Decomp119bLeavesA2_e

namespace LL_Decomp119bLeavesA2

noncomputable section

open scoped ArithmeticFunction

noncomputable def fhat (f : ℝ → ℝ) (t : ℝ) : ℂ := ∫ y : ℝ, e (-(y * t)) * (f y : ℂ)

end

end LL_Decomp119bLeavesA2


