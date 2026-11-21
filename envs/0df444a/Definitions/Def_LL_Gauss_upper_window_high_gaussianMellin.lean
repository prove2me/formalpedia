-- Prove2me | Definitions.Def_LL_Gauss_upper_window_high_gaussianMellin
-- name    : LL_Gauss_upper_window_high_gaussianMellin
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:48:10.677684+00:00
-- url     : https://prove2.me/theorems/2a94d319-f0b3-4543-a710-e4620e19d4c6
-- title:
--   The Mellin transform $F_\delta$ of a modulated Gaussian
-- statement:
--   For real $\delta$ and complex $s$, the complex number $F_\delta(s)=\int_0^\infty t^{s-1}e^{-t^2/2}e(\delta t)\,dt$, the Mellin transform of $t\mapsto e^{-t^2/2}e(\delta t)$ on $(0,\infty)$, where $e(x)=e^{2\pi i x}$. As for every Bochner integral, the value is $0$ when the integrand is not integrable; for $\operatorname{Re}s>0$ it is integrable.

import Mathlib
import Definitions.Def_LL_Gauss_upper_window_high_e

namespace LL_Gauss_upper_window_high

noncomputable section

open Real

noncomputable def gaussianMellin (δ : ℝ) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)) s

end

end LL_Gauss_upper_window_high


