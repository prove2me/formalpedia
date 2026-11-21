-- Prove2me | Definitions.Def_LL_Gauss_upper_window_mid_gaussianMellin
-- name    : LL_Gauss_upper_window_mid_gaussianMellin
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:55:30.308676+00:00
-- url     : https://prove2.me/theorems/58580abe-84c5-4cc3-89f1-8c4fa9994adf
-- title:
--   The Mellin transform $F_\delta$ of a modulated Gaussian
-- statement:
--   For real $\delta$ and complex $s$, the complex number $F_\delta(s)=\int_0^\infty t^{s-1}e^{-t^2/2}e(\delta t)\,dt$, the Mellin transform of $t\mapsto e^{-t^2/2}e(\delta t)$ on $(0,\infty)$, where $e(x)=e^{2\pi i x}$. As for every Bochner integral, the value is $0$ when the integrand is not integrable; for $\operatorname{Re}s>0$ it is integrable.

import Mathlib
import Definitions.Def_LL_Gauss_upper_window_mid_e

namespace LL_Gauss_upper_window_mid

noncomputable section

open Real

noncomputable def gaussianMellin (δ : ℝ) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)) s

end

end LL_Gauss_upper_window_mid


