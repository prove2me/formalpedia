-- Prove2me | Definitions.Def_LL_Gauss_lower_window_high_gaussianMellin
-- name    : LL_Gauss_lower_window_high_gaussianMellin
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:59:10.549162+00:00
-- url     : https://prove2.me/theorems/b0b99ffe-b0be-48e5-ab07-5067dffb2630
-- title:
--   The Mellin transform $F_\delta$ of a modulated Gaussian
-- statement:
--   For real $\delta$ and complex $s$, the complex number $F_\delta(s)=\int_0^\infty t^{s-1}e^{-t^2/2}e(\delta t)\,dt$, the Mellin transform of $t\mapsto e^{-t^2/2}e(\delta t)$ on $(0,\infty)$, where $e(x)=e^{2\pi i x}$. As for every Bochner integral, the value is $0$ when the integrand is not integrable; for $\operatorname{Re}s>0$ it is integrable.

import Mathlib
import Definitions.Def_LL_Gauss_lower_window_high_e

namespace LL_Gauss_lower_window_high

noncomputable section

open Real

noncomputable def gaussianMellin (δ : ℝ) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)) s

end

end LL_Gauss_lower_window_high


