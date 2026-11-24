-- Prove2me | Definitions.Def_LL_Decomp269bLeavesVeryLow_gaussianMellin
-- name    : LL_Decomp269bLeavesVeryLow_gaussianMellin
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T15:22:46.14064+00:00
-- url     : https://prove2.me/theorems/9fd611fd-4898-44f6-ad58-a5aa66eb5e33
-- title:
--   Mellin transform of the twisted Gaussian $e^{-t^2/2}e(\delta t)$
-- statement:
--   For real $\delta$ and complex $s$, $G_\delta(s)$ is the Mellin transform at $s$ of the function $t\mapsto e^{-t^2/2}\,e(\delta t)$, that is $\int_0^\infty e^{-t^2/2}e(\delta t)t^{s-1}\,dt$ in the sense of the Mathlib Mellin transform.

import Mathlib
import Definitions.Def_LL_Decomp269bLeavesVeryLow_e

namespace LL_Decomp269bLeavesVeryLow

noncomputable section

open Real

noncomputable def gaussianMellin (δ : ℝ) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)) s

end

end LL_Decomp269bLeavesVeryLow


