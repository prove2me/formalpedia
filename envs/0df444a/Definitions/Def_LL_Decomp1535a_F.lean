-- Prove2me | Definitions.Def_LL_Decomp1535a_F
-- name    : LL_Decomp1535a_F
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-30T14:08:31.676531+00:00
-- url     : https://prove2.me/theorems/188db3a5-d90e-4a19-ac52-73d4d1c0d426
-- title:
--   Circle method integrand
-- statement:
--   $F_N(\alpha)=S_N(\alpha)^3 \, e^{-2\pi i \alpha N}$, a complex number for natural $N$ and real $\alpha$.

import Mathlib
import Definitions.Def_LL_Decomp1535a_S

namespace LL_Decomp1535a

noncomputable section

open MeasureTheory

noncomputable def F (N : ℕ) (α : ℝ) : ℂ :=
  S N α ^ 3 * Complex.exp (-(2 * Real.pi * Complex.I * α * N))

end

end LL_Decomp1535a


