-- Prove2me | Definitions.Def_LL_Burst9MatrixR2_alpha
-- name    : LL_Burst9MatrixR2_alpha
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-21T04:33:33.171263+00:00
-- url     : https://prove2.me/theorems/b13f2234-3493-4b4c-83de-680b65ebf043
-- title:
--   Wu's nine endpoints $\alpha_1,\dots,\alpha_9$
-- statement:
--   For parameters $p$, the function on Fin 9 whose value at index $j$, counted from 0, is Wu's $\alpha_{j+1}$: $\alpha_1=\kappa_1-2$, $\alpha_2=s'-2$, $\alpha_3=s'-s'/s-1$, $\alpha_4=s'-s'/\kappa_2-1$, $\alpha_5=s'-s'/\kappa_3-1$, $\alpha_6=s'-2s'/\kappa_2$, $\alpha_7=s'-s'/\kappa_1-s'/\kappa_3$, $\alpha_8=s'-s'/\kappa_1-s'/\kappa_2$, $\alpha_9=\kappa_1-\kappa_1/\kappa_2-1$. Division is real division, which returns 0 on a zero denominator.

import Mathlib
import Definitions.Def_LL_Burst9MatrixR2_Params

namespace LL_Burst9MatrixR2

noncomputable section

open Real Set MeasureTheory
open scoped Classical

def alpha (p : Params) : Fin 9 → ℝ :=
  ![p.k1 - 2, p.sp - 2, p.sp - p.sp / p.s - 1,
    p.sp - p.sp / p.k2 - 1, p.sp - p.sp / p.k3 - 1, p.sp - 2 * p.sp / p.k2,
    p.sp - p.sp / p.k1 - p.sp / p.k3,
    p.sp - p.sp / p.k1 - p.sp / p.k2, p.k1 - p.k1 / p.k2 - 1]

end

end LL_Burst9MatrixR2


