-- Prove2me | Definitions.Def_LL_Burst9MatrixR2_Xi1
-- name    : LL_Burst9MatrixR2_Xi1
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-21T04:35:07.267178+00:00
-- url     : https://prove2.me/theorems/edca51e5-dd28-4663-900d-8ee1ad51a78a
-- title:
--   Wu's kernel $\Xi_1$ of display 3.21
-- statement:
--   $\Xi_1(s,s',t)=\frac{\sigma_0(t)}{2t}\log\frac{16}{(s-1)(s'-1)}+\frac{\mathbf 1_{[s'-2,3]}(t)}{2t}\log\frac{(t+1)^2}{(s-1)(s'-1)}+\frac{\mathbf 1_{[s'-s'/s-1,\,s'-2]}(t)}{2t}\log\frac{t+1}{(s-1)(s'-1-t)}$, where the indicators are those of closed intervals, so $s'-2=\alpha_2$ and $s'-s'/s-1=\alpha_3$. Real log and division follow the conventions $\log 0=0$, $\log x=\log|x|$ for $x<0$ and $x/0=0$.

import Mathlib
import Definitions.Def_LL_Burst9MatrixR2_ind
import Definitions.Def_LL_Burst9MatrixR2_sigma0

namespace LL_Burst9MatrixR2

noncomputable section

open Real Set MeasureTheory
open scoped Classical

def Xi1 (s sp t : ℝ) : ℝ :=
  sigma0 t / (2 * t) * log (16 / ((s - 1) * (sp - 1))) +
  ind (sp - 2) 3 t / (2 * t) * log ((t + 1) ^ 2 / ((s - 1) * (sp - 1))) +
  ind (sp - sp / s - 1) (sp - 2) t / (2 * t) *
    log ((t + 1) / ((s - 1) * (sp - 1 - t)))

end

end LL_Burst9MatrixR2


