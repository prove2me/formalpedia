-- Prove2me | Definitions.Def_LL_Task580_eta2
-- name    : LL_Task580_eta2
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T17:38:55.396687+00:00
-- url     : https://prove2.me/theorems/02a22110-a560-4410-99d1-5e11bf608840
-- title:
--   Helfgott's weight $\eta_2(t)=4\max(\log 2-|\log 2t|,0)$
-- statement:
--   For real $t$, $\eta_2(t)=4\max(\log 2-|\log 2t|,0)$ when $t>0$ and $\eta_2(t)=0$ otherwise; it is supported on $[1/4,1]$ with peak $4\log 2$ at $t=1/2$.

import Mathlib

namespace LL_Task580

noncomputable section

noncomputable def eta2 (t : ℝ) : ℝ :=
  if 0 < t then 4 * max (Real.log 2 - |Real.log (2 * t)|) 0 else 0

end

end LL_Task580


