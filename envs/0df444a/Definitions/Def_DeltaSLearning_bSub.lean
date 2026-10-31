-- Prove2me | Definitions.Def_DeltaSLearning_bSub
-- name    : DeltaSLearning_bSub
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:07:17.934588+00:00
-- url     : https://prove2.me/theorems/a6407c92-fa82-4e60-9d56-f21845a8f26c
-- title:
--   Sub-exponential parameter $b=2\gamma$
-- statement:
--   The constant $b := 2\gamma$, the second sub-exponential parameter of Lemma 3 and of the tuning constant $\theta$.
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (19), p.17, and eq. (31), p.23

import Mathlib
import Definitions.Def_DeltaSLearning_gamma

namespace DeltaSLearning

/-- The sub-exponential parameter `b = 2γ` of (19) and (31).
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (19),
p.17, and eq. (31), p.23. -/
noncomputable def bSub (cp : Params) : ℝ :=
  2 * gamma cp

end DeltaSLearning


