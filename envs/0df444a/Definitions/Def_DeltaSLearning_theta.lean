-- Prove2me | Definitions.Def_DeltaSLearning_theta
-- name    : DeltaSLearning_theta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:09:24.667992+00:00
-- url     : https://prove2.me/theorems/c5d13bb8-bf61-4b3e-b37d-6eed42966d9d
-- title:
--   Confidence constant $\theta$
-- statement:
--   The constant
--   $$\theta := (2\gamma+4)\max(\nu,b)+1.5\,\beta\xi ,$$
--   which sets the confidence sizes $\Delta^n=2\theta\log(8N^2)/\sqrt n$ of Theorem 3 and the width of the estimation bound of Lemma 4.
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (18), p.17, and eq. (32), p.24

import Mathlib
import Definitions.Def_DeltaSLearning_xi
import Definitions.Def_DeltaSLearning_bSub

namespace DeltaSLearning

/-- The confidence constant `θ = (2γ + 4) max(ν, b) + 1.5 β ξ` of (18) and (32).
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (18),
p.17, and eq. (32), p.24. -/
noncomputable def theta (cp : Params) : ℝ :=
  (2 * gamma cp + 4) * max (nu cp) (bSub cp) + 1.5 * cp.β * xi cp

end DeltaSLearning


