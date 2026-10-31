-- Prove2me | Definitions.Def_DeltaSLearning_xi
-- name    : DeltaSLearning_xi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:08:22.079994+00:00
-- url     : https://prove2.me/theorems/73c99c50-b8fa-4c95-ac46-739a09fefc74
-- title:
--   Step-size constant $\xi=\nu/\sqrt2$
-- statement:
--   The constant $\xi := \nu/\sqrt{2}$ of (18). The algorithm's step sizes are $\eta^n=\beta/(\xi\sqrt n)$, and $\xi^2=\nu^2/2$ bounds the second moment of the stochastic gradient (Lemma 3(b)).
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (18), p.17

import Mathlib
import Definitions.Def_DeltaSLearning_nu

namespace DeltaSLearning

/-- The step-size constant `ξ = ν/√2` of (18).
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (18),
p.17. -/
noncomputable def xi (cp : Params) : ℝ :=
  nu cp / Real.sqrt 2

end DeltaSLearning


