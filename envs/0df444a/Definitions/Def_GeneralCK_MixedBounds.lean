-- Prove2me | Definitions.Def_GeneralCK_MixedBounds
-- name    : GeneralCK_MixedBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T21:06:23.397964+00:00
-- url     : https://prove2.me/theorems/a0bb5725-0330-4547-bd0e-b3b6ee1a1499
-- title:
--   Natural entropy and the compact mixed profile
-- statement:
--   For a real number $v$, define $h(v)=-v\log v-(1-v)\log(1-v)$ and $k(v)=-\log(v(1-v))/2$, using natural logarithms. The mixed profile is $$P(v)=\frac{2(1-2v)h(v)^2\left(2k(v)-(1-2v)^2\right)}{\log2\,(4v(1-v))^2k(v)^3}.$$ These formulas are defined for all real $v$ using Lean's real logarithm and division conventions; later interval estimates impose $0<v<1/2$. They are the exact source definitions hn, kap, and profile used in the Courtade–Kumar compact mixed-region certificates.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/MixedBounds.lean#L7-L11

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace GeneralCK.Certificates.Mixed

noncomputable def hn (v : ℝ) : ℝ := -v * Real.log v - (1-v) * Real.log (1-v)
noncomputable def kap (v : ℝ) : ℝ := -Real.log (v*(1-v))/2
noncomputable def profile (v : ℝ) : ℝ :=
  2*(1-2*v)*(hn v)^2*(2*kap v-(1-2*v)^2) /
    (Real.log 2*(4*v*(1-v))^2*(kap v)^3)









end GeneralCK.Certificates.Mixed


