-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_InfDiff
-- name    : DiscreteConvex_ConjugacyDualityB_InfDiff
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:31:44.273988+00:00
-- url     : https://prove2.me/theorems/b6c56043-28db-420e-abe3-5eafcde12c83
-- title:
--   InfDiff
-- statement:
--   $\inf\{f(x)-h(x):x\in\mathbb Z^V\}$, computed as $\inf\{f(x)+h_2(x)\}$ since $h_2=-h$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.222, Eq. (8.31).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.222, Eq. (8.31)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ToEReal

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `inf{f(x) - h(x) : x ∈ Zⱽ} = inf{f(x) + h2(x) : x ∈ Zⱽ}` since `h2 = -h`. -/
noncomputable def InfDiff (f h2 : (V → ℤ) → WithTop ℝ) : EReal :=
  sInf {v : EReal | ∃ x : V → ℤ, v = ToEReal (f x) + ToEReal (h2 x)}

end DiscreteConvex.ConjugacyDualityB


