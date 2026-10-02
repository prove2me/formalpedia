-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_LiftedFunctionL
-- name    : DiscreteConvex_ConjugacyDualityB_LiftedFunctionL
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:27:02.174111+00:00
-- url     : https://prove2.me/theorems/39840f2a-43a2-4999-8ce7-bd421ad24964
-- title:
--   LiftedFunctionL
-- statement:
--   The lift of $g$ to $\tilde V$ (as `Option V`).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, Eq. (7.2).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, Eq. (7.2)

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The lift `g̃` of `g` to `Ṽ` (as `Option V`). -/
def LiftedFunctionL (g : (V → ℤ) → WithTop ℝ) : (Option V → ℤ) → WithTop ℝ :=
  fun x => g (fun v => x (some v) - x none)

end DiscreteConvex.ConjugacyDualityB


