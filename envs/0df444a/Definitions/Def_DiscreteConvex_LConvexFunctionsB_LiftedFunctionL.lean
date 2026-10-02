-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsB_LiftedFunctionL
-- name    : DiscreteConvex_LConvexFunctionsB_LiftedFunctionL
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:20:47.214153+00:00
-- url     : https://prove2.me/theorems/bc466cea-243f-4f8c-a246-051e329f3afe
-- title:
--   LiftedFunctionL
-- statement:
--   The lift $\tilde g:\mathbb Z^{\tilde V}\to\mathbb R\cup\{+\infty\}$ of $g$ to $\tilde V=\{0\}\cup V$ (as `Option V`), Eq. (7.2).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, Eq. (7.2).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, Eq. (7.2)

import Mathlib

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The lift `g̃ : Z^Ṽ → R∪{+∞}` of `g` to `Ṽ = {0}∪V` (as `Option V`), Eq. (7.2). -/
def LiftedFunctionL (g : (V → ℤ) → WithTop ℝ) : (Option V → ℤ) → WithTop ℝ :=
  fun x => g (fun v => x (some v) - x none)

end DiscreteConvex.LConvexFunctionsB


