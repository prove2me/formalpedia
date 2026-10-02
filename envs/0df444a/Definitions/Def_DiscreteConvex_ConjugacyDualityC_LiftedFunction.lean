-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_LiftedFunction
-- name    : DiscreteConvex_ConjugacyDualityC_LiftedFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:40:59.445093+00:00
-- url     : https://prove2.me/theorems/7581c875-9d4c-43b4-b95c-ea8b1acaad95
-- title:
--   LiftedFunction
-- statement:
--   The lift of $f$ to $\tilde V=\{0\}\cup V$ (as `Option V`).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, Eq. (6.4).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, Eq. (6.4)

import Mathlib

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The lift of `f` to `Ṽ = {0}∪V` (as `Option V`). -/
def LiftedFunction (f : (V → ℤ) → WithTop ℝ) : (Option V → ℤ) → WithTop ℝ :=
  fun x => if x none = -(∑ v : V, x (some v)) then f (fun v => x (some v)) else ⊤

end DiscreteConvex.ConjugacyDualityC


