-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_LevelSet
-- name    : DiscreteConvex_MConvexFunctionsE_LevelSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:03:43.342987+00:00
-- url     : https://prove2.me/theorems/833d02c5-3a20-4318-b2f9-87b4895737dc
-- title:
--   LevelSet
-- statement:
--   The level set $L(f,\alpha)=\{x\in\mathbb Z^V : f(x)\le\alpha\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.172, Eq. (6.95).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.172, Eq. (6.95)

import Mathlib

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The level set `L(f, α) = {x ∈ Zⱽ | f(x) ≤ α}`, Eq. (6.95). -/
def LevelSet (f : (V → ℤ) → WithTop ℝ) (alpha : ℝ) : Set (V → ℤ) :=
  {x | f x ≤ (alpha : WithTop ℝ)}

end DiscreteConvex.MConvexFunctionsE


