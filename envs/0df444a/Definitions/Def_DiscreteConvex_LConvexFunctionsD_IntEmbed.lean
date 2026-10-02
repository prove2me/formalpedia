-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_IntEmbed
-- name    : DiscreteConvex_LConvexFunctionsD_IntEmbed
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:42.128985+00:00
-- url     : https://prove2.me/theorems/cfa04a4d-9c9f-4f37-b2d6-7925cc73f365
-- title:
--   IntEmbed
-- statement:
--   The real embedding of a set of integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115, redeclared

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The real embedding of a set of integer vectors. -/
def IntEmbed (D : Set (V → ℤ)) : Set (V → ℝ) :=
  (fun x : V → ℤ => fun v => (x v : ℝ)) '' D

end DiscreteConvex.LConvexFunctionsD


