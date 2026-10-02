-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_IntEmbed
-- name    : DiscreteConvex_LConvexFunctionsC_IntEmbed
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:32:10.217088+00:00
-- url     : https://prove2.me/theorems/82c66f9e-e23a-4f89-a376-e09400e9aec2
-- title:
--   IntEmbed
-- statement:
--   The real embedding of a set of integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115, redeclared

import Mathlib

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The real embedding of a set of integer vectors. -/
def IntEmbed (D : Set (V → ℤ)) : Set (V → ℝ) :=
  (fun x : V → ℤ => fun v => (x v : ℝ)) '' D

end DiscreteConvex.LConvexFunctionsC


