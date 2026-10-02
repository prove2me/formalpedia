-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_IntEmbed
-- name    : DiscreteConvex_MConvexFunctionsC_IntEmbed
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:15:26.116886+00:00
-- url     : https://prove2.me/theorems/58d85ce8-4597-4e6e-95c5-6533de61d92a
-- title:
--   IntEmbed
-- statement:
--   The real embedding of a set of integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results

import Mathlib

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The real embedding of a set of integer vectors. -/
def IntEmbed (B : Set (V → ℤ)) : Set (V → ℝ) := (fun x : V → ℤ => fun v => (x v : ℝ)) '' B

end DiscreteConvex.MConvexFunctionsC


