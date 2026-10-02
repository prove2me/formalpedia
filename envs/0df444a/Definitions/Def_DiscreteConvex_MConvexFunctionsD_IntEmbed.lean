-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_IntEmbed
-- name    : DiscreteConvex_MConvexFunctionsD_IntEmbed
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:48:21.899322+00:00
-- url     : https://prove2.me/theorems/b1514536-11b5-4f9e-aef9-807ae7cb7614
-- title:
--   IntEmbed
-- statement:
--   The real embedding of a set of integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def IntEmbed (B : Set (V → ℤ)) : Set (V → ℝ) := (fun x : V → ℤ => fun v => (x v : ℝ)) '' B

end DiscreteConvex.MConvexFunctionsD


