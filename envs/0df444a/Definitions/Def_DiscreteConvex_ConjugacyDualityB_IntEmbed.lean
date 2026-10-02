-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_IntEmbed
-- name    : DiscreteConvex_ConjugacyDualityB_IntEmbed
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:27:17.183974+00:00
-- url     : https://prove2.me/theorems/e77e6c61-1901-48b6-b53e-49a449d44b28
-- title:
--   IntEmbed
-- statement:
--   The real embedding of a set of integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115, redeclared

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The real embedding of a set of integer vectors. -/
def IntEmbed (D : Set (V → ℤ)) : Set (V → ℝ) :=
  (fun x : V → ℤ => fun v => (x v : ℝ)) '' D

end DiscreteConvex.ConjugacyDualityB


