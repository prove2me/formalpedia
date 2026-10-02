-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_IntEmbed
-- name    : DiscreteConvex_ConjugacyDualityC_IntEmbed
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:41:22.453984+00:00
-- url     : https://prove2.me/theorems/8a888b2f-6c4f-4c3d-afd7-82c09c6e14a5
-- title:
--   IntEmbed
-- statement:
--   The real embedding of a set of integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115, redeclared

import Mathlib

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The real embedding of a set of integer vectors. -/
def IntEmbed (D : Set (V → ℤ)) : Set (V → ℝ) :=
  (fun x : V → ℤ => fun v => (x v : ℝ)) '' D

end DiscreteConvex.ConjugacyDualityC


