-- Prove2me | Definitions.Def_PHigherOrder_Plane
-- name    : PHigherOrder_Plane
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:08:51.093769+00:00
-- url     : https://prove2.me/theorems/9c067e95-06eb-4565-bcf8-5f808fae4ff0
-- title:
--   Plane
-- statement:
--   Definitions and structural lemmas for Plane, from na0b and contributors's pinned Higher-order estimates for planar p-harmonic functions under the stated hypotheses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/Plane.lean

import Definitions.Def_PHigherOrder_Preamble
set_option autoImplicit false
abbrev Plane : Type :=
  EuclideanSpace ℝ (Fin 2)


