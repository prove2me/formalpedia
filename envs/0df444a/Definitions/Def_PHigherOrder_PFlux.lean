-- Prove2me | Definitions.Def_PHigherOrder_PFlux
-- name    : PHigherOrder_PFlux
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:09:17.225595+00:00
-- url     : https://prove2.me/theorems/c5795f4a-74c5-4e67-b696-46a246edd94c
-- title:
--   PFlux
-- statement:
--   Definitions and structural lemmas for PFlux, from na0b and contributors's pinned Higher-order estimates for planar p-harmonic functions under the stated hypotheses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PFlux.lean

import Definitions.Def_PHigherOrder_Plane
set_option autoImplicit false
noncomputable def PFlux (p : ℝ) (ξ : Plane) : Plane :=
  ‖ξ‖ ^ (p - 2) • ξ


