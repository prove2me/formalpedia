-- Prove2me | Definitions.Def_PHigherOrder_ApproxFiniteCase
-- name    : PHigherOrder_ApproxFiniteCase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:35:11.001935+00:00
-- url     : https://prove2.me/theorems/428e6caf-faf7-4b94-af3f-302e26d3d235
-- title:
--   Approx Finite Case
-- statement:
--   Definitions and structural lemmas for Approx Finite Case, from na0b and contributors's pinned Higher-order estimates for planar p-harmonic functions under the stated hypotheses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/ApproxFiniteCase.lean

import Definitions.Def_PHigherOrder_IMRegularityInput
import Definitions.Def_PHigherOrder_Noncritical
import Definitions.Def_PHigherOrder_PHarmNormalize
import Definitions.Def_PHigherOrder_TaylorPolyDeriv
import Definitions.Def_PHigherOrder_TaylorPolyFarBound
import Definitions.Def_PHigherOrder_TaylorPolyRescale
import Definitions.Def_PHigherOrder_TaylorRemainder
import Theorems.Thm_Noncritical
import Theorems.Thm_PHarmNormalize
import Theorems.Thm_TaylorPolyDeriv
import Theorems.Thm_TaylorPolyFarBound
import Theorems.Thm_TaylorPolyRescale
import Theorems.Thm_TaylorRemainder

set_option autoImplicit false


