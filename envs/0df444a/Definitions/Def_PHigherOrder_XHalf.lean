-- Prove2me | Definitions.Def_PHigherOrder_XHalf
-- name    : PHigherOrder_XHalf
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:15:46.186493+00:00
-- url     : https://prove2.me/theorems/e85317de-4fe0-42ce-940d-7852ece83e89
-- title:
--   XHalf
-- statement:
--   Definitions and structural lemmas for XHalf, from na0b and contributors's pinned Higher-order estimates for planar p-harmonic functions under the stated hypotheses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/XHalf.lean

import Definitions.Def_PHigherOrder_Plane
set_option autoImplicit false
abbrev XHalf : Type :=
  ↥(Metric.closedBall (0 : Plane) (1 / 2))


