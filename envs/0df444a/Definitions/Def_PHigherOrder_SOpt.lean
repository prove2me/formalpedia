-- Prove2me | Definitions.Def_PHigherOrder_SOpt
-- name    : PHigherOrder_SOpt
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:08:52.583063+00:00
-- url     : https://prove2.me/theorems/1bce5e2c-c418-428a-a8b2-307231206ecf
-- title:
--   SOpt
-- statement:
--   Definitions and structural lemmas for SOpt, from na0b and contributors's pinned Higher-order estimates for planar p-harmonic functions under the stated hypotheses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/SOpt.lean

import Definitions.Def_PHigherOrder_Preamble
set_option autoImplicit false
noncomputable def SOpt (p : ℝ) : ℝ :=
  (7 + 1 / (p - 1) + Real.sqrt (1 + 14 / (p - 1) + 1 / (p - 1) ^ 2)) / 6


