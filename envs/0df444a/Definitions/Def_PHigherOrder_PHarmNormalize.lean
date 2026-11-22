-- Prove2me | Definitions.Def_PHigherOrder_PHarmNormalize
-- name    : PHigherOrder_PHarmNormalize
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:15:35.854539+00:00
-- url     : https://prove2.me/theorems/a5d0810a-abfd-44eb-8a10-9e69faac133d
-- title:
--   PHarm Normalize
-- statement:
--   Definitions and structural lemmas for PHarm Normalize, from na0b and contributors's pinned Higher-order estimates for planar p-harmonic functions under the stated hypotheses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PHarmNormalize.lean

import Definitions.Def_PHigherOrder_IsPHarm
import Definitions.Def_PHigherOrder_TestFunctionGradientIntegral
import Definitions.Def_PHigherOrder_AffineTestFunctionPullback
import Definitions.Def_PHigherOrder_VanishingOffTsupport
import Definitions.Def_PHigherOrder_NormalizedWeakGradient
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Theorems.Thm_AffineTestFunctionPullback
import Theorems.Thm_NormalizedWeakGradient
import Theorems.Thm_TestFunctionGradientIntegral
import Theorems.Thm_VanishingOffTsupport

set_option autoImplicit false
set_option linter.unusedVariables false


