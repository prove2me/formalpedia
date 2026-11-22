-- Prove2me | Definitions.Def_PHigherOrder_NormalizedWeakGradient
-- name    : PHigherOrder_NormalizedWeakGradient
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:11:40.129804+00:00
-- url     : https://prove2.me/theorems/b5c40ec5-4381-4129-a718-30965ee4c8dd
-- title:
--   Normalized Weak Gradient
-- statement:
--   Definitions and structural lemmas for Normalized Weak Gradient, from na0b and contributors's pinned Higher-order estimates for planar p-harmonic functions under the stated hypotheses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/NormalizedWeakGradient.lean

import Definitions.Def_PHigherOrder_IsPHarm
import Definitions.Def_PHigherOrder_TestFunctionGradientIntegral
import Definitions.Def_PHigherOrder_AffineTestFunctionPullback
import Definitions.Def_PHigherOrder_VanishingOffTsupport
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Theorems.Thm_AffineTestFunctionPullback
import Theorems.Thm_TestFunctionGradientIntegral
import Theorems.Thm_VanishingOffTsupport

set_option autoImplicit false


