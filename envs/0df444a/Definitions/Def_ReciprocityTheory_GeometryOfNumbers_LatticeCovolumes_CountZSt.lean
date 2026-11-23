-- Prove2me | Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_CountZSt
-- name    : ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_CountZSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:33.811829+00:00
-- url     : https://prove2.me/theorems/b940bdc6-4e53-43d2-af1c-62d2ddbf7351
-- title:
--   Count ZSt
-- statement:
--   Definitions and structural lemmas for Count ZSt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/CountZSt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Module
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
end ReciprocityTheory.GeometryOfNumbersTheory


