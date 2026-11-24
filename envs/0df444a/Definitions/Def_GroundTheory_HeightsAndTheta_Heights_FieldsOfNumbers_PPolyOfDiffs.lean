-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:59.367163+00:00
-- url     : https://prove2.me/theorems/42935fa2-64f8-471f-8044-e3a7932add54
-- title:
--   PPoly Of Diffs
-- statement:
--   Definitions and structural lemmas for PPoly Of Diffs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPolyOfDiffs.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
namespace PolyOfDiffs
variable {K : Type}
variable [DecidableEq K]
noncomputable def freeze (s : Finset K) (N : K → ℚ) : K → MvPolynomial K ℚ :=
  fun j => if j ∈ s then X j else C (N j)
def pathPt (N : K → ℤ) (s : Finset K) (m : K → ℤ) : K → ℤ :=
  fun j => if j ∈ s then m j else N j
end PolyOfDiffs
end GroundTheory.Heights₂.Heights.FieldNumbers


