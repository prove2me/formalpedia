-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
-- name    : ReciprocityTheory_SemistableReduction_TorusMeanA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:48.864125+00:00
-- url     : https://prove2.me/theorems/06a77a64-4f0b-4310-a067-dbae7d404e14
-- title:
--   Torus Mean A
-- statement:
--   Definitions and structural lemmas for Torus Mean A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Polynomial Real
def circPt (t : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * (t : ℂ))
instance isProbabilityMeasure_restrict_Ioc :
    IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
  ⟨by simp⟩
end ReciprocityTheory.MultiplicativeHeights


