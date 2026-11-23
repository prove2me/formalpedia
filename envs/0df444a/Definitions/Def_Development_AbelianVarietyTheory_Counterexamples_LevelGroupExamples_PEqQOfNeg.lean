-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_PEqQOfNeg
-- name    : Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_PEqQOfNeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:03.449288+00:00
-- url     : https://prove2.me/theorems/1da7d6ed-1574-410a-8cb7-091c64206420
-- title:
--   PEq QOf Neg
-- statement:
--   Definitions and structural lemmas for PEq QOf Neg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/PEqQOfNeg.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DatumSign
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Module
open scoped TensorProduct
section Lin
variable {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
end Lin
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
end GlobalTheory.DatumSign


