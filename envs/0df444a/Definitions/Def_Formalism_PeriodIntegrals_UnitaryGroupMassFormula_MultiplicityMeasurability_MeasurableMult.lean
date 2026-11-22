-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MultiplicityMeasurability_MeasurableMult
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MultiplicityMeasurability_MeasurableMult
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:15.05089+00:00
-- url     : https://prove2.me/theorems/df581c6a-7cf7-45ff-9c95-f382955a09ea
-- title:
--   Measurable Mult
-- statement:
--   Definitions and structural lemmas for Measurable Mult, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MultiplicityMeasurability/MeasurableMult.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FoldMult
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
namespace PI.FoldMult.UnitaryGroupMassFormula
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
def cnt (Γ : Subgroup G) (Ω : Set G) (x y : G) : Set Γ := {γ : Γ | x⁻¹ * ((γ : G) * y) ∈ Ω}
def hitSet (Γ : Subgroup G) (Ω : Set G) (A : Finset Γ) : Set G :=
  {x | ∃ y : G, ∀ a ∈ A, x⁻¹ * ((a : G) * y) ∈ Ω}
end PI.FoldMult.UnitaryGroupMassFormula


