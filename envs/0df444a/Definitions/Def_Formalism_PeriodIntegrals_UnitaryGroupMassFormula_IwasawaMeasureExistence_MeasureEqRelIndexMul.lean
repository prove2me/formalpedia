-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IwasawaMeasureExistence_MeasureEqRelIndexMul
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IwasawaMeasureExistence_MeasureEqRelIndexMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:24.058068+00:00
-- url     : https://prove2.me/theorems/12affe03-153d-4c17-abbd-8635e35d768b
-- title:
--   Measure Eq Rel Index Mul
-- statement:
--   Definitions and structural lemmas for Measure Eq Rel Index Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IwasawaMeasureExistence/MeasureEqRelIndexMul.lean

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
namespace PI.IwaMeasEx.MF
open MeasureTheory Measure Set
open scoped ENNReal NNReal
section Idx
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
end Idx
section Conj
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def conjSub (H : Subgroup G) (g : G) (hg : ∀ x, x ∈ H ↔ g * x * g⁻¹ ∈ H) : H ≃ₜ* H where
  toFun x := ⟨g * x * g⁻¹, (hg x).1 x.2⟩
  invFun x := ⟨g⁻¹ * x * g, (hg _).2 (by
    have e : g * (g⁻¹ * (x : G) * g) * g⁻¹ = x := by group
    rw [e]; exact x.2)⟩
  left_inv x := by ext; simp only; group
  right_inv x := by ext; simp only; group
  map_mul' x y := by ext; simp only [Subgroup.coe_mul]; group
  continuous_toFun := Continuous.subtype_mk
    ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  continuous_invFun := Continuous.subtype_mk
    ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
end Conj
section Scale
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
end Scale
end PI.IwaMeasEx.MF
end


