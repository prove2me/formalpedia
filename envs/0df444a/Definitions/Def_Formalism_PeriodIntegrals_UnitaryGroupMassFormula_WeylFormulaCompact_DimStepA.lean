-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStepA
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStepA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:59.739788+00:00
-- url     : https://prove2.me/theorems/a2b15072-a443-448e-b569-57349fdcf8d3
-- title:
--   Dim Step A
-- statement:
--   Definitions and structural lemmas for Dim Step A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/DimStepA.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace PI.WeylForKWork.DimensionInduction
open scoped InnerProductSpace
open Module
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι κ : Type*}
def Stab (ρ : ι → H →L[ℂ] H) (W : Submodule ℂ H) : Prop := ∀ i, ∀ v ∈ W, ρ i v ∈ W
def Irr (ρ : ι → H →L[ℂ] H) (W : Submodule ℂ H) : Prop :=
  ∀ W' : Submodule ℂ H, W' ≤ W → Stab ρ W' → W' = ⊥ ∨ W' = W
structure Good (ρ : ι → H →L[ℂ] H) : Prop where
  isom : ∀ i v, ‖ρ i v‖ = ‖v‖
  inv : ∀ i, ∃ j, ∀ v, ρ i (ρ j v) = v
  mul : ∀ i i', ∃ k, ∀ v, ρ i (ρ i' v) = ρ k v
  one : ∃ i, ∀ v, ρ i v = v
def Comm (ρ : ι → H →L[ℂ] H) (c : H →ₗ[ℂ] H) : Prop := ∀ i v, c (ρ i v) = ρ i (c v)
def commSub (ρ : ι → H →L[ℂ] H) : Submodule ℂ (H →ₗ[ℂ] H) where
  carrier := {c | Comm ρ c}
  add_mem' := by
    intro c d hc hd
    have hc : Comm ρ c := hc
    have hd : Comm ρ d := hd
    show Comm ρ (c + d)
    intro i v
    simp only [LinearMap.add_apply, map_add, hc i v, hd i v]
  zero_mem' := by
    show Comm ρ 0
    intro i v
    simp
  smul_mem' := by
    intro a c hc
    have hc : Comm ρ c := hc
    show Comm ρ (a • c)
    intro i v
    simp only [LinearMap.smul_apply, map_smul, hc i v]
def slice (ρ : ι → H →L[ℂ] H) (x₀ : H) : Submodule ℂ H where
  carrier := {v | ∃ c : H →ₗ[ℂ] H, Comm ρ c ∧ c x₀ = v}
  add_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact ⟨c + d, (commSub ρ).add_mem hc hd, rfl⟩
  zero_mem' := ⟨0, (commSub ρ).zero_mem, rfl⟩
  smul_mem' := by
    rintro a _ ⟨c, hc, rfl⟩
    exact ⟨a • c, (commSub ρ).smul_mem a hc, rfl⟩
variable {ρ : ι → H →L[ℂ] H} {ρ' : κ → H →L[ℂ] H}
end PI.WeylForKWork.DimensionInduction


