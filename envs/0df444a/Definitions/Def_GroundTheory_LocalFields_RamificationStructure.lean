-- Prove2me | Definitions.Def_GroundTheory_LocalFields_RamificationStructure
-- name    : GroundTheory_LocalFields_RamificationStructure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:03.459801+00:00
-- url     : https://prove2.me/theorems/9ad93fff-74bf-4bd7-b95b-fdcb625efa28
-- title:
--   Ramification Structure
-- statement:
--   Definitions and structural lemmas for Ramification Structure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationStructure.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_RamificationUnits
import Theorems.Thm_GroundTheory_LocalField_ramificationQuotientToUnits_mk
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_residue_integerAlgEquiv_of_mem_zero
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.ramificationQuotientToUnits_mk
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel IsLocalRing
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
section Tame
variable {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include hϖ
def inertiaToResidueUnits : lowerRamificationGroup K L 0 →* 𝓀[L]ˣ where
  toFun σ := unitsToResidue L (uniformizerRatio hϖ (σ : L ≃ₐ[K] L))
  map_one' := by simp
  map_mul' σ τ := by
    rw [Subgroup.coe_mul, uniformizerRatio_mul, map_mul]
    congr 1
    ext
    exact residue_integerAlgEquiv_of_mem_zero K L σ.2 _
theorem inertiaToResidueUnits_apply (σ : lowerRamificationGroup K L 0) :
    inertiaToResidueUnits hϖ σ = unitsToResidue L (uniformizerRatio hϖ (σ : L ≃ₐ[K] L)) :=
  rfl
theorem ker_inertiaToResidueUnits :
    (inertiaToResidueUnits hϖ).ker =
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0) := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, inertiaToResidueUnits_apply,
    ← MonoidHom.mem_ker, ker_unitsToResidue]
  exact (mem_lowerRamificationGroup_iff_uniformizerRatio hϖ σ.2 1).symm
def inertiaQuotientToResidueUnits :
    lowerRamificationGroup K L 0 ⧸
        (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0) →* 𝓀[L]ˣ :=
  (QuotientGroup.kerLift (inertiaToResidueUnits hϖ)).comp
    (QuotientGroup.quotientMulEquivOfEq (ker_inertiaToResidueUnits hϖ).symm).toMonoidHom
omit hϖ
variable (K L)
variable {K L}
variable (K L)
end Tame
section Wild
variable (K L)
end Wild
end GroundTheory.LocalField


