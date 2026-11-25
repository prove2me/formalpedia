-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnfoldAlongSubgroup
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnfoldAlongSubgroup
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:41:02.406421+00:00
-- url     : https://prove2.me/theorems/9b70e78f-2ae4-4b23-8d37-b565731c76f0
-- title:
--   Statements Unfold Along Subgroup
-- statement:
--   Definitions and structural lemmas for Statements Unfold Along Subgroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsUnfoldAlongSubgroup.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory
open scoped ENNReal
noncomputable section
def UnfoldAlongSubgroup.Statement (G Y : Type*) [Group G] [MeasurableSpace G] [MeasurableSpace Y] :
    Prop :=
  ∀ (μ : Measure G) (H : Subgroup G) [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant]
    [SFinite ν] (ρ : Measure Y) [SFinite ρ] (s : Y → G),
    Measurable (fun p : H × Y => (p.1 : G) * s p.2) →
    (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ x, f (x * s y) ∂ν ∂ρ) →
    ∀ (Γ : Subgroup G) [Countable Γ], Γ ≤ H →
    ∀ (FD : Set G) (FD₀ : Set H), IsFundamentalDomain Γ FD μ →
      IsFundamentalDomain (Γ.subgroupOf H) FD₀ ν →
    ∀ f : G → ℝ≥0∞, Measurable f → (∀ x : H, ∀ g, f (x * g) = f g) →
      ∫⁻ g in FD, f g ∂μ = ν FD₀ * ∫⁻ y, f (s y) ∂ρ
section Inhabitants
theorem measurableSingletonClass_cyclicTwo : MeasurableSingletonClass C2 :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
attribute [local instance] measurableSingletonClass_cyclicTwo
abbrev topSubgroupCyclicTwo : Subgroup C2 := ⊤
instance : MeasurableMul topSubgroupCyclicTwo :=
  ⟨fun _ => measurable_of_countable _, fun _ => measurable_of_countable _⟩
instance : (Measure.count : Measure topSubgroupCyclicTwo).IsMulLeftInvariant :=
  ⟨fun g => by
    ext s hs
    rw [Measure.map_apply (measurable_of_countable _) hs]
    have he : (fun x : topSubgroupCyclicTwo => g * x) ⁻¹' s = (fun x => g⁻¹ * x) '' s := by
      ext x
      simp
    rw [he, Measure.count_apply ((Set.to_countable _).measurableSet), Measure.count_apply hs]
    exact congrArg _ ((mul_right_injective (g⁻¹ : topSubgroupCyclicTwo)).injOn.encard_image)⟩
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


