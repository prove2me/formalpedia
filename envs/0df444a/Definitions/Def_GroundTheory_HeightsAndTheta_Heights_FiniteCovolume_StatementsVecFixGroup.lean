-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVecFixGroup
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVecFixGroup
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:19.691773+00:00
-- url     : https://prove2.me/theorems/f6fe1825-214d-568e-b002-ce1d01aa629a
-- title:
--   Statements Vec Fix Group
-- statement:
--   Definitions and structural lemmas for Statements Vec Fix Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsVecFixGroup.lean

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
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]
def vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    Subgroup (archUnitary h v) where
  carrier := {g | ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
    vecAt v x₀ w}
  one_mem' w := by simp
  mul_mem' {a b} ha hb w := by
    simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, ← Matrix.mulVec_mulVec, hb w, ha w]
  inv_mem' {a} ha w := by
    have e : (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *
        ((a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = 1 := by
      rw [Subgroup.coe_inv, Pi.inv_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w
        = (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
            (((a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w) := by rw [ha w]
      _ = vecAt v x₀ w := by rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
omit [NumberField E] in
theorem mem_vecFixGroup {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W}
    {g : archUnitary h v} : g ∈ vecFixGroup h v x₀ ↔
      ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = vecAt v x₀ w :=
  Iff.rfl
omit [NumberField E] in

theorem isClosed_vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    IsClosed (vecFixGroup h v x₀ : Set (archUnitary h v)) := by
  have : (vecFixGroup h v x₀ : Set (archUnitary h v)) = ⋂ w, {g : archUnitary h v |
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = vecAt v x₀ w} := by
    ext g
    simp [mem_vecFixGroup]
  rw [this]
  refine isClosed_iInter fun w => isClosed_eq ?_ continuous_const
  exact (Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)).matrix_mulVec
    continuous_const
instance locallyCompactSpace_vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    LocallyCompactSpace (vecFixGroup h v x₀) :=
  (isClosed_vecFixGroup h v x₀).isClosedEmbedding_subtypeVal.locallyCompactSpace
instance secondCountableTopology_vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    SecondCountableTopology (vecFixGroup h v x₀) :=
  TopologicalSpace.Subtype.secondCountableTopology _
instance sigmaFinite_vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W)
    (ν : Measure (vecFixGroup h v x₀)) [ν.IsHaarMeasure] : SigmaFinite ν :=
  inferInstance
instance measurableMul_vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    MeasurableMul (vecFixGroup h v x₀) :=
  inferInstance
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


