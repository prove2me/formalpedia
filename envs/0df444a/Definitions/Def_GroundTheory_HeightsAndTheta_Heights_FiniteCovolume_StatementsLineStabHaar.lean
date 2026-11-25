-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsLineStabHaar
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsLineStabHaar
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:47:57.502166+00:00
-- url     : https://prove2.me/theorems/da4e0872-84ab-4a9d-aae0-bed66f2c94ca
-- title:
--   Statements Line Stab Haar
-- statement:
--   Definitions and structural lemmas for Statements Line Stab Haar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsLineStabHaar.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVecFixGroup
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
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal
noncomputable section
section LineStab
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]
def lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    Subgroup (archUnitary h v) where
  carrier := {g | ∀ w, ∃ c : ℂ, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
    c • vecAt v x₀ w}
  one_mem' w := ⟨1, by simp⟩
  mul_mem' {a b} ha hb w := by
    obtain ⟨c, hc⟩ := ha w
    obtain ⟨d, hd⟩ := hb w
    refine ⟨c * d, ?_⟩
    simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, ← Matrix.mulVec_mulVec, hd,
      Matrix.mulVec_smul, hc, smul_smul, mul_comm d c]
  inv_mem' {a} ha w := by
    obtain ⟨c, hc⟩ := ha w
    have e : (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *
        ((a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = 1 := by
      rw [Subgroup.coe_inv, Pi.inv_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hz : vecAt v x₀ w = (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
        Matrix ι ι ℂ) *ᵥ (((a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w) := by
      rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
    by_cases hc0 : c = 0
    · have h0 : vecAt v x₀ w = 0 := by
        rw [hz, hc, hc0, zero_smul, Matrix.mulVec_zero]
      exact ⟨0, by rw [h0, Matrix.mulVec_zero, smul_zero]⟩
    · refine ⟨c⁻¹, ?_⟩
      calc (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w
          = c⁻¹ • ((((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
              (c • vecAt v x₀ w)) := by
            rw [Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        _ = c⁻¹ • vecAt v x₀ w := by rw [← hc, ← hz]
omit [NumberField E] in
theorem mem_lineStab {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W} {g : archUnitary h v} :
    g ∈ lineStab h v x₀ ↔ ∀ w, ∃ c : ℂ,
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = c • vecAt v x₀ w :=
  Iff.rfl
omit [NumberField E] in

theorem isClosed_lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    IsClosed (lineStab h v x₀ : Set (archUnitary h v)) := by
  have : (lineStab h v x₀ : Set (archUnitary h v)) = ⋂ w, (fun g : archUnitary h v =>
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w) ⁻¹'
        (Submodule.span ℂ {vecAt v x₀ w} : Set (ι → ℂ)) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, Submodule.mem_span_singleton,
      mem_lineStab]
    exact forall_congr' fun w => ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩
  rw [this]
  refine isClosed_iInter fun w => IsClosed.preimage ?_ (Submodule.closed_of_finiteDimensional _)
  exact (Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)).matrix_mulVec
    continuous_const
instance locallyCompactSpace_lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    LocallyCompactSpace (lineStab h v x₀) :=
  (isClosed_lineStab h v x₀).isClosedEmbedding_subtypeVal.locallyCompactSpace
instance secondCountableTopology_lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    SecondCountableTopology (lineStab h v x₀) :=
  TopologicalSpace.Subtype.secondCountableTopology _
end LineStab
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def LineStabHaar.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ : W, x₀ ≠ 0 → h.toSesq x₀ x₀ = 0 →
    ∀ (μP : Measure (lineStab h v x₀)) [μP.IsHaarMeasure],
    ∃ (ν : Measure (vecFixGroup h v x₀)) (τ : (InfinitePlace E → ℂ) → archUnitary h v),
      ν.IsHaarMeasure ∧ Measurable τ ∧ (∀ b, τ b ∈ lineStab h v x₀) ∧
      (∀ b : InfinitePlace E → ℂ, (∀ w, b w ≠ 0) →
        invApply (τ b) (vecAt v x₀) = fun w => b w • vecAt v x₀ w) ∧
      ∀ φ : archUnitary h v → ℝ≥0∞, Measurable φ →
        ∫⁻ p, φ (p : archUnitary h v) ∂μP = ∫⁻ b : InfinitePlace E → ℂ,
          (∏ w, ‖b w‖ₑ ^ (2 * (finrank E W - 2))) *
            ∫⁻ x : vecFixGroup h v x₀, φ ((x : archUnitary h v) * τ b) ∂ν
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


