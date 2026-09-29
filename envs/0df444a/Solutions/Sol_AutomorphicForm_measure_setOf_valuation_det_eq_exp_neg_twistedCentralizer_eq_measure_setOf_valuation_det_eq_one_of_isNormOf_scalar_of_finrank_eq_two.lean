-- Prove2me | solution 1 for AutomorphicForm.measure_setOf_valuation_det_eq_exp_neg_twistedCentralizer_eq_measure_setOf_valuation_det_eq_one_of_isNormOf_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/dd12ce9a-9bb4-554e-9320-5dad002e3bc5

import Theorems.Thm_AutomorphicForm_exists_mem_twistedCentralizer_valuation_eq_exp_neg_one_and_det_eq_of_isNormOf_scalar_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_measure_setOf_valuation_det_eq_exp_neg_twistedCentralizer_eq_measure_setOf_valuation_det_eq_one_of_isNormOf_scalar_of_finrank_eq_two
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions Pointwise

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

namespace AutomorphicForm
p2m_export "AutomorphicForm" "exists_mem_twistedCentralizer_valuation_eq_exp_neg_one_and_det_eq_of_isNormOf_scalar_of_finrank_eq_two IsNormOf twistedCentralizer twistedCentralizerBorel"
namespace TwistedNrdShell
p2m_open "AutomorphicForm"

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)} {σ : L ≃ₐ[K] L} {δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}

noncomputable abbrev incl (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* (L ⊗[K] v.adicCompletion K)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight :
    v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom

variable (K L v σ δ) in

def shell (k : ℤ) : Set (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) :=
  {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = WithZero.exp (-k) ∧
    Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) = incl K L v s}

theorem valued_zpow_mul (ϖ s : (v.adicCompletion K)ˣ) (n : ℤ)
    (hϖ : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1)) :
    Valued.v (((ϖ ^ n * s : (v.adicCompletion K)ˣ)) : v.adicCompletion K) =
      WithZero.exp (-n) * Valued.v (s : v.adicCompletion K) := by
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_neg,
    zsmul_eq_mul, mul_one, Int.cast_id]

theorem shell_eq_smul (g : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
    (ϖ : (v.adicCompletion K)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1))
    (hg : Matrix.GeneralLinearGroup.det (g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) = incl K L v ϖ) (k : ℤ) :
    shell K L v σ δ k = (g ^ k) • shell K L v σ δ 0 := by
  ext t
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp only [shell, Set.mem_setOf_eq, smul_eq_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow,
    map_mul, map_inv, map_zpow, hg, neg_zero, WithZero.exp_zero]
  constructor
  · rintro ⟨s, hs, hdet⟩
    refine ⟨ϖ ^ (-k) * s, ?_, ?_⟩
    · rw [valued_zpow_mul ϖ s (-k) hϖ, hs, neg_neg, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
    · rw [hdet, map_mul, map_zpow, ← zpow_neg]
  · rintro ⟨s, hs, hdet⟩
    refine ⟨ϖ ^ k * s, ?_, ?_⟩
    · rw [valued_zpow_mul ϖ s k hϖ, hs, mul_one]
    · have h := congrArg (fun z => incl K L v ϖ ^ k * z) hdet
      simp only [← mul_assoc, ← zpow_neg, ← zpow_add, add_neg_cancel, zpow_zero, one_mul] at h
      rw [h, map_mul, map_zpow]

end AutomorphicForm.TwistedNrdShell

open AutomorphicForm.TwistedNrdShell in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (μ : Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ))
    (hμ : μ.IsMulLeftInvariant) (k : ℤ) :
    μ {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = WithZero.exp (-k) ∧
        Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
          Units.map (Algebra.TensorProduct.includeRight :
            v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} =
    μ {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
        Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
          Units.map (Algebra.TensorProduct.includeRight :
            v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} := by
  haveI := hμ
  haveI : SMulInvariantMeasure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) μ :=
    Measure.IsMulLeftInvariant.smulInvariantMeasure
  obtain ⟨g, hgmem, ϖ, hϖ, hg⟩ :=
    AutomorphicForm.exists_mem_twistedCentralizer_valuation_eq_exp_neg_one_and_det_eq_of_isNormOf_scalar_of_finrank_eq_two
      K L h2 σ hgen v c δ hδ
  have h0 : shell K L v σ δ 0 =
      {t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
        Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
          Units.map (Algebra.TensorProduct.includeRight :
            v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} := by
    simp only [shell, neg_zero, WithZero.exp_zero]
  have hk : shell K L v σ δ k =
      {t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = WithZero.exp (-k) ∧
        Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
          Units.map (Algebra.TensorProduct.includeRight :
            v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} := rfl
  rw [← hk, ← h0, shell_eq_smul ⟨g, hgmem⟩ ϖ hϖ hg k, measure_smul]

end S_AutomorphicForm_measure_setOf_valuation_det_eq_exp_neg_twistedCentralizer_eq_measure_setOf_valuation_det_eq_one_of_isNormOf_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_measure_setOf_valuation_det_eq_exp_neg_twistedCentralizer_eq_measure_setOf_valuation_det_eq_one_of_isNormOf_scalar_of_finrank_eq_two (solution)
