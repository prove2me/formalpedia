-- Prove2me | solution 1 for AutomorphicForm.ne_top_and_setLIntegral_iUnion_detShell_twistedCentralizer_norm_algebraNorm_det_rpow_eq_mul_and_tendsto_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/96a9e191-c87b-5f32-895c-ec3fbedd6f78

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_lintegral_iUnion_detShell_twistedCentralizer_eq_mul_inv_sub_one_mul_inv_one_sub_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_det_mem_range_and_isOpen_isCompact_detUnits_twistedCentralizer_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_ne_top_and_setLIntegral_iUnion_detShell_twistedCentralizer_norm_algebraNorm_det_rpow_eq_mul_and_tendsto_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal NNReal Topology

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open scoped Classical

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace Ws46P2

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem finrank_tensor : Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) = Module.finrank K L := by
  rw [Module.finrank_eq_card_basis (TensorProduct.RightActions.Algebra.TensorProduct.basis (v.adicCompletion K) (Module.finBasis K L)),
    Fintype.card_fin]

theorem norm_incl (d : v.adicCompletion K) :
    Algebra.norm (v.adicCompletion K) ((Algebra.TensorProduct.includeRight :
      v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) d) = d ^ Module.finrank K L := by
  rw [← finrank_tensor K L v]
  exact Algebra.norm_algebraMap d

omit L in

theorem norm_of_valuation_eq (x : v.adicCompletion K) (n : ℕ) (hx : Valued.v x = WithZero.exp (-(n : ℤ))) :
    ‖x‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(n : ℤ)) := by
  rw [NumberField.FinitePlace.norm_def, hx, WithZero.exp, WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero,
    WithZero.unzero_coe, toAdd_ofAdd]
  push_cast
  rfl

end Ws46P2

open Ws46P2 in
set_option maxHeartbeats 4000000 in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)) (hτ'h : τ'.IsHaarMeasure)
    (tv : ℝ≥0∞)
    (htv : τ' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} *
          (Ideal.absNorm v.asIdeal : ℝ≥0∞) =
        tv + τ' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}) :
    tv ≠ ⊤ ∧
    (∀ s' : ℝ, 1 ≤ s' →
      ∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) |
          (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ ⋃ n : ℕ, {x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) | ∃ s : (v.adicCompletion K)ˣ,
              Valued.v (s : v.adicCompletion K) = WithZero.exp (-(n : ℤ)) ∧
              Matrix.GeneralLinearGroup.det x =
                Units.map (Algebra.TensorProduct.includeRight :
                  v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}},
        ENNReal.ofReal (‖Algebra.norm (v.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ ^ s') ∂τ' =
        (tv * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) - 1)⁻¹ * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))) *
          ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹)) ∧
    (∀ s' : ℝ, 1 ≤ s' → tv * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) - 1)⁻¹ * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s')) ≠ ⊤) ∧
    Tendsto (fun s' : ℝ => tv * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) - 1)⁻¹ * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s')))
      (𝓝[>] (1 : ℝ)) (𝓝 (tv * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) - 1)⁻¹ * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * (1 : ℝ))))) := by
  haveI := hτ'h
  have hq1 : (1 : ℝ≥0∞) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hqtop : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hq0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans hq1).ne'
  have hqR : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v))

  have hDU := AutomorphicForm.det_mem_range_and_isOpen_isCompact_detUnits_twistedCentralizer_of_not_isSigmaConjugate_scalar_of_finrank_eq_two K L h2 σ hgen v c δ hδ hδq
  have hSh0 : τ' {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} < ⊤ := hDU.2.2.measure_lt_top
  have htvne : tv ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hSh0.ne hqtop) ?_
    calc tv ≤ tv + τ' {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} := le_self_add
      _ = τ' {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} * (Ideal.absNorm v.asIdeal : ℝ≥0∞) := htv.symm
      _ = τ' {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) := by norm_cast

  have hpow_lt : ∀ e : ℝ, e < 0 → ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ e < 1 := fun e he => ENNReal.rpow_lt_one_of_one_lt_of_neg hq1 he
  have hsub_ne0 : ∀ e : ℝ, e < 0 → (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ e) ≠ 0 := fun e he => (tsub_pos_iff_lt.2 (hpow_lt e he)).ne'
  have hsub_netop : ∀ e : ℝ, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ e) ≠ ⊤ := fun e => ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hq1' : (((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) - 1) ≠ 0 := (tsub_pos_iff_lt.2 hq1).ne'
  refine ⟨htvne, ?_, ?_, ?_⟩
  ·
    intro s' hs'
    set r : ℝ≥0∞ := ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')) with hr
    have hrlt : r < 1 := hpow_lt _ (by linarith)
    have hE4 := (AutomorphicForm.lintegral_iUnion_detShell_twistedCentralizer_eq_mul_inv_sub_one_mul_inv_one_sub_of_not_isSigmaConjugate_scalar_of_finrank_eq_two K L h2 σ hgen v c δ hδ hδq τ' hτ'h tv htv r hrlt
      (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) => ENNReal.ofReal (‖Algebra.norm (v.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ ^ s')) ?_).1
    ·
      have hset : {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ ⋃ n : ℕ, {x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) | ∃ s : (v.adicCompletion K)ˣ,
              Valued.v (s : v.adicCompletion K) = WithZero.exp (-(n : ℤ)) ∧
              Matrix.GeneralLinearGroup.det x =
                Units.map (Algebra.TensorProduct.includeRight :
                  v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}} =
          ⋃ n : ℕ, {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = WithZero.exp (-(n : ℤ)) ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} := by
        ext t; simp
      rw [hset, hE4, hr]
      have ha0 := hsub_ne0 (1 - 2 * s') (by linarith)
      have hat := hsub_netop (1 - 2 * s')
      calc tv * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) - 1)⁻¹ * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹
          = tv * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) - 1)⁻¹ * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ * ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s')) * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹) := by
            rw [ENNReal.mul_inv_cancel ha0 hat, mul_one]
        _ = tv * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) - 1)⁻¹ * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s')) *
            ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹) := by ring
    ·
      intro n t ht
      beta_reduce
      obtain ⟨s, hsval, hdet⟩ := ht
      have hdet' : Matrix.det ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
          (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) (s : v.adicCompletion K) := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet]; rfl
      rw [hdet', norm_incl, h2, norm_pow, norm_of_valuation_eq K v _ n hsval, hr]
      rw [← Real.rpow_natCast, ← Real.rpow_intCast, ← Real.rpow_mul hqR.le, ← Real.rpow_mul hqR.le,
        show ((-(n : ℤ) : ℤ) : ℝ) * ((2 : ℕ) : ℝ) * s' = (-(2 * s')) * (n : ℕ) by push_cast; ring,
        Real.rpow_mul_natCast hqR.le, ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_rpow_of_pos hqR,
        ENNReal.ofReal_natCast]
  ·
    intro s' hs'
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top htvne (ENNReal.inv_ne_top.2 hq1')) (hsub_netop _)
  ·
    have hcont : Continuous fun s' : ℝ => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s') := by
      have h1 : Continuous fun s' : ℝ => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - 2 * s') :=
        continuous_const.rpow (continuous_const.sub (continuous_const.mul continuous_id)) fun _ => Or.inl hqR.ne'
      have h2' : (fun s' : ℝ => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s')) = fun s' => ENNReal.ofReal (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - 2 * s')) := by
        funext s'; rw [← ENNReal.ofReal_rpow_of_pos hqR, ENNReal.ofReal_natCast]
      rw [h2']; exact ENNReal.continuous_ofReal.comp h1
    have hsub : Continuous fun s' : ℝ => 1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s') :=
      (ENNReal.continuous_sub_left ENNReal.one_ne_top).comp hcont
    have hT := ((hsub.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ))))
    exact ENNReal.Tendsto.const_mul hT (Or.inr (ENNReal.mul_ne_top htvne (ENNReal.inv_ne_top.2 hq1')))

end

end S_AutomorphicForm_ne_top_and_setLIntegral_iUnion_detShell_twistedCentralizer_norm_algebraNorm_det_rpow_eq_mul_and_tendsto_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_ne_top_and_setLIntegral_iUnion_detShell_twistedCentralizer_norm_algebraNorm_det_rpow_eq_mul_and_tendsto_of_not_isSigmaConjugate_scalar_of_finrank_eq_two (solution)
