-- Prove2me | solution 1 for AutomorphicForm.exists_ellipticTransport_coupled_and_weilConst_mul_eq_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b2301655-40ae-5c98-a716-1d438fdb999e

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_exists_ellipticTransport_coupled_straighten_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_weilConst_mul_measureReal_torusUnits_eq_of_isNormConjugator_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_measureReal_torusUnits_pos_and_measure_detUnits_lt_top_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_ellipticTransport_coupled_and_weilConst_mul_eq_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ') :
    ∃ (u₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (γ₀ : GL (Fin 2) (v.adicCompletion K))
      (y₁ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
      (τS : @Measure ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
          AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) (borel _))
      (τT : @Measure (AutomorphicForm.localCentralizer K v γ₀) (AutomorphicForm.localCentralizerBorel K v γ₀)),
      u₀ ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ∧
      AutomorphicForm.IsRegularSemisimple γ₀ ∧
      (∀ g : GL (Fin 2) (v.adicCompletion K),
        ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
           ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)) ∧
      AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ γ₀ (u₀ * δ) ∧
      @Measure.IsHaarMeasure _ _ _ (borel _) τS ∧
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) τT ∧

      (letI := AutomorphicForm.localGLBorel K v
       letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       ∀ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (v.adicCompletion K)),
       ∀ V ∈ nhds (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
         ∃ u ∈ V, u ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
             AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) ∧
           AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ (u * δ)) ∧
           ∃ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ ∧ AutomorphicForm.IsRegularSemisimple γ ∧
             AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ (u * δ) y₁ ∧
             ∃ (τγ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
               (τu : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u * δ))
                 (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (u * δ))),
               @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τγ ∧
               @Measure.IsHaarMeasure _ _ _
                 (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (u * δ)) τu ∧
               (letI := AutomorphicForm.localCentralizerBorel K v γ
                letI := AutomorphicForm.localCentralizerBorel K v γ₀
                Measure.map Subtype.val τγ = Measure.map Subtype.val τT) ∧
               (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (u * δ)
                letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
                    AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _
                Measure.map Subtype.val τu = Measure.map Subtype.val τS) ∧
               AutomorphicForm.Coupled K L (v.adicCompletion K) σ γ (u * δ) y₁ τγ τu ∧
               (∀ φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ, AutomorphicForm.IsSemiLocalTestFn K L v φv →
                 ∃ J : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ (u * δ) τu φv J)) ∧

      (letI := AutomorphicForm.localGLBorel K v
       letI := AutomorphicForm.localCentralizerBorel K v γ₀
       letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
       ∀ ρ : ℝ,
        (∀ w : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) → ℝ,
          (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
           letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
               AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _
           (∀ t, 0 ≤ w t) ∧ Measurable w ∧ HasCompactSupport w ∧
             ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ),
               ∫ s : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
                   AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)),
                 w ((⟨(s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)), (Subgroup.mem_inf.mp s.2).1⟩ :
                   ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)) * t) ∂τS = 1) →
          (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
           ∫ t, w t ∂τ' = ρ)) →
        ((∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ)) →
          ρ * ((Measure.map Subtype.val τT) {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal = (τ' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}).toReal) ∧
        ((¬ (∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ))) →
          ρ * ((Measure.map Subtype.val τT) {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal = 2 * (τ' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}).toReal)) ∧

      (letI := AutomorphicForm.localGLBorel K v
       letI := AutomorphicForm.localCentralizerBorel K v γ₀
       0 < ((Measure.map Subtype.val τT) {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal) ∧
      (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
       τ' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} < ⊤) := by
  obtain ⟨u₀, γ₀, y₁, τS, τT, hu₀, hγ₀, hγ₀e, hN, hτS, hτT, h1, hy₁, hS, hlink⟩ :=
    AutomorphicForm.exists_ellipticTransport_coupled_straighten_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
      K L h2 σ hgen v c δ hδ hδq τ' hτ'
  exact ⟨u₀, γ₀, y₁, τS, τT, hu₀, hγ₀, hγ₀e, hN, hτS, hτT, h1,
    AutomorphicForm.weilConst_mul_measureReal_torusUnits_eq_of_isNormConjugator_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
      K L h2 σ hgen v c δ hδ hδq τ' hτ' u₀ hu₀ γ₀ hγ₀ hγ₀e y₁ hy₁ hS τS hτS τT hτT hlink,
    AutomorphicForm.measureReal_torusUnits_pos_and_measure_detUnits_lt_top_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
      K L h2 σ hgen v c δ hδ hδq τ' hτ' u₀ hu₀ γ₀ hγ₀ hγ₀e y₁ hy₁ hS τS hτS τT hτT hlink⟩

end S_AutomorphicForm_exists_ellipticTransport_coupled_and_weilConst_mul_eq_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_exists_ellipticTransport_coupled_and_weilConst_mul_eq_of_not_isSigmaConjugate_scalar_of_finrank_eq_two (solution)
