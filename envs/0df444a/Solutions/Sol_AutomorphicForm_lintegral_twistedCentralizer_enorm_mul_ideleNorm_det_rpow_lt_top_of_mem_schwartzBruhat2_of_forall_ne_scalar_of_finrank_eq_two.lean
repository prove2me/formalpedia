-- Prove2me | solution 1 for AutomorphicForm.lintegral_twistedCentralizer_enorm_mul_ideleNorm_det_rpow_lt_top_of_mem_schwartzBruhat2_of_forall_ne_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/46d8dcb4-dd0c-56d3-9591-8f7a5f087bd8

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_AdelicFourier_exists_norm_le_mul_inv_one_add_norm_sq_pow_mul_indicator_integralFiniteAdeles_of_mem_schwartzBruhat2
import Theorems.Thm_AutomorphicForm_exists_lintegral_twistedCentralizer_inv_one_add_norm_sq_pow_mul_indicator_mul_ideleNorm_det_rpow_lt_top_of_forall_ne_scalar_of_finrank_eq_two
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_lintegral_twistedCentralizer_enorm_mul_ideleNorm_det_rpow_lt_top_of_mem_schwartzBruhat2_of_forall_ne_scalar_of_finrank_eq_two
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace"
p2m_attr_erase "instance" "NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add AutomorphicForm.rightTranslationEmbed_smul_apply LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk"
p2m_attr_erase "simp" "LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply"

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm

open scoped TensorProduct TensorProduct.RightActions ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

set_option autoImplicit false

namespace ZetaConv28

theorem inv_pow_le (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hn : 0 < n) (M : ℕ) :
    ((1 + a ^ 2) ^ M)⁻¹ ≤ (n : ℝ) ^ (2 * M) * ((1 + ((n : ℝ) * a) ^ 2) ^ M)⁻¹ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have key : (1 + ((n : ℝ) * a) ^ 2) ^ M ≤ (((n : ℝ) ^ 2) * (1 + a ^ 2)) ^ M :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) M
  have hA : 0 < (1 + ((n : ℝ) * a) ^ 2) ^ M := by positivity
  calc ((1 + a ^ 2) ^ M)⁻¹ = ((n : ℝ) ^ 2) ^ M * ((((n : ℝ) ^ 2) * (1 + a ^ 2)) ^ M)⁻¹ := by
        rw [mul_pow]; field_simp
    _ ≤ ((n : ℝ) ^ 2) ^ M * ((1 + ((n : ℝ) * a) ^ 2) ^ M)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ hA key) (by positivity)
    _ = (n : ℝ) ^ (2 * M) * ((1 + ((n : ℝ) * a) ^ 2) ^ M)⁻¹ := by rw [← pow_mul]

end ZetaConv28

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

open ZetaConv28 in
open scoped Classical in
set_option maxHeartbeats 4000000 in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)

    (τa' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
      (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτa' : τa'.IsHaarMeasure)
    (τf' : ∀ v : HeightOneSpectrum (𝓞 K), Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτf' : ∀ v, (τf' v).IsHaarMeasure)

    (s : ENNReal)
    (harch :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      ∃ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
        LinearIndependent ℝ e₂ ∧
          (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            {X | X * ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
              ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
                X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
              (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τa' =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))

    (t : HeightOneSpectrum (𝓞 K) → ENNReal) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (ht : ∀ v ∉ S₀, t v = 1)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K v
       ∃ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)))
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) y ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
              (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) (τf' v) =
          t v • Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v)) ∨
      ((∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
        ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ∧
       τf' v {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} *
          (Ideal.absNorm v.asIdeal : ENNReal) =
        t v +
          τf' v {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}))

    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ' : τ'.IsHaarMeasure) (cτ' : ℝ) (hcτ' : 0 < cτ')
    (hτ'prod : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₀ ⊆ S →
        ∀ (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) => Wa t) τa' →
        (∀ v ∈ S, AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) => WS v t) (τf' v)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = Wa (AutomorphicForm.tensorArch K L t) *
              ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = 0) →
          ∫ t, W t ∂τ' = cτ' * (∫ t, Wa t ∂τa') * ∏ v ∈ S, ∫ t, WS v t ∂(τf' v))

    (v : Fin 2 → L) (hv : v ≠ 0)
    (Ψ : (Fin 2 → AdeleRing (𝓞 L) L) → ℂ) (hΨ : Ψ ∈ schwartzBruhat2 L) (s₁ : ℝ) (hs₁ : 1 < s₁) :
    ∫⁻ t, ‖Ψ (((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i))‖ₑ *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ^ s₁) ∂τ' < ⊤ := by

  obtain ⟨M, hM⟩ :=
    AutomorphicForm.exists_lintegral_twistedCentralizer_inv_one_add_norm_sq_pow_mul_indicator_mul_ideleNorm_det_rpow_lt_top_of_forall_ne_scalar_of_finrank_eq_two
      K L h2 σ hgen δ₀ c u hN hns τa' hτa' τf' hτf' s harch t S₀ ht hfin τ' hτ' cτ' hcτ' hτ'prod v hv s₁ hs₁
  obtain ⟨C, n, hC, hn, hΨb⟩ :=
    NumberField.AdelicFourier.exists_norm_le_mul_inv_one_add_norm_sq_pow_mul_indicator_integralFiniteAdeles_of_mem_schwartzBruhat2
      L Ψ hΨ M

  set φ : L ⊗[K] AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L :=
    ((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
      (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom with hφ
  set E : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) →* GL (Fin 2) (AdeleRing (𝓞 L) L) :=
    Matrix.GeneralLinearGroup.map φ with hE
  set vv : Fin 2 → AdeleRing (𝓞 L) L := fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i) with hvv

  haveI hTG := AutomorphicForm.isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  haveI : BorelSpace ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) := ⟨rfl⟩
  haveI := hτ'

  have hn0K : ((n : ℕ) : K) ≠ 0 := by exact_mod_cast hn.ne'
  have hn0L : ((n : ℕ) : L) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨zU, hzUval⟩ : ∃ zU : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ, (zU : L ⊗[K] AdeleRing (𝓞 K) K) = (n : ℕ) :=
    ⟨Units.map (algebraMap K (L ⊗[K] AdeleRing (𝓞 K) K)).toMonoidHom (Units.mk0 ((n : ℕ) : K) hn0K), by
      simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_mk0, map_natCast]⟩
  obtain ⟨zG, hzGval⟩ : ∃ zG : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      zG.val =
        Matrix.diagonal (fun _ : Fin 2 => ((n : ℕ) : L ⊗[K] AdeleRing (𝓞 K) K)) :=
    ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) zU, by
      rw [← hzUval]; simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply]⟩
  have hzG_mem : zG ∈ AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
    rw [AutomorphicForm.mem_sigmaCentralizer_iff]
    have hσz : AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ zG = zG := by
      apply Units.ext
      ext i j
      rw [show (AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ zG).val i j
          = AutomorphicForm.sigmaTensor K L (AdeleRing (𝓞 K) K) σ (zG.val i j) from
          Matrix.GeneralLinearGroup.map_apply _ i j zG, hzGval, Matrix.diagonal_apply]
      split_ifs
      · exact map_natCast _ n
      · exact map_zero _
    have hcomm' := hzGval
    have hcomm : zG * (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) = (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) * zG := by
      apply Units.ext
      simp only [Units.val_mul]
      rw [hzGval]
      ext i j
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
    rw [hσz, hcomm, mul_inv_cancel_right]
  obtain ⟨z, hzval⟩ : ∃ z : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)), z.1 = zG :=
    ⟨⟨zG, hzG_mem⟩, rfl⟩

  have hEz : (E zG).val =
      Matrix.diagonal (fun _ : Fin 2 => ((n : ℕ) : AdeleRing (𝓞 L) L)) := by
    rw [show (E zG).val =
        zG.val.map φ from rfl, hzGval, Matrix.diagonal_map (map_zero φ)]
    congr 1
    funext i
    exact map_natCast φ n

  have hcol : ∀ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      (E (zG * g)).val.mulVec vv =
        fun i => ((n : ℕ) : AdeleRing (𝓞 L) L) * ((E g).val.mulVec vv) i := by
    intro g
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hEz]
    funext i
    rw [Matrix.mulVec_diagonal]

  have hN1 : NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (E zG)) = 1 := by
    have hdet : Matrix.GeneralLinearGroup.det (E zG) =
        Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom (Units.mk0 ((n : ℕ) : L) hn0L) *
        Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom (Units.mk0 ((n : ℕ) : L) hn0L) := by
      apply Units.ext
      rw [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, hEz, Matrix.det_diagonal]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Units.coe_map, RingHom.toMonoidHom_eq_coe,
        MonoidHom.coe_coe, Units.val_mk0, map_natCast, pow_two]
    rw [hdet, NumberField.TateGlobal.ideleNorm_mul]
    unfold NumberField.TateGlobal.ideleNorm
    rw [NumberField.AdeleRing.distribHaarChar_algebraMap]
    simp
  have hN : ∀ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (E (zG * g))) =
        NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (E g)) := by
    intro g
    rw [map_mul, map_mul, NumberField.TateGlobal.ideleNorm_mul, hN1, one_mul]

  obtain ⟨G, hGdef, hMG⟩ : ∃ G : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) → ℝ≥0∞,
      (∀ t, G t =
    ENNReal.ofReal (((1 + ‖(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L
        ((E t.1).val.mulVec vv i).1)‖ ^ 2) ^ M)⁻¹) *
      Set.indicator {t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) |
          ∀ i, ((E t.1).val.mulVec vv i).2 ∈
            NumberField.AdelicBox.integralFiniteAdeles (𝓞 L) L}
        (fun _ => (1 : ℝ≥0∞)) t *
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
        (Matrix.GeneralLinearGroup.det (E t.1)) ^ s₁)) ∧ ∫⁻ t, G t ∂τ' < ⊤ :=
    ⟨fun t => _, fun t => rfl, hM⟩

  have key : ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      ‖Ψ ((E t.1).val.mulVec vv)‖ₑ *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det (E t.1)) ^ s₁)
      ≤ ENNReal.ofReal (C * (n : ℝ) ^ (2 * M)) * G (z * t) := by
    intro t
    obtain ⟨y, hy⟩ : ∃ y : Fin 2 → AdeleRing (𝓞 L) L, y = (E t.1).val.mulVec vv := ⟨_, rfl⟩
    have hzt : (z * t).1 = zG * t.1 := by rw [Subgroup.coe_mul, hzval]

    have hPQ : (∀ i, ((E (z * t).1).val.mulVec vv i).2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 L) L) ↔
        (∀ i, (((n : ℕ) : FiniteAdeleRing (𝓞 L) L) * (y i).2) ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 L) L) := by
      rw [hzt, hcol, ← hy]
      exact Iff.rfl
    have hind : Set.indicator {t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) |
          ∀ i, ((E t.1).val.mulVec vv i).2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 L) L}
          (fun _ => (1 : ℝ≥0∞)) (z * t) =
        Set.indicator {x : Fin 2 → AdeleRing (𝓞 L) L |
          ∀ i, (((n : ℕ) : FiniteAdeleRing (𝓞 L) L) * (x i).2) ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 L) L}
          (fun _ => (1 : ℝ≥0∞)) y := by
      by_cases hq : ∀ i, (((n : ℕ) : FiniteAdeleRing (𝓞 L) L) * (y i).2) ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 L) L
      · rw [Set.indicator_of_mem (show y ∈ {x : Fin 2 → AdeleRing (𝓞 L) L | ∀ i, (((n : ℕ) : FiniteAdeleRing (𝓞 L) L) * (x i).2) ∈
            NumberField.AdelicBox.integralFiniteAdeles (𝓞 L) L} from hq),
          Set.indicator_of_mem (show z * t ∈ {t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) | ∀ i, ((E t.1).val.mulVec vv i).2 ∈
            NumberField.AdelicBox.integralFiniteAdeles (𝓞 L) L} from hPQ.mpr hq)]
      · rw [Set.indicator_of_notMem (show y ∉ {x : Fin 2 → AdeleRing (𝓞 L) L | ∀ i, (((n : ℕ) : FiniteAdeleRing (𝓞 L) L) * (x i).2) ∈
            NumberField.AdelicBox.integralFiniteAdeles (𝓞 L) L} from hq),
          Set.indicator_of_notMem (show z * t ∉ {t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) | ∀ i, ((E t.1).val.mulVec vv i).2 ∈
            NumberField.AdelicBox.integralFiniteAdeles (𝓞 L) L} from fun h => hq (hPQ.mp h))]

    have harch_fun : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L ((E (z * t).1).val.mulVec vv i).1) =
        (n : ℝ) • (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (y i).1) := by
      rw [hzt, hcol, ← hy]
      funext i
      have h1 : (((n : ℕ) : AdeleRing (𝓞 L) L) * y i).1 = ((n : ℕ) : InfiniteAdeleRing L) * (y i).1 := rfl
      rw [Pi.smul_apply, h1, map_mul, map_natCast, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
    have harch_eq : ‖(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L ((E (z * t).1).val.mulVec vv i).1)‖ =
        (n : ℝ) * ‖(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (y i).1)‖ := by
      rw [harch_fun, norm_smul, Real.norm_natCast]
    have hNz : NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (E (z * t).1)) =
        NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (E t.1)) := by
      rw [hzt, hN]
    have hreal := hΨb y
    have hA : ((1 + ‖(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (y i).1)‖ ^ 2) ^ M)⁻¹ ≤
        (n : ℝ) ^ (2 * M) *
          ((1 + ‖(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L ((E (z * t).1).val.mulVec vv i).1)‖ ^ 2) ^ M)⁻¹ := by
      rw [harch_eq]
      exact inv_pow_le _ (norm_nonneg _) n hn M
    rw [hGdef, hind, hNz, ← hy, ← ofReal_norm_eq_enorm]
    by_cases hq : ∀ i, (((n : ℕ) : FiniteAdeleRing (𝓞 L) L) * (y i).2) ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 L) L
    · rw [Set.indicator_of_mem (show y ∈ {x : Fin 2 → AdeleRing (𝓞 L) L | ∀ i, (((n : ℕ) : FiniteAdeleRing (𝓞 L) L) * (x i).2) ∈
          NumberField.AdelicBox.integralFiniteAdeles (𝓞 L) L} from hq)] at hreal ⊢
      rw [mul_one] at hreal ⊢
      have hreal' : ‖Ψ y‖ ≤ (C * (n : ℝ) ^ (2 * M)) *
          ((1 + ‖(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L ((E (z * t).1).val.mulVec vv i).1)‖ ^ 2) ^ M)⁻¹ :=
        calc ‖Ψ y‖ ≤ C * ((1 + ‖(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (y i).1)‖ ^ 2) ^ M)⁻¹ := hreal
          _ ≤ C * ((n : ℝ) ^ (2 * M) *
              ((1 + ‖(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L ((E (z * t).1).val.mulVec vv i).1)‖ ^ 2) ^ M)⁻¹) :=
                mul_le_mul_of_nonneg_left hA hC
          _ = _ := by ring
      calc ENNReal.ofReal ‖Ψ y‖ *
            ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (E t.1)) ^ s₁)
          ≤ ENNReal.ofReal ((C * (n : ℝ) ^ (2 * M)) *
              ((1 + ‖(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L ((E (z * t).1).val.mulVec vv i).1)‖ ^ 2) ^ M)⁻¹) *
            ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (E t.1)) ^ s₁) :=
            mul_le_mul_left (ENNReal.ofReal_le_ofReal hreal') _
        _ = _ := by rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
    · rw [Set.indicator_of_notMem (show y ∉ {x : Fin 2 → AdeleRing (𝓞 L) L | ∀ i, (((n : ℕ) : FiniteAdeleRing (𝓞 L) L) * (x i).2) ∈
          NumberField.AdelicBox.integralFiniteAdeles (𝓞 L) L} from hq)] at hreal ⊢
      rw [mul_zero] at hreal
      have h0 : ‖Ψ y‖ = 0 := le_antisymm hreal (norm_nonneg _)
      rw [h0, ENNReal.ofReal_zero, zero_mul]
      exact bot_le

  have hc : ENNReal.ofReal (C * (n : ℝ) ^ (2 * M)) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc ∫⁻ t, ‖Ψ ((E t.1).val.mulVec vv)‖ₑ *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
            (Matrix.GeneralLinearGroup.det (E t.1)) ^ s₁) ∂τ'
      ≤ ∫⁻ t, ENNReal.ofReal (C * (n : ℝ) ^ (2 * M)) * G (z * t) ∂τ' := lintegral_mono fun t => key t
    _ = ENNReal.ofReal (C * (n : ℝ) ^ (2 * M)) * ∫⁻ t, G (z * t) ∂τ' := lintegral_const_mul' _ _ hc
    _ = ENNReal.ofReal (C * (n : ℝ) ^ (2 * M)) * ∫⁻ t, G t ∂τ' := by rw [lintegral_mul_left_eq_self]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hMG

end S_AutomorphicForm_lintegral_twistedCentralizer_enorm_mul_ideleNorm_det_rpow_lt_top_of_mem_schwartzBruhat2_of_forall_ne_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_lintegral_twistedCentralizer_enorm_mul_ideleNorm_det_rpow_lt_top_of_mem_schwartzBruhat2_of_forall_ne_scalar_of_finrank_eq_two (solution)
