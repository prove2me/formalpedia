-- Prove2me | solution 1 for AutomorphicForm.exists_lintegral_twistedCentralizer_inv_one_add_norm_sq_pow_mul_indicator_mul_ideleNorm_det_rpow_lt_top_of_forall_ne_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/eb72456a-b4b8-5fcd-8ff3-31262d11864d

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_exists_finset_level_isOpen_isCompact_box_subset_indicator_mulVec_eq_prod_indicator_tensorPlace_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_lintegral_twistedCentralizer_mul_indicator_mul_ideleNorm_det_rpow_eq_mul_lintegral_arch_mul_dedekindZeta_mul_prod_of_forall_le_mul_one_add_norm_rpow_neg
import Theorems.Thm_AutomorphicForm_lintegral_twistedCentralizer_mul_rpow_abs_algebraNorm_det_lt_top_of_map_coe_eq_smul_withDensity_gram_of_forall_le_mul_one_add_norm_rpow_neg
import Theorems.Thm_AutomorphicForm_exists_pos_forall_norm_le_mul_norm_archIdent_sum_smul_mulVec_tmul_of_linearIndependent_of_span_eq
import Theorems.Thm_AutomorphicForm_moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det
import Theorems.Thm_NumberField_AdelicBox_exists_isAddHaarMeasure_adelicBox_eq_one
import Theorems.Thm_AutomorphicForm_ne_top_of_isHaarMeasure_twistedCentralizer_of_map_coe_eq_smul
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_lintegral_twistedCentralizer_inv_one_add_norm_sq_pow_mul_indicator_mul_ideleNorm_det_rpow_lt_top_of_forall_ne_scalar_of_finrank_eq_two
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace"
p2m_attr_erase "instance" "NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add AutomorphicForm.rightTranslationEmbed_smul_apply LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk"
p2m_attr_erase "simp" "LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply"

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm

open scoped TensorProduct TensorProduct.RightActions ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace ZetaStd28

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

theorem decay_of_le (κ a b : ℝ) (hκ : 0 < κ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ κ * b) (M : ℕ) :
    ((1 + b ^ 2) ^ M)⁻¹ ≤ (2 * (max 1 κ) ^ 2) ^ M * (1 + a) ^ (-(2 * (M : ℝ))) := by
  have hk1 : 1 ≤ max 1 κ := le_max_left _ _
  have hk : κ ≤ max 1 κ := le_max_right _ _
  have hkpos : 0 < max 1 κ := lt_of_lt_of_le one_pos hk1
  have hab' : a ≤ max 1 κ * b := hab.trans (mul_le_mul_of_nonneg_right hk hb)

  have h1 : (1 + a) ^ 2 ≤ 2 * (max 1 κ) ^ 2 * (1 + b ^ 2) := by
    have : a ^ 2 ≤ (max 1 κ) ^ 2 * b ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ ha hab' 2
    nlinarith [sq_nonneg (1 - a), sq_nonneg b, hk1]
  have hpos : 0 < (1 + a) ^ 2 := by positivity
  have h2 : ((1 + b ^ 2) ^ M)⁻¹ ≤ ((2 * (max 1 κ) ^ 2) ^ M) * (((1 + a) ^ 2) ^ M)⁻¹ := by
    have h3 : ((1 + a) ^ 2) ^ M ≤ (2 * (max 1 κ) ^ 2 * (1 + b ^ 2)) ^ M := pow_le_pow_left₀ (by positivity) h1 M
    rw [mul_pow] at h3
    have h4 : 0 < ((1 + a) ^ 2) ^ M := by positivity
    have h5 : 0 < (1 + b ^ 2) ^ M := by positivity
    calc ((1 + b ^ 2) ^ M)⁻¹ = (2 * (max 1 κ) ^ 2) ^ M * (((2 * (max 1 κ) ^ 2) ^ M * (1 + b ^ 2) ^ M))⁻¹ := by
          field_simp
      _ ≤ (2 * (max 1 κ) ^ 2) ^ M * (((1 + a) ^ 2) ^ M)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ h4 h3) (by positivity)
  refine h2.trans (le_of_eq ?_)
  congr 1
  rw [← pow_mul, Real.rpow_neg (by positivity), ← Real.rpow_natCast, Nat.cast_mul, Nat.cast_two]

theorem fst_col_eq_archIdent (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : Fin 2 → L) (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (i : Fin 2) :
    ((Matrix.GeneralLinearGroup.map
        (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
          (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom) t).val.mulVec
        (fun j => algebraMap L (AdeleRing (𝓞 L) L) (v j)) i).1 =
      AutomorphicForm.archIdent K L
        (((AutomorphicForm.tensorArch K L t).val.mulVec (fun j => v j ⊗ₜ[K] (1 : InfiniteAdeleRing K))) i) := by

  have hπ : ∀ x y : AdeleRing (𝓞 L) L, (x * y).1 = x.1 * y.1 := fun _ _ => rfl
  have hπs : ∀ (f : Fin 2 → AdeleRing (𝓞 L) L), (∑ j, f j).1 = ∑ j, (f j).1 := by
    intro f
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    rfl
  simp only [Matrix.mulVec, dotProduct]
  rw [hπs, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hπ, map_mul, Matrix.GeneralLinearGroup.map_apply, AutomorphicForm.tensorArch_apply]
  congr 1
  · exact AutomorphicForm.fst_baseChangeEquiv K L _
  · rw [← AutomorphicForm.baseChangeEquiv_tmul_one (K := K)]
    rw [AutomorphicForm.fst_baseChangeEquiv, AutomorphicForm.tensorArchHom_tmul]
    rfl

end ZetaStd28

open ZetaStd28 in
set_option maxHeartbeats 6400000 in
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
    (s₁ : ℝ) (hs₁ : 1 < s₁) :
    ∃ M : ℕ,
      ∫⁻ t, ENNReal.ofReal (((1 + ‖fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).1‖ ^ 2) ^ M)⁻¹) *
          Set.indicator {t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
              (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                Matrix.GeneralLinearGroup.scalar (Fin 2) c)) |
              ∀ i, ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2 ∈ integralFiniteAdeles (𝓞 L) L}
            (fun _ => (1 : ℝ≥0∞)) t *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ^ s₁) ∂τ' < ⊤ := by

  letI iRK : Algebra ℝ (InfiniteAdeleRing K) :=
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
      (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
  letI iRL : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
    ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
      (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
  obtain ⟨_, _, hfinL, _, hcsmul, _, _⟩ := AutomorphicForm.moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det K L
  haveI := hfinL

  obtain ⟨M, hM⟩ : ∃ M : ℕ, (4 * (Module.finrank ℝ (L ⊗[K] InfiniteAdeleRing K) : ℝ)) +
      2 * (Module.finrank ℝ (L ⊗[K] InfiniteAdeleRing K) : ℝ) * (s₁ - 1) < 2 * (M : ℝ) := by
    obtain ⟨M, hM⟩ := exists_nat_gt ((4 * (Module.finrank ℝ (L ⊗[K] InfiniteAdeleRing K) : ℝ)) +
      2 * (Module.finrank ℝ (L ⊗[K] InfiniteAdeleRing K) : ℝ) * (s₁ - 1))
    exact ⟨M, by linarith⟩
  refine ⟨M, ?_⟩

  obtain ⟨μ₁, hμ₁H, hμ₁⟩ := NumberField.AdelicBox.exists_isAddHaarMeasure_adelicBox_eq_one L
  haveI := hμ₁H

  obtain ⟨S₁, W, U, Corr, hUo, hUc, hUne, hS₁, hWm, hW₀, hW₁, hunit, hCorr, hCorr₁, n, hn, hUbox⟩ :=
    AutomorphicForm.exists_finset_level_isOpen_isCompact_box_subset_indicator_mulVec_eq_prod_indicator_tensorPlace_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two K L h2 σ hgen δ₀ c u hN hns τa' hτa' τf' hτf' s harch t S₀ ht hfin τ' hτ' cτ' hcτ' hτ'prod v hv μ₁ hμ₁
  have hCorr₁' : ∀ w ∈ S₁, Corr w 1 ≠ ⊤ ∧ Tendsto (Corr w) (𝓝[>] (1 : ℝ)) (𝓝 (Corr w 1)) :=
    fun w hw => ⟨(hCorr₁ w hw).1 1 le_rfl, (hCorr₁ w hw).2⟩

  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI hTR := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)

  obtain ⟨G, hGdef⟩ : ∃ G : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞,
      ∀ X, G X = ENNReal.ofReal (((1 + ‖(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((X.mulVec (fun j => v j ⊗ₜ[K] (1 : InfiniteAdeleRing K))) i)))‖ ^ 2) ^ M)⁻¹) := ⟨_, fun X => rfl⟩
  have hΛ : Continuous fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((X.mulVec (fun j => v j ⊗ₜ[K] (1 : InfiniteAdeleRing K))) i))) := by
    refine continuous_pi fun i => ?_
    refine (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace L).comp ?_
    show Continuous fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
      AutomorphicForm.archIdentHomeomorph K L ((X.mulVec (fun j => v j ⊗ₜ[K] (1 : InfiniteAdeleRing K))) i)
    refine (AutomorphicForm.archIdentHomeomorph K L).continuous.comp ?_
    simp only [Matrix.mulVec, dotProduct]
    refine continuous_finset_sum _ fun j _ => ?_
    exact (continuous_apply_apply i j).mul continuous_const
  have hGm : Measurable[borel _] G := by
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
    haveI : BorelSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := ⟨rfl⟩
    have hG' : G = fun X => ENNReal.ofReal (((1 + ‖(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((X.mulVec (fun j => v j ⊗ₜ[K] (1 : InfiniteAdeleRing K))) i)))‖ ^ 2) ^ M)⁻¹) := funext hGdef
    rw [hG']
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    have hc0 : Continuous fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => (1 + ‖(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((X.mulVec (fun j => v j ⊗ₜ[K] (1 : InfiniteAdeleRing K))) i)))‖ ^ 2) ^ M :=
      (continuous_const.add (hΛ.norm.pow 2)).pow M
    exact hc0.inv₀ fun X => by positivity

  have hdecay : ∀ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
      LinearIndependent ℝ e₂ →
      (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
        {X | X * ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
          ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
            X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} →
      ∃ r C : ℝ, (n₂ : ℝ) + 2 * (Module.finrank ℝ (L ⊗[K] InfiniteAdeleRing K) : ℝ) * (s₁ - 1) < r ∧
        ∀ cc : Fin n₂ → ℝ, G (∑ i, cc i • e₂ i) ≤ ENNReal.ofReal (C * (1 + ‖cc‖) ^ (-r)) := by
    intro n₂ e₂ hli hspan
    obtain ⟨κ, hκ, hκb⟩ := AutomorphicForm.exists_pos_forall_norm_le_mul_norm_archIdent_sum_smul_mulVec_tmul_of_linearIndependent_of_span_eq K L h2 σ hgen δ₀ c u hN hns v hv n₂ e₂ hli hspan

    have h4 : n₂ ≤ 4 * Module.finrank ℝ (L ⊗[K] InfiniteAdeleRing K) := by
      have h := hli.fintype_card_le_finrank
      rw [Fintype.card_fin, Module.finrank_matrix, Fintype.card_fin] at h
      omega
    have hn₂ : (n₂ : ℝ) ≤ 4 * (Module.finrank ℝ (L ⊗[K] InfiniteAdeleRing K) : ℝ) := by exact_mod_cast h4
    refine ⟨2 * (M : ℝ), (2 * (max 1 κ) ^ 2) ^ M, by linarith, fun cc => ?_⟩
    rw [hGdef]
    refine ENNReal.ofReal_le_ofReal ?_
    have := decay_of_le κ ‖cc‖ ‖(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (((∑ i, cc i • e₂ i).mulVec (fun j => v j ⊗ₜ[K] (1 : InfiniteAdeleRing K))) i)))‖ hκ (norm_nonneg _) (norm_nonneg _) (hκb cc) M
    simpa [mul_comm] using this

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
  have hNsc : ∀ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (E (zG * g))) =
        NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (E g)) := by
    intro g
    rw [map_mul, map_mul, NumberField.TateGlobal.ideleNorm_mul, hN1, one_mul]

  have hCZ := AutomorphicForm.lintegral_twistedCentralizer_mul_indicator_mul_ideleNorm_det_rpow_eq_mul_lintegral_arch_mul_dedekindZeta_mul_prod_of_forall_le_mul_one_add_norm_rpow_neg K L h2 σ hgen δ₀ c u hN hns τa' hτa' τf' hτf' s harch t S₀ ht hfin τ' hτ' cτ' hcτ' hτ'prod
    v hv μ₁ hμ₁ U G hGm S₁ hS₁ W hWm hW₀ hW₁ hunit Corr hCorr hCorr₁' s₁ hs₁ hdecay

  obtain ⟨n₂, e₂, hli, hspan, hpush⟩ := harch
  have hs : s ≠ ⊤ := AutomorphicForm.ne_top_of_isHaarMeasure_twistedCentralizer_of_map_coe_eq_smul K L σ _ τa' hτa' s _ hpush
  obtain ⟨r, Cd, hr, hGdec⟩ := hdecay n₂ e₂ hli hspan
  have hE := AutomorphicForm.lintegral_twistedCentralizer_mul_rpow_abs_algebraNorm_det_lt_top_of_map_coe_eq_smul_withDensity_gram_of_forall_le_mul_one_add_norm_rpow_neg K L σ _ τa' s hs G hGm n₂ e₂ hli hpush s₁ hs₁.le r Cd hr hGdec
  have hprod : ∏ w ∈ S₁, Corr w s₁ ≠ ⊤ := ENNReal.prod_ne_top fun w hw => (hCorr₁ w hw).1 s₁ hs₁.le

  set F : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) → ℝ≥0∞ := fun t =>
    G (AutomorphicForm.tensorArch K L t.1).val *
      U.indicator (fun _ => (1 : ℝ≥0∞)) (fun i => (((E t.1).val.mulVec vv) i).2) *
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (E t.1)) ^ s₁) with hF
  have hFfin : ∫⁻ t, F t ∂τ' < ⊤ := by
    rw [hCZ]
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
    exact lt_top_iff_ne_top.mpr hprod

  have hdict : ∀ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (((AutomorphicForm.tensorArch K L g).val.mulVec (fun j => v j ⊗ₜ[K] (1 : InfiniteAdeleRing K))) i))) =
        fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L ((((E g).val.mulVec vv) i).1) := by
    intro g; funext i
    rw [fst_col_eq_archIdent K L v g i]

  have key : ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      ENNReal.ofReal (((1 + ‖(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L ((((E t.1).val.mulVec vv) i).1))‖ ^ 2) ^ M)⁻¹) *
        Set.indicator {t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) | ∀ i, ((((E t.1).val.mulVec vv)) i).2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 L) L} (fun _ => (1 : ℝ≥0∞)) t *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (E t.1)) ^ s₁)
      ≤ ENNReal.ofReal ((n : ℝ) ^ (2 * M)) * F (z * t) := by
    intro t
    obtain ⟨y, hy⟩ : ∃ y : Fin 2 → AdeleRing (𝓞 L) L, y = (E t.1).val.mulVec vv := ⟨_, rfl⟩
    have hzt : (z * t).1 = zG * t.1 := by rw [Subgroup.coe_mul, hzval]

    have harch_fun : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L ((((E (z * t).1).val.mulVec vv) i).1)) =
        (n : ℝ) • (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L ((y i).1)) := by
      rw [hzt, hcol, ← hy]
      funext i
      have h1 : (((n : ℕ) : AdeleRing (𝓞 L) L) * y i).1 = ((n : ℕ) : InfiniteAdeleRing L) * (y i).1 := rfl
      rw [Pi.smul_apply, h1, map_mul, map_natCast, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
    have hGzt : G (AutomorphicForm.tensorArch K L (z * t).1).val =
        ENNReal.ofReal (((1 + ((n : ℝ) * ‖(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L ((y i).1))‖) ^ 2) ^ M)⁻¹) := by
      rw [hGdef, hdict, harch_fun, norm_smul, Real.norm_natCast]
    have hNzt : NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (E (z * t).1)) =
        NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (E t.1)) := by
      rw [hzt, hNsc]
    have hcolzt : (fun i => (((E (z * t).1).val.mulVec vv) i).2) = fun i => ((n : ℕ) : FiniteAdeleRing (𝓞 L) L) * (y i).2 := by
      rw [hzt, hcol, ← hy]
      rfl
    have hFzt : F (z * t) = ENNReal.ofReal (((1 + ((n : ℝ) * ‖(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L ((y i).1))‖) ^ 2) ^ M)⁻¹) *
        U.indicator (fun _ => (1 : ℝ≥0∞)) (fun i => ((n : ℕ) : FiniteAdeleRing (𝓞 L) L) * (y i).2) *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (E t.1)) ^ s₁) := by
      rw [hF]
      show G (AutomorphicForm.tensorArch K L (z * t).1).val *
        U.indicator (fun _ => (1 : ℝ≥0∞)) (fun i => (((E (z * t).1).val.mulVec vv) i).2) *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (E (z * t).1)) ^ s₁) = _
      rw [hGzt, hcolzt, hNzt]
    rw [hFzt, ← hy]
    by_cases hq : ∀ i, (y i).2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 L) L
    · have hU1 : U.indicator (fun _ => (1 : ℝ≥0∞)) (fun i => ((n : ℕ) : FiniteAdeleRing (𝓞 L) L) * (y i).2) = 1 :=
        Set.indicator_of_mem (hUbox (fun i => (y i).2) hq) _
      rw [hU1, Set.indicator_of_mem (show t ∈ {t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) | ∀ i, ((((E t.1).val.mulVec vv)) i).2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 L) L} by
        rw [Set.mem_setOf_eq, ← hy]; exact hq)]
      rw [mul_one, mul_one, ← mul_assoc]
      refine mul_le_mul_left ?_ _
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (inv_pow_le _ (norm_nonneg _) n hn M)
    · rw [Set.indicator_of_notMem (show t ∉ {t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) | ∀ i, ((((E t.1).val.mulVec vv)) i).2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 L) L} by
        rw [Set.mem_setOf_eq, ← hy]; exact hq)]
      rw [mul_zero, zero_mul]
      exact bot_le

  have hc : ENNReal.ofReal ((n : ℝ) ^ (2 * M)) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc ∫⁻ t, ENNReal.ofReal (((1 + ‖(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L ((((E t.1).val.mulVec vv) i).1))‖ ^ 2) ^ M)⁻¹) *
        Set.indicator {t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) | ∀ i, ((((E t.1).val.mulVec vv)) i).2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 L) L} (fun _ => (1 : ℝ≥0∞)) t *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (E t.1)) ^ s₁) ∂τ'
      ≤ ∫⁻ t, ENNReal.ofReal ((n : ℝ) ^ (2 * M)) * F (z * t) ∂τ' := lintegral_mono fun t => key t
    _ = ENNReal.ofReal ((n : ℝ) ^ (2 * M)) * ∫⁻ t, F (z * t) ∂τ' := lintegral_const_mul' _ _ hc
    _ = ENNReal.ofReal ((n : ℝ) ^ (2 * M)) * ∫⁻ t, F t ∂τ' := by rw [lintegral_mul_left_eq_self]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFfin

end S_AutomorphicForm_exists_lintegral_twistedCentralizer_inv_one_add_norm_sq_pow_mul_indicator_mul_ideleNorm_det_rpow_lt_top_of_forall_ne_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_exists_lintegral_twistedCentralizer_inv_one_add_norm_sq_pow_mul_indicator_mul_ideleNorm_det_rpow_lt_top_of_forall_ne_scalar_of_finrank_eq_two (solution)
