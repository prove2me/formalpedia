-- Prove2me | solution 1 for AutomorphicForm.prod_corr_one_mul_sqrt_discr_pow_mul_norm_det_mul_measure_pi_adelicBox_eq_measure_colPreimage_mul_two_pow_mul_prod_mul_discr_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/822064c9-6fd8-5886-b7b1-aab9cec30468

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_setLIntegral_twistedCentralizer_norm_det_mul_measure_pi_integers_eq_setLIntegral_lattice_mul_measure_preimage_of_isAddHaarMeasure
import Theorems.Thm_AutomorphicForm_setLIntegral_lattice_norm_det_mul_norm_four_eq_mul_sqrt_norm_det_trace_of_map_conj_eq_smul_map_toTensorGL_localHaar
import Theorems.Thm_AutomorphicForm_setLIntegral_lattice_norm_det_mul_norm_four_eq_mul_sqrt_norm_det_trace_of_not_isSigmaConjugate_scalar
import Theorems.Thm_AutomorphicForm_exists_finset_measure_colPreimage_mul_prod_measure_pi_integers_eq_measure_pi_adelicBox_mul_prod_measure_preimage_level
import Theorems.Thm_AutomorphicForm_setLIntegral_twistedCentralizer_semiLocalIntegers_norm_det_eq_inv_one_sub_mul_inv_one_sub_of_map_conj_eq_map_toTensorGL_localHaar_of_measure_semiLocalIntegralSet_eq_one
import Theorems.Thm_AutomorphicForm_det_trace_matrix_trace_mul_ne_zero_of_forall_mul_eq_mul_map_iff_mem_span_of_normString_eq_toTensorGL_centralScalar
import Theorems.Thm_NumberField_exists_finset_forall_prod_infinitePlace_pow_mul_prod_norm_algebraMap_adicCompletion_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_prod_corr_one_mul_sqrt_discr_pow_mul_norm_det_mul_measure_pi_adelicBox_eq_measure_colPreimage_mul_two_pow_mul_prod_mul_discr_sq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ContinuousAddEquiv.restrictedProductPi_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply"

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm

open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical

theorem E8F_sqrt_prod {α : Type} (s : Finset α) (f : α → ℝ) (hf : ∀ a ∈ s, 0 ≤ f a) :
    ∏ a ∈ s, Real.sqrt (f a) = Real.sqrt (∏ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Real.sqrt_mul (hf a (Finset.mem_insert_self a s)),
      ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))]

theorem E8F_key {α : Type} [DecidableEq α] (S S₁ S₀ : Finset α) (hS₁ : S₁ ⊆ S) (hS₀ : S₀ ⊆ S)
    (I J O Pm n4 nd ζ t C : α → ℝ≥0∞) (R B sqN d2 pw : ℝ≥0∞)
    (hO : ∀ w ∈ S, O w ≠ 0 ∧ O w ≠ ⊤) (hζ : ∀ w ∈ S, ζ w ≠ 0 ∧ ζ w ≠ ⊤)
    (h1 : ∀ w ∈ S, I w * O w = J w * Pm w) (h2 : ∀ w ∈ S, J w * n4 w = t w * nd w * ζ w)
    (h3 : R * ∏ w ∈ S, O w = B * ∏ w ∈ S, Pm w)
    (hI₁ : ∀ w ∈ S₁, I w = C w * ζ w) (hI₂ : ∀ w ∈ S, w ∉ S₁ → I w = ζ w)
    (ht : ∀ w ∈ S, w ∉ S₀ → t w = 1) (hN : sqN * ∏ w ∈ S, nd w = 1) (h4 : pw * ∏ w ∈ S, n4 w = 1) :
    (∏ w ∈ S₁, C w) * (d2 * sqN * B) = R * (pw * (∏ w ∈ S₀, t w) * d2) := by
  have hprodO : (∏ w ∈ S, O w) ≠ 0 ∧ (∏ w ∈ S, O w) ≠ ⊤ :=
    ⟨Finset.prod_ne_zero_iff.mpr fun w hw => (hO w hw).1, ENNReal.prod_ne_top fun w hw => (hO w hw).2⟩
  have hprodζ : (∏ w ∈ S, ζ w) ≠ 0 ∧ (∏ w ∈ S, ζ w) ≠ ⊤ :=
    ⟨Finset.prod_ne_zero_iff.mpr fun w hw => (hζ w hw).1, ENNReal.prod_ne_top fun w hw => (hζ w hw).2⟩
  have e1 : (∏ w ∈ S, I w) * ∏ w ∈ S, O w = (∏ w ∈ S, J w) * ∏ w ∈ S, Pm w := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl h1
  have e2 : (∏ w ∈ S, I w) * B = (∏ w ∈ S, J w) * R := by
    have h : (∏ w ∈ S, I w) * B * ∏ w ∈ S, O w = (∏ w ∈ S, J w) * R * ∏ w ∈ S, O w := by
      calc (∏ w ∈ S, I w) * B * ∏ w ∈ S, O w = ((∏ w ∈ S, I w) * ∏ w ∈ S, O w) * B := by ring
        _ = ((∏ w ∈ S, J w) * ∏ w ∈ S, Pm w) * B := by rw [e1]
        _ = (∏ w ∈ S, J w) * (B * ∏ w ∈ S, Pm w) := by ring
        _ = (∏ w ∈ S, J w) * (R * ∏ w ∈ S, O w) := by rw [h3]
        _ = (∏ w ∈ S, J w) * R * ∏ w ∈ S, O w := by ring
    exact (ENNReal.mul_left_inj hprodO.1 hprodO.2).mp h
  have e3 : (∏ w ∈ S, I w) = (∏ w ∈ S₁, C w) * ∏ w ∈ S, ζ w := by
    have a : ∏ w ∈ S \ S₁, I w = ∏ w ∈ S \ S₁, ζ w :=
      Finset.prod_congr rfl fun w hw => hI₂ w (Finset.mem_sdiff.mp hw).1 (Finset.mem_sdiff.mp hw).2
    have b' : ∏ w ∈ S₁, I w = (∏ w ∈ S₁, C w) * ∏ w ∈ S₁, ζ w := by
      rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl hI₁
    rw [← Finset.prod_sdiff hS₁, ← Finset.prod_sdiff (f := ζ) hS₁, a, b']; ring
  have e4 : (∏ w ∈ S, J w) * ∏ w ∈ S, n4 w = (∏ w ∈ S₀, t w) * (∏ w ∈ S, nd w) * ∏ w ∈ S, ζ w := by
    rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl h2, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_subset hS₀ (fun w hw hw0 => ht w hw hw0)]
  have e5 : (∏ w ∈ S₁, C w) * (d2 * sqN * B) * ((∏ w ∈ S, ζ w) * (pw * ∏ w ∈ S, n4 w)) =
      R * (pw * (∏ w ∈ S₀, t w) * d2) * ((∏ w ∈ S, ζ w) * (sqN * ∏ w ∈ S, nd w)) := by
    calc (∏ w ∈ S₁, C w) * (d2 * sqN * B) * ((∏ w ∈ S, ζ w) * (pw * ∏ w ∈ S, n4 w))
        = ((∏ w ∈ S₁, C w) * ∏ w ∈ S, ζ w) * B * (∏ w ∈ S, n4 w) * (d2 * sqN * pw) := by ring
      _ = (∏ w ∈ S, I w) * B * (∏ w ∈ S, n4 w) * (d2 * sqN * pw) := by rw [e3]
      _ = (∏ w ∈ S, J w) * R * (∏ w ∈ S, n4 w) * (d2 * sqN * pw) := by rw [e2]
      _ = ((∏ w ∈ S, J w) * ∏ w ∈ S, n4 w) * R * (d2 * sqN * pw) := by ring
      _ = ((∏ w ∈ S₀, t w) * (∏ w ∈ S, nd w) * ∏ w ∈ S, ζ w) * R * (d2 * sqN * pw) := by rw [e4]
      _ = R * (pw * (∏ w ∈ S₀, t w) * d2) * ((∏ w ∈ S, ζ w) * (sqN * ∏ w ∈ S, nd w)) := by ring
  rw [hN, h4, mul_one] at e5
  exact (ENNReal.mul_left_inj hprodζ.1 hprodζ.2).mp e5

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

    (τf' : ∀ v : HeightOneSpectrum (𝓞 K), Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτf' : ∀ v, (τf' v).IsHaarMeasure)

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

    (hone : ∀ v ∉ S₀, τf' v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)

    (v : Fin 2 → L) (hv : v ≠ 0)
    (U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L)) (hUo : IsOpen U) (hUc : IsCompact U)
    (S₁ : Finset (HeightOneSpectrum (𝓞 K))) (hS₁ : S₀ ⊆ S₁)
    (W : ∀ v : HeightOneSpectrum (𝓞 K), Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hWm : ∀ v, MeasurableSet[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] (W v))
    (hW₀ : ∀ v ∉ S₁, ∀ x : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
      ((x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ W v ↔
        ∀ i j, ((x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j ∈
          AutomorphicForm.semiLocalIntegers K L v))
    (hW₁ : ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ S → ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      (∀ v ∉ S, AutomorphicForm.tensorPlace K L v (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∈
          AutomorphicForm.semiLocalIntegralSet K L v) →
        U.indicator (fun _ => (1 : ℂ)) (fun i =>
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2) =
          ∏ v ∈ S, (W v).indicator (fun _ => (1 : ℂ))
            (AutomorphicForm.tensorPlace K L v (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))))
    (hunit : ∀ v ∉ S₁,
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
          Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v)))
    (Corr : HeightOneSpectrum (𝓞 K) → ℝ → ℝ≥0∞)
    (hCorr : ∀ v ∈ S₁, ∀ s' : ℝ, 1 ≤ s' →
      ∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ W v},
          ENNReal.ofReal (‖Algebra.norm (v.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ ^ s') ∂(τf' v) =
        Corr v s' * ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹))
    (hCorr₁ : ∀ v ∈ S₁, Corr v 1 ≠ ⊤ ∧ Tendsto (Corr v) (𝓝[>] (1 : ℝ)) (𝓝 (Corr v 1)))

    (ι : Type) [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 4)
    (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range b))
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (ρ : Measure (ι → AdeleRing (𝓞 K) K)) [ρ.IsAddHaarMeasure] :
    ENNReal.ofReal (Real.sqrt (|(NumberField.discr K : ℝ)| ^ Fintype.card ι *
            |((Algebra.norm ℚ (Matrix.of fun i j : ι => Algebra.trace K L (Matrix.trace (b i * b j))).det : ℚ) : ℝ)|)) *
          ρ {a : ι → AdeleRing (𝓞 K) K | ∀ k, a k ∈ adelicBox K} ≠ 0 ∧
    ENNReal.ofReal (Real.sqrt (|(NumberField.discr K : ℝ)| ^ Fintype.card ι *
            |((Algebra.norm ℚ (Matrix.of fun i j : ι => Algebra.trace K L (Matrix.trace (b i * b j))).det : ℚ) : ℝ)|)) *
          ρ {a : ι → AdeleRing (𝓞 K) K | ∀ k, a k ∈ adelicBox K} ≠ ⊤ ∧
    (∏ v ∈ S₁, Corr v 1) *
        (ENNReal.ofReal (Real.sqrt (|(NumberField.discr K : ℝ)| ^ Fintype.card ι *
            |((Algebra.norm ℚ (Matrix.of fun i j : ι => Algebra.trace K L (Matrix.trace (b i * b j))).det : ℚ) : ℝ)|)) *
          ρ {a : ι → AdeleRing (𝓞 K) K | ∀ k, a k ∈ adelicBox K}) =
      ρ {a : ι → AdeleRing (𝓞 K) K | (∀ k, (a k).1 ∈ infiniteBox K) ∧
          (fun i => ((((∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k).map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)).mulVec
            fun j => algebraMap L (AdeleRing (𝓞 L) L) (v j)) i).2) ∈ U} *
        (2 ^ (2 * Module.finrank ℚ K) * (∏ v ∈ S₀, t v) * ENNReal.ofReal ((NumberField.discr K : ℝ) ^ 2)) := by

  letI mK : ∀ w : HeightOneSpectrum (𝓞 K), MeasurableSpace (w.adicCompletion K) := fun w => borel _
  haveI bK : ∀ w : HeightOneSpectrum (𝓞 K), BorelSpace (w.adicCompletion K) := fun w => ⟨rfl⟩
  let μ : ∀ w : HeightOneSpectrum (𝓞 K), Measure (ι → w.adicCompletion K) := fun w => Measure.addHaar

  have hdet := AutomorphicForm.det_trace_matrix_trace_mul_ne_zero_of_forall_mul_eq_mul_map_iff_mem_span_of_normString_eq_toTensorGL_centralScalar K L h2 σ hgen δ₀ c u hN hns ι b hb hbspan
  have hnorm : ((Algebra.norm ℚ (Matrix.of fun i j : ι => Algebra.trace K L (Matrix.trace (b i * b j))).det : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast Algebra.norm_ne_zero_iff.mpr hdet

  have hB0 : (ρ {a : ι → AdeleRing (𝓞 K) K | ∀ k, a k ∈ adelicBox K}) ≠ 0 := by
    obtain ⟨U₀, hU₀o, hU₀ne, hU₀sub⟩ := NumberField.AdelicBox.exists_isOpen_subset_adelicBox K
    obtain ⟨x₀, hx₀⟩ := hU₀ne
    have hsub : Set.pi Set.univ (fun _ : ι => U₀) ⊆ {a : ι → AdeleRing (𝓞 K) K | ∀ k, a k ∈ adelicBox K} :=
      fun a ha k => hU₀sub (ha k (Set.mem_univ k))
    have hopen : IsOpen (Set.pi Set.univ (fun _ : ι => U₀)) := isOpen_set_pi Set.finite_univ (fun _ _ => hU₀o)
    exact fun h => (hopen.measure_ne_zero ρ ⟨fun _ => x₀, fun k _ => hx₀⟩) (measure_mono_null hsub h)
  have hBT : (ρ {a : ι → AdeleRing (𝓞 K) K | ∀ k, a k ∈ adelicBox K}) ≠ ⊤ := by
    obtain ⟨C₀, hC₀, hsubC⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset K
    have hsub : {a : ι → AdeleRing (𝓞 K) K | ∀ k, a k ∈ adelicBox K} ⊆ Set.pi Set.univ (fun _ : ι => C₀) := fun a ha k _ => hsubC (ha k)
    exact ((measure_mono hsub).trans_lt (isCompact_univ_pi (fun _ => hC₀)).measure_lt_top).ne

  have hO : ∀ w : HeightOneSpectrum (𝓞 K), μ w {a : ι → w.adicCompletion K | ∀ k, a k ∈ w.adicCompletionIntegers K} ≠ 0 ∧ μ w {a : ι → w.adicCompletion K | ∀ k, a k ∈ w.adicCompletionIntegers K} ≠ ⊤ := fun w => by
    have hOo : IsOpen ((w.adicCompletionIntegers K : Set (w.adicCompletion K))) := Valued.isOpen_valuationSubring _
    haveI : CompactSpace ((w.adicCompletionIntegers K : Set (w.adicCompletion K))) :=
      inferInstanceAs (CompactSpace (w.adicCompletionIntegers K))
    have hOc : IsCompact ((w.adicCompletionIntegers K : Set (w.adicCompletion K))) :=
      isCompact_iff_compactSpace.mpr inferInstance
    have hset : {a : ι → w.adicCompletion K | ∀ k, a k ∈ w.adicCompletionIntegers K} =
        Set.pi Set.univ (fun _ : ι => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) := by
      ext a; simp [Set.mem_pi]
    rw [hset]
    exact ⟨(isOpen_set_pi Set.finite_univ fun _ _ => hOo).measure_ne_zero (μ w)
        ⟨fun _ => 0, fun k _ => zero_mem _⟩,
      ((isCompact_univ_pi fun _ => hOc).measure_lt_top).ne⟩

  have hζ : ∀ w : HeightOneSpectrum (𝓞 K), ((1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 : ℝ)))⁻¹ * (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - (2 : ℝ)))⁻¹) ≠ 0 ∧ ((1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 : ℝ)))⁻¹ * (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - (2 : ℝ)))⁻¹) ≠ ⊤ := fun w => by
    have hq : (1 : ℝ≥0∞) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) := by
      have h0 : Ideal.absNorm w.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr w.ne_bot
      have h1 : Ideal.absNorm w.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr w.isPrime.ne_top
      have : (2 : ℕ) ≤ Ideal.absNorm w.asIdeal := by omega
      exact_mod_cast (lt_of_lt_of_le one_lt_two this)
    have hlt : ∀ r : ℝ, r < 0 → ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ r < 1 := fun r hr =>
      ENNReal.rpow_lt_one_of_one_lt_of_neg hq hr
    have hfac : ∀ r : ℝ, r < 0 →
        (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ r)⁻¹ ≠ 0 ∧ (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ r)⁻¹ ≠ ⊤ :=
      fun r hr => ⟨ENNReal.inv_ne_zero.mpr (ENNReal.sub_ne_top ENNReal.one_ne_top),
        ENNReal.inv_ne_top.mpr (tsub_pos_of_lt (hlt r hr)).ne'⟩
    have ha := hfac (-(2 : ℝ)) (by norm_num)
    have hb' := hfac (1 - (2 : ℝ)) (by norm_num)
    exact ⟨mul_ne_zero ha.1 hb'.1, ENNReal.mul_ne_top ha.2 hb'.2⟩

  obtain ⟨T₀, hT₀⟩ := NumberField.exists_finset_forall_prod_infinitePlace_pow_mul_prod_norm_algebraMap_adicCompletion_eq_one K (Matrix.of fun i j : ι => Algebra.trace K L (Matrix.trace (b i * b j))).det hdet
  obtain ⟨T₁, hT₁⟩ := NumberField.exists_finset_forall_prod_infinitePlace_pow_mul_prod_norm_algebraMap_adicCompletion_eq_one K (4 : K) (by norm_num)

  obtain ⟨S₂, hS₁₂, hL3⟩ := AutomorphicForm.exists_finset_measure_colPreimage_mul_prod_measure_pi_integers_eq_measure_pi_adelicBox_mul_prod_measure_preimage_level K L h2 σ hgen δ₀ c u hN hns v hv U hUo hUc S₁ W hWm hW₀ hW₁ ι hι b hb hbspan ρ μ
  set S : Finset (HeightOneSpectrum (𝓞 K)) := S₂ ∪ (T₀ ∪ T₁) with hSdef
  have hS₂S : S₂ ⊆ S := Finset.subset_union_left
  have hT₀S : T₀ ⊆ S := Finset.subset_union_left.trans Finset.subset_union_right
  have hT₁S : T₁ ⊆ S := Finset.subset_union_right.trans Finset.subset_union_right
  have hS₁S : S₁ ⊆ S := hS₁₂.trans hS₂S
  have hS₀S : S₀ ⊆ S := hS₁.trans hS₁S

  have hL1 := fun w : HeightOneSpectrum (𝓞 K) =>
    AutomorphicForm.setLIntegral_twistedCentralizer_norm_det_mul_measure_pi_integers_eq_setLIntegral_lattice_mul_measure_preimage_of_isAddHaarMeasure K L h2 σ hgen δ₀ c u hN hns w (τf' w) (hτf' w) ι b hb hbspan (μ w) (W w) (hWm w)
  have hI₁ := fun w (hw : w ∈ S₁) => hCorr w hw 1 le_rfl
  simp only [Real.rpow_one, mul_one] at hI₁
  have hI₂ : ∀ w ∈ S, w ∉ S₁ → (∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L w (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) |
          (t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ W w}, ENNReal.ofReal ‖Algebra.norm (w.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)))‖ ∂(τf' w)) = ((1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 : ℝ)))⁻¹ * (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - (2 : ℝ)))⁻¹) := fun w _ hw1 => by
    obtain ⟨y, hy, hmap⟩ := hunit w hw1
    have e : {t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L w (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) | (t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ W w} = {t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L w (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) |
        ∀ i j, ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) i j ∈ AutomorphicForm.semiLocalIntegers K L w} :=
      Set.ext fun x => hW₀ w hw1 x
    show (∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L w (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) | (t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ W w}, ENNReal.ofReal ‖Algebra.norm (w.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)))‖ ∂(τf' w)) = _
    rw [e]
    exact AutomorphicForm.setLIntegral_twistedCentralizer_semiLocalIntegers_norm_det_eq_inv_one_sub_mul_inv_one_sub_of_map_conj_eq_map_toTensorGL_localHaar_of_measure_semiLocalIntegralSet_eq_one K L h2 σ hgen δ₀ c u hN hns w (τf' w) (hτf' w) y hy hmap (hone w (fun h0 => hw1 (hS₁ h0)))

  have hN' : (ENNReal.ofReal (Real.sqrt |((Algebra.norm ℚ (Matrix.of fun i j : ι => Algebra.trace K L (Matrix.trace (b i * b j))).det : ℚ) : ℝ)|)) * ∏ w ∈ S, ENNReal.ofReal (Real.sqrt ‖algebraMap K (w.adicCompletion K) (Matrix.of fun i j : ι => Algebra.trace K L (Matrix.trace (b i * b j))).det‖) = 1 := by
    have h := hT₀ S hT₀S
    rw [NumberField.InfinitePlace.prod_eq_abs_norm, Rat.cast_abs] at h
    have hnn : ∀ w ∈ S, 0 ≤ ‖algebraMap K (w.adicCompletion K) (Matrix.of fun i j : ι => Algebra.trace K L (Matrix.trace (b i * b j))).det‖ := fun _ _ => norm_nonneg _
    rw [← ENNReal.ofReal_prod_of_nonneg (fun w _ => Real.sqrt_nonneg _), E8F_sqrt_prod S _ hnn,
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← Real.sqrt_mul (abs_nonneg _), h, Real.sqrt_one, ENNReal.ofReal_one]
  have h4' : ((2 : ℝ≥0∞) ^ (2 * Module.finrank ℚ K)) * ∏ w ∈ S, ENNReal.ofReal ‖(4 : w.adicCompletion K)‖ = 1 := by
    have h := hT₁ S hT₁S
    rw [NumberField.InfinitePlace.prod_eq_abs_norm, Rat.cast_abs] at h
    have hn4 : |((Algebra.norm ℚ (4 : K) : ℚ) : ℝ)| = (4 : ℝ) ^ Module.finrank ℚ K := by
      rw [show (4 : K) = algebraMap ℚ K 4 from (map_ofNat (algebraMap ℚ K) 4).symm, Algebra.norm_algebraMap]
      push_cast
      exact abs_of_nonneg (by positivity)
    rw [hn4] at h
    simp only [map_ofNat] at h
    have hpw : ((2 : ℝ≥0∞) ^ (2 * Module.finrank ℚ K)) = ENNReal.ofReal ((4 : ℝ) ^ Module.finrank ℚ K) := by
      rw [pow_mul, ENNReal.ofReal_pow (by norm_num)]; norm_num
    rw [hpw, ← ENNReal.ofReal_prod_of_nonneg (fun w _ => norm_nonneg _), ← ENNReal.ofReal_mul (by positivity), h,
      ENNReal.ofReal_one]

  have hL2 := fun w : HeightOneSpectrum (𝓞 K) => (hfin w).elim
    (fun h => h.elim fun y hy =>
      AutomorphicForm.setLIntegral_lattice_norm_det_mul_norm_four_eq_mul_sqrt_norm_det_trace_of_map_conj_eq_smul_map_toTensorGL_localHaar K L h2 σ hgen δ₀ c u hN hns w (τf' w) (hτf' w) (t w) y hy.1 hy.2 ι b hb hbspan)
    (fun h => AutomorphicForm.setLIntegral_lattice_norm_det_mul_norm_four_eq_mul_sqrt_norm_det_trace_of_not_isSigmaConjugate_scalar K L h2 σ hgen δ₀ c u hN hns w (τf' w) (hτf' w) (t w) h.1 h.2 ι b hb hbspan)

  have hkey := E8F_key S S₁ S₀ hS₁S hS₀S _ _ _ _ _ _ _ t _ (ρ {a : ι → AdeleRing (𝓞 K) K | (∀ k, (a k).1 ∈ infiniteBox K) ∧
          (fun i => ((((∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k).map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)).mulVec
            fun j => algebraMap L (AdeleRing (𝓞 L) L) (v j)) i).2) ∈ U}) (ρ {a : ι → AdeleRing (𝓞 K) K | ∀ k, a k ∈ adelicBox K}) (ENNReal.ofReal (Real.sqrt |((Algebra.norm ℚ (Matrix.of fun i j : ι => Algebra.trace K L (Matrix.trace (b i * b j))).det : ℚ) : ℝ)|)) (ENNReal.ofReal ((NumberField.discr K : ℝ) ^ 2)) ((2 : ℝ≥0∞) ^ (2 * Module.finrank ℚ K))
    (fun w _ => hO w) (fun w _ => hζ w) (fun w _ => hL1 w) (fun w _ => hL2 w) (hL3 S hS₂S) hI₁ hI₂
    (fun w _ hw0 => ht w hw0) hN' h4'

  have hQ : ENNReal.ofReal (Real.sqrt (|(NumberField.discr K : ℝ)| ^ Fintype.card ι *
      |((Algebra.norm ℚ (Matrix.of fun i j : ι => Algebra.trace K L (Matrix.trace (b i * b j))).det : ℚ) : ℝ)|)) = (ENNReal.ofReal ((NumberField.discr K : ℝ) ^ 2)) * (ENNReal.ofReal (Real.sqrt |((Algebra.norm ℚ (Matrix.of fun i j : ι => Algebra.trace K L (Matrix.trace (b i * b j))).det : ℚ) : ℝ)|)) := by
    rw [hι, show |(NumberField.discr K : ℝ)| ^ 4 = ((NumberField.discr K : ℝ) ^ 2) ^ 2 by rw [← sq_abs (NumberField.discr K : ℝ)]; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), ENNReal.ofReal_mul (by positivity)]
  have hQ0 : (ENNReal.ofReal ((NumberField.discr K : ℝ) ^ 2)) * (ENNReal.ofReal (Real.sqrt |((Algebra.norm ℚ (Matrix.of fun i j : ι => Algebra.trace K L (Matrix.trace (b i * b j))).det : ℚ) : ℝ)|)) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity [NumberField.discr_ne_zero K])
    · exact ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr (abs_pos.mpr hnorm))
  refine ⟨?_, ?_, ?_⟩
  · rw [hQ]; exact mul_ne_zero hQ0 hB0
  · rw [hQ]; exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hBT
  · rw [hQ]; exact hkey

end S_AutomorphicForm_prod_corr_one_mul_sqrt_discr_pow_mul_norm_det_mul_measure_pi_adelicBox_eq_measure_colPreimage_mul_two_pow_mul_prod_mul_discr_sq
end P2MW
export P2MW.S_AutomorphicForm_prod_corr_one_mul_sqrt_discr_pow_mul_norm_det_mul_measure_pi_adelicBox_eq_measure_colPreimage_mul_two_pow_mul_prod_mul_discr_sq (solution)
