-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a3b35578-ea2d-57cd-86d3-e11e9941dd81

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_monoidHom_isCuspLift_rightTranslate_and_norm_eq_and_continuous
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_rightTranslate
import Theorems.Thm_MeasureTheory_exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous
import Theorems.Thm_AutomorphicForm_exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one
import Theorems.Thm_AutomorphicForm_apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective
import Theorems.Thm_AutomorphicForm_isCompact_rowIsometrySubgroup_detOne
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 320000

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace Topology ComplexConjugate Matrix

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

p2m_attr_erase "instance" "WithCStarModule.instCStarModuleComplex"

namespace KwProof

section Incl

variable (F : Type) [Field F] [NumberField F]

abbrev Kw (w : InfinitePlace F) : Type := rowIsometrySubgroup₀ w.Completion

abbrev Kprod : Type := ∀ w : InfinitePlace F, Kw F w

omit [NumberField F] in
theorem commute_archRowIsometryInclAt₀ {v w : InfinitePlace F} (hvw : v ≠ w)
    (a : Kw F v) (b : Kw F w) :
    Commute (archRowIsometryInclAt₀ F v a) (archRowIsometryInclAt₀ F w b) := by
  unfold archRowIsometryInclAt₀
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  exact commute_archGLIncl_of_ne F hvw _ _

noncomputable def inclArch : Kprod F →* GL (Fin 2) (InfiniteAdeleRing F) :=
  MonoidHom.noncommPiCoprod (archRowIsometryInclAt₀ F) (fun _ _ hvw => commute_archRowIsometryInclAt₀ F hvw)

variable {F}

theorem inclArch_mulSingle [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) (k : Kw F w) :
    inclArch F (Pi.mulSingle w k) = archRowIsometryInclAt₀ F w k :=
  MonoidHom.noncommPiCoprod_mulSingle _ w k

theorem inclArch_entry (κ : Kprod F) (i j : Fin 2) (w : InfinitePlace F) :
    ((inclArch F κ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w
      = ((κ w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
  classical
  let f : Kprod F →* (∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) :=
    ((archMatrixPiEquiv F : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) →*
        ∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion).comp
      (Units.coeHom (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)))).comp (inclArch F)
  let g : Kprod F →* (∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) :=
    MonoidHom.pi fun v : InfinitePlace F =>
      ((Units.coeHom (Matrix (Fin 2) (Fin 2) v.Completion)).comp
        (rowIsometrySubgroup₀ v.Completion).subtype).comp
          (Pi.evalMonoidHom (fun u : InfinitePlace F => Kw F u) v)
  have hfg : f = g := by
    refine MonoidHom.pi_ext fun v k => ?_
    funext u
    show archMatrixPiEquiv F
        ((inclArch F (Pi.mulSingle v k) : GL (Fin 2) (InfiniteAdeleRing F)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) u
      = ((Pi.mulSingle v k u : Kw F u) : GL (Fin 2) u.Completion)
    rw [inclArch_mulSingle]
    show archMatrixPiEquiv F (archMatrixUpdate F v ((k : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion)) u = _
    rw [archMatrixPiEquiv_archMatrixUpdate]
    by_cases huv : u = v
    · subst huv
      simp
    · simp [Function.update_of_ne huv, Pi.mulSingle_eq_of_ne huv]
  have h : f κ = g κ := by rw [hfg]
  have hw := congrFun h w
  exact congrFun (congrFun hw i) j

theorem archComponent_inclArch (κ : Kprod F) (w : InfinitePlace F) :
    archComponent F w (inclArch F κ) = (κ w : GL (Fin 2) w.Completion) := by
  ext i j
  rw [AdelicLevel.archComponent_apply, inclArch_entry]

theorem continuous_inclArch : Continuous (inclArch F) := by
  have hval : Continuous fun κ : Kprod F =>
      ((inclArch F κ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
    refine continuous_matrix fun i j => ?_
    refine continuous_pi fun w => ?_
    simp only [inclArch_entry]
    exact (Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply w))).matrix_elem i j
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl F) := by
  have hval : Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      ((adelicArchGLIncl F g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      (((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) :
          InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

theorem eq_inclArch (ι : Kprod F →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : Kprod F) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)) :
    ι = inclArch F := by
  refine MonoidHom.ext fun κ => Units.ext (Matrix.ext fun i j => funext fun w => ?_)
  have h1 := AdelicLevel.archComponent_apply (K := F) w (ι κ) i j
  have h2 := AdelicLevel.archComponent_apply (K := F) w (inclArch F κ) i j
  rw [← h1, ← h2, hι, archComponent_inclArch]

theorem ideleNorm_det_eq_one (ι : Kprod F →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : Kprod F) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)) (κ : Kprod F) :
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (ι κ))) = 1 := by
  have hX : glFin (𝓞 F) F (adelicArchGLIncl F (ι κ)) ∈ finiteIntegralGL2 (𝓞 F) F := by
    rw [glFin_adelicArchGLIncl]; exact one_mem _
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult F _ hX]
  refine Finset.prod_eq_one fun w _ => ?_
  have h1 : NumberField.AdelicVolume.archDetNorm w (adelicArchGLIncl F (ι κ)) = 1 := by
    unfold NumberField.AdelicVolume.archDetNorm
    rw [glArch_adelicArchGLIncl, hι, ((mem_rowIsometrySubgroup₀_iff w.Completion).mp (κ w).2).1, norm_one]
  rw [h1, one_pow]

end Incl

section Misc

variable {F : Type} [Field F] [NumberField F]

theorem commute_of_glArch_eq_one {u : AdelicGL2 (𝓞 F) F} (hu : glArch (𝓞 F) F u = 1)
    (a : GL (Fin 2) (InfiniteAdeleRing F)) : u * adelicArchGLIncl F a = adelicArchGLIncl F a * u := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · have h := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j)
      (show glArch (𝓞 F) F (u * adelicArchGLIncl F a) = glArch (𝓞 F) F (adelicArchGLIncl F a * u) by
        rw [map_mul, map_mul, hu, one_mul, mul_one])
    simpa only [glArch_apply] using h
  · have h := congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)
      (show glFin (𝓞 F) F (u * adelicArchGLIncl F a) = glFin (𝓞 F) F (adelicArchGLIncl F a * u) by
        rw [map_mul, map_mul, glFin_adelicArchGLIncl, one_mul, mul_one])
    simpa only [glFin_apply] using h

theorem continuous_finEmbed : Continuous (AdelicDock.finEmbed (𝓞 F) F) := by
  have hval : ∀ {f : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}, Continuous f →
      Continuous fun g => ((AdelicDock.finEmbed (𝓞 F) F (f g) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    intro f hf
    refine continuous_matrix fun i j => ?_
    show Continuous fun g => (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        ((f g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F)
    exact continuous_const.prodMk ((Units.continuous_val.comp hf).matrix_elem i j)
  refine Units.continuous_iff.mpr ⟨hval continuous_id, ?_⟩
  simp only [← map_inv]
  exact hval continuous_inv

noncomputable def matRep {K : Type*} [Group K] {n : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) :
    Representation ℂ K (Fin n → ℂ) where
  toFun k := Matrix.toLin' (ρ k)
  map_one' := by rw [map_one, Matrix.toLin'_one]; rfl
  map_mul' a b := by rw [map_mul, Matrix.toLin'_mul]; rfl

theorem matRep_apply {K : Type*} [Group K] {n : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (k : K) (v : Fin n → ℂ) :
    matRep ρ k v = ρ k *ᵥ v := Matrix.toLin'_apply _ _

noncomputable def coeffMap {K : Type*} [Group K] {n : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (Fin n → ℂ) →ₗ[ℂ] (K → ℂ) where
  toFun v := fun κ => (ρ κ *ᵥ v) i
  map_add' v v' := by funext κ; simp [Matrix.mulVec_add]
  map_smul' c v := by funext κ; simp [Matrix.mulVec_smul]

theorem coeffMap_single {K : Type*} [Group K] {n : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) (κ : K) :
    coeffMap ρ i (Pi.single j 1) κ = ρ κ i j := by
  classical
  show (ρ κ *ᵥ Pi.single j 1) i = ρ κ i j
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem inner_apply_eq {K : Type*} [Group K] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (π : K →* (E →L[ℂ] E)) (hπn : ∀ (k : K) (v : E), ‖π k v‖ = ‖v‖) (κ : K) (a b : E) :
    ⟪π κ a, b⟫_ℂ = ⟪a, π κ⁻¹ b⟫_ℂ := by
  let L : E →ₗᵢ[ℂ] E := { toLinearMap := (π κ : E →ₗ[ℂ] E), norm_map' := hπn κ }
  have hL : ∀ x, L x = π κ x := fun _ => rfl
  have hsurj : π κ (π κ⁻¹ b) = b := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]
  have h := L.inner_map_map a (π κ⁻¹ b)
  rw [hL, hL, hsurj] at h
  exact h

theorem inner_ne_zero_of_norm_sub_lt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {w a : E} (hw : w ≠ 0) (hwa : ‖w - a‖ < ‖w‖ / 2) : ⟪w, a⟫_ℂ ≠ 0 := by
  intro h0
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have h1 : ⟪w, w⟫_ℂ = ⟪w, w - a⟫_ℂ := by rw [inner_sub_right, h0, sub_zero]
  have h2 : ‖w‖ ^ 2 ≤ ‖w‖ * (‖w‖ / 2) := by
    calc ‖w‖ ^ 2 = ‖⟪w, w⟫_ℂ‖ := by rw [inner_self_eq_norm_sq_to_K]; norm_cast; rw [abs_of_nonneg (by positivity)]
      _ = ‖⟪w, w - a⟫_ℂ‖ := by rw [h1]
      _ ≤ ‖w‖ * ‖w - a‖ := norm_inner_le_norm _ _
      _ ≤ ‖w‖ * (‖w‖ / 2) := mul_le_mul_of_nonneg_left hwa.le (norm_nonneg _)
  nlinarith

end Misc

section Dense

variable (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
  (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)

theorem cusp_inner_smul_left (c : ℂ) (x y : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : ⟪c • x, y⟫_ℂ = conj c * ⟪x, y⟫_ℂ := by
  rw [Submodule.coe_inner, Submodule.coe_inner, Submodule.coe_smul, inner_smul_left]

theorem cusp_inner_smul_right (c : ℂ) (x y : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : ⟪x, c • y⟫_ℂ = c * ⟪x, y⟫_ℂ := by
  rw [Submodule.coe_inner, Submodule.coe_inner, Submodule.coe_smul, inner_smul_right]

theorem exists_mem_norm_sub_lt (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
      ‖v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩‖ < ε := by
  have hv : (v : Carrier F Φ₀ σ) ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) : Set (Carrier F Φ₀ σ))) := by
    rw [← Submodule.topologicalClosure_coe]; exact v.2
  obtain ⟨a, haA, hav⟩ := Metric.mem_closure_iff.mp hv ε hε
  obtain ⟨φm, hφm, rfl⟩ := haA
  refine ⟨φm, hφm, ?_⟩
  rw [Submodule.coe_norm, Submodule.coe_sub, toCuspSubcarrier_apply_coe, ← dist_eq_norm]
  exact hav

end Dense

end KwProof

set_option maxHeartbeats 3200000 in
open KwProof in
theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hv : v ≠ 0) :
    ∃ (tys : AutomorphicForm.ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F)),
      U ≤ finiteAdelicGL2Subgroup F ∧
      IsOpen ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) ∧
      IsCompact ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) ∧
      (AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) ⊆ (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) ∧
      ∃ (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : ψ ∈ cuspMemberSubmodule F Φ₀ ξ),
        ψ ∈ archCutSubmodule F tys ∧ (∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, ψ (g * u) = ψ g) ∧
        ⟪v, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩⟫_ℂ ≠ 0 := by
  classical

  letI ipInst : InnerProductSpace ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ) := Submodule.innerProductSpace _

  haveI : ∀ w : InfinitePlace F, CompactSpace ↥(rowIsometrySubgroup₀ w.Completion) := fun w =>
    isCompact_iff_compactSpace.mp (AutomorphicForm.isCompact_rowIsometrySubgroup_detOne F w)
  letI mK : MeasurableSpace (Kprod F) := borel _
  haveI : BorelSpace (Kprod F) := ⟨rfl⟩
  set μ : Measure (Kprod F) := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (Kprod F)) with hμ
  haveI hprob : IsProbabilityMeasure μ :=
    ⟨by rw [hμ, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩
  have huniq : ∀ μ' : Measure (Kprod F), μ'.IsMulLeftInvariant → IsProbabilityMeasure μ' → μ' = μ := by
    intro μ' h1 h2
    have h := Measure.isMulInvariant_eq_smul_of_compactSpace μ' μ
    have hc : Measure.haarScalarFactor μ' μ = 1 := by
      have h1 := congrArg (fun ν : Measure (Kprod F) => ν Set.univ) h
      simp only [Measure.smul_apply, measure_univ] at h1
      rw [ENNReal.smul_def, smul_eq_mul, mul_one] at h1
      exact_mod_cast h1.symm
    rw [h, hc, one_smul]
  haveI hright : μ.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    haveI : IsProbabilityMeasure (μ.map (· * g)) := Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
    exact huniq _ inferInstance inferInstance
  haveI hinv : μ.IsInvInvariant := by
    refine ⟨?_⟩
    haveI : IsProbabilityMeasure μ.inv := by
      rw [Measure.inv_def]; exact Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
    exact huniq _ inferInstance inferInstance

  let ι : Kprod F →* GL (Fin 2) (InfiniteAdeleRing F) := inclArch F
  have hι : ∀ (κ : Kprod F) (w : InfinitePlace F), archComponent F w (ι κ) = (κ w : GL (Fin 2) w.Completion) :=
    archComponent_inclArch
  let y : Kprod F →* AdelicGL2 (𝓞 F) F := (adelicArchGLIncl F).comp ι
  have hy : ∀ κ, y κ = adelicArchGLIncl F (ι κ) := fun _ => rfl
  have hyc : Continuous y := continuous_adelicArchGLIncl.comp continuous_inclArch
  obtain ⟨π, hπlift, hπn, hπc⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_monoidHom_isCuspLift_rightTranslate_and_norm_eq_and_continuous F hΦ₀ σ ξ hσ ι hι
  letI normedInst : NormedAddCommGroup (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  haveI : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := by
    have hcl : IsClosed ((cuspSubcarrier F hΦ₀ σ ξ : Submodule ℂ (Carrier F Φ₀ σ)) : Set (Carrier F Φ₀ σ)) :=
      Submodule.isClosed_topologicalClosure _
    exact hcl.completeSpace_coe

  have hunit : ∀ (κ : Kprod F) (a b : ↥(cuspSubcarrier F hΦ₀ σ ξ)), ⟪π κ a, b⟫_ℂ = ⟪a, π κ⁻¹ b⟫_ℂ :=
    inner_apply_eq π hπn

  obtain ⟨n, ρ, i, j, hρ, hw⟩ :=
    MeasureTheory.exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous μ π hπn hπc
      (AutomorphicForm.exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one F) v hv
  set w : ↥(cuspSubcarrier F hΦ₀ σ ξ) := ∫ κ, (conj (ρ κ i j)) • π κ v ∂μ with hwdef

  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  obtain ⟨φ, hφ, hwa⟩ := exists_mem_norm_sub_lt F hΦ₀ σ ξ w (‖w‖ / 2) (by positivity)
  set a : ↥(cuspSubcarrier F hΦ₀ σ ξ) := toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩ with ha
  have hwa0 : ⟪w, a⟫_ℂ ≠ 0 := inner_ne_zero_of_norm_sub_lt hw hwa

  let c : Kprod F → ℂ := fun κ => ρ κ⁻¹ i j
  have hcc : Continuous c := (hρ.comp continuous_inv).matrix_elem i j
  have hcK : IsCompact (Set.univ : Set (Kprod F)) := isCompact_univ
  have hint1 : Integrable (fun κ => (conj (ρ κ i j)) • π κ v) μ :=
    Continuous.integrable_of_hasCompactSupport (((hρ.matrix_elem i j).star).smul (hπc v))
      (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))
  have hint2 : Integrable (fun κ => (ρ κ i j) • π κ⁻¹ a) μ :=
    Continuous.integrable_of_hasCompactSupport ((hρ.matrix_elem i j).smul ((hπc a).comp continuous_inv))
      (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))
  have hadj : ⟪w, a⟫_ℂ = ⟪v, ∫ κ, c κ • π κ a ∂μ⟫_ℂ := by
    calc ⟪w, a⟫_ℂ = conj ⟪a, w⟫_ℂ := (inner_conj_symm w a).symm
      _ = conj (∫ κ, ⟪a, (conj (ρ κ i j)) • π κ v⟫_ℂ ∂μ) := by rw [hwdef, ← integral_inner hint1 a]
      _ = ∫ κ, conj ⟪a, (conj (ρ κ i j)) • π κ v⟫_ℂ ∂μ := integral_conj.symm
      _ = ∫ κ, ⟪v, (ρ κ i j) • π κ⁻¹ a⟫_ℂ ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
          show conj ⟪a, (conj (ρ κ i j)) • π κ v⟫_ℂ = ⟪v, (ρ κ i j) • π κ⁻¹ a⟫_ℂ
          rw [inner_conj_symm ((conj (ρ κ i j)) • π κ v) a, cusp_inner_smul_left, Complex.conj_conj, cusp_inner_smul_right,
            hunit κ v a]
      _ = ⟪v, ∫ κ, (ρ κ i j) • π κ⁻¹ a ∂μ⟫_ℂ := integral_inner hint2 v
      _ = ⟪v, ∫ κ, c κ • π κ a ∂μ⟫_ℂ := by
          congr 1
          rw [← integral_inv_eq_self (fun κ => (ρ κ i j) • π κ⁻¹ a) μ]
          refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
          show (ρ κ⁻¹ i j) • π κ⁻¹⁻¹ a = c κ • π κ a
          rw [inv_inv]

  obtain ⟨hψ, hψeq⟩ :=
    AutomorphicForm.CuspidalSpectrum.integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_rightTranslate
      F hΦ₀ σ ξ μ ι hι (fun κ => π κ) hπlift hπc c hcc φ hφ
  set ψ : AdelicGL2 (𝓞 F) F → ℂ := fun x => ∫ κ, c κ * φ (x * adelicArchGLIncl F (ι κ)) ∂μ with hψdef
  have hvψ : ⟪v, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩⟫_ℂ ≠ 0 := by
    rw [← hψeq, ← ha, ← hadj]; exact hwa0

  let tys : AutomorphicForm.ArchTypeFamily F :=
    ⟨fun _ => 1, fun w _ => ⟨n, matRep (ρ.comp (MonoidHom.mulSingle (fun v : InfinitePlace F => Kw F v) w))⟩⟩

  have hψ' : ∀ x, ψ x = ∫ κ, ρ κ i j * φ (x * (adelicArchGLIncl F (ι κ))⁻¹) ∂μ := by
    intro x
    rw [hψdef]
    show ∫ κ, ρ κ⁻¹ i j * φ (x * adelicArchGLIncl F (ι κ)) ∂μ = _
    rw [← integral_inv_eq_self (fun κ => ρ κ i j * φ (x * (adelicArchGLIncl F (ι κ))⁻¹)) μ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    show ρ κ⁻¹ i j * φ (x * adelicArchGLIncl F (ι κ)) = ρ κ⁻¹ i j * φ (x * (adelicArchGLIncl F (ι κ⁻¹))⁻¹)
    rw [map_inv ι, map_inv (adelicArchGLIncl F), inv_inv]

  have hφc : Continuous φ := hφ.2
  have hintC : ∀ (u : Kprod F → ℂ), Continuous u → ∀ x : AdelicGL2 (𝓞 F) F,
      Integrable (fun κ => u κ * φ (x * (adelicArchGLIncl F (ι κ))⁻¹)) μ := by
    intro u hu x
    refine Continuous.integrable_of_hasCompactSupport (hu.mul (hφc.comp (continuous_const.mul ?_)))
      (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))
    exact (hyc.comp continuous_id).inv
  have hcut : ψ ∈ archCutSubmodule F tys := by
    rw [mem_archCutSubmodule_iff]
    intro w
    let jw : Kw F w →* Kprod F := MonoidHom.mulSingle (fun v : InfinitePlace F => Kw F v) w

    let C : Submodule ℂ (Kprod F → ℂ) :=
      { carrier := {u | Continuous u}
        add_mem' := fun {u u'} hu hu' => Continuous.add hu hu'
        zero_mem' := continuous_const
        smul_mem' := fun c' u hu => by
          show Continuous fun κ => c' • u κ
          exact continuous_const.fun_smul hu }
    have hCmem : ∀ u : Kprod F → ℂ, u ∈ C ↔ Continuous u := fun _ => Iff.rfl
    have hC : ∀ (k : Kw F w) (u : Kprod F → ℂ), u ∈ C → (fun κ => u (κ * jw k)) ∈ C :=
      fun k u hu => ((hCmem u).mp hu).comp (continuous_id.mul continuous_const)

    let A : ↥C →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
      { toFun := fun u x => ∫ κ, (u : Kprod F → ℂ) κ * φ (x * (adelicArchGLIncl F (ι κ))⁻¹) ∂μ
        map_add' := fun u u' => by
          funext x
          show ∫ κ, ((u : Kprod F → ℂ) κ + (u' : Kprod F → ℂ) κ) * φ (x * (adelicArchGLIncl F (ι κ))⁻¹) ∂μ =
            ∫ κ, (u : Kprod F → ℂ) κ * φ (x * (adelicArchGLIncl F (ι κ))⁻¹) ∂μ +
              ∫ κ, (u' : Kprod F → ℂ) κ * φ (x * (adelicArchGLIncl F (ι κ))⁻¹) ∂μ
          simp only [add_mul]
          exact integral_add (hintC _ u.2 x) (hintC _ u'.2 x)
        map_smul' := fun c' u => by
          funext x
          show ∫ κ, (c' • (u : Kprod F → ℂ) κ) * φ (x * (adelicArchGLIncl F (ι κ))⁻¹) ∂μ =
            c' • ∫ κ, (u : Kprod F → ℂ) κ * φ (x * (adelicArchGLIncl F (ι κ))⁻¹) ∂μ
          simp only [smul_eq_mul, mul_assoc]
          exact integral_const_mul _ _ }
    have hAapply : ∀ (u : ↥C) (x : AdelicGL2 (𝓞 F) F),
        A u x = ∫ κ, (u : Kprod F → ℂ) κ * φ (x * (adelicArchGLIncl F (ι κ))⁻¹) ∂μ := fun _ _ => rfl

    have hyj : ∀ k : Kw F w, adelicArchGLIncl F (ι (jw k)) = rowIsometryInclAt₀ F w k := by
      intro k
      show adelicArchGLIncl F (inclArch F (Pi.mulSingle w k)) = rowIsometryInclAt₀ F w k
      rw [inclArch_mulSingle]
      rfl

    have hA : ∀ (k : Kw F w) (u : ↥C) (x : AdelicGL2 (𝓞 F) F),
        A ⟨fun κ => (u : Kprod F → ℂ) (κ * jw k), hC k u u.2⟩ x = A u (x * rowIsometryInclAt₀ F w k) := by
      intro k u x
      rw [hAapply, hAapply]
      show ∫ κ, (u : Kprod F → ℂ) (κ * jw k) * φ (x * (adelicArchGLIncl F (ι κ))⁻¹) ∂μ = _
      rw [← integral_mul_right_eq_self (fun κ => (u : Kprod F → ℂ) (κ * jw k) * φ (x * (adelicArchGLIncl F (ι κ))⁻¹)) (jw k)⁻¹]
      refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
      show (u : Kprod F → ℂ) (κ * (jw k)⁻¹ * jw k) * φ (x * (adelicArchGLIncl F (ι (κ * (jw k)⁻¹)))⁻¹) =
        (u : Kprod F → ℂ) κ * φ (x * rowIsometryInclAt₀ F w k * (adelicArchGLIncl F (ι κ))⁻¹)
      rw [inv_mul_cancel_right, map_mul, map_mul, map_inv, map_inv, mul_inv_rev, inv_inv, hyj, mul_assoc]

    have hu : (fun κ => ρ κ i j) ∈ C := (hCmem _).mpr (hρ.matrix_elem i j)
    have hT : IsRightEquivariant jw (matRep (ρ.comp jw)) (coeffMap ρ i) := by
      intro k vv κ
      show (ρ κ *ᵥ (matRep (ρ.comp jw) k vv)) i = (ρ (κ * jw k) *ᵥ vv) i
      rw [matRep_apply, Matrix.mulVec_mulVec, MonoidHom.comp_apply, ← map_mul]
    have hut : (fun κ => ρ κ i j) ∈ ⨆ _ : Fin 1, typeSubmodule jw (matRep (ρ.comp jw)) := by
      refine Submodule.mem_iSup_of_mem 0 ?_
      have hfun : (fun κ => ρ κ i j) = coeffMap ρ i (Pi.single j 1) := funext fun κ => (coeffMap_single ρ i j κ).symm
      rw [hfun]
      exact mem_typeSubmodule_of_isRightEquivariant hT _
    have hinj : Function.Injective (rowIsometryInclAt₀ F w) := by
      intro k k' hk
      have h1 := congrArg (fun g => archComponent F w (glArch (𝓞 F) F g)) hk
      simp only [glArch_rowIsometryInclAt₀] at h1
      have h2 : ∀ k : Kw F w, archComponent F w (archRowIsometryInclAt₀ F w k) = (k : GL (Fin 2) w.Completion) :=
        fun k => archComponent_archGLIncl_self F w _
      rw [h2, h2] at h1
      exact Subtype.ext h1
    have hpush := AutomorphicForm.apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective
      jw (rowIsometryInclAt₀ F w) hinj C hC A hA (fun _ : Fin 1 => matRep (ρ.comp jw)) (fun κ => ρ κ i j) hu hut
    have hAψ : A ⟨fun κ => ρ κ i j, hu⟩ = ψ := funext fun x => by rw [hAapply, hψ' x]
    rw [hAψ] at hpush
    exact hpush

  let Sφ : Subgroup ↥(finiteAdelicGL2Subgroup F) :=
    MulAction.stabilizer ↥(finiteAdelicGL2Subgroup F) (FLT.SmoothVectors.RightTranslationFn.mk φ)
  have hSo : IsOpen (Sφ : Set ↥(finiteAdelicGL2Subgroup F)) := hφ.1.2
  let fK : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) →* ↥(finiteAdelicGL2Subgroup F) :=
    (AdelicDock.finEmbed (𝓞 F) F).codRestrict (finiteAdelicGL2Subgroup F)
      (fun g => (mem_finiteAdelicGL2Subgroup_iff F _).mpr (AdelicDock.glArch_finEmbed (𝓞 F) F g))
  have hfKc : Continuous fK := continuous_finEmbed.subtype_mk _
  let V₀ : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := Sφ.comap fK
  have hV₀o : IsOpen (V₀ : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := hSo.preimage hfKc
  have hV₀cl : IsClosed (V₀ : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := Subgroup.isClosed_of_isOpen V₀ hV₀o
  let V : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := V₀ ⊓ finiteIntegralGL2 (𝓞 F) F
  have hVo : IsOpen (V : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
    hV₀o.inter (isOpen_finiteLevelZero (𝓞 F) F top_ne_bot)
  have hVc : IsCompact (V : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
    (isCompact_finiteLevelZero (𝓞 F) F ⊤).inter_left hV₀cl
  let U : Subgroup (AdelicGL2 (𝓞 F) F) := V.map (AdelicDock.finEmbed (𝓞 F) F)
  have hglU : (AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) = (V : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
    rw [Subgroup.coe_map, Set.image_image]
    simp only [AdelicDock.glFin_finEmbed, Set.image_id']
  have hUle : U ≤ finiteAdelicGL2Subgroup F := by
    rintro _ ⟨g, hg, rfl⟩
    exact (mem_finiteAdelicGL2Subgroup_iff F _).mpr (AdelicDock.glArch_finEmbed (𝓞 F) F g)

  have hfix : ∀ u ∈ U, ∀ x : AdelicGL2 (𝓞 F) F, φ (x * u) = φ x := by
    rintro _ ⟨g, hg, rfl⟩ x
    have hgS : fK g ∈ Sφ := (Subgroup.mem_inf.mp hg).1
    rw [MulAction.mem_stabilizer_iff] at hgS
    have h1 := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f x) hgS
    simp only [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
      FLT.SmoothVectors.RightTranslationFn.toFun_mk] at h1
    exact h1
  have hUinv : ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, ψ (g * u) = ψ g := by
    intro g u hu
    rw [hψdef]
    show ∫ κ, c κ * φ (g * u * adelicArchGLIncl F (ι κ)) ∂μ = ∫ κ, c κ * φ (g * adelicArchGLIncl F (ι κ)) ∂μ
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    show c κ * φ (g * u * adelicArchGLIncl F (ι κ)) = c κ * φ (g * adelicArchGLIncl F (ι κ))
    rw [mul_assoc, commute_of_glArch_eq_one ((mem_finiteAdelicGL2Subgroup_iff F u).mp (hUle hu)) (ι κ), ← mul_assoc,
      hfix u hu]
  refine ⟨tys, U, hUle, ?_, ?_, ?_, ψ, hψ, hcut, hUinv, hvψ⟩
  · rw [hglU]; exact hVo
  · rw [hglU]; exact hVc
  · rw [hglU]; exact fun g hg => (Subgroup.mem_inf.mp hg).2

end S_AutomorphicForm_CuspidalSpectrum_exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero (solution)
