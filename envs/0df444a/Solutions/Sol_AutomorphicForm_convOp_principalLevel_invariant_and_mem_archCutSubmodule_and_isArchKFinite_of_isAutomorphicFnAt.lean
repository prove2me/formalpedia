-- Prove2me | solution 1 for AutomorphicForm.convOp_principalLevel_invariant_and_mem_archCutSubmodule_and_isArchKFinite_of_isAutomorphicFnAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b30e480e-f482-5453-9847-0f8863b84425

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Mathlib
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_AdelicVolume
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_memLp_two_restrict_of_isCompact_of_isAutomorphicFnAt_canonicalTruncationDomain
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt
import Theorems.Thm_AutomorphicForm_le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_comp_mul_and_eLpNorm_eq_and_eLpNorm_levelTypeAverage_le_of_kernel_maximalCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_convOp_principalLevel_invariant_and_mem_archCutSubmodule_and_isArchKFinite_of_isAutomorphicFnAt
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec"
p2m_attr_erase "simp" "AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent NumberField.AdelicVolume
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
noncomputable section

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicVolume AutomorphicForm.SiegelCovering

namespace V2Aux

variable {K : Type} [Field K] [NumberField K]

def sc (w : InfinitePlace K) (z : (w.Completion)ˣ) : GL (Fin 2) w.Completion :=
  Units.map (Matrix.scalar (Fin 2) : w.Completion →+* Matrix (Fin 2) (Fin 2) w.Completion).toMonoidHom z

theorem sc_apply (w : InfinitePlace K) (z : (w.Completion)ˣ) (i j : Fin 2) :
    ((sc w z : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j = if i = j then (z : w.Completion) else 0 := by
  show (Matrix.scalar (Fin 2) (z : w.Completion)) i j = _
  rw [Matrix.scalar_apply]
  by_cases h : i = j
  · subst h; rw [Matrix.diagonal_apply_eq, if_pos rfl]
  · rw [Matrix.diagonal_apply_ne _ h, if_neg h]

theorem sc_mul_sc_inv (w : InfinitePlace K) (z : (w.Completion)ˣ) : sc w z * sc w z⁻¹ = 1 := by
  unfold sc; rw [← map_mul, mul_inv_cancel, map_one]

theorem det_sc (w : InfinitePlace K) (z : (w.Completion)ˣ) :
    ((sc w z : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det = (z : w.Completion) ^ 2 := by
  rw [Matrix.det_fin_two, sc_apply, sc_apply, sc_apply, sc_apply]; simp; ring

theorem isRowIsometry_of_diag {L : Type*} [NormedField L] (M : GL (Fin 2) L) (u₁ u₂ : L) (hu₁ : ‖u₁‖ = 1) (hu₂ : ‖u₂‖ = 1)
    (h00 : (M : Matrix (Fin 2) (Fin 2) L) 0 0 = u₁) (h01 : (M : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (h10 : (M : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (h11 : (M : Matrix (Fin 2) (Fin 2) L) 1 1 = u₂) :
    IsRowIsometry M := by
  refine ⟨?_, fun x y => ?_⟩
  · rw [Matrix.det_fin_two, h00, h01, h10, h11, mul_zero, sub_zero, norm_mul, hu₁, hu₂, mul_one]
  · rw [h00, h01, h10, h11]
    simp only [mul_zero, add_zero, zero_add, norm_mul, hu₁, hu₂, mul_one]

theorem isRowIsometry_sc (w : InfinitePlace K) (z : (w.Completion)ˣ) (hz : ‖(z : w.Completion)‖ = 1) :
    IsRowIsometry (sc w z) :=
  isRowIsometry_of_diag _ _ _ hz hz (by rw [sc_apply]; simp) (by rw [sc_apply]; simp) (by rw [sc_apply]; simp)
    (by rw [sc_apply]; simp)

theorem inclAt_sc_eq_centralScalar (w : InfinitePlace K) (z : (w.Completion)ˣ) :
    adelicArchGLInclAt K w (sc w z) = centralScalar (𝓞 K) K (archCentralUnit K w z) := by
  classical
  apply eq_of_glArch_eq_of_glFin_eq
  · show NumberField.AdelicLevel.glArch (𝓞 K) K (adelicArchGLIncl K (archGLIncl K w (sc w z))) = _
    rw [glArch_adelicArchGLIncl]
    refine Matrix.GeneralLinearGroup.ext fun i j => funext fun v => ?_
    show archMatrixUpdate K w ((sc w z : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j v =
      ((NumberField.AdelicLevel.glArch (𝓞 K) K (centralScalar (𝓞 K) K (archCentralUnit K w z)) :
        GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j v
    rw [NumberField.AdelicLevel.glArch_apply]
    by_cases hv : v = w
    · subst hv
      rw [archMatrixUpdate_apply_self, sc_apply]
      by_cases hij : i = j
      · subst hij; rw [if_pos rfl, centralScalar_apply_eq, archCentralUnit_fst_self]
      · rw [if_neg hij, centralScalar_apply_ne _ hij]; rfl
    · rw [archMatrixUpdate_apply_of_ne _ _ _ _ _ hv]
      by_cases hij : i = j
      · subst hij; rw [Matrix.one_apply_eq, centralScalar_apply_eq, archCentralUnit_fst_of_ne _ _ hv]
      · rw [Matrix.one_apply_ne hij, centralScalar_apply_ne _ hij]; rfl
  · show NumberField.AdelicLevel.glFin (𝓞 K) K (adelicArchGLIncl K (archGLIncl K w (sc w z))) = _
    rw [glFin_adelicArchGLIncl, glFin_centralScalar_archCentralUnit]

theorem det_eq_one_or_of_isReal (w : InfinitePlace K) (hw : w.IsReal) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k) :
    (k : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 ∨ (k : Matrix (Fin 2) (Fin 2) w.Completion).det = -1 := by
  have hn := hk.1
  set d := (k : Matrix (Fin 2) (Fin 2) w.Completion).det
  let eR := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hw
  have h1 : |eR d| = 1 := by
    have : dist (eR d) (eR 0) = dist d 0 := eR.dist_eq d 0
    rw [dist_zero_right, hn, Real.dist_eq] at this
    have h0 : eR 0 = 0 := map_zero (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
    rwa [h0, sub_zero] at this
  rcases abs_eq (zero_le_one) |>.mp h1 with h | h
  · left; apply eR.injective
    rw [h]; exact (map_one (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)).symm
  · right; apply eR.injective
    rw [h, show eR (-1) = NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw (-1) from rfl, map_neg, map_one]

theorem exists_sq_eq_of_isComplex (w : InfinitePlace K) (hw : w.IsComplex) (d : w.Completion) :
    ∃ u : w.Completion, u ^ 2 = d := by
  let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (e d) (by norm_num : 0 < 2)
  refine ⟨e.symm s, ?_⟩
  apply e.injective
  rw [map_pow, RingEquiv.apply_symm_apply, hs]

def refl (w : InfinitePlace K) : GL (Fin 2) w.Completion where
  val := Matrix.of ![![1, 0], ![0, -1]]
  inv := Matrix.of ![![1, 0], ![0, -1]]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem refl_mul_refl (w : InfinitePlace K) : refl w * refl w = (1 : GL (Fin 2) w.Completion) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [refl, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_refl (w : InfinitePlace K) : ((refl w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det = -1 := by
  simp [refl, Matrix.det_fin_two]

theorem isRowIsometry_refl (w : InfinitePlace K) : IsRowIsometry (refl (K := K) w) :=
  isRowIsometry_of_diag _ 1 (-1) norm_one (by rw [norm_neg, norm_one]) (by simp [refl]) (by simp [refl]) (by simp [refl])
    (by simp [refl])

theorem isArchKFinite_of_mem_archCutSubmodule_of_central
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ξ : (AdeleRing (𝓞 K) K)ˣ → ℂ) (tysK : ArchTypeFamily K)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hcen : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
        φ (g * AutomorphicForm.centralScalar (𝓞 K) K z) = ξ z * φ g)
    (hcut : φ ∈ archCutSubmodule K tysK) :
    IsArchKFinite K φ := by
  classical
  intro w
  have hφw : φ ∈ ⨆ i, archTypeSubmoduleAt K w (tysK.rep w i) := (mem_archCutSubmodule_iff K tysK φ).mp hcut w
  obtain ⟨hfd, -, -⟩ :=
    AutomorphicForm.CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt
      K w (tysK.card w) (tysK.rep w) φ hφw
  set S : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) := Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
    CuspidalConstituent.rightTranslate K (rowIsometryInclAt₀ K w k) φ) with hS
  haveI : FiniteDimensional ℂ S := hfd

  let Lr : (AdelicGL2 (𝓞 K) K → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun x => x * adelicArchGLInclAt K w (refl w))
  set T : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) := S ⊔ S.map Lr with hT
  haveI : FiniteDimensional ℂ T := Submodule.finiteDimensional_sup S (S.map Lr)
  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.mp (inferInstance : Module.Finite ℂ T)
  refine ⟨s, fun k hk => ?_⟩
  rw [hs]
  obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.mp hk
  have hk₀' : IsRowIsometry k₀ := hk₀

  have hmemS : ∀ (h : GL (Fin 2) w.Completion) (hh : h ∈ rowIsometrySubgroup₀ w.Completion),
      (fun x => φ (x * adelicArchGLInclAt K w h)) ∈ S := by
    intro h hh
    exact Submodule.subset_span ⟨⟨h, hh⟩, rfl⟩
  by_cases hw : w.IsReal
  ·
    rcases det_eq_one_or_of_isReal w hw k₀ hk₀' with hd | hd
    · exact Submodule.mem_sup_left (hmemS k₀ ((mem_rowIsometrySubgroup₀_iff _).mpr ⟨hd, hk₀'⟩))
    · have hh : refl w * k₀ ∈ rowIsometrySubgroup₀ w.Completion := by
        refine (mem_rowIsometrySubgroup₀_iff _).mpr ⟨?_, (isRowIsometry_refl w).mul hk₀'⟩
        rw [Units.val_mul, Matrix.det_mul, hd, det_refl]; norm_num
      have hk₀eq : k₀ = refl w * (refl w * k₀) := by rw [← mul_assoc, refl_mul_refl, one_mul]
      have heq : (fun x => φ (x * adelicArchGLInclAt K w k₀)) =
          Lr (fun x => φ (x * adelicArchGLInclAt K w (refl w * k₀))) := by
        funext x
        show φ (x * adelicArchGLInclAt K w k₀) = φ (x * adelicArchGLInclAt K w (refl w) * adelicArchGLInclAt K w (refl w * k₀))
        rw [mul_assoc, ← map_mul, ← hk₀eq]
      rw [heq]
      exact Submodule.mem_sup_right (Submodule.mem_map_of_mem (hmemS _ hh))
  ·
    have hwc : w.IsComplex := (NumberField.InfinitePlace.isReal_or_isComplex w).resolve_left hw
    obtain ⟨u, hu⟩ := exists_sq_eq_of_isComplex w hwc ((k₀ : Matrix (Fin 2) (Fin 2) w.Completion).det)
    have hdn : ‖(k₀ : Matrix (Fin 2) (Fin 2) w.Completion).det‖ = 1 := hk₀'.1
    have hun : ‖u‖ = 1 := by
      have h2 : ‖u‖ ^ 2 = 1 := by rw [← norm_pow, hu, hdn]
      have h3 : (‖u‖ - 1) * (‖u‖ + 1) = 0 := by ring_nf; linarith [h2]
      rcases mul_eq_zero.mp h3 with h | h
      · linarith
      · linarith [norm_nonneg u]
    have hu0 : u ≠ 0 := fun h => by rw [h, norm_zero] at hun; exact zero_ne_one hun
    set z : (w.Completion)ˣ := Units.mk0 u hu0 with hz
    have hzn : ‖(z : w.Completion)‖ = 1 := hun
    have hzin : ‖((z⁻¹ : (w.Completion)ˣ) : w.Completion)‖ = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv, hzn, inv_one]
    have hh : sc w z⁻¹ * k₀ ∈ rowIsometrySubgroup₀ w.Completion := by
      refine (mem_rowIsometrySubgroup₀_iff _).mpr ⟨?_, (isRowIsometry_sc w z⁻¹ hzin).mul hk₀'⟩
      rw [Units.val_mul, Matrix.det_mul, det_sc, ← hu, Units.val_inv_eq_inv_val]
      show ((u : w.Completion)⁻¹) ^ 2 * u ^ 2 = 1
      rw [← mul_pow, inv_mul_cancel₀ hu0, one_pow]
    set h' : GL (Fin 2) w.Completion := sc w z⁻¹ * k₀ with hh'
    have hk₀eq : k₀ = sc w z * h' := by rw [hh', ← mul_assoc, sc_mul_sc_inv, one_mul]
    have heq : (fun x => φ (x * adelicArchGLInclAt K w k₀)) =
        ξ (archCentralUnit K w z) • fun x => φ (x * adelicArchGLInclAt K w h') := by
      funext x
      rw [Pi.smul_apply, smul_eq_mul]
      calc φ (x * adelicArchGLInclAt K w k₀)
          = φ (x * (centralScalar (𝓞 K) K (archCentralUnit K w z) * adelicArchGLInclAt K w h')) := by
            rw [hk₀eq, map_mul, inclAt_sc_eq_centralScalar]
        _ = φ (x * adelicArchGLInclAt K w h' * centralScalar (𝓞 K) K (archCentralUnit K w z)) := by
            rw [← mul_centralScalar_comm, mul_assoc]
        _ = ξ (archCentralUnit K w z) * φ (x * adelicArchGLInclAt K w h') := hcen _ _
    rw [heq]
    exact Submodule.mem_sup_left (S.smul_mem _ (hmemS _ hh))

end V2Aux

namespace V2Aux
open AutomorphicForm

variable (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]

theorem integral_conj_eq (k : AdelicGL2 (𝓞 K) K) (F : AdelicGL2 (𝓞 K) K → ℂ) :
    ∫ x, F (k⁻¹ * x * k) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = ∫ x, F x ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  have h1 : ∫ x, F (k⁻¹ * x * k) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = ∫ x, (fun t => F (k⁻¹ * t)) (x * k) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    congr 1; funext x; simp only [mul_assoc]
  rw [h1, MeasureTheory.integral_mul_right_eq_self (fun t => F (k⁻¹ * t)) k]
  exact MeasureTheory.integral_mul_left_eq_self F k⁻¹

theorem convOp_apply_mul (f φ : AdelicGL2 (𝓞 K) K → ℂ) (k : AdelicGL2 (𝓞 K) K)
    (hfk : ∀ y : AdelicGL2 (𝓞 K) K, f (k⁻¹ * y * k) = f y) (g : AdelicGL2 (𝓞 K) K) :
    convOp K f φ (g * k) = convOp K f (fun x => φ (x * k)) g := by
  simp only [convOp_apply, rightConv_apply]
  rw [← integral_conj_eq K k⁻¹ (fun x => φ (g * x * k) * f x)]
  congr 1; funext x
  have hf' : f (k * x * k⁻¹) = f x := by
    have := hfk (k * x * k⁻¹)
    rw [← this]; congr 1; group
  simp only [inv_inv]
  rw [hf']
  congr 1
  congr 1
  group

end V2Aux

set_option maxHeartbeats 1600000 in
open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (_hfN : ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ∀ y : AdelicGL2 (𝓞 K) K, f (u * y) = f y)
    (_hfK : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 K) K),
      f (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹) = f y)
    (v : AdelicGL2 (𝓞 K) K → ℂ)
    (_hv : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v)
    (_hvN : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, v (g * u') = v g)
    (_hvt : v ∈ archCutSubmodule K tysK) :
    (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
        convOp K f v (g * u') = convOp K f v g) ∧
      convOp K f v ∈ archCutSubmodule K tysK ∧
      IsArchKFinite K (convOp K f v) := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

  have ha : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      convOp K f v (g * u') = convOp K f v g := by
    intro g u hu
    simp only [convOp_apply, rightConv_apply]
    have h := MeasureTheory.integral_mul_left_eq_self (fun y => v (g * y) * f (u⁻¹ * y)) u (μ := (adelicGLHaar (Fin 2) (𝓞 K) K))
    have h1 : (fun x => (fun y => v (g * y) * f (u⁻¹ * y)) (u * x)) = fun x => v (g * u * x) * f x := by
      funext x; simp only [mul_assoc, inv_mul_cancel_left]
    rw [h1] at h
    rw [h]
    congr 1; funext y
    rw [_hfN u⁻¹ (Subgroup.inv_mem _ hu) y]

  have hRauto := AutomorphicForm.isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain K α β hα hαβ ξK hξc hξu v _hv f _hf _hfc

  have hb : convOp K f v ∈ archCutSubmodule K tysK := by
    rw [mem_archCutSubmodule_iff]
    intro w
    have hvw := (mem_archCutSubmodule_iff K tysK v).1 _hvt w
    obtain ⟨hSfin, hSstab, hSle⟩ :=
      AutomorphicForm.CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt K w (tysK.card w) (tysK.rep w) v hvw
    set S : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) := Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
        rightTranslate K (rowIsometryInclAt₀ K w k) v) with hS
    haveI : FiniteDimensional ℂ ↥S := hSfin

    have hι : Function.Injective (rowIsometryInclAt₀ K w) := by
      intro a b h
      apply Subtype.ext
      have := congrArg (fun x => archComponent K w (glArch (𝓞 K) K x)) h
      simpa [rowIsometryInclAt₀_apply, adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl,
        archComponent_archGLIncl_self] using this
    have hKw : ∀ k : rowIsometrySubgroup₀ w.Completion, rowIsometryInclAt₀ K w k ∈ adelicMaximalCompact K := by
      intro k
      rw [rowIsometryInclAt₀_apply, mem_adelicMaximalCompact_iff]
      refine ⟨?_, fun w' => ?_⟩
      · show glFin (𝓞 K) K (adelicArchGLIncl K (archGLIncl K w (k : GL (Fin 2) w.Completion))) ∈ finiteIntegralGL2 (𝓞 K) K
        rw [glFin_adelicArchGLIncl]
        exact (finiteIntegralGL2 (𝓞 K) K).one_mem
      · show IsRowIsometry (archComponent K w' (glArch (𝓞 K) K (adelicArchGLIncl K (archGLIncl K w (k : GL (Fin 2) w.Completion)))))
        rw [glArch_adelicArchGLIncl]
        by_cases h : w' = w
        · subst h; rw [archComponent_archGLIncl_self]; exact ((mem_rowIsometrySubgroup₀_iff _).mp k.2).2
        · rw [archComponent_archGLIncl_of_ne K h]; exact isRowIsometry_one

    have hmem : ∀ {u : AdelicGL2 (𝓞 K) K → ℂ}, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u ↔
        IsLsXiFunction (𝓞 K) K (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) ξK u ∧
          MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
      fun {u} => AutomorphicForm.lsXiMemberAt_iff (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) ⊤ ξK
        (AutomorphicForm.canonicalTruncationDomain K α β) u
    let A : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
      { carrier := {u | IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u}
        add_mem' := by
          intro u u' hu hu'
          refine hmem.2 ⟨⟨fun γ g => ?_, fun z g => ?_⟩, (hmem.1 hu).2.add (hmem.1 hu').2⟩
          · simp only [Pi.add_apply, (hmem.1 hu).1.left_invariant, (hmem.1 hu').1.left_invariant]
          · simp only [Pi.add_apply, (hmem.1 hu).1.central_transform, (hmem.1 hu').1.central_transform, mul_add]
        zero_mem' := by
          show IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK 0
          exact AutomorphicForm.isAutomorphicFnAt_zero K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK
        smul_mem' := by
          intro c u hu
          refine hmem.2 ⟨⟨fun γ g => ?_, fun z g => ?_⟩, (hmem.1 hu).2.const_smul c⟩
          · simp only [Pi.smul_apply, (hmem.1 hu).1.left_invariant]
          · simp only [Pi.smul_apply, smul_eq_mul, (hmem.1 hu).1.central_transform]; ring }
    have hSA_aut : S ≤ A := by
      rw [hS]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      show IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (rightTranslate K (rowIsometryInclAt₀ K w k) v)
      exact ((AutomorphicForm.isAutomorphicFnAt_comp_mul_and_eLpNorm_eq_and_eLpNorm_levelTypeAverage_le_of_kernel_maximalCompact K α β hα hαβ ξK (fun _ => 0) continuous_const v v _hv _hv).1
        ⟨rowIsometryInclAt₀ K w k, hKw k⟩).1

    have hint : ∀ u : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u →
        ∀ g : AdelicGL2 (𝓞 K) K, Integrable (fun x => u (g * x) * f x) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
      intro u hu g
      have hCc : IsCompact (tsupport f) := _hfc
      have hgC : IsCompact ((fun x : AdelicGL2 (𝓞 K) K => g * x) '' tsupport f) := hCc.image (continuous_const_mul g)
      have hL2 := AutomorphicForm.memLp_two_restrict_of_isCompact_of_isAutomorphicFnAt_canonicalTruncationDomain K α β hα hαβ ξK hξc u hu _ hgC
      have hmp : MeasurePreserving (fun x : AdelicGL2 (𝓞 K) K => g * x) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (tsupport f))
          ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict ((fun x : AdelicGL2 (𝓞 K) K => g * x) '' tsupport f)) := by
        have h0 := (measurePreserving_mul_left (adelicGLHaar (Fin 2) (𝓞 K) K) g).restrict_preimage hgC.isClosed.measurableSet
        have hpre : (fun x : AdelicGL2 (𝓞 K) K => g * x) ⁻¹' ((fun x : AdelicGL2 (𝓞 K) K => g * x) '' tsupport f) = tsupport f :=
          Set.preimage_image_eq _ (mul_right_injective g)
        rwa [hpre] at h0
      have hL2' : MemLp (fun x => u (g * x)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (tsupport f)) := hL2.comp_measurePreserving hmp
      haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (tsupport f)) := ⟨by
        rw [Measure.restrict_apply_univ]; exact hCc.measure_lt_top⟩
      have hL1 : Integrable (fun x => u (g * x)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (tsupport f)) := hL2'.integrable one_le_two
      obtain ⟨B, hB⟩ := _hf.bounded_above_of_compact_support _hfc
      have hIC : IntegrableOn (fun x => u (g * x) * f x) (tsupport f) (adelicGLHaar (Fin 2) (𝓞 K) K) :=
        hL1.mul_bdd _hf.aestronglyMeasurable (Filter.Eventually.of_forall hB)
      have hsupp : Function.support (fun x => u (g * x) * f x) ⊆ tsupport f := by
        intro x hx
        rw [Function.mem_support] at hx
        have hfx : f x ≠ 0 := fun h0 => hx (by rw [h0, mul_zero])
        exact subset_tsupport _ (Function.mem_support.mpr hfx)
      exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hIC

    have hadd : ∀ s t : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK s → IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK t →
        convOp K f (s + t) = convOp K f s + convOp K f t := by
      intro s t hs ht; funext g
      simp only [convOp_apply, rightConv_apply, Pi.add_apply, add_mul]
      exact integral_add (hint s hs g) (hint t ht g)
    have hcomm : ∀ (k : rowIsometrySubgroup₀ w.Completion) (φ : AdelicGL2 (𝓞 K) K → ℂ),
        (fun x => convOp K f φ (x * rowIsometryInclAt₀ K w k)) =
          convOp K f (fun x => φ (x * rowIsometryInclAt₀ K w k)) := by
      intro k φ; funext x
      refine V2Aux.convOp_apply_mul K f φ _ (fun y => ?_) x
      have := _hfK w k⁻¹ y
      rwa [map_inv, inv_inv] at this
    let θ₀ : ↥S →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) :=
      { toFun := fun s => convOp K f (s : AdelicGL2 (𝓞 K) K → ℂ)
        map_add' := fun s t => by
          simpa only [Submodule.coe_add] using hadd s t (hSA_aut s.2) (hSA_aut t.2)
        map_smul' := fun c s => by
          simp only [Submodule.coe_smul, RingHom.id_apply]
          exact convOp_smul K f c s }
    have hθ₀ : ∀ s : ↥S, θ₀ s = convOp K f (s : AdelicGL2 (𝓞 K) K → ℂ) := fun _ => rfl
    let S' : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) := LinearMap.range θ₀
    have hSstab' : ∀ k : rowIsometrySubgroup₀ w.Completion, ∀ s ∈ S,
        (fun x => s (x * rowIsometryInclAt₀ K w k)) ∈ S := fun k s hs => hSstab k s hs
    have hS' : ∀ k : rowIsometrySubgroup₀ w.Completion, ∀ s' ∈ S',
        (fun x => s' (x * rowIsometryInclAt₀ K w k)) ∈ S' := by
      rintro k _ ⟨s, rfl⟩
      refine ⟨⟨fun x => (s : AdelicGL2 (𝓞 K) K → ℂ) (x * rowIsometryInclAt₀ K w k), hSstab' k s s.2⟩, ?_⟩
      rw [hθ₀, hθ₀]
      exact (hcomm k s).symm
    have key := AutomorphicForm.le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule (rowIsometryInclAt₀ K w) hι
      (fun i : Fin (tysK.card w) => Fin (tysK.rep w i).n → ℂ) (fun i => (tysK.rep w i).ρ)
      S S' hS' hSstab' θ₀.rangeRestrict (LinearMap.surjective_rangeRestrict θ₀)
      (fun k s => by
        show convOp K f (fun x => (s : AdelicGL2 (𝓞 K) K → ℂ) (x * rowIsometryInclAt₀ K w k)) =
          fun x => convOp K f (s : AdelicGL2 (𝓞 K) K → ℂ) (x * rowIsometryInclAt₀ K w k)
        exact (hcomm k s).symm)
      hSle
    have hvS : v ∈ S := by
      rw [hS]
      refine Submodule.subset_span ⟨1, ?_⟩
      funext x; simp [rightTranslate, map_one]
    exact key ⟨⟨v, hvS⟩, rfl⟩

  refine ⟨ha, hb, V2Aux.isArchKFinite_of_mem_archCutSubmodule_of_central K
    (fun z => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) tysK (convOp K f v) (fun z g => ?_) hb⟩
  rw [mul_centralScalar_comm]
  exact ((AutomorphicForm.lsXiMemberAt_iff (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) ⊤ ξK
    (AutomorphicForm.canonicalTruncationDomain K α β) _).1 hRauto).1.central_transform ⟨z, Subgroup.mem_top z⟩ g

end

end S_AutomorphicForm_convOp_principalLevel_invariant_and_mem_archCutSubmodule_and_isArchKFinite_of_isAutomorphicFnAt
end P2MW
export P2MW.S_AutomorphicForm_convOp_principalLevel_invariant_and_mem_archCutSubmodule_and_isArchKFinite_of_isAutomorphicFnAt (solution)
