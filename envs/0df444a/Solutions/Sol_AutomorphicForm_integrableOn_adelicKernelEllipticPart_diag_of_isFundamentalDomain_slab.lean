-- Prove2me | solution 1 for AutomorphicForm.integrableOn_adelicKernelEllipticPart_diag_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e87a3a96-dbec-5d62-ac18-25efa719400f

import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import Theorems.Thm_AutomorphicForm_exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_WindowedSiegel_isCompact_centreCutSiegelSet_inter_heightCap
import Theorems.Thm_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrableOn_adelicKernelEllipticPart_diag_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.TateGlobal NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal Pointwise Topology

noncomputable section

namespace R1EllDiag

variable {K : Type} [Field K] [NumberField K]

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem isHaar : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

attribute [local instance] isHaar

theorem coe_centralScalar (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((centralScalar (𝓞 K) K z : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 K) K) := rfl

theorem continuous_centralScalar : Continuous (centralScalar (𝓞 K) K) := by
  have h : Continuous ((Matrix.scalar (Fin 2)).toMonoidHom :
      AdeleRing (𝓞 K) K → Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    show Continuous fun a : AdeleRing (𝓞 K) K => Matrix.scalar (Fin 2) a
    simp_rw [Matrix.scalar_apply]
    exact (continuous_pi fun _ => continuous_id).matrix_diagonal
  exact h.units_map

theorem centralScalar_comm (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    centralScalar (𝓞 K) K z * g = g * centralScalar (𝓞 K) K z := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_centralScalar]
  exact (Matrix.scalar_commute (n := Fin 2) (z : AdeleRing (𝓞 K) K) (fun r' => Commute.all _ r') _).eq

theorem det_globalPoints (γ : GL (Fin 2) K) :
    Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ) =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom (Matrix.GeneralLinearGroup.det γ) := by
  unfold globalPoints
  rw [Matrix.GeneralLinearGroup.map_det]
  rfl

theorem ideleNorm_principal (a : Kˣ) :
    ideleNorm K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom a) = 1 := by
  unfold ideleNorm
  rw [@NumberField.AdeleRing.distribHaarChar_algebraMap K _ _ (adeleBorel (𝓞 K) K)
    (borelSpace_adeleBorel (𝓞 K) K) a]
  simp

theorem ideleNorm_det_globalPoints_mul (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ * g)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, ideleNorm_mul, det_globalPoints, ideleNorm_principal, one_mul]

private theorem _root_.R1EllDiag.continuous_ideleNorm_det :
    Continuous fun g : AdelicGL2 (𝓞 K) K => ideleNorm K (Matrix.GeneralLinearGroup.det g) :=
  NumberField.TateGlobal.continuous_ideleNorm_det K

p2m_export "R1EllDiag" "continuous_ideleNorm_det"
theorem globalPoints_injective : Function.Injective (globalPoints (𝓞 K) K) := by
  intro a b h
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have := congrArg (fun g : AdelicGL2 (𝓞 K) K => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) h
  exact NumberField.AdeleRing.algebraMap_injective (𝓞 K) K this

def slab (K : Type) [Field K] [NumberField K] (α β : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

theorem mem_slab_iff {α β : ℝ} {g : AdelicGL2 (𝓞 K) K} :
    g ∈ slab K α β ↔ ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β := Iff.rfl

theorem measurableSet_slab (α β : ℝ) : MeasurableSet (slab K α β) :=
  measurableSet_preimage continuous_ideleNorm_det.measurable measurableSet_Icc

theorem globalPoints_mul_mem_slab_iff {α β : ℝ} (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) :
    globalPoints (𝓞 K) K γ * g ∈ slab K α β ↔ g ∈ slab K α β := by
  rw [mem_slab_iff, mem_slab_iff, ideleNorm_det_globalPoints_mul]

theorem smulInvariantMeasure_restrict_slab (α β : ℝ) :
    SMulInvariantMeasure (globalPoints (𝓞 K) K).range (AdelicGL2 (𝓞 K) K)
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K α β)) := by
  refine ⟨fun γ A hA => ?_⟩
  obtain ⟨γ, hγ⟩ := γ
  obtain ⟨γ₀, rfl⟩ := hγ
  have hpre : (fun x : AdelicGL2 (𝓞 K) K =>
      (⟨globalPoints (𝓞 K) K γ₀, ⟨γ₀, rfl⟩⟩ : (globalPoints (𝓞 K) K).range) • x) ⁻¹' A =
      (fun x => globalPoints (𝓞 K) K γ₀ * x) ⁻¹' A := rfl
  rw [hpre, Measure.restrict_apply (measurableSet_preimage (measurable_const_mul _) hA),
    Measure.restrict_apply hA]
  have hset : (fun x => globalPoints (𝓞 K) K γ₀ * x) ⁻¹' A ∩ slab K α β =
      (fun x => globalPoints (𝓞 K) K γ₀ * x) ⁻¹' (A ∩ slab K α β) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, globalPoints_mul_mem_slab_iff]
  rw [hset]
  exact measure_preimage_mul _ _ _

theorem conj_mem_ellipticCell_iff (γ δ : GL (Fin 2) K) :
    γ⁻¹ * δ * γ ∈ ellipticCell K ↔ δ ∈ ellipticCell K := by
  rw [mem_ellipticCell_iff, mem_ellipticCell_iff, IsEllipticType, IsEllipticType]
  have : (((γ⁻¹ * δ * γ : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K).charpoly =
      ((δ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly := by
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj' γ _
  rw [this]

theorem bijOn_conj_ellipticCell (γ : GL (Fin 2) K) :
    Set.BijOn (fun δ => γ⁻¹ * δ * γ) (ellipticCell K) (ellipticCell K) := by
  refine ⟨fun δ hδ => (conj_mem_ellipticCell_iff γ δ).mpr hδ, fun δ _ δ' _ h => ?_, fun δ hδ => ?_⟩
  · have := congrArg (fun x => γ * x * γ⁻¹) h
    simpa [mul_assoc] using this
  · refine ⟨γ * δ * γ⁻¹, ?_, by simp [mul_assoc]⟩
    have := (conj_mem_ellipticCell_iff γ⁻¹ δ).mpr hδ
    simpa using this

theorem eval_charpoly_fin_two (M : Matrix (Fin 2) (Fin 2) K) (t : K) :
    (M.charpoly).eval t = t ^ 2 - M.trace * t + M.det := by
  rw [Matrix.charpoly_fin_two]
  simp

theorem not_mem_ellipticCell_of_apply_one_zero_eq_zero {δ : GL (Fin 2) K}
    (h : ((δ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) : δ ∉ ellipticCell K := by
  intro hδ
  rw [mem_ellipticCell_iff] at hδ
  refine hδ (((δ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0) ?_
  rw [Polynomial.IsRoot, eval_charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, h]
  ring

def cellSum (𝒞 : Set (GL (Fin 2) K)) {E : Type*} [AddCommMonoid E] (h : AdelicGL2 (𝓞 K) K → E)
    (x y : AdelicGL2 (𝓞 K) K) : E :=
  ∑ᶠ γ ∈ 𝒞, h (x⁻¹ * globalPoints (𝓞 K) K γ * y)

theorem adelicKernelEllipticPart_eq_cellSum {E : Type*} [AddCommMonoid E] (h : AdelicGL2 (𝓞 K) K → E)
    (x y : AdelicGL2 (𝓞 K) K) : adelicKernelEllipticPart K h x y = cellSum (ellipticCell K) h x y := rfl

theorem finite_conj_mem {C : Set (AdelicGL2 (𝓞 K) K)} (hC : IsCompact C) (x y : AdelicGL2 (𝓞 K) K) :
    {γ : GL (Fin 2) K | x⁻¹ * globalPoints (𝓞 K) K γ * y ∈ C}.Finite :=
  AutomorphicForm.adelicKernelLocalFiniteness K C hC x y

theorem finite_conj_mem_of_isCompact {N : Set (AdelicGL2 (𝓞 K) K)} (hN : IsCompact N)
    {C : Set (AdelicGL2 (𝓞 K) K)} (hC : IsCompact C) :
    {γ : GL (Fin 2) K | ∃ x ∈ N, x⁻¹ * globalPoints (𝓞 K) K γ * x ∈ C}.Finite := by
  set φ : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K :=
    fun p => p.1 * p.2 * p.1⁻¹ with hφ
  have hφc : Continuous φ := (continuous_fst.mul continuous_snd).mul continuous_fst.inv
  have hC' : IsCompact (φ '' (N ×ˢ C)) := (hN.prod hC).image hφc
  refine (finite_conj_mem hC' 1 1).subset ?_
  rintro γ ⟨x, hx, hmem⟩
  simp only [Set.mem_setOf_eq, inv_one, one_mul, mul_one]
  refine ⟨(x, x⁻¹ * globalPoints (𝓞 K) K γ * x), ⟨hx, hmem⟩, ?_⟩
  simp only [hφ]
  group

theorem cellSum_eq_sum {𝒞 : Set (GL (Fin 2) K)} {E : Type*} [AddCommMonoid E]
    (h : AdelicGL2 (𝓞 K) K → E) (x y : AdelicGL2 (𝓞 K) K) {T : Finset (GL (Fin 2) K)}
    (hT : (T : Set (GL (Fin 2) K)) ⊆ 𝒞)
    (hsupp : ∀ γ ∈ 𝒞, h (x⁻¹ * globalPoints (𝓞 K) K γ * y) ≠ 0 → γ ∈ T) :
    cellSum 𝒞 h x y = ∑ γ ∈ T, h (x⁻¹ * globalPoints (𝓞 K) K γ * y) := by
  unfold cellSum
  refine finsum_mem_eq_sum_of_subset _ ?_ hT
  rintro γ ⟨hγ, hne⟩
  exact hsupp γ hγ hne

theorem continuous_cellSum_diag (𝒞 : Set (GL (Fin 2) K)) {E : Type*} [AddCommMonoid E]
    [TopologicalSpace E] [ContinuousAdd E] (h : AdelicGL2 (𝓞 K) K → E) (hh : Continuous h)
    (hhc : HasCompactSupport h) :
    Continuous fun x : AdelicGL2 (𝓞 K) K => cellSum 𝒞 h x x := by
  classical
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨N, hN, hNx⟩ := exists_compact_mem_nhds x₀
  have hfin := finite_conj_mem_of_isCompact hN hhc.isCompact
  set T : Finset (GL (Fin 2) K) := hfin.toFinset.filter (· ∈ 𝒞) with hTdef
  have hT : (T : Set (GL (Fin 2) K)) ⊆ 𝒞 := by
    intro γ hγ
    rw [hTdef, Finset.coe_filter] at hγ
    exact hγ.2
  have heq : Set.EqOn
      (fun x : AdelicGL2 (𝓞 K) K => ∑ γ ∈ T, h (x⁻¹ * globalPoints (𝓞 K) K γ * x))
      (fun x => cellSum 𝒞 h x x) N := by
    intro x hx
    refine (cellSum_eq_sum h x x hT fun γ hγ hne => ?_).symm
    rw [hTdef, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨x, hx, subset_tsupport _ hne⟩, hγ⟩
  have hcont : Continuous fun x : AdelicGL2 (𝓞 K) K =>
      ∑ γ ∈ T, h (x⁻¹ * globalPoints (𝓞 K) K γ * x) := by
    refine continuous_finsetSum _ fun γ _ => hh.comp ?_
    exact (continuous_id.inv.mul continuous_const).mul continuous_id
  exact hcont.continuousAt.congr_of_eventuallyEq ((Filter.eventuallyEq_of_mem hNx heq).symm)

theorem cellSum_ellipticCell_globalPoints_mul {E : Type*} [AddCommMonoid E] (h : AdelicGL2 (𝓞 K) K → E)
    (γ : GL (Fin 2) K) (x : AdelicGL2 (𝓞 K) K) :
    cellSum (ellipticCell K) h (globalPoints (𝓞 K) K γ * x) (globalPoints (𝓞 K) K γ * x) =
      cellSum (ellipticCell K) h x x := by
  unfold cellSum
  refine finsum_mem_eq_of_bijOn (fun δ => γ⁻¹ * δ * γ) (bijOn_conj_ellipticCell γ) fun δ _ => ?_
  simp only [map_mul, map_inv, mul_inv_rev]
  congr 1
  simp only [mul_assoc]

theorem cellSum_mul_centralScalar (𝒞 : Set (GL (Fin 2) K)) {E : Type*} [AddCommMonoid E]
    (h : AdelicGL2 (𝓞 K) K → E) (x : AdelicGL2 (𝓞 K) K) (z : (AdeleRing (𝓞 K) K)ˣ) :
    cellSum 𝒞 h (x * centralScalar (𝓞 K) K z) (x * centralScalar (𝓞 K) K z) = cellSum 𝒞 h x x := by
  unfold cellSum
  refine finsum_mem_congr rfl fun δ _ => ?_
  congr 1
  calc (x * centralScalar (𝓞 K) K z)⁻¹ * globalPoints (𝓞 K) K δ * (x * centralScalar (𝓞 K) K z)
      = (centralScalar (𝓞 K) K z)⁻¹ * (x⁻¹ * globalPoints (𝓞 K) K δ * x) * centralScalar (𝓞 K) K z := by
        group
    _ = (centralScalar (𝓞 K) K z)⁻¹ * (centralScalar (𝓞 K) K z * (x⁻¹ * globalPoints (𝓞 K) K δ * x)) := by
        rw [centralScalar_comm z (x⁻¹ * globalPoints (𝓞 K) K δ * x), mul_assoc]
    _ = x⁻¹ * globalPoints (𝓞 K) K δ * x := inv_mul_cancel_left _ _

theorem cellSum_mul_right (𝒞 : Set (GL (Fin 2) K)) {E : Type*} [AddCommMonoid E]
    (h : AdelicGL2 (𝓞 K) K → E) (x t : AdelicGL2 (𝓞 K) K) :
    cellSum 𝒞 h (x * t) (x * t) = cellSum 𝒞 (fun k => h (t⁻¹ * k * t)) x x := by
  unfold cellSum
  refine finsum_mem_congr rfl fun δ _ => ?_
  congr 1
  simp only [mul_inv_rev, mul_assoc]

theorem norm_cellSum_le (𝒞 : Set (GL (Fin 2) K)) {f : AdelicGL2 (𝓞 K) K → ℂ}
    (hfc : HasCompactSupport f) (x : AdelicGL2 (𝓞 K) K) :
    ‖cellSum 𝒞 f x x‖ ≤ cellSum 𝒞 (fun g => ‖f g‖) x x := by
  classical
  have hT₁ := finite_conj_mem hfc.isCompact x x
  set T : Finset (GL (Fin 2) K) := hT₁.toFinset.filter (· ∈ 𝒞) with hTdef
  have hT : (T : Set (GL (Fin 2) K)) ⊆ 𝒞 := by
    intro γ hγ; rw [hTdef, Finset.coe_filter] at hγ; exact hγ.2
  rw [cellSum_eq_sum f x x hT, cellSum_eq_sum (fun g => ‖f g‖) x x hT]
  · exact norm_sum_le _ _
  · intro γ hγ hne
    rw [hTdef, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨subset_tsupport _ (norm_ne_zero_iff.mp hne), hγ⟩
  · intro γ hγ hne
    rw [hTdef, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨subset_tsupport _ hne, hγ⟩

theorem cellSum_norm_nonneg (𝒞 : Set (GL (Fin 2) K)) (f : AdelicGL2 (𝓞 K) K → ℂ) (x : AdelicGL2 (𝓞 K) K) :
    0 ≤ cellSum 𝒞 (fun g => ‖f g‖) x x :=
  finsum_nonneg fun _ => finsum_nonneg fun _ => norm_nonneg _

theorem localHeight_le_of_archHeight_le {c T₀ : ℝ} (hc : 0 < c) (g : GL (Fin 2) (InfiniteAdeleRing K))
    (hfloor : ∀ w : InfinitePlace K, c ≤ localHeight (archComponent K w g))
    (hT : archHeight K g ≤ T₀) (w₀ : InfinitePlace K) :
    localHeight (archComponent K w₀ g) ≤
      max 1 (max T₀ 1 / (min c 1) ^ (∑ w : InfinitePlace K, w.mult)) := by
  set m : ℝ := min c 1 with hm
  set N : ℕ := ∑ w : InfinitePlace K, w.mult with hN
  have hm0 : 0 < m := lt_min hc one_pos
  have hm1 : m ≤ 1 := min_le_right _ _
  set L := localHeight (archComponent K w₀ g) with hL
  by_contra hlt
  push Not at hlt
  have hL1 : 1 < L := lt_of_le_of_lt (le_max_left _ _) hlt
  have hL2 : max T₀ 1 / m ^ N < L := lt_of_le_of_lt (le_max_right _ _) hlt

  have hfac : ∀ w, m ^ w.mult ≤ localHeight (archComponent K w g) ^ w.mult := fun w =>
    pow_le_pow_left₀ hm0.le ((min_le_left _ _).trans (hfloor w)) _
  have hprod : L * m ^ N ≤ archHeight K g := by
    classical
    unfold archHeight
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₀)]
    have h1 : L ≤ localHeight (archComponent K w₀ g) ^ w₀.mult := by
      rw [← hL]
      have := InfinitePlace.mult_pos (w := w₀)
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ w₀.mult := pow_le_pow_right₀ hL1.le this
    have h2 : m ^ N ≤ ∏ w ∈ Finset.univ.erase w₀, localHeight (archComponent K w g) ^ w.mult := by
      calc m ^ N ≤ m ^ (∑ w ∈ Finset.univ.erase w₀, w.mult) := by
            refine pow_le_pow_of_le_one hm0.le hm1 ?_
            rw [hN]
            exact Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
        _ = ∏ w ∈ Finset.univ.erase w₀, m ^ w.mult := (Finset.prod_pow_eq_pow_sum _ _ _).symm
        _ ≤ ∏ w ∈ Finset.univ.erase w₀, localHeight (archComponent K w g) ^ w.mult :=
            Finset.prod_le_prod (fun w _ => pow_nonneg hm0.le _) fun w _ => hfac w
    exact mul_le_mul h1 h2 (pow_nonneg hm0.le _) (pow_nonneg (localHeight_pos _).le _)
  have hmN : 0 < m ^ N := pow_pos hm0 N
  have : max T₀ 1 < L * m ^ N := by rwa [div_lt_iff₀ hmN] at hL2
  linarith [le_max_left T₀ 1]

theorem countable_numberField : Countable K :=
  (Module.Free.chooseBasis ℚ K).equivFun.toEquiv.countable_iff.2 inferInstance

theorem countable_gl2 : Countable (GL (Fin 2) K) := by
  haveI := countable_numberField (K := K)
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  exact Function.Injective.countable (f := (Units.val : GL (Fin 2) K → _)) Units.val_injective

theorem countable_range_globalPoints : Countable (globalPoints (𝓞 K) K).range := by
  haveI := countable_gl2 (K := K)
  exact Function.Surjective.countable (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 K) K))

theorem main (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K α β)))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    IntegrableOn (fun x => cellSum (ellipticCell K) f x x) Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K α β)) := by
  classical
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ

  obtain ⟨T, c, hc, u, hcov⟩ :=
    AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet K
  have hcov12 := hcov 1 2 two_pos (by norm_num)
  obtain ⟨Zf, hZf⟩ :=
    AutomorphicForm.exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc
      K c u 1 2 T one_pos (by norm_num) hcov12 α β hα hαβ.le

  set h : AdelicGL2 (𝓞 K) K → ℝ := fun g => ‖f g‖ with hhdef
  have hh : Continuous h := hf.norm
  have hhc : HasCompactSupport h := hfc.norm
  set E : AdelicGL2 (𝓞 K) K → ℝ := fun x => cellSum (ellipticCell K) h x x with hEdef
  have hEc : Continuous E := continuous_cellSum_diag _ h hh hhc

  set C : Set (AdelicGL2 (𝓞 K) K) := ⋃ t ∈ T, (fun k => t * k * t⁻¹) '' tsupport h with hCdef
  have hCc : IsCompact C :=
    T.finite_toSet.isCompact_biUnion fun t _ =>
      hhc.isCompact.image ((continuous_const.mul continuous_id).mul continuous_const)
  obtain ⟨T₀, hT₀⟩ :=
    AutomorphicForm.WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem K hCc

  have hvan : ∀ s ∈ centreCutSiegelSet K c u 1 2, ∀ t ∈ T,
      T₀ < archHeight K (glArch (𝓞 K) K s) → E (s * t) = 0 := by
    intro s hs t ht hhigh
    show cellSum (ellipticCell K) h (s * t) (s * t) = 0
    rw [cellSum_mul_right]
    unfold cellSum
    refine finsum_mem_eq_zero_of_forall_eq_zero fun δ hδ => ?_
    by_contra hne
    have hmem : s⁻¹ * globalPoints (𝓞 K) K δ * s ∈ C := by
      have hts : t⁻¹ * (s⁻¹ * globalPoints (𝓞 K) K δ * s) * t ∈ tsupport h := subset_tsupport _ hne
      refine Set.mem_iUnion₂.mpr ⟨t, ht, ⟨_, hts, ?_⟩⟩
      show t * (t⁻¹ * (s⁻¹ * globalPoints (𝓞 K) K δ * s) * t) * t⁻¹ = _
      group
    have hint : glFin (𝓞 K) K s ∈ finiteIntegralGL2 (𝓞 K) K := (mem_centreCutSiegelSet_iff.mp hs).1
    exact not_mem_ellipticCell_of_apply_one_zero_eq_zero (hT₀ s s hint hint hhigh hhigh δ hmem) hδ

  set C₁ : ℝ := max 1 (max T₀ 1 / (min c 1) ^ (∑ w : InfinitePlace K, w.mult)) with hC₁
  set Q₁ : Set (AdelicGL2 (𝓞 K) K) := centreCutSiegelSet K c u 1 2 ∩
    {g | ∀ w : InfinitePlace K, localHeight (archComponent K w (glArch (𝓞 K) K g)) ≤ C₁} with hQ₁def
  have hQ₁ : IsCompact Q₁ :=
    AutomorphicForm.WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap K hc one_pos
  set ψ : (AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ → AdelicGL2 (𝓞 K) K :=
    fun p => p.1.1 * p.1.2 * (centralScalar (𝓞 K) K p.2)⁻¹ with hψdef
  have hψ : Continuous ψ :=
    ((continuous_fst.comp continuous_fst).mul (continuous_snd.comp continuous_fst)).mul
      (continuous_centralScalar.comp continuous_snd).inv
  set Q : Set (AdelicGL2 (𝓞 K) K) :=
    ψ '' ((Q₁ ×ˢ (T : Set (AdelicGL2 (𝓞 K) K))) ×ˢ (Zf : Set (AdeleRing (𝓞 K) K)ˣ)) with hQdef
  have hQ : IsCompact Q :=
    ((hQ₁.prod T.finite_toSet.isCompact).prod Zf.finite_toSet.isCompact).image hψ

  have hkey : ∀ x ∈ slab K α β, E x ≠ 0 →
      ∃ γ : GL (Fin 2) K, globalPoints (𝓞 K) K γ * x ∈ Q ∧ E x = E (globalPoints (𝓞 K) K γ * x) := by
    intro x hx hEx
    obtain ⟨γ, z, hz, hmem⟩ := hZf x hx
    obtain ⟨t, ht, s, hs, hst⟩ : ∃ t ∈ T, ∃ s ∈ centreCutSiegelSet K c u 1 2,
        s * t = globalPoints (𝓞 K) K γ * x * centralScalar (𝓞 K) K z := by
      simpa only [Set.mem_iUnion, Set.mem_image, exists_prop] using hmem
    have hEeq : E x = E (s * t) := by
      show cellSum (ellipticCell K) h x x = cellSum (ellipticCell K) h (s * t) (s * t)
      rw [hst, cellSum_mul_centralScalar, cellSum_ellipticCell_globalPoints_mul]
    have hlow : archHeight K (glArch (𝓞 K) K s) ≤ T₀ := by
      by_contra hgt
      push Not at hgt
      exact hEx (hEeq.trans (hvan s hs t ht hgt))
    have hsQ₁ : s ∈ Q₁ :=
      ⟨hs, fun w => localHeight_le_of_archHeight_le hc _ (mem_centreCutSiegelSet_iff.mp hs).2.1 hlow w⟩
    refine ⟨γ, ⟨((s, t), z), ⟨⟨hsQ₁, ht⟩, hz⟩, ?_⟩, (cellSum_ellipticCell_globalPoints_mul h γ x).symm⟩
    show s * t * (centralScalar (𝓞 K) K z)⁻¹ = globalPoints (𝓞 K) K γ * x
    rw [hst, mul_inv_cancel_right]

  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ q ∈ Q, E q ≤ M :=
    ⟨sSup (E '' Q), fun q hq => le_csSup (hQ.bddAbove_image hEc.continuousOn) (Set.mem_image_of_mem _ hq)⟩
  haveI : Countable (GL (Fin 2) K) := countable_gl2
  set W : Set (AdelicGL2 (𝓞 K) K) := ⋃ γ : GL (Fin 2) K, (fun x => globalPoints (𝓞 K) K γ * x) ⁻¹' Q
    with hWdef
  have hWm : MeasurableSet W :=
    MeasurableSet.iUnion fun γ => measurableSet_preimage (measurable_const_mul _) hQ.isClosed.measurableSet
  have hbound : ∀ x ∈ slab K α β,
      ‖cellSum (ellipticCell K) f x x‖ₑ ≤ ENNReal.ofReal M * W.indicator 1 x := by
    intro x hx
    rw [← ofReal_norm]
    have hle : ‖cellSum (ellipticCell K) f x x‖ ≤ E x := norm_cellSum_le _ hfc x
    by_cases hEx : E x = 0
    · rw [hEx] at hle
      rw [le_antisymm hle (norm_nonneg _), ENNReal.ofReal_zero]
      exact zero_le
    · obtain ⟨γ, hγQ, hEeq⟩ := hkey x hx hEx
      have hxW : x ∈ W := Set.mem_iUnion.mpr ⟨γ, hγQ⟩
      rw [Set.indicator_of_mem hxW, Pi.one_apply, mul_one]
      exact ENNReal.ofReal_le_ofReal (hle.trans (hEeq ▸ hM _ hγQ))

  haveI := smulInvariantMeasure_restrict_slab (K := K) α β
  haveI : Countable (globalPoints (𝓞 K) K).range := countable_range_globalPoints
  have hΦW : (μ.restrict (slab K α β)) (W ∩ Φ) ≤ μ Q := by
    calc (μ.restrict (slab K α β)) (W ∩ Φ)
        ≤ (μ.restrict (slab K α β)) (⋃ g : (globalPoints (𝓞 K) K).range, g • Q ∩ Φ) := by
          refine measure_mono fun x hx => ?_
          obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp hx.1
          refine Set.mem_iUnion.mpr ⟨⟨globalPoints (𝓞 K) K γ, ⟨γ, rfl⟩⟩⁻¹, ?_, hx.2⟩
          refine Set.mem_smul_set.mpr ⟨globalPoints (𝓞 K) K γ * x, hγ, ?_⟩
          show (globalPoints (𝓞 K) K γ)⁻¹ * (globalPoints (𝓞 K) K γ * x) = x
          rw [inv_mul_cancel_left]
      _ ≤ ∑' g : (globalPoints (𝓞 K) K).range, (μ.restrict (slab K α β)) (g • Q ∩ Φ) :=
          measure_iUnion_le _
      _ = (μ.restrict (slab K α β)) Q := (hΦ.measure_eq_tsum Q).symm
      _ ≤ μ Q := Measure.le_iff'.1 Measure.restrict_le_self Q

  refine ⟨(continuous_cellSum_diag _ f hf hfc).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hae : ∀ᵐ x ∂((μ.restrict (slab K α β)).restrict Φ),
      ‖cellSum (ellipticCell K) f x x‖ₑ ≤ ENNReal.ofReal M * W.indicator 1 x := by
    have : ∀ᵐ x ∂((μ.restrict (slab K α β)).restrict Φ), x ∈ slab K α β :=
      ae_restrict_of_ae (ae_restrict_mem (measurableSet_slab α β))
    exact this.mono fun x hx => hbound x hx
  calc ∫⁻ x, ‖cellSum (ellipticCell K) f x x‖ₑ ∂((μ.restrict (slab K α β)).restrict Φ)
      ≤ ∫⁻ x, ENNReal.ofReal M * W.indicator 1 x ∂((μ.restrict (slab K α β)).restrict Φ) :=
        lintegral_mono_ae hae
    _ = ENNReal.ofReal M * ((μ.restrict (slab K α β)).restrict Φ) W := by
        rw [lintegral_const_mul _ (measurable_one.indicator hWm), lintegral_indicator_one hWm]
    _ = ENNReal.ofReal M * (μ.restrict (slab K α β)) (W ∩ Φ) := by rw [Measure.restrict_apply hWm]
    _ ≤ ENNReal.ofReal M * μ Q := by gcongr
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hQ.measure_lt_top

end R1EllDiag

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    IntegrableOn (fun x => AutomorphicForm.adelicKernelEllipticPart K f x x) Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) :=
  R1EllDiag.main α β hα hαβ Φ hΦ f hf hfc

end
end S_AutomorphicForm_integrableOn_adelicKernelEllipticPart_diag_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_integrableOn_adelicKernelEllipticPart_diag_of_isFundamentalDomain_slab (solution)
