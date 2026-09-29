-- Prove2me | solution 1 for AutomorphicForm.exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_chiDet_mul_chiDet_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b4aa643e-9901-5561-95cc-cbe5e4eb3dcc

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_TruncationOperator
import Theorems.Thm_AutomorphicForm_integral_mul_chiDet_eq_prod_pow_mul_pow_mul_integral_mul_chiDet_of_isUnitFactorization
import Theorems.Thm_AutomorphicForm_finite_setOf_squaresToXi_continuous_apply_det_eq_one_of_mem_principalLevel
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_IdeleBox
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_chiDet_mul_chiDet_inv
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel
open AutomorphicForm
open scoped ENNReal NNReal

set_option maxHeartbeats 1600000

noncomputable section

namespace ResBlock

variable (K : Type) [Field K] [NumberField K]

theorem det_unipotentGL2 (t : AdeleRing (𝓞 K) K) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 t : AdelicGL2 (𝓞 K) K) = 1 := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]

theorem chiDet_unipotentGL2_mul (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (t : AdeleRing (𝓞 K) K)
    (y : AdelicGL2 (𝓞 K) K) :
    chiDet (𝓞 K) K χ (unipotentGL2 t * y) = chiDet (𝓞 K) K χ y := by
  simp only [chiDet, map_mul, det_unipotentGL2, one_mul]

theorem lambdaT_eq_indicator_of_forall_unipotentGL2_mul
    (Dc : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (F : AdelicGL2 (𝓞 K) K → ℂ) (hF : ∀ (t : AdeleRing (𝓞 K) K) (y : AdelicGL2 (𝓞 K) K), F (unipotentGL2 t * y) = F y)
    (H : AdelicGL2 (𝓞 K) K → ℝ) (T : ℝ) (y : AdelicGL2 (𝓞 K) K) :
    @lambdaT _ (productionPinsOf K Dc U gen (adelicBox K)).nS _ _ (productionPinsOf K Dc U gen (adelicBox K)).ν
        (fun t => unipotentGL2 t) H T F y = {y' | H y' ≤ T}.indicator F y := by
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := (productionPinsOf K Dc U gen (adelicBox K)).nS
  haveI : IsProbabilityMeasure (productionPinsOf K Dc U gen (adelicBox K)).ν :=
    isProbabilityMeasure_cond_adelicBox K
  have hct : constantTerm (productionPinsOf K Dc U gen (adelicBox K)).ν (fun t => unipotentGL2 t) F y = F y := by
    simp only [constantTerm, constantTermIntegrand, hF, integral_const, probReal_univ, one_smul]
  simp only [lambdaT, Set.indicator_apply, Set.mem_setOf_eq, highSet, hct]
  by_cases h : H y ≤ T
  · rw [if_pos h, if_neg (not_lt.mpr h), sub_zero]
  · rw [if_neg h, if_pos (not_le.mp h), sub_self]

open NumberField.AdelicLevel in
theorem adelicGLHaar_canonicalTruncationDomain_lt_top {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    adelicGLHaar (Fin 2) (𝓞 K) K (canonicalTruncationDomain K α β) < ⊤ := by
  obtain ⟨-, -, -, hsub, hFD⟩ := canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have h := adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ _ hFD
  rwa [Set.inter_eq_left.mpr hsub] at h

theorem continuous_ideleNorm_det :
    Continuous fun g : AdelicGL2 (𝓞 K) K => NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) := by
  refine (NumberField.TateGlobal.continuous_ideleNorm K).comp ?_
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_id.matrix_det).comp Units.continuous_val
  · have heq : (fun g : AdelicGL2 (𝓞 K) K =>
        (((Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) =
        fun g => ((g⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det := by
      funext g; rw [← map_inv]; rfl
    show Continuous fun g : AdelicGL2 (𝓞 K) K =>
        (((Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
    rw [heq]
    exact (continuous_id.matrix_det).comp Units.continuous_coe_inv

open NumberField.AdelicLevel in
theorem adelicGLHaar_canonicalTruncationDomain_ne_zero {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    adelicGLHaar (Fin 2) (𝓞 K) K (canonicalTruncationDomain K α β) ≠ 0 := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  obtain ⟨-, -, -, hsub, hFD⟩ := canonicalTruncationData_isTruncationDatum K α β hα hαβ
  set slab : Set (AdelicGL2 (𝓞 K) K) :=
    {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} with hslab
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  intro h0

  have hpos : 0 < μ slab := by
    obtain ⟨s, -, hs, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq K
    have hr : (0 : ℝ) < (α + β) / 2 := by linarith
    set r : ℝ≥0ˣ := Units.mk0 ⟨(α + β) / 2, hr.le⟩ (by
      intro h; have := Subtype.ext_iff.mp h; change (α + β) / 2 = 0 at this; linarith) with hrdef
    have hrval : (((r : ℝ≥0ˣ) : ℝ≥0) : ℝ) = (α + β) / 2 := rfl
    have hopen : IsOpen {g : AdelicGL2 (𝓞 K) K |
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo α β} :=
      isOpen_Ioo.preimage (continuous_ideleNorm_det K)
    have hne : (diagOne (s r) : AdelicGL2 (𝓞 K) K) ∈ {g : AdelicGL2 (𝓞 K) K |
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo α β} := by
      have hdet : Matrix.GeneralLinearGroup.det (diagOne (s r) : AdelicGL2 (𝓞 K) K) = s r := by
        apply Units.ext
        simp [diagOne, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.diagonal]
      simp only [Set.mem_setOf_eq, hdet, hs r, hrval, Set.mem_Ioo]
      constructor <;> linarith
    have h1 : 0 < μ {g : AdelicGL2 (𝓞 K) K |
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo α β} :=
      hopen.measure_pos μ ⟨_, hne⟩
    exact h1.trans_le (measure_mono fun g hg => ⟨hg.1.le, hg.2.le⟩)

  haveI : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) K) := Units.val_injective.countable
  haveI : Countable (globalPoints (𝓞 K) K).range := (Set.countable_range _).to_subtype
  haveI : MeasurableConstSMul (globalPoints (𝓞 K) K).range (AdelicGL2 (𝓞 K) K) :=
    ⟨fun c => measurable_const_mul (c : AdelicGL2 (𝓞 K) K)⟩
  have hslab_inv : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      globalPoints (𝓞 K) K γ * g ∈ slab ↔ g ∈ slab := by
    intro γ g
    simp only [hslab, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
      ideleNorm_det_globalPoints, one_mul]
  haveI : SMulInvariantMeasure (globalPoints (𝓞 K) K).range (AdelicGL2 (𝓞 K) K) (μ.restrict slab) := by
    refine ⟨fun c t ht => ?_⟩
    obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp c.2
    have hpre : (fun x => c • x) ⁻¹' t ∩ slab = (fun x => (c : AdelicGL2 (𝓞 K) K) * x) ⁻¹' (t ∩ slab) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Subgroup.smul_def, smul_eq_mul]
      rw [← hγ, hslab_inv γ x]
    rw [Measure.restrict_apply ht, Measure.restrict_apply (measurable_const_smul c ht), hpre,
      measure_preimage_mul]
  have hslab_meas : MeasurableSet slab :=
    (isClosed_Icc.preimage (continuous_ideleNorm_det K)).measurableSet
  have hΦ0' : μ.restrict slab (canonicalTruncationDomain K α β) = 0 := by
    rw [Measure.restrict_apply' hslab_meas]
    exact measure_mono_null Set.inter_subset_left h0
  have hcover := hFD.measure_eq_tsum (Set.univ : Set (AdelicGL2 (𝓞 K) K))
  have huniv : μ.restrict slab Set.univ = 0 := by
    rw [hcover]
    simp [Set.smul_set_univ, hΦ0']
  rw [Measure.restrict_apply_univ] at huniv
  exact hpos.ne' huniv

theorem measurableSet_heightLE (R : ℝ) :
    MeasurableSet {y' : AdelicGL2 (𝓞 K) K | NumberField.AdelicHeight.adelicHeight K y' ≤ Real.exp R} := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 K) K
  exact (isClosed_le (NumberField.AdelicHeight.continuous_adelicHeight K) continuous_const).measurableSet

theorem integrableOn_indicator_heightLE_const {α β : ℝ} (hα : 0 < α) (hαβ : α < β) (D : ℂ) (R : ℝ) :
    IntegrableOn (fun x => {y' : AdelicGL2 (𝓞 K) K | NumberField.AdelicHeight.adelicHeight K y' ≤ Real.exp R}.indicator
        (fun _ => D) x) (canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  have hfin := (adelicGLHaar_canonicalTruncationDomain_lt_top K hα hαβ).ne
  have hc : IntegrableOn (fun _ : AdelicGL2 (𝓞 K) K => D) (canonicalTruncationDomain K α β)
      (adelicGLHaar (Fin 2) (𝓞 K) K) := integrableOn_const hfin
  exact hc.indicator (measurableSet_heightLE K R)

theorem setIntegral_indicator_heightLE_const {α β : ℝ} (D : ℂ) (R : ℝ) :
    ∫ x in canonicalTruncationDomain K α β,
        {y' : AdelicGL2 (𝓞 K) K | NumberField.AdelicHeight.adelicHeight K y' ≤ Real.exp R}.indicator (fun _ => D) x
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ((adelicGLHaar (Fin 2) (𝓞 K) K (canonicalTruncationDomain K α β ∩
          {y' : AdelicGL2 (𝓞 K) K | NumberField.AdelicHeight.adelicHeight K y' ≤ Real.exp R})).toReal : ℂ) * D := by
  rw [setIntegral_indicator (measurableSet_heightLE K R), setIntegral_const, Complex.real_smul,
    measureReal_def]

theorem tendsto_setIntegral_indicator_heightLE_const {α β : ℝ} (hα : 0 < α) (hαβ : α < β) (D : ℂ) :
    Filter.Tendsto (fun R : ℝ => ∫ x in canonicalTruncationDomain K α β,
        {y' : AdelicGL2 (𝓞 K) K | NumberField.AdelicHeight.adelicHeight K y' ≤ Real.exp R}.indicator (fun _ => D) x
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
      Filter.atTop (nhds (((adelicGLHaar (Fin 2) (𝓞 K) K (canonicalTruncationDomain K α β)).toReal : ℂ) * D)) := by
  simp_rw [setIntegral_indicator_heightLE_const]
  refine Filter.Tendsto.mul_const D ?_
  refine ((Complex.continuous_ofReal.tendsto _).comp ?_)
  refine (ENNReal.tendsto_toReal (adelicGLHaar_canonicalTruncationDomain_lt_top K hα hαβ).ne).comp ?_
  have hmono : Monotone fun R : ℝ => canonicalTruncationDomain K α β ∩
      {y' : AdelicGL2 (𝓞 K) K | NumberField.AdelicHeight.adelicHeight K y' ≤ Real.exp R} := by
    intro a b hab
    exact Set.inter_subset_inter_right _ fun y hy => le_trans hy (Real.exp_le_exp.mpr hab)
  have hU : (⋃ R : ℝ, canonicalTruncationDomain K α β ∩
      {y' : AdelicGL2 (𝓞 K) K | NumberField.AdelicHeight.adelicHeight K y' ≤ Real.exp R}) =
      canonicalTruncationDomain K α β := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨R, hy, -⟩; exact hy
    · intro hy
      refine ⟨NumberField.AdelicHeight.adelicHeight K y, hy, ?_⟩
      have := Real.add_one_le_exp (NumberField.AdelicHeight.adelicHeight K y)
      linarith
  have h := tendsto_measure_iUnion_atTop (μ := adelicGLHaar (Fin 2) (𝓞 K) K) hmono
  rwa [hU] at h

theorem integral_mul_chiDet_eq_zero_of_apply_det_ne_one
    (U : Subgroup (AdelicGL2 (𝓞 K) K)) (f : AdelicGL2 (𝓞 K) K → ℂ) (hbi : IsBiInvariantUnder K U f)
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (u : AdelicGL2 (𝓞 K) K) (hu : u ∈ U)
    (hχu : χ (Matrix.GeneralLinearGroup.det u) ≠ 1) :
    ∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  set I : ℂ := ∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hI
  have h : I = ((χ (Matrix.GeneralLinearGroup.det u) : ℂˣ) : ℂ) * I := by
    conv_lhs => rw [hI, ← integral_mul_left_eq_self (fun g => f g * chiDet (𝓞 K) K χ g) u]
    rw [hI, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [chiDet, map_mul, Units.val_mul, (hbi u hu g).1]
    ring
  have hne : ((χ (Matrix.GeneralLinearGroup.det u) : ℂˣ) : ℂ) ≠ 1 := fun h1 =>
    hχu (Units.ext (by simpa using h1))
  have : (1 - ((χ (Matrix.GeneralLinearGroup.det u) : ℂˣ) : ℂ)) * I = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hne
  · rw [hI] at h0; exact h0

open NumberField.AdelicLevel in

theorem isLevelOneMatrix_weyl_conj_heckeGenAt (N : Ideal (𝓞 K)) (hN0 : N ≠ ⊥) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ v.asIdeal ∣ N) (s : (v.adicCompletion K)ˣ) (hs : Valued.v (s : v.adicCompletion K) = 1) :
    IsLevelOneMatrix (𝓞 K) K N
      (glFin (𝓞 K) K ((weyl (𝓞 K) K)⁻¹ * heckeGenAt (𝓞 K) K v s * weyl (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := by
  classical

  have hint : ((localUnit (𝓞 K) K v s : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K)
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    intro w
    by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self, HeightOneSpectrum.mem_adicCompletionIntegers, hs]
    · rw [localUnit_apply_of_ne (𝓞 K) K v s hw]; exact one_mem _

  have hent : ∀ i j : Fin 2,
      (glFin (𝓞 K) K ((weyl (𝓞 K) K)⁻¹ * heckeGenAt (𝓞 K) K v s * weyl (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j =
      !![(1 : FiniteAdeleRing (𝓞 K) K), 0; 0,
        ((localUnit (𝓞 K) K v s : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K)] i j := by
    intro i j
    rw [glFin_apply]
    simp only [Units.val_mul]
    have hwinv : (((weyl (𝓞 K) K)⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
        = !![0, 1; 1, 0] := rfl
    have hw : ((weyl (𝓞 K) K : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
        = !![0, 1; 1, 0] := rfl
    have hh : ((heckeGenAt (𝓞 K) K v s : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
        = !![((Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v s) : (AdeleRing (𝓞 K) K)ˣ) :
            AdeleRing (𝓞 K) K), 0; 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    have h2 : (((Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v s) : (AdeleRing (𝓞 K) K)ˣ) :
            AdeleRing (𝓞 K) K)).2 = ((localUnit (𝓞 K) K v s : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) := rfl
    have h02 : (0 : AdeleRing (𝓞 K) K).2 = 0 := rfl
    have h12 : (1 : AdeleRing (𝓞 K) K).2 = 1 := rfl
    rw [hwinv, hw, hh, Matrix.mul_fin_two, Matrix.mul_fin_two]
    have h2' : ((finIncl (𝓞 K) K) ((localUnit (𝓞 K) K v s : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K)).2
        = ((localUnit (𝓞 K) K v s : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) := rfl
    fin_cases i <;> fin_cases j <;>
      simp [h2, h2', h02, h12, Prod.snd_add, Prod.snd_mul]
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
  · rw [hent]
    fin_cases i <;> fin_cases j
    · exact one_mem_integralFiniteAdeles
    · exact zero_mem_integralFiniteAdeles
    · exact zero_mem_integralFiniteAdeles
    · exact hint
  · rw [hent]
    exact zero_mem_idealBall N
  · rw [hent]
    show ((localUnit (𝓞 K) K v s : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) - 1 ∈ idealBall (𝓞 K) K N
    intro w
    rw [coe_sub_apply, coe_one_apply]
    by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self, idealBound_eq_one_of_not_dvd hN0 hv]
      have h1 : (s : w.adicCompletion K) ∈ w.adicCompletionIntegers K := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, hs]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (sub_mem h1 (one_mem _))
    · rw [localUnit_apply_of_ne (𝓞 K) K v s hw, sub_self, map_zero]
      exact zero_le'

open NumberField.AdelicLevel in
theorem isUnramifiedCharAt_of_forall_mem_principalLevel (N : Ideal (𝓞 K)) (hN0 : N ≠ ⊥)
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχ : ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, χ (Matrix.GeneralLinearGroup.det u) = 1)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ N) :
    NumberField.TateGlobal.IsUnramifiedCharAt χ v := by
  intro t ht ht'
  show χ (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)) = 1
  have hdet : Matrix.GeneralLinearGroup.det (heckeGenAt (𝓞 K) K v t) =
      Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t) := by
    apply Units.ext
    simp [heckeGenAt, diagOne, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.diagonal]
  rw [← hdet]
  apply hχ
  have hval : Valued.v (t : v.adicCompletion K) = 1 := by
    apply le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp ht)
    have h' := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp ht'
    rw [Units.val_inv_eq_inv_val, map_inv₀] at h'
    have h0 : Valued.v (t : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr t.ne_zero
    have h1 := mul_le_mul_left h' (Valued.v (t : v.adicCompletion K))
    rwa [inv_mul_cancel₀ h0, one_mul] at h1
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_principalLevel_iff]
    refine ⟨?_, ?_⟩
    · have h := heckeGenAt_inv_mul_heckeGenAt_mem_levelOne (R := 𝓞 K) (K := K) (v := v) 1 t
        (by rw [Units.val_one, map_one, hval]) N
      simpa using h
    · refine Subgroup.mem_map.mpr ⟨(weyl (𝓞 K) K)⁻¹ * heckeGenAt (𝓞 K) K v t * weyl (𝓞 K) K, ?_, ?_⟩
      · rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
        refine ⟨isLevelOneMatrix_weyl_conj_heckeGenAt K N hN0 v hv t hval, ?_⟩
        have hinv : (glFin (𝓞 K) K ((weyl (𝓞 K) K)⁻¹ * heckeGenAt (𝓞 K) K v t * weyl (𝓞 K) K))⁻¹ =
            glFin (𝓞 K) K ((weyl (𝓞 K) K)⁻¹ * heckeGenAt (𝓞 K) K v t⁻¹ * weyl (𝓞 K) K) := by
          rw [← map_inv, map_inv (heckeGenAt (𝓞 K) K v)]
          congr 1
          simp only [mul_inv_rev, inv_inv, mul_assoc]
        rw [hinv]
        exact isLevelOneMatrix_weyl_conj_heckeGenAt K N hN0 v hv t⁻¹
          (by rw [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one])
      · simp [mul_assoc]
  · rw [AutomorphicForm.mem_finiteAdelicGL2Subgroup_iff]
    apply Units.ext
    ext i j
    rw [glArch_apply, heckeGenAt_fst, Units.val_one]

theorem det_heckeGen (v : HeightOneSpectrum (𝓞 K)) :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v) = uniformizerIdele K v := by
  apply Units.ext
  simp [heckeGen, heckeGenAt, uniformizerIdele, diagOne, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.det_fin_two, Matrix.diagonal]

theorem ideal_ne_bot_of_forall_dvd_mem (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S) : N ≠ ⊥ := by
  classical
  intro hbot
  have hall : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ S := fun v => hN v (by rw [hbot]; exact dvd_zero _)
  have hMpos : 0 < ∏ v ∈ S, Ideal.absNorm v.asIdeal := by
    refine Finset.prod_pos fun v _ => Nat.pos_of_ne_zero ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (∏ v ∈ S, Ideal.absNorm v.asIdeal + 1)

  have hptop : Ideal.span {(p : 𝓞 K)} ≠ ⊤ := by
    intro htop
    have h1 : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = 1 := by rw [htop, Ideal.absNorm_top]
    rw [Ideal.absNorm_span_singleton] at h1
    have hn : Algebra.norm ℤ (p : 𝓞 K) = (p : ℤ) ^ Module.finrank ℤ (𝓞 K) := by
      rw [show (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp, Algebra.norm_algebraMap]
    rw [hn, Int.natAbs_pow, Int.natAbs_natCast] at h1
    have hr : 0 < Module.finrank ℤ (𝓞 K) := Module.finrank_pos
    exact hp.one_lt.ne' (Nat.pow_eq_one.mp h1 |>.resolve_right hr.ne')
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hptop
  have h𝔪bot : 𝔪 ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff, Ideal.span_singleton_eq_bot] at hle
    exact hp.ne_zero (by exact_mod_cast hle)
  let v₀ : HeightOneSpectrum (𝓞 K) := ⟨𝔪, h𝔪.isPrime, h𝔪bot⟩

  have hpmem : (p : 𝓞 K) ∈ 𝔪 := hle (Ideal.mem_span_singleton_self _)
  have hdvd : (Ideal.absNorm 𝔪 : ℤ) ∣ (p : ℤ) ^ Module.finrank ℤ (𝓞 K) := by
    have := Ideal.absNorm_dvd_norm_of_mem hpmem
    rwa [show (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp, Algebra.norm_algebraMap] at this
  have hdvd' : Ideal.absNorm 𝔪 ∣ p ^ Module.finrank ℤ (𝓞 K) := by
    rw [← Nat.cast_pow] at hdvd
    exact Int.natCast_dvd_natCast.mp hdvd
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp hdvd'
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.absNorm_eq_one_iff] at hk'
    exact h𝔪.ne_top hk'
  have hp_le : p ≤ Ideal.absNorm 𝔪 := by
    rw [hk']
    exact Nat.le_self_pow hk0 p

  have hdvM : Ideal.absNorm v₀.asIdeal ∣ ∏ v ∈ S, Ideal.absNorm v.asIdeal :=
    Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 K) => Ideal.absNorm v.asIdeal) (hall v₀)
  have hle' : Ideal.absNorm 𝔪 ≤ ∏ v ∈ S, Ideal.absNorm v.asIdeal := Nat.le_of_dvd hMpos hdvM
  omega

def normInvChar : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ where
  toFun x := Units.mk0 (((NumberField.TateGlobal.ideleNorm K x : ℝ) : ℂ)⁻¹)
    (inv_ne_zero (by exact_mod_cast (NumberField.TateGlobal.ideleNorm_pos x).ne'))
  map_one' := Units.ext (by
    rw [Units.val_mk0, NumberField.TateGlobal.ideleNorm_one, Complex.ofReal_one, inv_one, Units.val_one])
  map_mul' x y := Units.ext (by
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, NumberField.TateGlobal.ideleNorm_mul,
      Complex.ofReal_mul, mul_inv])

theorem coe_normInvChar_apply (x : (AdeleRing (𝓞 K) K)ˣ) :
    ((normInvChar K x : ℂˣ) : ℂ) = ((NumberField.TateGlobal.ideleNorm K x : ℝ) : ℂ)⁻¹ := rfl

theorem continuous_normInvChar : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((normInvChar K z : ℂˣ) : ℂ) := by
  simp only [coe_normInvChar_apply]
  exact (Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm K)).inv₀
    fun x => by
      show ((NumberField.TateGlobal.ideleNorm K x : ℝ) : ℂ) ≠ 0
      exact_mod_cast (NumberField.TateGlobal.ideleNorm_pos x).ne'

theorem ideleNorm_eq_one_of_mem_range {z : (AdeleRing (𝓞 K) K)ˣ}
    (hz : z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range) :
    NumberField.TateGlobal.ideleNorm K z = 1 := by
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hz
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap K a
  simp only [NumberField.TateGlobal.ideleNorm]
  rw [show Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom a from rfl, h]
  simp

theorem normInvChar_eq_one_of_mem_range {z : (AdeleRing (𝓞 K) K)ˣ}
    (hz : z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range) :
    normInvChar K z = 1 :=
  Units.ext (by rw [coe_normInvChar_apply, ideleNorm_eq_one_of_mem_range K hz, Complex.ofReal_one, inv_one,
    Units.val_one])

open NumberField.AdelicLevel NumberField.AdeleRing in

theorem isUnramifiedCharAt_normInvChar (v : HeightOneSpectrum (𝓞 K)) :
    NumberField.TateGlobal.IsUnramifiedCharAt (normInvChar K) v := by
  intro u hu hu'
  show normInvChar K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v u)) = 1
  apply Units.ext
  rw [coe_normInvChar_apply, Units.val_one,
    NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles, Complex.ofReal_one,
    inv_one]
  · rfl
  · rw [IsDedekindDomain.FiniteAdeleRing.mem_unitIdeles_iff]
    have hfp : finitePartUnits (𝓞 K) K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v u))
        = localUnit (𝓞 K) K v u := Units.ext rfl
    rw [hfp]
    refine ⟨fun w => ?_, fun w => ?_⟩
    · by_cases hw : w = v
      · subst hw; rw [localUnit_apply_self]; exact hu
      · rw [localUnit_apply_of_ne _ _ _ _ hw]; exact one_mem _
    · rw [← map_inv]
      by_cases hw : w = v
      · subst hw; rw [localUnit_apply_self]; exact hu'
      · rw [localUnit_apply_of_ne _ _ _ _ hw]; exact one_mem _

theorem coe_normInvChar_uniformizerIdele (v : HeightOneSpectrum (𝓞 K)) :
    ((normInvChar K (uniformizerIdele K v) : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) := by
  rw [coe_normInvChar_apply, NumberField.TateGlobal.ideleNorm_uniformizerIdele, Complex.ofReal_inv, inv_inv,
    Complex.ofReal_natCast]

theorem isUnramifiedCharAt_mul {χ ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {v : HeightOneSpectrum (𝓞 K)}
    (hχ : NumberField.TateGlobal.IsUnramifiedCharAt χ v) (hψ : NumberField.TateGlobal.IsUnramifiedCharAt ψ v) :
    NumberField.TateGlobal.IsUnramifiedCharAt (χ * ψ) v := by
  intro t ht ht'
  have h1 := hχ t ht ht'
  have h2 := hψ t ht ht'
  simp only [NumberField.TateGlobal.localChar, MonoidHom.coe_comp, Function.comp_apply] at h1 h2 ⊢
  rw [MonoidHom.mul_apply, h1, h2, one_mul]

end ResBlock

end

open ResBlock in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 K) → ℂ × ℂ)) (hXc : IsCompact X)
    (hX : {x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ |
        (∀ v ∈ SK, x v = 0) ∧
        ∀ v ∉ SK,
          (x v).2 = HeckeEigensystem.cNorm v *
              ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x v).1‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x v).1 = conj (x v).2 / ((‖(x v).2‖ : ℝ) : ℂ) * (x v).1} ⊆ X) :
    ∃ (tabs : ℕ → (HeightOneSpectrum (𝓞 K) → ℂ × ℂ)) (htabs : ∀ n, tabs n ∈ X) (cs : ℕ → ℂ),
    (Summable fun n => ‖cs n‖) ∧
    (∀ n, cs n ≠ 0 →
      ∃ (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            χ₁ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            χ₂ z = 1) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
          NumberField.TateGlobal.IsUnramifiedCharAt χ₁ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt χ₂ v) ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
          tabs n v = ((LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂).a v,
            (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂).b v)) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T SK → 2 ≤ T.card →
      ∀ (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K),
        (∀ v ∈ T, Irreducible (ϖKs v)) →
      ∀ (hϖKs0 : ∀ v ∈ T,
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
        (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
        (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
            (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v)) →
      ∀ (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K)),
        (∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
            (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
        (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ),
        IsUnitFactorization K (SK ∪ T) f faK ff
          (fun v => if v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (nKs v),
              (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ js v)⁻¹ * x)
            else fSK v) →
        IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
        IsArchBiFinite K tysK f →
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v).1 ^ ks v *
            ((HeckeEigensystem.cNorm v)⁻¹ *
              ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v).2) ^ js v) →
        (∀ R : ℝ, IntegrableOn (fun x =>
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y'))
                x))
            (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
        Filter.Tendsto (fun R : ℝ =>
          ∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y'))
                x)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) Filter.atTop (nhds (∑' n, cs n * g ⟨tabs n, htabs n⟩)) := by
  classical

  have hN0 : N ≠ ⊥ := ResBlock.ideal_ne_bot_of_forall_dvd_mem K N SK hN
  set C : Set ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := {χ |
      AutomorphicForm.SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1) ∧
      (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) ∧
      ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
        χ (Matrix.GeneralLinearGroup.det u) = 1} with hC
  have hCfin : C.Finite :=
    AutomorphicForm.finite_setOf_squaresToXi_continuous_apply_det_eq_one_of_mem_principalLevel K ξK N hN0

  set F₀ : AdelicGL2 (𝓞 K) K → ℂ := {g : AdelicGL2 (𝓞 K) K |
      ∀ v ∉ SK, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈ localIntegralSet K v}.indicator
    (fun g => faK (AdelicLevel.glArch (𝓞 K) K g) *
      ∏ v ∈ SK, fSK v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) with hF₀
  set band : ℂ := ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) with hband
  set I₀ : ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → ℂ := fun χ =>
    ∫ g, F₀ g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hI₀
  set tab : ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → (HeightOneSpectrum (𝓞 K) → ℂ × ℂ) := fun χ v =>
    if v ∈ SK then 0 else
      (((HeckeEigensystem.cNorm v) + 1) * ((χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ),
        (HeckeEigensystem.cNorm v) * ((χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) ^ 2)
    with htab
  set tab₀ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ := fun v =>
    if v ∈ SK then 0 else
      (0, HeckeEigensystem.cNorm v *
        ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) with htab₀
  have hcNorm : ∀ v : HeightOneSpectrum (𝓞 K), HeckeEigensystem.cNorm v = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) :=
    fun v => rfl
  have htab_mem : ∀ χ ∈ C, tab χ ∈ X := by
    intro χ hχ
    apply hX
    refine ⟨fun v hv => by simp only [htab, if_pos hv], fun v hv => ?_⟩
    set c : ℂ := ((χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) with hc
    have hc0 : c ≠ 0 := Units.ne_zero _
    have hsq : c ^ 2 = ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by
      rw [hc, ← Units.val_pow_eq_pow_val, hχ.1 ⟨_, Subgroup.mem_top _⟩]
    have hNpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by
      have : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
      exact_mod_cast Nat.pos_of_ne_zero this
    simp only [htab, if_neg hv]
    refine ⟨?_, ?_, ?_⟩
    · rw [hsq]
    · rw [← hsq, norm_mul, norm_pow, Real.sqrt_sq (norm_nonneg _), hcNorm]
      have : ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 1‖ = (Ideal.absNorm v.asIdeal : ℝ) + 1 := by
        rw [show ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 1 = (((Ideal.absNorm v.asIdeal : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [this]
    ·
      have hcc : conj c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hnc : ((‖c‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hc0)
      have hN0' : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
      rw [hcNorm, norm_mul, norm_pow, Complex.norm_natCast, map_mul, map_mul, map_pow,
        show conj (((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) from Complex.conj_natCast _,
        show conj (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 1) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 1 by
          rw [map_add, map_one, Complex.conj_natCast]]
      push_cast
      field_simp
      rw [hcc]
      push_cast
      ring
  have htab₀_mem : tab₀ ∈ X := by
    apply hX
    refine ⟨fun v hv => by simp only [htab₀, if_pos hv], fun v hv => ?_⟩
    simp only [htab₀, if_neg hv]
    refine ⟨?_, ?_, ?_⟩
    · first | rfl | trivial
    · first | (rw [norm_zero]; positivity) | positivity | trivial
    · first | (rw [map_zero, mul_zero]) | simp

  set Cf : Finset ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := hCfin.toFinset with hCf
  have hCf_mem : ∀ χ, χ ∈ Cf ↔ χ ∈ C := fun χ => by rw [hCf, Set.Finite.mem_toFinset]
  set m : ℕ := Cf.card with hm
  set e : Fin m → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := fun i => ((Cf.equivFin.symm i : Cf) : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    with he
  have he_range : Set.range e = C := by
    ext χ
    constructor
    · rintro ⟨i, rfl⟩
      exact (hCf_mem _).mp (Cf.equivFin.symm i).2
    · intro hχ
      refine ⟨Cf.equivFin ⟨χ, (hCf_mem χ).mpr hχ⟩, ?_⟩
      simp [e]
  let tabs : ℕ → (HeightOneSpectrum (𝓞 K) → ℂ × ℂ) := fun n =>
    if h : n < m then tab (e ⟨n, h⟩) else tab₀
  have htabs : ∀ n, tabs n ∈ X := by
    intro n
    by_cases h : n < m
    · simp only [tabs, dif_pos h]
      exact htab_mem _ (he_range ▸ Set.mem_range_self _)
    · simp only [tabs, dif_neg h]
      exact htab₀_mem
  let cs : ℕ → ℂ := fun n => if h : n < m then band * I₀ (e ⟨n, h⟩) else 0
  refine ⟨tabs, htabs, cs, ?_, ?_, ?_⟩
  ·
    refine summable_of_ne_finset_zero (s := Finset.range m) fun n hn => ?_
    have h : ¬ n < m := by simpa [Finset.mem_range] using hn
    simp only [cs, dif_neg h, norm_zero]
  ·
    intro n hn
    have hlt : n < m := by
      by_contra h
      exact hn (by simp only [cs, dif_neg h])
    have hχC : e ⟨n, hlt⟩ ∈ C := he_range ▸ Set.mem_range_self _
    refine ⟨⊤, top_ne_bot, e ⟨n, hlt⟩, e ⟨n, hlt⟩ * ResBlock.normInvChar K, hχC.2.2.1, hχC.2.1, ?_, ?_, ?_, ?_⟩
    · have : (fun z : (AdeleRing (𝓞 K) K)ˣ => (((e ⟨n, hlt⟩ * ResBlock.normInvChar K) z : ℂˣ) : ℂ)) =
          fun z => ((e ⟨n, hlt⟩ z : ℂˣ) : ℂ) * ((ResBlock.normInvChar K z : ℂˣ) : ℂ) := by
        funext z; rw [MonoidHom.mul_apply, Units.val_mul]
      rw [this]
      exact hχC.2.2.1.mul (ResBlock.continuous_normInvChar K)
    · intro z hz
      rw [MonoidHom.mul_apply, hχC.2.1 z hz, ResBlock.normInvChar_eq_one_of_mem_range K hz, one_mul]
    · intro v hv
      have hvN : ¬ v.asIdeal ∣ N := fun h => hv (hN v h)
      have hu := ResBlock.isUnramifiedCharAt_of_forall_mem_principalLevel K N hN0 _ hχC.2.2.2 v hvN
      exact ⟨hu, ResBlock.isUnramifiedCharAt_mul K hu (ResBlock.isUnramifiedCharAt_normInvChar K v)⟩
    · intro v hv
      simp only [tabs, dif_pos hlt, htab, if_neg hv, LanglandsTunnell.Converse.eisensteinTableOf,
        MonoidHom.mul_apply, Units.val_mul, ResBlock.det_heckeGen, ResBlock.coe_normInvChar_uniformizerIdele, hcNorm]
      refine Prod.ext ?_ ?_ <;> simp only <;> ring
  · intro T hTS hT2 ϖKs hirr hϖKs0 nKs rKs hcos zKs hzKs ks js f hf hfc ff hfact hbi harch g hg
    set vol : ℂ := ((adelicGLHaar (Fin 2) (𝓞 K) K (canonicalTruncationDomain K α β)).toReal : ℂ) with hvol
    set Sset : Set ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
        SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            χ z = 1) ∧
        Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)} with hSset
    set If : ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → ℂ := fun χ =>
      ∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hIf
    set D : ℂ := band / vol * ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ Sset), If χ with hD

    have hker : ∀ (x : AdelicGL2 (𝓞 K) K) (R : ℝ),
        @AutomorphicForm.lambdaT _
          (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
          (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (fun y' => band / vol *
            ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ Sset), If χ *
              (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y')) x =
        {y' : AdelicGL2 (𝓞 K) K | NumberField.AdelicHeight.adelicHeight K y' ≤ Real.exp R}.indicator
          (fun _ => D) x := by
      intro x R
      rw [ResBlock.lambdaT_eq_indicator_of_forall_unipotentGL2_mul]
      · simp only [Set.indicator_apply, Set.mem_setOf_eq]
        split_ifs with h
        · rw [hD]
          congr 1
          refine finsum_congr fun χ => finsum_congr fun _ => ?_
          have : chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ x = 1 := by
            simp only [chiDet, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
            exact mul_inv_cancel₀ (Units.ne_zero _)
          rw [this, mul_one]
        · rfl
      · intro t y
        simp only [ResBlock.chiDet_unipotentGL2_mul]
    refine ⟨fun R => ?_, ?_⟩
    · have hfun : (fun x => @AutomorphicForm.lambdaT _
          (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
          (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (fun y' => band / vol *
            ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ Sset), If χ *
              (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y')) x) =
          fun x => {y' : AdelicGL2 (𝓞 K) K | NumberField.AdelicHeight.adelicHeight K y' ≤ Real.exp R}.indicator
            (fun _ => D) x := funext fun x => hker x R
      rw [hfun]
      exact ResBlock.integrableOn_indicator_heightLE_const K hα hαβ D R
    · have hfun : (fun R : ℝ => ∫ x in canonicalTruncationDomain K α β, @AutomorphicForm.lambdaT _
          (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
          (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (fun y' => band / vol *
            ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ Sset), If χ *
              (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y')) x ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
          fun R : ℝ => ∫ x in canonicalTruncationDomain K α β,
            {y' : AdelicGL2 (𝓞 K) K | NumberField.AdelicHeight.adelicHeight K y' ≤ Real.exp R}.indicator
              (fun _ => D) x ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
        funext fun R => integral_congr_ae (Filter.Eventually.of_forall fun x => hker x R)
      rw [hfun]
      have hval : (∑' n, cs n * g ⟨tabs n, htabs n⟩) = vol * D := by

        set monoH : ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → ℂ := fun χ =>
          ∏ v ∈ T,
            (((HeckeEigensystem.cNorm v) + 1) *
                ((χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ)) ^ ks v *
              ((HeckeEigensystem.cNorm v)⁻¹ *
                ((HeckeEigensystem.cNorm v) *
                  ((χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) ^ 2)) ^ js v with hmonoH
        have hTSK : ∀ v ∈ T, v ∉ SK := fun v hv hvS => Finset.disjoint_left.mp hTS hv hvS

        have hg_tab : ∀ χ (hχ : χ ∈ C), g ⟨tab χ, htab_mem χ hχ⟩ = monoH χ := by
          intro χ hχ
          rw [hg, hmonoH]
          refine Finset.prod_congr rfl fun v hv => ?_
          simp only [htab, if_neg (hTSK v hv)]

        have h1 : (∑' n, cs n * g ⟨tabs n, htabs n⟩) = ∑ n ∈ Finset.range m, cs n * g ⟨tabs n, htabs n⟩ := by
          refine tsum_eq_sum fun n hn => ?_
          have h : ¬ n < m := by simpa [Finset.mem_range] using hn
          simp only [cs, dif_neg h, zero_mul]

        have h2 : ∑ n ∈ Finset.range m, cs n * g ⟨tabs n, htabs n⟩ =
            ∑ i : Fin m, band * I₀ (e i) * monoH (e i) := by
          rw [Finset.sum_range]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hi : (i : ℕ) < m := i.2
          have hmemC : e ⟨i, hi⟩ ∈ C := he_range ▸ Set.mem_range_self _
          have htabsi : tabs i = tab (e ⟨i, hi⟩) := by simp only [tabs, dif_pos hi]
          have hgi : g ⟨tabs i, htabs i⟩ = monoH (e ⟨i, hi⟩) := by
            rw [← hg_tab _ hmemC]
            congr 1
            exact Subtype.ext htabsi
          rw [hgi]
          simp only [cs, dif_pos hi]

        have h3 : ∑ i : Fin m, band * I₀ (e i) * monoH (e i) = ∑ χ ∈ Cf, band * I₀ χ * monoH χ := by
          rw [← Finset.sum_coe_sort Cf (fun χ => band * I₀ χ * monoH χ)]
          exact Fintype.sum_equiv Cf.equivFin.symm _ _ fun i => rfl

        have h4 : ∀ χ ∈ Cf, If χ = monoH χ * I₀ χ := by
          intro χ hχ
          have hχC : χ ∈ C := (hCf_mem χ).mp hχ
          have hχT : ∀ v ∈ T, NumberField.TateGlobal.IsUnramifiedCharAt χ v := fun v hv =>
            ResBlock.isUnramifiedCharAt_of_forall_mem_principalLevel K N hN0 χ hχC.2.2.2 v
              (fun hdvd => hTSK v hv (hN v hdvd))
          rw [hIf, hI₀, hmonoH, hF₀]
          exact AutomorphicForm.integral_mul_chiDet_eq_prod_pow_mul_pow_mul_integral_mul_chiDet_of_isUnitFactorization K SK T hTS ϖKs hirr hϖKs0 nKs rKs
            hcos zKs hzKs faK fSK ks js f hf hfc ff hfact χ hχT

        have h5 : (∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ Sset), If χ) = ∑ χ ∈ Cf, If χ := by
          refine finsum_mem_eq_sum_of_subset If ?_ ?_
          · intro χ hχ
            rw [Finset.mem_coe, hCf_mem]
            refine ⟨hχ.1.1, hχ.1.2.1, hχ.1.2.2, ?_⟩
            intro u hu
            by_contra hne
            exact hχ.2 (ResBlock.integral_mul_chiDet_eq_zero_of_apply_det_ne_one K _ f hbi χ u hu hne)
          · intro χ hχ
            have hχC : χ ∈ C := (hCf_mem χ).mp hχ
            exact ⟨hχC.1, hχC.2.1, hχC.2.2.1⟩

        have hvol0 : vol ≠ 0 := by
          rw [hvol]
          have hne : (adelicGLHaar (Fin 2) (𝓞 K) K (canonicalTruncationDomain K α β)).toReal ≠ 0 := by
            rw [Ne, ENNReal.toReal_eq_zero_iff, not_or]
            exact ⟨ResBlock.adelicGLHaar_canonicalTruncationDomain_ne_zero K hα hαβ,
              (ResBlock.adelicGLHaar_canonicalTruncationDomain_lt_top K hα hαβ).ne⟩
          exact_mod_cast hne
        have hvb : vol * (band / vol) = band := by field_simp
        rw [h1, h2, h3, hD, h5, ← mul_assoc, hvb, Finset.mul_sum]
        refine Finset.sum_congr rfl fun χ hχ => ?_
        rw [h4 χ hχ]
        ring
      rw [hval]
      exact ResBlock.tendsto_setIntegral_indicator_heightLE_const K hα hαβ D

end S_AutomorphicForm_exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_chiDet_mul_chiDet_inv
end P2MW
export P2MW.S_AutomorphicForm_exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_chiDet_mul_chiDet_inv (solution)
