-- Prove2me | solution 1 for AutomorphicForm.exists_forall_lintegral_localHaar_eq_mul_lintegral_pi_norm_det_inv_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/8c159f7f-e245-578b-990a-bc90277d669b

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Theorems.Thm_NumberField_AdicCompletion_map_matrix_mulVec_pi_eq_smul_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_lintegral_localHaar_eq_mul_lintegral_pi_norm_det_inv_sq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory Set Function Matrix
open scoped ENNReal NNReal Classical

noncomputable section

namespace KcAdicGLHaar

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

local notation "F" => v.adicCompletion K
local notation "P" => Fin 4 → v.adicCompletion K
local notation "G" => GL (Fin 2) (v.adicCompletion K)

def mat (x : P) : Matrix (Fin 2) (Fin 2) F := !![x 0, x 1; x 2, x 3]

def flat (M : Matrix (Fin 2) (Fin 2) F) : P := ![M 0 0, M 0 1, M 1 0, M 1 1]

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
@[scoped simp] theorem mat_flat (M : Matrix (Fin 2) (Fin 2) F) : mat (flat M) = M := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
@[scoped simp] theorem flat_mat (x : P) : flat (mat x) = x := by
  funext i; fin_cases i <;> rfl

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem det_mat (x : P) : (mat x).det = x 0 * x 3 - x 1 * x 2 := by
  simp [mat, Matrix.det_fin_two_of]

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem continuous_mat : Continuous (mat : P → Matrix (Fin 2) (Fin 2) F) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_apply 2
  · exact continuous_apply 3

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem continuous_flat : Continuous (flat : Matrix (Fin 2) (Fin 2) F → P) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact (continuous_apply_apply 0 0)
  · exact (continuous_apply_apply 0 1)
  · exact (continuous_apply_apply 1 0)
  · exact (continuous_apply_apply 1 1)

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem continuous_det_mat : Continuous fun x : P => (mat x).det :=
  continuous_mat.matrix_det

def good : Set P := {x | (mat x).det ≠ 0}

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem isOpen_good : IsOpen (good : Set P) :=
  isOpen_ne_fun continuous_det_mat continuous_const

theorem measurableSet_good : MeasurableSet (good : Set P) := isOpen_good.measurableSet

noncomputable def chart (x : P) : G :=
  if h : (mat x).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (mat x) h else 1

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem chart_of_mem {x : P} (h : (mat x).det ≠ 0) :
    chart x = Matrix.GeneralLinearGroup.mkOfDetNeZero (mat x) h := by
  simp [chart, h]

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem coe_chart_of_mem {x : P} (h : (mat x).det ≠ 0) :
    ((chart x : G) : Matrix (Fin 2) (Fin 2) F) = mat x := by
  rw [chart_of_mem h]; rfl

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem chart_flat (g : G) : chart (flat (g : Matrix (Fin 2) (Fin 2) F)) = g := by
  have h : (mat (flat (g : Matrix (Fin 2) (Fin 2) F))).det ≠ 0 := by
    rw [mat_flat]; exact (Matrix.GeneralLinearGroup.det_ne_zero g)
  apply Units.ext
  rw [coe_chart_of_mem h, mat_flat]

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem t2Space_GL : T2Space G := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → F))
  exact Units.isEmbedding_embedProduct.t2Space

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem secondCountableTopology_GL : SecondCountableTopology G := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → F))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

attribute [local instance] t2Space_GL secondCountableTopology_GL
  AutomorphicForm.locallyCompactSpace_localGL
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel AutomorphicForm.isHaarMeasure_localHaar

theorem continuous_GL_of {X : Type*} [TopologicalSpace X] {f : X → G}
    (hval : ∀ i j, Continuous fun x => ((f x : G) : Matrix (Fin 2) (Fin 2) F) i j)
    (hinv : ∀ i j, Continuous fun x => (((f x)⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) i j) :
    Continuous f := by
  rw [Units.continuous_iff]
  exact ⟨continuous_matrix fun i j => hval i j, continuous_matrix fun i j => hinv i j⟩

theorem continuous_chart_restrict : Continuous ((good : Set P).domRestrict (chart : P → G)) := by
  have hdet : Continuous fun x : (good : Set P) => (mat (x : P)).det :=
    continuous_det_mat.comp continuous_subtype_val
  have hdet0 : ∀ x : (good : Set P), (mat (x : P)).det ≠ 0 := fun x => x.2
  have hent : ∀ i j, Continuous fun x : (good : Set P) => mat (x : P) i j := fun i j =>
    (continuous_mat.matrix_elem i j).comp continuous_subtype_val
  refine continuous_GL_of (fun i j => ?_) (fun i j => ?_)
  · have : (fun x : (good : Set P) => (((good : Set P).domRestrict chart x : G) : Matrix (Fin 2) (Fin 2) F) i j)
        = fun x : (good : Set P) => mat (x : P) i j := by
      funext x; rw [Set.domRestrict_apply, coe_chart_of_mem x.2]
    rw [this]; exact hent i j
  · have : (fun x : (good : Set P) =>
        ((((good : Set P).domRestrict chart x)⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) i j)
        = fun x : (good : Set P) => ((mat (x : P)).det)⁻¹ * (mat (x : P)).adjugate i j := by
      funext x
      rw [Set.domRestrict_apply, Matrix.coe_units_inv, coe_chart_of_mem x.2,
        Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    rw [this]
    refine (hdet.inv₀ hdet0).mul ?_
    have hadj : Continuous fun x : (good : Set P) => (mat (x : P)).adjugate :=
      (continuous_mat.comp continuous_subtype_val).matrix_adjugate
    exact hadj.matrix_elem i j

theorem measurable_chart : Measurable (chart : P → G) := by
  refine measurable_of_restrict_of_restrict_compl measurableSet_good ?_ ?_
  · exact continuous_chart_restrict.measurable
  · have : (goodᶜ : Set P).domRestrict (chart : P → G) = fun _ => 1 := by
      funext x
      have hx : ¬ ((mat (x : P)).det ≠ 0) := x.2
      simp [Set.domRestrict_apply, chart, hx]
    rw [this]; exact measurable_const

theorem measurable_flat_coe : Measurable fun g : G => flat (g : Matrix (Fin 2) (Fin 2) F) :=
  (continuous_flat.comp Units.continuous_val).measurable

def Lmat (g : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![g 0 0, 0, g 0 1, 0; 0, g 0 0, 0, g 0 1; g 1 0, 0, g 1 1, 0; 0, g 1 0, 0, g 1 1]

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem mat_Lmat_mulVec (g : Matrix (Fin 2) (Fin 2) F) (x : P) :
    mat ((Lmat g).mulVec x) = g * mat x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mat, Lmat, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.mul_apply, Fin.sum_univ_two,
      mul_comm]

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem det_Lmat (g : Matrix (Fin 2) (Fin 2) F) : (Lmat g).det = g.det ^ 2 := by
  simp [Lmat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, Matrix.det_fin_two]
  ring

theorem measurable_Lmat_mulVec (g : Matrix (Fin 2) (Fin 2) F) :
    Measurable fun x : P => (Lmat g).mulVec x :=
  (continuous_const.matrix_mulVec continuous_id).measurable

section Main

variable (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

local notation "π" => Measure.pi fun _ : Fin 4 => μ

def Dinv (x : P) : ℝ≥0∞ := ENNReal.ofReal ((‖(mat x).det‖ ^ 2)⁻¹)

theorem measurable_Dinv : Measurable (Dinv : P → ℝ≥0∞) :=
  ENNReal.measurable_ofReal.comp ((continuous_det_mat.norm.pow 2).measurable.inv)

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem Dinv_ne_zero {x : P} (hx : x ∈ good) : Dinv x ≠ 0 := by
  simp only [Dinv, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  have : 0 < ‖(mat x).det‖ := norm_pos_iff.2 hx
  positivity

def m : Measure G := Measure.map chart (((π).restrict good).withDensity Dinv)

theorem lintegral_m {H : G → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ g, H g ∂(m μ) = ∫⁻ x in good, H (chart x) * Dinv x ∂π := by
  rw [m, lintegral_map hH measurable_chart]
  rw [show (fun a => H (chart a)) = H ∘ chart from rfl,
    lintegral_withDensity_eq_lintegral_mul _ measurable_Dinv (hH.comp measurable_chart)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, Function.comp_apply, mul_comm]

theorem m_apply {A : Set G} (hA : MeasurableSet A) :
    m μ A = ∫⁻ x in good, A.indicator 1 (chart x) * Dinv x ∂π := by
  rw [← lintegral_indicator_one hA, lintegral_m μ (measurable_one.indicator hA)]

theorem chart_Lmat_mulVec (g : G) {x : P} (hx : x ∈ good) :
    chart ((Lmat (g : Matrix (Fin 2) (Fin 2) F)).mulVec x) = g * chart x := by
  have hdet : (mat ((Lmat (g : Matrix (Fin 2) (Fin 2) F)).mulVec x)).det ≠ 0 := by
    rw [mat_Lmat_mulVec, Matrix.det_mul]
    exact mul_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero g) hx
  apply Units.ext
  rw [coe_chart_of_mem hdet, mat_Lmat_mulVec, Units.val_mul, coe_chart_of_mem hx]

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem mem_good_Lmat_mulVec_iff (g : G) (x : P) :
    (Lmat (g : Matrix (Fin 2) (Fin 2) F)).mulVec x ∈ good ↔ x ∈ good := by
  simp only [good, mem_setOf_eq, mat_Lmat_mulVec, Matrix.det_mul]
  exact ⟨fun h hx => h (by rw [hx, mul_zero]),
    fun h => mul_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero g) h⟩

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem Dinv_Lmat_mulVec (g : G) (x : P) :
    Dinv ((Lmat (g : Matrix (Fin 2) (Fin 2) F)).mulVec x) =
      ENNReal.ofReal ((‖(g : Matrix (Fin 2) (Fin 2) F).det‖ ^ 2)⁻¹) * Dinv x := by
  simp only [Dinv, mat_Lmat_mulVec, Matrix.det_mul, norm_mul, mul_pow, mul_inv]
  rw [ENNReal.ofReal_mul (by positivity)]

theorem cg_ne_zero (g : G) : ENNReal.ofReal ((‖(g : Matrix (Fin 2) (Fin 2) F).det‖ ^ 2)⁻¹) ≠ 0 := by
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  have : 0 < ‖(g : Matrix (Fin 2) (Fin 2) F).det‖ := norm_pos_iff.2 (Matrix.GeneralLinearGroup.det_ne_zero g)
  positivity

theorem setLIntegral_comp_mul_left (g : G) {A : Set G} (hA : MeasurableSet A) :
    ∫⁻ x in good, A.indicator 1 (g * chart x) * Dinv x ∂π =
      ∫⁻ x in good, A.indicator 1 (chart x) * Dinv x ∂π := by
  set L : Matrix (Fin 4) (Fin 4) F := Lmat (g : Matrix (Fin 2) (Fin 2) F) with hL
  have hLdet : L.det ≠ 0 := by
    rw [hL, det_Lmat]; exact pow_ne_zero 2 (Matrix.GeneralLinearGroup.det_ne_zero g)
  set cg : ℝ≥0∞ := ENNReal.ofReal ((‖(g : Matrix (Fin 2) (Fin 2) F).det‖ ^ 2)⁻¹) with hcg

  have hmap := NumberField.AdicCompletion.map_matrix_mulVec_pi_eq_smul_pi K v μ L hLdet
  have hnorm : ENNReal.ofReal ‖L.det‖⁻¹ = cg := by
    rw [hcg, hL, det_Lmat, norm_pow]
  rw [hnorm] at hmap
  set Hh : P → ℝ≥0∞ := good.indicator fun x => A.indicator 1 (chart x) * Dinv x with hHh
  have hHm : Measurable Hh := by
    refine Measurable.indicator ?_ measurableSet_good
    exact ((measurable_one.indicator hA).comp measurable_chart).mul measurable_Dinv

  have h1 : ∫⁻ x, Hh (L.mulVec x) ∂π = cg * ∫⁻ x, Hh x ∂π := by
    have hlm : ∫⁻ x, Hh x ∂(Measure.map (fun x : P => L.mulVec x) π) = ∫⁻ x, Hh (L.mulVec x) ∂π :=
      lintegral_map hHm (measurable_Lmat_mulVec _)
    rw [hmap, lintegral_smul_measure, smul_eq_mul] at hlm
    exact hlm.symm

  have h2 : ∀ x : P, Hh (L.mulVec x) =
      cg * good.indicator (fun x => A.indicator 1 (g * chart x) * Dinv x) x := by
    intro x
    by_cases hx : x ∈ good
    · rw [hHh, indicator_of_mem ((mem_good_Lmat_mulVec_iff g x).2 hx), indicator_of_mem hx,
        chart_Lmat_mulVec g hx, Dinv_Lmat_mulVec, ← hcg]
      ring
    · rw [hHh, indicator_of_notMem (fun h => hx ((mem_good_Lmat_mulVec_iff g x).1 h)),
        indicator_of_notMem hx, mul_zero]
  simp_rw [h2] at h1
  rw [lintegral_const_mul _ (by
      refine Measurable.indicator ?_ measurableSet_good
      exact ((measurable_one.indicator hA).comp ((measurable_const_mul g).comp measurable_chart)).mul
        measurable_Dinv)] at h1
  have h3 := (ENNReal.mul_right_inj (cg_ne_zero g) ENNReal.ofReal_ne_top).1 h1
  rw [lintegral_indicator measurableSet_good, hHh, lintegral_indicator measurableSet_good] at h3
  exact h3

theorem isMulLeftInvariant_m : (m μ).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  ext A hA
  rw [Measure.map_apply (measurable_const_mul g) hA, m_apply μ hA,
    m_apply μ (measurable_const_mul g hA)]
  have : ∀ x : P, ((fun h : G => g * h) ⁻¹' A).indicator (1 : G → ℝ≥0∞) (chart x) =
      A.indicator 1 (g * chart x) := by
    intro x
    simp only [Set.indicator, mem_preimage, Pi.one_apply]
  simp_rw [this]
  exact setLIntegral_comp_mul_left μ g hA

theorem isFiniteMeasureOnCompacts_m : IsFiniteMeasureOnCompacts (m μ) := by
  refine ⟨fun C hC => ?_⟩
  rw [m_apply μ hC.measurableSet]
  by_cases hCe : C = ∅
  · subst hCe; simp

  have hne : C.Nonempty := Set.nonempty_iff_ne_empty.2 hCe
  obtain ⟨g₀, hg₀, hmin⟩ := hC.exists_isMinOn hne
    ((Units.continuous_val.matrix_det.norm).continuousOn (s := C))
  set δ : ℝ := ‖((g₀ : G) : Matrix (Fin 2) (Fin 2) F).det‖ with hδ
  have hδ0 : 0 < δ := norm_pos_iff.2 (Matrix.GeneralLinearGroup.det_ne_zero g₀)

  set Cf : Set P := (fun g : G => flat (g : Matrix (Fin 2) (Fin 2) F)) '' C with hCf
  have hCfc : IsCompact Cf := hC.image (continuous_flat.comp Units.continuous_val)
  have hbound : ∀ x : P, good.indicator (fun x => C.indicator (1 : G → ℝ≥0∞) (chart x) * Dinv x) x ≤
      Cf.indicator (fun _ => ENNReal.ofReal ((δ ^ 2)⁻¹)) x := by
    intro x
    by_cases hx : x ∈ good
    · rw [indicator_of_mem hx]
      by_cases hxC : chart x ∈ C
      · have hxCf : x ∈ Cf := by
          refine ⟨chart x, hxC, ?_⟩
          show flat ((chart x : G) : Matrix (Fin 2) (Fin 2) F) = x
          rw [coe_chart_of_mem hx, flat_mat]
        rw [indicator_of_mem hxC, indicator_of_mem hxCf, Pi.one_apply, one_mul]
        simp only [Dinv]
        apply ENNReal.ofReal_le_ofReal
        have hle : δ ≤ ‖(mat x).det‖ := by
          have := hmin hxC
          simp only [mem_setOf_eq] at this
          rw [coe_chart_of_mem hx] at this
          exact this
        have h1 : δ ^ 2 ≤ ‖(mat x).det‖ ^ 2 := by gcongr
        exact inv_anti₀ (by positivity) h1
      · rw [indicator_of_notMem hxC, zero_mul]; exact zero_le
    · rw [indicator_of_notMem hx]; exact zero_le
  calc ∫⁻ x in good, C.indicator (1 : G → ℝ≥0∞) (chart x) * Dinv x ∂π
      = ∫⁻ x, good.indicator (fun x => C.indicator (1 : G → ℝ≥0∞) (chart x) * Dinv x) x ∂π := by
        rw [lintegral_indicator measurableSet_good]
    _ ≤ ∫⁻ x, Cf.indicator (fun _ => ENNReal.ofReal ((δ ^ 2)⁻¹)) x ∂π := lintegral_mono hbound
    _ = ENNReal.ofReal ((δ ^ 2)⁻¹) * π Cf := lintegral_indicator_const hCfc.measurableSet _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCfc.measure_lt_top

theorem m_univ_ne_zero : m μ Set.univ ≠ 0 := by
  rw [m_apply μ MeasurableSet.univ]
  simp only [indicator_univ, Pi.one_apply, one_mul]
  intro h
  rw [← lintegral_indicator measurableSet_good,
    lintegral_eq_zero_iff (measurable_Dinv.indicator measurableSet_good)] at h

  have hpos : 0 < π good := isOpen_good.measure_pos π ⟨flat 1, by
    show (mat (flat (1 : Matrix (Fin 2) (Fin 2) F))).det ≠ 0
    rw [mat_flat, Matrix.det_one]; exact one_ne_zero⟩
  have hae : ∀ᵐ x ∂π, x ∉ good := by
    filter_upwards [h] with x hx
    intro hxg
    rw [Pi.zero_apply, indicator_of_mem hxg] at hx
    exact Dinv_ne_zero hxg hx
  rw [← measure_eq_zero_iff_ae_notMem] at hae
  exact absurd hae hpos.ne'

theorem main : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
    ∀ H : G → ℝ≥0∞, Measurable H →
      ∫⁻ g, H g ∂(AutomorphicForm.localHaar K v) = c * ∫⁻ x in good, H (chart x) * Dinv x ∂π := by
  haveI := isMulLeftInvariant_m μ
  haveI := isFiniteMeasureOnCompacts_m μ
  have heq := Measure.isMulLeftInvariant_eq_smul (m μ) (AutomorphicForm.localHaar K v)
  set c₀ : ℝ≥0 := (m μ).haarScalarFactor (AutomorphicForm.localHaar K v) with hc₀
  have hc₀0 : c₀ ≠ 0 := by
    intro h0
    apply m_univ_ne_zero μ
    rw [heq, h0]; simp
  refine ⟨(c₀ : ℝ≥0∞)⁻¹, ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top,
    ENNReal.inv_ne_top.2 (ENNReal.coe_ne_zero.2 hc₀0), fun H hH => ?_⟩
  rw [← lintegral_m μ hH, heq, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hc₀0) ENNReal.coe_ne_top, one_mul]

theorem integrand_eq (H : G → ℝ≥0∞) :
    ∫⁻ x in good, H (chart x) * Dinv x ∂π =
      ∫⁻ x : P, (if h : (mat x).det ≠ 0 then H (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) *
        ENNReal.ofReal ((‖(mat x).det‖ ^ 2)⁻¹) ∂π := by
  rw [← lintegral_indicator measurableSet_good]
  refine lintegral_congr fun x => ?_
  by_cases hx : (mat x).det ≠ 0
  · rw [indicator_of_mem (show x ∈ good from hx), dif_pos hx, chart_of_mem hx]; rfl
  · rw [indicator_of_notMem (show x ∉ good from hx), dif_neg hx, zero_mul]

end Main

end KcAdicGLHaar
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_localHaar_eq_mul_lintegral_pi_norm_det_inv_sq.KcAdicGLHaar"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_localHaar_eq_mul_lintegral_pi_norm_det_inv_sq.KcAdicGLHaar"

open KcAdicGLHaar in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ H : GL (Fin 2) (v.adicCompletion K) → ENNReal,
        Measurable[AutomorphicForm.localGLBorel K v] H →
        (letI := AutomorphicForm.localGLBorel K v
         ∫⁻ g, H g ∂(AutomorphicForm.localHaar K v)) =
          c * ∫⁻ x : Fin 4 → v.adicCompletion K,
            (if h : (!![x 0, x 1; x 2, x 3] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0 then
                H (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) *
              ENNReal.ofReal
                ((‖(!![x 0, x 1; x 2, x 3] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ ^ 2)⁻¹)
            ∂(Measure.pi fun _ : Fin 4 => μ) := by
  obtain ⟨c, hc0, hct, h⟩ := main (K := K) (v := v) μ
  refine ⟨c, hc0, hct, fun H hH => ?_⟩
  rw [h H hH, integrand_eq]
  rfl

end S_AutomorphicForm_exists_forall_lintegral_localHaar_eq_mul_lintegral_pi_norm_det_inv_sq
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_lintegral_localHaar_eq_mul_lintegral_pi_norm_det_inv_sq (solution)
