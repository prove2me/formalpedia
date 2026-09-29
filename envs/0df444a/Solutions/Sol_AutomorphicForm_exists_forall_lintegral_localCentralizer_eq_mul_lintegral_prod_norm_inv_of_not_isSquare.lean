-- Prove2me | solution 1 for AutomorphicForm.exists_forall_lintegral_localCentralizer_eq_mul_lintegral_prod_norm_inv_of_not_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/e07e6fb9-21f1-5923-9103-9f8d97c905ad

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Theorems.Thm_NumberField_AdicCompletion_map_matrix_mulVec_pi_eq_smul_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_lintegral_localCentralizer_eq_mul_lintegral_prod_norm_inv_of_not_isSquare
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory Set Function Matrix
open scoped ENNReal NNReal Classical

noncomputable section

namespace KcAdicTorusHaar

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

local notation "F" => v.adicCompletion K
local notation "Q" => v.adicCompletion K × v.adicCompletion K
local notation "G" => GL (Fin 2) (v.adicCompletion K)

section Torus

variable (d : v.adicCompletion K)

def tm (q : Q) : Matrix (Fin 2) (Fin 2) F := !![q.1, q.2; d * q.2, q.1]

def nf (q : Q) : F := q.1 ^ 2 - d * q.2 ^ 2

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem det_tm (q : Q) : (tm d q).det = nf d q := by
  simp [tm, nf, Matrix.det_fin_two_of]; ring

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem continuous_tm : Continuous (tm d : Q → Matrix (Fin 2) (Fin 2) F) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact continuous_fst
  · exact continuous_snd
  · exact continuous_const.mul continuous_snd
  · exact continuous_fst

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem continuous_nf : Continuous (nf d : Q → F) := by
  unfold nf; fun_prop

variable {d}

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in

theorem nf_eq_zero_iff (hd : ¬ IsSquare d) (q : Q) : nf d q = 0 ↔ q = 0 := by
  constructor
  · intro h
    simp only [nf, sub_eq_zero] at h
    by_cases h2 : q.2 = 0
    · have h1 : q.1 = 0 := by
        rw [h2] at h; simpa using h
      exact Prod.ext h1 h2
    · exfalso
      apply hd
      refine ⟨q.1 / q.2, ?_⟩
      field_simp
      linear_combination -h
  · rintro rfl
    simp [nf]

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem d_ne_zero (hd : ¬ IsSquare d) : d ≠ 0 := by
  rintro rfl; exact hd ⟨0, by simp⟩

private theorem _root_.KcAdicTorusHaar.mem_centralizer_iff (hd : ¬ IsSquare d) {p₀ r₀ : F} (hr₀ : r₀ ≠ 0) {u : G}
    (hu : (u : Matrix (Fin 2) (Fin 2) F) = !![p₀, r₀; d * r₀, p₀]) (g : G) :
    g ∈ AutomorphicForm.localCentralizer K v u ↔
      ((g : Matrix (Fin 2) (Fin 2) F) 1 0 = d * (g : Matrix (Fin 2) (Fin 2) F) 0 1 ∧
        (g : Matrix (Fin 2) (Fin 2) F) 1 1 = (g : Matrix (Fin 2) (Fin 2) F) 0 0) := by
  rw [AutomorphicForm.localCentralizer, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [Units.ext_iff, Units.val_mul, Units.val_mul, hu]
  have hd0 := d_ne_zero hd
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
    constructor
    · have : r₀ * ((g : Matrix (Fin 2) (Fin 2) F) 1 0 - d * (g : Matrix (Fin 2) (Fin 2) F) 0 1) = 0 := by
        linear_combination h00
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hr₀
      · exact sub_eq_zero.1 h
    · have : r₀ * ((g : Matrix (Fin 2) (Fin 2) F) 1 1 - (g : Matrix (Fin 2) (Fin 2) F) 0 0) = 0 := by
        linear_combination h01
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hr₀
      · exact sub_eq_zero.1 h
  · rintro ⟨h10, h11⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h11] <;> ring

p2m_export "KcAdicTorusHaar" "mem_centralizer_iff"

theorem coe_eq_tm_of_mem (hd : ¬ IsSquare d) {p₀ r₀ : F} (hr₀ : r₀ ≠ 0) {u : G}
    (hu : (u : Matrix (Fin 2) (Fin 2) F) = !![p₀, r₀; d * r₀, p₀]) {g : G}
    (hg : g ∈ AutomorphicForm.localCentralizer K v u) :
    (g : Matrix (Fin 2) (Fin 2) F) =
      tm d ((g : Matrix (Fin 2) (Fin 2) F) 0 0, (g : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  obtain ⟨h10, h11⟩ := (mem_centralizer_iff hd hr₀ hu g).1 hg
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tm, h10, h11]

theorem tm_mem (hd : ¬ IsSquare d) {p₀ r₀ : F} (hr₀ : r₀ ≠ 0) {u : G}
    (hu : (u : Matrix (Fin 2) (Fin 2) F) = !![p₀, r₀; d * r₀, p₀]) {q : Q} (h : (tm d q).det ≠ 0) :
    Matrix.GeneralLinearGroup.mkOfDetNeZero (tm d q) h ∈ AutomorphicForm.localCentralizer K v u := by
  rw [mem_centralizer_iff hd hr₀ hu]
  constructor <;> rfl

end Torus

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
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel
  AutomorphicForm.localCentralizerBorel

theorem borelSpace_localCentralizer (γ : G) :
    @BorelSpace (AutomorphicForm.localCentralizer K v γ) _ (AutomorphicForm.localCentralizerBorel K v γ) :=
  @BorelSpace.mk _ _ (AutomorphicForm.localCentralizerBorel K v γ) rfl

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem isClosed_localCentralizer (γ : G) :
    IsClosed ((AutomorphicForm.localCentralizer K v γ : Subgroup G) : Set G) :=
  Set.isClosed_centralizer _

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem locallyCompactSpace_localCentralizer (γ : G) :
    LocallyCompactSpace (AutomorphicForm.localCentralizer K v γ) :=
  (isClosed_localCentralizer γ).isClosedEmbedding_subtypeVal.locallyCompactSpace

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem secondCountableTopology_localCentralizer (γ : G) :
    SecondCountableTopology (AutomorphicForm.localCentralizer K v γ) :=
  TopologicalSpace.Subtype.secondCountableTopology _

attribute [local instance] borelSpace_localCentralizer locallyCompactSpace_localCentralizer
  secondCountableTopology_localCentralizer

theorem continuous_GL_of {X : Type*} [TopologicalSpace X] {f : X → G}
    (hval : ∀ i j, Continuous fun x => ((f x : G) : Matrix (Fin 2) (Fin 2) F) i j)
    (hinv : ∀ i j, Continuous fun x => (((f x)⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) i j) :
    Continuous f := by
  rw [Units.continuous_iff]
  exact ⟨continuous_matrix fun i j => hval i j, continuous_matrix fun i j => hinv i j⟩

section Chart

variable {d : v.adicCompletion K} (hd : ¬ IsSquare d) {p₀ r₀ : v.adicCompletion K} (hr₀ : r₀ ≠ 0)
  {u : GL (Fin 2) (v.adicCompletion K)}
  (hu : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![p₀, r₀; d * r₀, p₀])

local notation "T" => AutomorphicForm.localCentralizer K v u

def good (d : v.adicCompletion K) : Set Q := {q | (tm d q).det ≠ 0}

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem isOpen_good : IsOpen (good d : Set Q) :=
  isOpen_ne_fun (continuous_tm d).matrix_det continuous_const

theorem measurableSet_good : MeasurableSet (good d : Set Q) := isOpen_good.measurableSet

include hd hr₀ hu in

def chart (q : Q) : T :=
  if h : (tm d q).det ≠ 0 then ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (tm d q) h, tm_mem hd hr₀ hu h⟩
  else 1

theorem chart_of_mem {q : Q} (h : (tm d q).det ≠ 0) :
    chart hd hr₀ hu q = ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (tm d q) h, tm_mem hd hr₀ hu h⟩ := by
  simp [chart, h]

theorem coe_chart_of_mem {q : Q} (h : (tm d q).det ≠ 0) :
    (((chart hd hr₀ hu q : T) : G) : Matrix (Fin 2) (Fin 2) F) = tm d q := by
  rw [chart_of_mem hd hr₀ hu h]; rfl

def coord (t : T) : Q := (((t : G) : Matrix (Fin 2) (Fin 2) F) 0 0, ((t : G) : Matrix (Fin 2) (Fin 2) F) 0 1)

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem continuous_coord : Continuous (coord : T → Q) :=
  ((Units.continuous_val.matrix_elem 0 0).comp continuous_subtype_val).prodMk
    ((Units.continuous_val.matrix_elem 0 1).comp continuous_subtype_val)

theorem chart_coord (t : T) : chart hd hr₀ hu (coord t) = t := by
  have hmat : (((t : G)) : Matrix (Fin 2) (Fin 2) F) = tm d (coord t) := coe_eq_tm_of_mem hd hr₀ hu t.2
  have h : (tm d (coord t)).det ≠ 0 := by
    rw [← hmat]; exact Matrix.GeneralLinearGroup.det_ne_zero _
  apply Subtype.ext
  apply Units.ext
  rw [coe_chart_of_mem hd hr₀ hu h, hmat]

theorem continuous_chart_restrict : Continuous ((good d).domRestrict (chart hd hr₀ hu : Q → T)) := by
  have hdet : Continuous fun q : (good d : Set Q) => (tm d (q : Q)).det :=
    (continuous_tm d).matrix_det.comp continuous_subtype_val
  have hdet0 : ∀ q : (good d : Set Q), (tm d (q : Q)).det ≠ 0 := fun q => q.2
  have hent : ∀ i j, Continuous fun q : (good d : Set Q) => tm d (q : Q) i j := fun i j =>
    ((continuous_tm d).matrix_elem i j).comp continuous_subtype_val
  have hG : Continuous fun q : (good d : Set Q) => (((good d).domRestrict (chart hd hr₀ hu) q : T) : G) := by
    refine continuous_GL_of (fun i j => ?_) (fun i j => ?_)
    · have : (fun q : (good d : Set Q) => ((((good d).domRestrict (chart hd hr₀ hu) q : T) : G) :
          Matrix (Fin 2) (Fin 2) F) i j) = fun q : (good d : Set Q) => tm d (q : Q) i j := by
        funext q; rw [Set.domRestrict_apply, coe_chart_of_mem hd hr₀ hu q.2]
      rw [this]; exact hent i j
    · have : (fun q : (good d : Set Q) =>
          (((((good d).domRestrict (chart hd hr₀ hu) q : T) : G)⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) i j)
          = fun q : (good d : Set Q) => ((tm d (q : Q)).det)⁻¹ * (tm d (q : Q)).adjugate i j := by
        funext q
        rw [Set.domRestrict_apply, Matrix.coe_units_inv, coe_chart_of_mem hd hr₀ hu q.2,
          Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
      rw [this]
      refine (hdet.inv₀ hdet0).mul ?_
      exact ((continuous_tm d).comp continuous_subtype_val).matrix_adjugate.matrix_elem i j
  have : (good d).domRestrict (chart hd hr₀ hu : Q → T) =
      fun q => ⟨(((good d).domRestrict (chart hd hr₀ hu) q : T) : G), ((good d).domRestrict (chart hd hr₀ hu) q).2⟩ := by
    funext q; rfl
  rw [this]
  exact hG.subtype_mk _

theorem measurable_chart : Measurable (chart hd hr₀ hu : Q → T) := by
  refine measurable_of_restrict_of_restrict_compl (measurableSet_good (d := d)) ?_ ?_
  · exact (continuous_chart_restrict hd hr₀ hu).measurable
  · have : ((good d)ᶜ : Set Q).domRestrict (chart hd hr₀ hu : Q → T) = fun _ => 1 := by
      funext q
      have hq : ¬ ((tm d (q : Q)).det ≠ 0) := q.2
      simp [Set.domRestrict_apply, chart, hq]
    rw [this]; exact measurable_const

variable (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

local notation "μ²" => Measure.prod μ μ

def Ninv (d : v.adicCompletion K) (q : Q) : ℝ≥0∞ := ENNReal.ofReal ‖(tm d q).det‖⁻¹

theorem measurable_Ninv : Measurable (Ninv d : Q → ℝ≥0∞) :=
  ENNReal.measurable_ofReal.comp ((continuous_tm d).matrix_det.norm.measurable.inv)

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem Ninv_ne_zero {q : Q} (hq : q ∈ good d) : Ninv d q ≠ 0 := by
  simp only [Ninv, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  have : 0 < ‖(tm d q).det‖ := norm_pos_iff.2 hq
  positivity

def m : Measure T := Measure.map (chart hd hr₀ hu) (((μ²).restrict (good d)).withDensity (Ninv d))

theorem lintegral_m {H : T → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ t, H t ∂(m hd hr₀ hu μ) = ∫⁻ q in good d, H (chart hd hr₀ hu q) * Ninv d q ∂μ² := by
  rw [m, lintegral_map hH (measurable_chart hd hr₀ hu)]
  rw [show (fun a => H (chart hd hr₀ hu a)) = H ∘ chart hd hr₀ hu from rfl,
    lintegral_withDensity_eq_lintegral_mul _ measurable_Ninv (hH.comp (measurable_chart hd hr₀ hu))]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, Function.comp_apply, mul_comm]

theorem m_apply {A : Set T} (hA : MeasurableSet A) :
    m hd hr₀ hu μ A = ∫⁻ q in good d, A.indicator 1 (chart hd hr₀ hu q) * Ninv d q ∂μ² := by
  rw [← lintegral_indicator_one hA, lintegral_m hd hr₀ hu μ (measurable_one.indicator hA)]

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in

theorem tm_mul_tm (c q : Q) :
    tm d c * tm d q = tm d (c.1 * q.1 + d * c.2 * q.2, c.2 * q.1 + c.1 * q.2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

def Ls (d : v.adicCompletion K) (c : Q) (q : Q) : Q := (c.1 * q.1 + d * c.2 * q.2, c.2 * q.1 + c.1 * q.2)

def Ms (d : v.adicCompletion K) (c : Q) : Matrix (Fin 2) (Fin 2) F := !![c.1, d * c.2; c.2, c.1]

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem det_Ms (c : Q) : (Ms d c).det = nf d c := by
  simp [Ms, nf, Matrix.det_fin_two_of]; ring

omit [BorelSpace (v.adicCompletion K)] in
theorem Ls_eq (c : Q) : (Ls d c : Q → Q) =
    (MeasurableEquiv.finTwoArrow : (Fin 2 → F) ≃ᵐ Q) ∘ (fun x : Fin 2 → F => (Ms d c).mulVec x) ∘
      (MeasurableEquiv.finTwoArrow : (Fin 2 → F) ≃ᵐ Q).symm := by
  funext q
  simp [Ls, Ms, MeasurableEquiv.finTwoArrow, dotProduct, Fin.sum_univ_two]

theorem measurable_Ls (c : Q) : Measurable (Ls d c : Q → Q) :=
  ((measurable_fst.const_mul c.1).add (measurable_snd.const_mul (d * c.2))).prodMk
    ((measurable_fst.const_mul c.2).add (measurable_snd.const_mul c.1))

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem nf_Ls (c q : Q) : nf d (Ls d c q) = nf d c * nf d q := by
  simp only [nf, Ls]; ring

theorem map_Ls {c : Q} (hc : nf d c ≠ 0) :
    Measure.map (Ls d c) μ² = ENNReal.ofReal ‖nf d c‖⁻¹ • μ² := by
  set e : (Fin 2 → F) ≃ᵐ Q := MeasurableEquiv.finTwoArrow with he
  have hmp : MeasurePreserving e (Measure.pi fun _ : Fin 2 => μ) μ² := measurePreserving_finTwoArrow μ
  have hdet : (Ms d c).det ≠ 0 := by rw [det_Ms]; exact hc
  have hL := NumberField.AdicCompletion.map_matrix_mulVec_pi_eq_smul_pi K v μ (Ms d c) hdet
  rw [det_Ms] at hL
  have hmv : Measurable fun x : Fin 2 → F => (Ms d c).mulVec x :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  rw [Ls_eq, ← he]
  rw [show (⇑e ∘ (fun x : Fin 2 → F => (Ms d c).mulVec x) ∘ ⇑e.symm) =
      (⇑e ∘ fun x : Fin 2 → F => (Ms d c).mulVec x) ∘ ⇑e.symm from rfl,
    ← Measure.map_map (e.measurable.comp hmv) e.symm.measurable,
    ← Measure.map_map e.measurable hmv]
  have h1 : Measure.map e.symm μ² = Measure.pi fun _ : Fin 2 => μ := hmp.symm.map_eq
  rw [h1, hL, Measure.map_smul, hmp.map_eq]

theorem chart_Ls (s : T) {q : Q} (hq : q ∈ good d) :
    chart hd hr₀ hu (Ls d (coord s) q) = s * chart hd hr₀ hu q := by
  have hs : (((s : G)) : Matrix (Fin 2) (Fin 2) F) = tm d (coord s) := coe_eq_tm_of_mem hd hr₀ hu s.2
  have hnf : nf d (coord s) ≠ 0 := by
    rw [← det_tm, ← hs]; exact Matrix.GeneralLinearGroup.det_ne_zero _
  have hdet : (tm d (Ls d (coord s) q)).det ≠ 0 := by
    rw [det_tm, nf_Ls]; exact mul_ne_zero hnf (by rw [← det_tm]; exact hq)
  apply Subtype.ext
  apply Units.ext
  show (((chart hd hr₀ hu (Ls d (coord s) q) : T) : G) : Matrix (Fin 2) (Fin 2) F) =
    ((s : G) : Matrix (Fin 2) (Fin 2) F) * (((chart hd hr₀ hu q : T) : G) : Matrix (Fin 2) (Fin 2) F)
  rw [coe_chart_of_mem hd hr₀ hu hdet, coe_chart_of_mem hd hr₀ hu hq, hs, tm_mul_tm]
  rfl

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem mem_good_Ls_iff {c : Q} (hc : nf d c ≠ 0) (q : Q) : Ls d c q ∈ good d ↔ q ∈ good d := by
  simp only [good, mem_setOf_eq, det_tm, nf_Ls]
  exact ⟨fun h hq => h (by rw [hq, mul_zero]), fun h => mul_ne_zero hc h⟩

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem Ninv_Ls (c q : Q) : Ninv d (Ls d c q) = ENNReal.ofReal ‖nf d c‖⁻¹ * Ninv d q := by
  simp only [Ninv, det_tm, nf_Ls, norm_mul, mul_inv]
  rw [ENNReal.ofReal_mul (by positivity)]

theorem setLIntegral_comp_mul_left (s : T) {A : Set T} (hA : MeasurableSet A) :
    ∫⁻ q in good d, A.indicator 1 (s * chart hd hr₀ hu q) * Ninv d q ∂μ² =
      ∫⁻ q in good d, A.indicator 1 (chart hd hr₀ hu q) * Ninv d q ∂μ² := by
  set c : Q := coord s with hcdef
  have hs : (((s : G)) : Matrix (Fin 2) (Fin 2) F) = tm d c := coe_eq_tm_of_mem hd hr₀ hu s.2
  have hnf : nf d c ≠ 0 := by
    rw [← det_tm, ← hs]; exact Matrix.GeneralLinearGroup.det_ne_zero _
  set cg : ℝ≥0∞ := ENNReal.ofReal ‖nf d c‖⁻¹ with hcg
  have hcg0 : cg ≠ 0 := by
    simp only [hcg, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have : 0 < ‖nf d c‖ := norm_pos_iff.2 hnf
    positivity
  have hmap := map_Ls (d := d) μ hnf
  set Hh : Q → ℝ≥0∞ := (good d).indicator fun q => A.indicator 1 (chart hd hr₀ hu q) * Ninv d q with hHh
  have hHm : Measurable Hh := by
    refine Measurable.indicator ?_ measurableSet_good
    exact ((measurable_one.indicator hA).comp (measurable_chart hd hr₀ hu)).mul measurable_Ninv
  have h1 : ∫⁻ q, Hh (Ls d c q) ∂μ² = cg * ∫⁻ q, Hh q ∂μ² := by
    have hlm : ∫⁻ q, Hh q ∂(Measure.map (Ls d c) μ²) = ∫⁻ q, Hh (Ls d c q) ∂μ² :=
      lintegral_map hHm (measurable_Ls c)
    rw [hmap, lintegral_smul_measure, smul_eq_mul] at hlm
    exact hlm.symm
  have h2 : ∀ q : Q, Hh (Ls d c q) =
      cg * (good d).indicator (fun q => A.indicator 1 (s * chart hd hr₀ hu q) * Ninv d q) q := by
    intro q
    by_cases hq : q ∈ good d
    · rw [hHh, indicator_of_mem ((mem_good_Ls_iff hnf q).2 hq), indicator_of_mem hq, hcdef,
        chart_Ls hd hr₀ hu s hq, Ninv_Ls, ← hcdef, ← hcg]
      ring
    · rw [hHh, indicator_of_notMem (fun h => hq ((mem_good_Ls_iff hnf q).1 h)),
        indicator_of_notMem hq, mul_zero]
  simp_rw [h2] at h1
  rw [lintegral_const_mul _ (by
      refine Measurable.indicator ?_ measurableSet_good
      exact ((measurable_one.indicator hA).comp
        ((measurable_const_mul s).comp (measurable_chart hd hr₀ hu))).mul measurable_Ninv)] at h1
  have h3 := (ENNReal.mul_right_inj hcg0 ENNReal.ofReal_ne_top).1 h1
  rw [lintegral_indicator measurableSet_good, hHh, lintegral_indicator measurableSet_good] at h3
  exact h3

theorem isMulLeftInvariant_m : (m hd hr₀ hu μ).IsMulLeftInvariant := by
  refine ⟨fun s => ?_⟩
  ext A hA
  rw [Measure.map_apply (measurable_const_mul s) hA, m_apply hd hr₀ hu μ hA,
    m_apply hd hr₀ hu μ (measurable_const_mul s hA)]
  have : ∀ q : Q, ((fun h : T => s * h) ⁻¹' A).indicator (1 : T → ℝ≥0∞) (chart hd hr₀ hu q) =
      A.indicator 1 (s * chart hd hr₀ hu q) := by
    intro q
    simp only [Set.indicator, mem_preimage, Pi.one_apply]
  simp_rw [this]
  exact setLIntegral_comp_mul_left hd hr₀ hu μ s hA

theorem isFiniteMeasureOnCompacts_m : IsFiniteMeasureOnCompacts (m hd hr₀ hu μ) := by
  refine ⟨fun C hC => ?_⟩
  rw [m_apply hd hr₀ hu μ hC.measurableSet]
  by_cases hCe : C = ∅
  · subst hCe; simp
  have hne : C.Nonempty := Set.nonempty_iff_ne_empty.2 hCe
  obtain ⟨t₀, ht₀, hmin⟩ := hC.exists_isMinOn hne
    (((Units.continuous_val.matrix_det.norm).comp continuous_subtype_val).continuousOn (s := C))
  set δ : ℝ := ‖(((t₀ : T) : G) : Matrix (Fin 2) (Fin 2) F).det‖ with hδ
  have hδ0 : 0 < δ := norm_pos_iff.2 (Matrix.GeneralLinearGroup.det_ne_zero _)
  set Cf : Set Q := coord '' C with hCf
  have hCfc : IsCompact Cf := hC.image continuous_coord
  have hbound : ∀ q : Q, (good d).indicator (fun q => C.indicator (1 : T → ℝ≥0∞) (chart hd hr₀ hu q) * Ninv d q) q ≤
      Cf.indicator (fun _ => ENNReal.ofReal δ⁻¹) q := by
    intro q
    by_cases hq : q ∈ good d
    · rw [indicator_of_mem hq]
      by_cases hqC : chart hd hr₀ hu q ∈ C
      · have hqCf : q ∈ Cf := by
          refine ⟨chart hd hr₀ hu q, hqC, ?_⟩
          show coord (chart hd hr₀ hu q) = q
          simp only [coord, coe_chart_of_mem hd hr₀ hu hq, tm]
          simp
        rw [indicator_of_mem hqC, indicator_of_mem hqCf, Pi.one_apply, one_mul]
        simp only [Ninv]
        apply ENNReal.ofReal_le_ofReal
        have hle : δ ≤ ‖(tm d q).det‖ := by
          have := hmin hqC
          simp only [mem_setOf_eq, Function.comp_apply] at this
          rw [coe_chart_of_mem hd hr₀ hu hq] at this
          exact this
        exact inv_anti₀ hδ0 hle
      · rw [indicator_of_notMem hqC, zero_mul]; exact zero_le
    · rw [indicator_of_notMem hq]; exact zero_le
  calc ∫⁻ q in good d, C.indicator (1 : T → ℝ≥0∞) (chart hd hr₀ hu q) * Ninv d q ∂μ²
      = ∫⁻ q, (good d).indicator (fun q => C.indicator (1 : T → ℝ≥0∞) (chart hd hr₀ hu q) * Ninv d q) q ∂μ² := by
        rw [lintegral_indicator measurableSet_good]
    _ ≤ ∫⁻ q, Cf.indicator (fun _ => ENNReal.ofReal δ⁻¹) q ∂μ² := lintegral_mono hbound
    _ = ENNReal.ofReal δ⁻¹ * μ² Cf := lintegral_indicator_const hCfc.measurableSet _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCfc.measure_lt_top

theorem m_univ_ne_zero : m hd hr₀ hu μ Set.univ ≠ 0 := by
  rw [m_apply hd hr₀ hu μ MeasurableSet.univ]
  simp only [indicator_univ, Pi.one_apply, one_mul]
  intro h
  rw [← lintegral_indicator measurableSet_good,
    lintegral_eq_zero_iff (measurable_Ninv.indicator measurableSet_good)] at h
  have hpos : 0 < μ² (good d) := isOpen_good.measure_pos μ² ⟨(1, 0), by
    show (tm d ((1 : F), (0 : F))).det ≠ 0
    rw [det_tm]; simp [nf]⟩
  have hae : ∀ᵐ q ∂μ², q ∉ good d := by
    filter_upwards [h] with q hq
    intro hqg
    rw [Pi.zero_apply, indicator_of_mem hqg] at hq
    exact Ninv_ne_zero hqg hq
  rw [← measure_eq_zero_iff_ae_notMem] at hae
  exact absurd hae hpos.ne'

theorem main (τ : Measure T) [τ.IsHaarMeasure] : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
    ∀ H : T → ℝ≥0∞, Measurable H →
      ∫⁻ t, H t ∂τ = c * ∫⁻ q in good d, H (chart hd hr₀ hu q) * Ninv d q ∂μ² := by
  haveI := isMulLeftInvariant_m hd hr₀ hu μ
  haveI := isFiniteMeasureOnCompacts_m hd hr₀ hu μ
  have heq := Measure.isMulLeftInvariant_eq_smul (m hd hr₀ hu μ) τ
  set c₀ : ℝ≥0 := (m hd hr₀ hu μ).haarScalarFactor τ with hc₀
  have hc₀0 : c₀ ≠ 0 := by
    intro h0
    apply m_univ_ne_zero hd hr₀ hu μ
    rw [heq, h0]; simp
  refine ⟨(c₀ : ℝ≥0∞)⁻¹, ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top,
    ENNReal.inv_ne_top.2 (ENNReal.coe_ne_zero.2 hc₀0), fun H hH => ?_⟩
  rw [← lintegral_m hd hr₀ hu μ hH, heq, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hc₀0) ENNReal.coe_ne_top, one_mul]

theorem integrand_eq (H : G → ℝ≥0∞) :
    ∫⁻ q in good d, H ((chart hd hr₀ hu q : T) : G) * Ninv d q ∂μ² =
      ∫⁻ q : Q, (if h : (tm d q).det ≠ 0 then H (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) *
        ENNReal.ofReal ‖q.1 ^ 2 - d * q.2 ^ 2‖⁻¹ ∂μ² := by
  rw [← lintegral_indicator measurableSet_good]
  refine lintegral_congr fun q => ?_
  by_cases hq : (tm d q).det ≠ 0
  · rw [indicator_of_mem (show q ∈ good d from hq), dif_pos hq, chart_of_mem hd hr₀ hu hq, Ninv, det_tm]
    rfl
  · rw [indicator_of_notMem (show q ∉ good d from hq), dif_neg hq, zero_mul]

end Chart

end KcAdicTorusHaar

end

open KcAdicTorusHaar in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (d : v.adicCompletion K) (hd : ¬ IsSquare d) (p₀ r₀ : v.adicCompletion K) (hr₀ : r₀ ≠ 0)
    (u : GL (Fin 2) (v.adicCompletion K))
    (hu : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![p₀, r₀; d * r₀, p₀])
    (τ : @Measure (AutomorphicForm.localCentralizer K v u) (AutomorphicForm.localCentralizerBorel K v u))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v u) τ) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ H : GL (Fin 2) (v.adicCompletion K) → ENNReal,
        Measurable[AutomorphicForm.localGLBorel K v] H →
        (letI := AutomorphicForm.localCentralizerBorel K v u
         ∫⁻ t, H (t : GL (Fin 2) (v.adicCompletion K)) ∂τ) =
          c * ∫⁻ q : v.adicCompletion K × v.adicCompletion K,
            (if h : (!![q.1, q.2; d * q.2, q.1] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0 then
                H (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) *
              ENNReal.ofReal ‖q.1 ^ 2 - d * q.2 ^ 2‖⁻¹ ∂(μ.prod μ) := by
  letI := AutomorphicForm.localCentralizerBorel K v u
  letI := AutomorphicForm.localGLBorel K v
  haveI := hτ
  haveI := borelSpace_localCentralizer (K := K) (v := v) u
  haveI := AutomorphicForm.borelSpace_localGLBorel K v
  obtain ⟨c, hc0, hct, h⟩ := main hd hr₀ hu μ τ
  refine ⟨c, hc0, hct, fun H hH => ?_⟩
  have hHm : Measurable fun t : AutomorphicForm.localCentralizer K v u => H (t : GL (Fin 2) (v.adicCompletion K)) :=
    hH.comp continuous_subtype_val.measurable
  rw [h _ hHm, integrand_eq hd hr₀ hu μ H]
  rfl

end S_AutomorphicForm_exists_forall_lintegral_localCentralizer_eq_mul_lintegral_prod_norm_inv_of_not_isSquare
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_lintegral_localCentralizer_eq_mul_lintegral_prod_norm_inv_of_not_isSquare (solution)
