-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0085
-- name    : PNT_ZeroFree_433_0085
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:50:06.989045+00:00
-- url     : https://prove2.me/theorems/c2116c58-689d-4950-87df-1ff08f0cc003
-- title:
--   Zero-free region foundations: Eisenstein.FourierCoefficients [0085]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.FourierCoefficients
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/FourierCoefficients.lean#L82-L639

import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0084

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/FourierCoefficients.lean#L82-L639
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Eisenstein.FourierCoefficients
section
namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal

open ActualEisensteinCubic ConcreteTraceCRT

lemma breveE_embedding_div_traceLambda (n : O) :
    ShortDraftTrace.breveE (eisEmbedding n/eisLam)=1 := by
  rw [← ActualEisensteinCoordinates.eval_coords n,eisEmbedding_eval]
  exact ConcreteBreveE.breveE_period_coordinates _ _

def cuspFrequency (h : O) : ℂ := eisEmbedding h/(3*eisLam)

lemma cuspFrequency_period (h n : O) :
    ShortDraftTrace.breveE (cuspFrequency h*(3*eisEmbedding n))=1 := by
  have heq : cuspFrequency h*(3*eisEmbedding n)=eisEmbedding (h*n)/eisLam := by
    rw [cuspFrequency,map_mul]
    field_simp
  rw [heq]
  exact breveE_embedding_div_traceLambda (h*n)

lemma cuspFrequency_negative_period (h n : O) (z : ℂ) :
    ShortDraftTrace.breveE (-cuspFrequency h*(z+3*eisEmbedding n))=
      ShortDraftTrace.breveE (-cuspFrequency h*z) := by
  rw [mul_add,AddChar.map_add_eq_mul]
  have hp : ShortDraftTrace.breveE (-cuspFrequency h*(3*eisEmbedding n))=1 := by
    rw [neg_mul,AddChar.map_neg_eq_inv,cuspFrequency_period,inv_one]
  rw [hp,mul_one]

lemma trace_mul_integrable (f : ℂ → ℂ) (hf : Integrable f) (freq : ℂ) :
    Integrable (fun z => f z*ShortDraftTrace.breveE (-freq*z)) := by
  have hchar : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-freq*z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop
  refine hf.norm.mono' (hf.aestronglyMeasurable.mul hchar.aestronglyMeasurable) ?_
  exact Eventually.of_forall fun z => by simp only [norm_mul,breveE_norm,mul_one,le_refl]

lemma integrableOn_periodization (f : ℂ → ℂ) (hf : Integrable f) :
    IntegrableOn (fun z => ∑' n : O,f (z+3*eisEmbedding n)) periodDomain := by
  let : Countable O := latticeCoordEquiv.injective.countable
  have hm (n : O) : AEStronglyMeasurable (fun z => f (z+3*eisEmbedding n))
      (volume.restrict periodDomain) :=
    (hf.comp_add_right (3*eisEmbedding n)).aestronglyMeasurable.restrict
  refine ⟨AEStronglyMeasurable.tsum hm, ?_⟩
  change (∫⁻ z in periodDomain,‖∑' n : O,f (z+3*eisEmbedding n)‖ₑ)<⊤
  apply lt_of_le_of_lt (lintegral_mono fun z => enorm_tsum_le_tsum_enorm) _
  rw [lintegral_tsum (fun n => (hm n).enorm)]
  exact lt_top_iff_ne_top.mpr (periodization_lintegral_norm_ne_top f hf)

theorem integral_fourier_periodization (f : ℂ → ℂ) (hf : Integrable f) (h : O) :
    (∫ z in periodDomain,(∑' n : O,f (z+3*eisEmbedding n))*
      ShortDraftTrace.breveE (-cuspFrequency h*z))=
        ∫ z : ℂ,f z*ShortDraftTrace.breveE (-cuspFrequency h*z) := by
  have heq : (fun z : ℂ => (∑' n : O,f (z+3*eisEmbedding n))*
      ShortDraftTrace.breveE (-cuspFrequency h*z)) =
      (fun z : ℂ => ∑' n : O,f (z+3*eisEmbedding n)*
        ShortDraftTrace.breveE (-cuspFrequency h*(z+3*eisEmbedding n))) := by
    funext z
    simp only [cuspFrequency_negative_period,tsum_mul_right]
  rw [heq]
  exact integral_periodization _ (trace_mul_integrable f hf (cuspFrequency h))

end

section
open MeasureTheory Set Filter Module
open scoped BigOperators Classical ENNReal MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT

lemma continuous_inverse_upper_operator (v : ℝ) (hv : 0 < v) :
    Continuous (fun z : ℂ => rowOperator (upperSection z v hv)⁻¹) := by
  apply continuous_clm_apply.mpr
  intro u
  apply continuous_pi
  intro i
  simp only [rowOperator_apply,upperSection,
    Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  fin_cases i <;> simp only [] <;> fun_prop

lemma continuous_upper_rowBound (v : ℝ) (hv : 0 < v) :
    Continuous (fun z : ℂ => rowBound (upperSection z v hv)) :=
  continuous_const.mul (continuous_const.add (continuous_inverse_upper_operator v hv).norm)

lemma norm_mem_periodDomain (z : ℂ) (hz : z ∈ periodDomain) :
    ‖z‖ ≤ ∑ i : Fin 2, ‖periodBasis i‖ := by
  have heq := (ZSpan.fract_eq_self (b := periodBasis)).mpr hz
  simpa only [heq] using ZSpan.norm_fract_le periodBasis z

lemma exists_upper_rowBound (v : ℝ) (hv : 0 < v) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ periodDomain, rowBound (upperSection z v hv) ≤ C := by
  let R : ℝ := ∑ i : Fin 2, ‖periodBasis i‖
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℂ) R).bddAbove_image
    (continuous_upper_rowBound v hv).continuousOn
  refine ⟨max 1 C,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro z hz
  apply (hC ?_).trans (le_max_right _ _)
  exact ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz,rfl⟩

lemma continuous_upper_summand (v : ℝ) (hv : 0 < v) (s : ℂ) (x : CuspCosets) :
    Continuous (fun z : ℂ => summand (upperSection z v hv) s x) := by
  simp_rw [summand_upperSection]
  apply continuous_const.mul
  apply Continuous.cpow
  · apply Complex.continuous_ofReal.comp
    apply continuous_const.div
    · unfold heightDenominator
      fun_prop
    · intro z
      exact (heightDenominator_pos z v hv _ (embeddedRow_ne_zero x)).ne'
  · exact continuous_const
  · intro z
    apply Complex.ofReal_mem_slitPlane.mpr
    exact div_pos hv (heightDenominator_pos z v hv _ (embeddedRow_ne_zero x))

lemma upper_summable_majorant (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    ∃ M : CuspCosets → ℝ, Summable M ∧ (∀ x,0 ≤ M x) ∧
      ∀ z ∈ periodDomain, ∀ x, ‖summand (upperSection z v hv) s x‖ ≤ M x := by
  obtain ⟨C,hC,hbound⟩ := exists_upper_rowBound v hv
  refine ⟨fun x => C^(2*s.re)*‖rowCoordinates (cosetRow x)‖^(-(2*s.re)),?_,?_,?_⟩
  · have hsumm := summable_integer_four_rpow (2*s.re) (by linarith)
    have hinj : Function.Injective (fun x : CuspCosets => rowCoordinates (cosetRow x)) :=
      rowCoordinates_injective.comp cosetRow_injective
    exact (hsumm.comp_injective hinj).mul_left _
  · intro x
    positivity
  · intro z hz x
    apply (norm_summand_bound (upperSection z v hv) s (by linarith) x).trans
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (rowBound_pos _).le (hbound z hz) (by linarith)) (by positivity)

lemma periodDomain_finiteMeasure : IsFiniteMeasure (volume.restrict periodDomain) := by
  constructor
  rw [Measure.restrict_apply_univ,periodDomain_volume]
  exact ENNReal.ofReal_lt_top

theorem hasSum_integral_upperEisenstein (v : ℝ) (hv : 0 < v) (s freq : ℂ) (hs : 2 < s.re) :
    HasSum (fun x : CuspCosets => ∫ z in periodDomain,
      summand (upperSection z v hv) s x*ShortDraftTrace.breveE (-freq*z))
      (∫ z in periodDomain,upperEisenstein z v hv s*ShortDraftTrace.breveE (-freq*z)) := by
  let : Countable CuspCosets :=
    (rowCoordinates_injective.comp cosetRow_injective).countable
  let := periodDomain_finiteMeasure
  obtain ⟨M,hM,hMnonneg,hbound⟩ := upper_summable_majorant v hv s hs
  have hchar : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-freq*z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop
  have hsum := hasSum_integral_of_dominated_convergence
    («μ» := volume.restrict periodDomain)
    (fun (x : CuspCosets) (_ : ℂ) => M x)
    (fun x => ((continuous_upper_summand v hv s x).mul hchar).aestronglyMeasurable.restrict)
    (fun x => (ae_restrict_mem periodDomain_measurable).mono fun z hz => by
      simpa only [Pi.mul_apply,norm_mul,breveE_norm,mul_one] using hbound z hz x)
    (Eventually.of_forall fun _ => hM)
    (integrable_const (∑' x,M x))
    (Eventually.of_forall fun z => (summable_summand (upperSection z v hv) s hs).hasSum.mul_right
      (ShortDraftTrace.breveE (-freq*z)))
  exact hsum

theorem integral_upperEisenstein_eq_sum (v : ℝ) (hv : 0 < v) (s freq : ℂ) (hs : 2 < s.re) :
    (∫ z in periodDomain,upperEisenstein z v hv s*ShortDraftTrace.breveE (-freq*z))=
      ∑' x : CuspCosets,∫ z in periodDomain,
        summand (upperSection z v hv) s x*ShortDraftTrace.breveE (-freq*z) :=
  (hasSum_integral_upperEisenstein v hv s freq hs).tsum_eq.symm

end

section
open MeasureTheory Set Filter
open scoped BigOperators Classical

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

def shiftedHeightKernel (v : ℝ) (s b z : ℂ) : ℂ :=
  (v:ℂ)^(-s)*hyperbolicKernel s ((z+b)/(v:ℂ))

lemma shiftedHeightKernel_integrable (v : ℝ) (hv : 0 < v) (s b : ℂ) (hs : 1 < s.re) :
    Integrable (shiftedHeightKernel v s b) := by
  have h := ((hyperbolicKernel_integrable s hs).comp_smul (inv_ne_zero hv.ne')).comp_add_right b
  apply (h.const_mul ((v:ℂ)^(-s))).congr
  exact Eventually.of_forall fun z => by
    simp only [shiftedHeightKernel,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm]

lemma primitiveTerm_eq_shiftedHeightKernel (z : ℂ) (v : ℝ) (hv : 0 < v)
    (s : ℂ) (c d : O) (hc : c ≠ 0) :
    primitiveTerm z v s c d =
      (eisEmbedding (symbol c d)*(‖eisEmbedding c‖^2:ℝ) ^ (-s:ℂ))*
        shiftedHeightKernel v s (eisEmbedding d/eisEmbedding c) z := by
  have hc' := eisEmbedding_ne_zero hc
  have hnorm : 0 < ‖eisEmbedding c‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hc')
  have hfac : eisEmbedding c*z+eisEmbedding d =
      eisEmbedding c*(z+eisEmbedding d/eisEmbedding c) := by field_simp
  have heq : v/(‖eisEmbedding c*z+eisEmbedding d‖^2+‖eisEmbedding c‖^2*v^2) =
      ((‖eisEmbedding c‖^2*v)*(1+‖(z+eisEmbedding d/eisEmbedding c)/(v:ℂ)‖^2))⁻¹ := by
    rw [hfac,norm_mul,mul_pow,norm_div,Complex.norm_real,Real.norm_of_nonneg hv.le]
    field_simp
    ; ring
  unfold primitiveTerm shiftedHeightKernel hyperbolicKernel
  rw [heq,Complex.ofReal_inv,Complex.inv_cpow_ofReal_nonneg (by positivity),← Complex.cpow_neg]
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (mul_nonneg hnorm.le hv.le) (by positivity),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hnorm.le hv.le]
  ring

lemma primitiveTerm_integrable (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 1 < s.re)
    (c d : O) (hc : c ≠ 0) : Integrable (fun z => primitiveTerm z v s c d) := by
  simp_rw [primitiveTerm_eq_shiftedHeightKernel _ v hv s c d hc]
  exact (shiftedHeightKernel_integrable v hv s _ hs).const_mul _

lemma traceIntegral_translate (f : ℂ → ℂ) (b freq : ℂ) :
    (∫ z : ℂ,f (z+b)*ShortDraftTrace.breveE (-freq*z))=
      ShortDraftTrace.breveE (freq*b)*(∫ z : ℂ,f z*ShortDraftTrace.breveE (-freq*z)) := by
  have heq (z : ℂ) : f (z+b)*ShortDraftTrace.breveE (-freq*z)=
      ShortDraftTrace.breveE (freq*b)*(f (z+b)*ShortDraftTrace.breveE (-freq*(z+b))) := by
    rw [mul_left_comm (ShortDraftTrace.breveE (freq*b)),
      ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [heq]
  rw [integral_const_mul,integral_add_right_eq_self (fun z => f z*ShortDraftTrace.breveE (-freq*z)) b]

lemma traceIntegral_scale (v : ℝ) (hv : 0 < v) (s freq : ℂ) :
    (∫ z : ℂ,hyperbolicKernel s (z/(v:ℂ))*ShortDraftTrace.breveE (-freq*z))=
      (v:ℂ)^2*sourceFourierKernel s (freq*v) := by
  have heq (z : ℂ) : hyperbolicKernel s (z/(v:ℂ))*ShortDraftTrace.breveE (-freq*z)=
      (fun w : ℂ => hyperbolicKernel s w*ShortDraftTrace.breveE (-(freq*v)*w)) (v⁻¹ • z) := by
    simp only [Complex.real_smul,Complex.ofReal_inv]
    congr 2
    · ring
    · field_simp [Complex.ofReal_ne_zero.mpr hv.ne']
  simp_rw [heq]
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure ℂ)
    (fun w : ℂ => hyperbolicKernel s w*ShortDraftTrace.breveE (-(freq*v)*w)) hv.le
  simpa only [Complex.finrank_real_complex,Complex.real_smul,Complex.ofReal_pow,sourceFourierKernel] using h

lemma traceIntegral_shiftedHeightKernel (v : ℝ) (hv : 0 < v) (s b freq : ℂ) :
    (∫ z : ℂ,shiftedHeightKernel v s b z*ShortDraftTrace.breveE (-freq*z))=
      (v:ℂ)^(2-s)*ShortDraftTrace.breveE (freq*b)*sourceFourierKernel s (freq*v) := by
  simp only [shiftedHeightKernel,mul_assoc]
  rw [integral_const_mul,traceIntegral_translate (fun z => hyperbolicKernel s (z/(v:ℂ))) b freq,
    traceIntegral_scale v hv s freq]
  have hp : (v:ℂ)^(-s)*(v:ℂ)^2=(v:ℂ)^(2-s) := by
    rw [← Complex.cpow_natCast,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne')]
    congr 1
    ring
  calc
    _ = ((v:ℂ)^(-s)*(v:ℂ)^2)*ShortDraftTrace.breveE (freq*b)*sourceFourierKernel s (freq*v) := by ring
    _ = _ := by rw [hp]; ring

end

section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal Pointwise

open ActualEisensteinCubic ConcreteTraceCRT

lemma period_integral_translation (f : ℂ → ℂ)
    (hperiod : ∀ (n : O) (z : ℂ), f (z+3*eisEmbedding n)=f z) (b : ℂ) :
    (∫ z in periodDomain,f (b+z))=∫ z in periodDomain,f z := by
  have hperiod' (n : periodLattice) (z : ℂ) : f (n+ᵥz)=f z := by
    obtain ⟨m,rfl⟩ := periodEquiv.surjective n
    change f (3*eisEmbedding m+z)=f z
    simpa only [add_comm] using hperiod m z
  have hD := periodDomain_fundamental.vadd_of_comm b
  have heq := periodDomain_fundamental.setIntegral_eq hD hperiod'
  have hchange := (measurePreserving_add_left volume b).setIntegral_image_emb
    (measurableEmbedding_const_vadd b) f periodDomain
  exact hchange.symm.trans heq.symm

lemma breveE_quarter_eq_neg_one : ShortDraftTrace.breveE (1/4:ℂ)=-1 := by
  change Complex.exp (2*Real.pi*Complex.I*((1/4:ℂ)+starRingEnd ℂ (1/4:ℂ)))=-1
  norm_num only [map_div₀,map_one,map_ofNat]
  convert! Complex.exp_pi_mul_I using 1 ; congr 1 ; ring

lemma cuspFrequency_ne_zero (h : O) (hh : h ≠ 0) : cuspFrequency h ≠ 0 :=
  div_ne_zero (eisEmbedding_ne_zero hh) (mul_ne_zero (by norm_num) eisLam_ne_zero)

theorem integral_cusp_character (h : O) :
    (∫ z in periodDomain,ShortDraftTrace.breveE (-cuspFrequency h*z))=
      if h=0 then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0 := by
  by_cases hh : h=0
  · subst h
    simp only [cuspFrequency,map_zero,zero_div,neg_zero,zero_mul,
      AddChar.map_zero_eq_one,ite_true,setIntegral_const,measureReal_def,periodDomain_volume,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 9*Real.sqrt 3/2),Complex.real_smul,mul_one]
  · rw [if_neg hh]
    let freq := cuspFrequency h
    let b : ℂ := -(4*freq)⁻¹
    have hfreq : freq ≠ 0 := cuspFrequency_ne_zero h hh
    have harg : -freq*b=(1/4:ℂ) := by dsimp [b]; field_simp
    have hphase : ShortDraftTrace.breveE (-freq*b)=-1 := by rw [harg,breveE_quarter_eq_neg_one]
    have heq := period_integral_translation
      (fun z => ShortDraftTrace.breveE (-freq*z))
      (fun n z => cuspFrequency_negative_period h n z) b
    have hpoint (z : ℂ) : ShortDraftTrace.breveE (-freq*(b+z))=
        -ShortDraftTrace.breveE (-freq*z) := by
      rw [mul_add,AddChar.map_add_eq_mul,hphase,neg_one_mul]
    simp_rw [hpoint,integral_neg] at heq
    linear_combination (-1/2:ℂ)*heq

end

section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

def primitiveRowIntegral (v : ℝ) (s freq : ℂ) (c d : O) : ℂ :=
  ∫ z in periodDomain,primitiveTerm z v s c d*ShortDraftTrace.breveE (-freq*z)

lemma integral_summand_eq_primitiveRowIntegral (v : ℝ) (hv : 0 < v)
    (s freq : ℂ) (x : CuspCosets) :
    (∫ z in periodDomain,summand (upperSection z v hv) s x*ShortDraftTrace.breveE (-freq*z))=
      primitiveRowIntegral v s freq (cosetRow x 0) (cosetRow x 1) := by
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [summand_upperSection,inverse_cosetCharacter_eq_row_symbol]
    rfl

lemma hasSum_primitiveRowIntegrals (v : ℝ) (hv : 0 < v) (s freq : ℂ) (hs : 2 < s.re) :
    HasSum (fun p : Σ c : LevelLower,AdmissibleDenominator c.1 =>
      primitiveRowIntegral v s freq p.1.1 p.2.1)
      (∫ z in periodDomain,upperEisenstein z v hv s*ShortDraftTrace.breveE (-freq*z)) := by
  apply primitiveSigmaEquiv.hasSum_iff.mp
  apply primitiveRowEquiv.hasSum_iff.mp
  exact (hasSum_integral_upperEisenstein v hv s freq hs).congr_fun
    fun x => (integral_summand_eq_primitiveRowIntegral v hv s freq x).symm

lemma primitiveRowIntegral_sum_translate (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 1 < s.re)
    (h c d : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) (hd : (3:O) ∣ d-1) :
    (∑' n : O,primitiveRowIntegral v s (cuspFrequency h) c (d+3*c*n))=
      ∫ z : ℂ,primitiveTerm z v s c d*ShortDraftTrace.breveE (-cuspFrequency h*z) := by
  have hint := trace_mul_integrable (fun z => primitiveTerm z v s c d)
    (primitiveTerm_integrable v hv s hs c d hc) (cuspFrequency h)
  rw [integral_eq_period_integrals _ hint]
  apply tsum_congr
  intro n
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [primitiveTerm_shift z v s c d n hlevel hd,cuspFrequency_negative_period]

lemma primitiveTerm_fourier_integral (v : ℝ) (hv : 0 < v) (s freq : ℂ)
    (c d : O) (hc : c ≠ 0) :
    (∫ z : ℂ,primitiveTerm z v s c d*ShortDraftTrace.breveE (-freq*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (freq*v))*
        ((‖eisEmbedding c‖^2:ℝ):ℂ)^(-s)*
        (eisEmbedding (symbol c d)*ShortDraftTrace.breveE (freq*eisEmbedding d/eisEmbedding c)) := by
  simp_rw [primitiveTerm_eq_shiftedHeightKernel _ v hv s c d hc,mul_assoc]
  rw [integral_const_mul,integral_const_mul,traceIntegral_shiftedHeightKernel v hv s (eisEmbedding d/eisEmbedding c) freq]
  ring_nf

def arithmeticResidueSum (h c : O) : ℂ :=
  ∑' r : AdmissibleResidue c,eisEmbedding (symbol c (denominatorRep c r.1))*
    ShortDraftTrace.breveE (cuspFrequency h*eisEmbedding (denominatorRep c r.1)/eisEmbedding c)

lemma arithmeticResidueSum_finite (h c : O) (hc : c ≠ 0) :
    letI : Fintype (AdmissibleResidue c) := @Fintype.ofFinite _ (finite_admissibleResidue c hc)
    arithmeticResidueSum h c = ∑ r : AdmissibleResidue c,
      eisEmbedding (symbol c (denominatorRep c r.1))*
      ShortDraftTrace.breveE (cuspFrequency h*eisEmbedding (denominatorRep c r.1)/eisEmbedding c) := by
  let : Fintype (AdmissibleResidue c) := @Fintype.ofFinite _ (finite_admissibleResidue c hc)
  exact tsum_fintype _

lemma denominator_integral_formula (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re)
    (h : O) (c : LevelLower) (hc : c.1 ≠ 0) :
    (∑' d : AdmissibleDenominator c.1,primitiveRowIntegral v s (cuspFrequency h) c.1 d.1)=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
        ((‖eisEmbedding c.1‖^2:ℝ):ℂ)^(-s)*arithmeticResidueSum h c.1 := by
  have hsum : Summable (fun d : AdmissibleDenominator c.1 =>
      primitiveRowIntegral v s (cuspFrequency h) c.1 d.1) :=
    (hasSum_primitiveRowIntegrals v hv s (cuspFrequency h) hs).summable.sigma_factor c
  rw [denominator_sum_residues c.1 hc
    (fun d : O => primitiveRowIntegral v s (cuspFrequency h) c.1 d) hsum]
  calc
    _ = ∑' r : AdmissibleResidue c.1, ∫ z : ℂ,
        primitiveTerm z v s c.1 (denominatorRep c.1 r.1)*
          ShortDraftTrace.breveE (-cuspFrequency h*z) := by
      apply tsum_congr
      intro r
      exact primitiveRowIntegral_sum_translate v hv s (by linarith) h c.1
        (denominatorRep c.1 r.1) hc c.2 r.2.2
    _ = _ := by
      simp_rw [primitiveTerm_fourier_integral v hv s (cuspFrequency h) c.1 _ hc]
      exact tsum_mul_left

end

section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal Matrix

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

instance : DiscreteTopology periodLattice := by unfold periodLattice; infer_instance
instance : IsZLattice ℝ periodLattice := by unfold periodLattice; infer_instance

lemma summable_embedding_rpow (k : ℝ) (hk : k < -2) :
    Summable (fun n : O => ‖eisEmbedding n‖^k) := by
  have hrank : Module.finrank ℤ periodLattice=2 := by
    rw [ZLattice.rank ℝ periodLattice,Complex.finrank_real_complex]
  have hs := ZLattice.summable_norm_rpow periodLattice k (by rw [hrank]; norm_num; exact hk)
  have hcomp := periodEquiv.summable_iff.mpr hs
  have hscale := hcomp.mul_left (((3:ℝ)^k)⁻¹)
  apply hscale.congr
  intro n
  change ((3:ℝ)^k)⁻¹*‖(3:ℂ)*eisEmbedding n‖^k=‖eisEmbedding n‖^k
  rw [norm_mul,show ‖(3:ℂ)‖=(3:ℝ) by norm_num,
    Real.mul_rpow (by norm_num) (norm_nonneg _)]
  rw [← mul_assoc,inv_mul_cancel₀ (Real.rpow_pos_of_pos (by norm_num) k).ne',one_mul]

lemma norm_row_symbol (c d : O) (hc : (3:O) ∣ c) (hd : denominatorCondition c d) :
    ‖eisEmbedding (symbol c d)‖=1 := by
  let r : PrimitiveRow := ⟨![c,d],hd.1,hc,hd.2⟩
  let x := primitiveRowEquiv.symm r
  have heq : (cosetCharacter x)⁻¹=eisEmbedding (symbol c d) := by
    rw [inverse_cosetCharacter_eq_row_symbol]
    change eisEmbedding (symbol (cosetRow (primitiveRowEquiv.symm r) 0)
      (cosetRow (primitiveRowEquiv.symm r) 1))=eisEmbedding (symbol c d)
    rw [primitiveRowEquiv_symm_row r]
    rfl
  rw [← heq,norm_inv,norm_cosetCharacter,inv_one]

lemma norm_arithmeticResidueSum_le (h c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) :
    ‖arithmeticResidueSum h c‖ ≤ 9*‖eisEmbedding c‖^2 := by
  let : Finite (DenominatorResidue c) := finite_quotient_span (mul_ne_zero (by norm_num) hc)
  let : Fintype (DenominatorResidue c) := Fintype.ofFinite _
  let : Fintype (AdmissibleResidue c) := Fintype.ofFinite _
  have hcard : (Fintype.card (DenominatorResidue c):ℝ)=9*‖eisEmbedding c‖^2 := by
    have hh := eisEmbedding_norm_sq_eq_absNorm_span (3*c)
    simp only [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card] at hh
    rw [← hh,map_mul,map_ofNat,norm_mul,mul_pow]
    norm_num
  rw [arithmeticResidueSum,tsum_fintype]
  calc
    _ ≤ ∑ r : AdmissibleResidue c, ‖eisEmbedding (symbol c (denominatorRep c r.1))*
        ShortDraftTrace.breveE (cuspFrequency h*eisEmbedding (denominatorRep c r.1)/eisEmbedding c)‖ :=
      norm_sum_le _ _
    _ = (Fintype.card (AdmissibleResidue c):ℝ) := by
      have hr (r : AdmissibleResidue c) :
          ‖eisEmbedding (symbol c (denominatorRep c r.1))‖=1 :=
        norm_row_symbol c (denominatorRep c r.1) hlevel r.2
      simp only [norm_mul,hr,breveE_norm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    _ ≤ (Fintype.card (DenominatorResidue c):ℝ) := by
      exact_mod_cast Fintype.card_subtype_le (fun r => denominatorCondition c (denominatorRep c r))
    _ = _ := hcard

def arithmeticDirichletTerm (s : ℂ) (h : O) (c : LevelLower) : ℂ :=
  if c.1=0 then 0 else ((‖eisEmbedding c.1‖^2:ℝ):ℂ)^(-s)*arithmeticResidueSum h c.1

lemma norm_arithmeticDirichletTerm_le (s : ℂ) (h : O) (c : LevelLower) :
    ‖arithmeticDirichletTerm s h c‖ ≤ 9*‖eisEmbedding c.1‖^(2-2*s.re) := by
  unfold arithmeticDirichletTerm
  split_ifs with hc
  · simp only [norm_zero]
    positivity
  · have hn : 0 < ‖eisEmbedding c.1‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero hc)
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (sq_pos_of_pos hn)]
    change (‖eisEmbedding c.1‖^2)^(-s.re)*‖arithmeticResidueSum h c.1‖ ≤ _
    calc
      _ ≤ (‖eisEmbedding c.1‖^2)^(-s.re)*(9*‖eisEmbedding c.1‖^2) :=
        mul_le_mul_of_nonneg_left (norm_arithmeticResidueSum_le h c.1 hc c.2) (by positivity)
      _ = _ := by
        rw [← Real.rpow_natCast_mul hn.le 2 (-s.re)]
        rw [show 2-2*s.re=2+2*(-s.re) by ring,Real.rpow_add hn]
        norm_num only [Nat.cast_ofNat,Real.rpow_two]
        ring

theorem arithmeticDirichletTerm_summable_norm (s : ℂ) (hs : 2 < s.re) (h : O) :
    Summable (fun c : LevelLower => ‖arithmeticDirichletTerm s h c‖) := by
  have hbase := (summable_embedding_rpow (2-2*s.re) (by linarith)).subtype
    (fun c : O => (3:O) ∣ c)
  exact (hbase.mul_left 9).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_arithmeticDirichletTerm_le s h)

def arithmeticDirichletSeries (s : ℂ) (h : O) : ℂ :=
  ∑' c : LevelLower,arithmeticDirichletTerm s h c

def scatteringCoefficient (s : ℂ) (h : O) : ℂ :=
  arithmeticDirichletSeries s h/((9*Real.sqrt 3/2:ℝ):ℂ)

end

open MeasureTheory Set Filter
open scoped BigOperators Classical

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

lemma zero_lower_integral (v : ℝ) (s : ℂ) (h : O) :
    (∑' d : AdmissibleDenominator 0,primitiveRowIntegral v s (cuspFrequency h) 0 d.1)=
      (v:ℂ)^s*(if h=0 then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0) := by
  let d0 : AdmissibleDenominator 0 := ⟨1,isCoprime_one_right,by simp⟩
  rw [tsum_eq_single d0]
  · simp only [d0,primitiveRowIntegral,primitiveTerm,map_zero,map_one,zero_mul,zero_add,
      norm_one,norm_zero,one_pow,zero_pow (by decide : (2:ℕ) ≠ 0),add_zero,
      div_one,symbol_one,map_one]
    rw [integral_const_mul,integral_cusp_character,one_mul]
  · intro d hd
    exact False.elim (hd (Subtype.ext (denominator_zero_unique d)))

lemma integral_upperEisenstein_arithmetic (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) (h : O) :
    (∫ z in periodDomain,upperEisenstein z v hv s*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      (v:ℂ)^s*(if h=0 then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0)+
        ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*arithmeticDirichletSeries s h := by
  let c0 : LevelLower := ⟨0,dvd_zero _⟩
  let F (c : LevelLower) := ∑' d : AdmissibleDenominator c.1,
    primitiveRowIntegral v s (cuspFrequency h) c.1 d.1
  have hsum := hasSum_primitiveRowIntegrals v hv s (cuspFrequency h) hs
  have hF : Summable F := hsum.summable.sigma
  have hzero : F c0=(v:ℂ)^s*(if h=0 then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0) :=
    zero_lower_integral v s h
  calc
    _ = ∑' c : LevelLower,F c := hsum.tsum_eq.symm.trans hsum.summable.tsum_sigma
    _ = F c0+∑' c : LevelLower,if c=c0 then 0 else F c := hF.tsum_eq_add_tsum_ite c0
    _ = _ := by
      rw [hzero]
      congr 1
      rw [arithmeticDirichletSeries,← tsum_mul_left]
      apply tsum_congr
      intro c
      by_cases hc : c.1=0
      · have heq : c=c0 := Subtype.ext hc
        simp only [heq,ite_true,arithmeticDirichletTerm,c0,mul_zero]
      · have heq : c ≠ c0 := fun heq => hc (congrArg Subtype.val heq)
        rw [if_neg heq]
        change (∑' d : AdmissibleDenominator c.1,
          primitiveRowIntegral v s (cuspFrequency h) c.1 d.1)=_
        rw [denominator_integral_formula v hv s hs h c hc]
        simp only [arithmeticDirichletTerm,if_neg hc]
        ring

def eisensteinFourierCoefficient (v : ℝ) (hv : 0 < v) (s : ℂ) (h : O) : ℂ :=
  (∫ z in periodDomain,upperEisenstein z v hv s*ShortDraftTrace.breveE (-cuspFrequency h*z))/
    ((9*Real.sqrt 3/2:ℝ):ℂ)

theorem eisensteinFourierCoefficient_formula (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) (h : O) :
    eisensteinFourierCoefficient v hv s h=(if h=0 then (v:ℂ)^s else 0)+
      (v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v)*scatteringCoefficient s h := by
  rw [eisensteinFourierCoefficient,integral_upperEisenstein_arithmetic v hv s hs h,scatteringCoefficient]
  have hvol : ((9*Real.sqrt 3/2:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  split_ifs <;> field_simp ; ring

theorem eisensteinConstantCoefficient_formula (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    eisensteinFourierCoefficient v hv s 0=(v:ℂ)^s+
      (v:ℂ)^(2-s)*((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0 := by
  rw [eisensteinFourierCoefficient_formula v hv s hs 0]
  simp only [ite_true,cuspFrequency,map_zero,zero_div,zero_mul]
  rw [sourceFourierKernel_zero s (by linarith)]

theorem eisensteinFourierCoefficient_bessel (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re)
    (h : O) (hh : h ≠ 0) :
    eisensteinFourierCoefficient v hv s h=
      (v:ℂ)^(2-s)*
        ((2*Real.pi:ℂ)/Complex.Gamma s *
          (2*Real.pi*‖cuspFrequency h*v‖:ℂ)^(s-1)*
          schlafliBesselK (s-1) (4*Real.pi*‖cuspFrequency h*v‖))*
        scatteringCoefficient s h := by
  rw [eisensteinFourierCoefficient_formula v hv s hs h,if_neg hh,zero_add]
  rw [sourceFourierKernel_bessel s (cuspFrequency h*v) (by linarith)
    (mul_ne_zero (cuspFrequency_ne_zero h hh) (Complex.ofReal_ne_zero.mpr hv.ne'))]

end CubicEisenstein

end

end OAI

end


