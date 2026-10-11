-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0075
-- name    : PNT_ZeroFree_433_0075
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T21:22:49.572257+00:00
-- url     : https://prove2.me/theorems/77bf2abb-523c-4c10-bdfd-7ac8e13722d0
-- title:
--   Zero-free region foundations: Eisenstein.HyperbolicSpace [0075]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/HyperbolicSpace.lean#L80-L613

import Definitions.Def_PNT_ZeroFree_433_0074

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/HyperbolicSpace.lean#L80-L613
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
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

section
open scoped BigOperators Classical MatrixGroups Matrix

section
open CubicKubota

def compactSubgroup : Subgroup (SL(2,ℂ)) where
  carrier := {k | (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ}
  one_mem' := (Matrix.unitaryGroup (Fin 2) ℂ).one_mem
  mul_mem' := by
    intro a b ha hb
    exact (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem ha hb
  inv_mem' := by
    intro k hk
    have hinv : (k⁻¹ : SL(2,ℂ)) * k = 1 := inv_mul_cancel k
    have hmat : ((k⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
        (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 := congrArg
          (fun a : SL(2,ℂ) => (a : Matrix (Fin 2) (Fin 2) ℂ)) hinv
    have he := Matrix.left_inv_eq_left_inv hmat (Matrix.mem_unitaryGroup_iff'.mp hk)
    change ((k⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ
    rw [he]
    exact Unitary.star_mem hk

abbrev HyperbolicSpace := SL(2,ℂ) ⧸ compactSubgroup

def hyperbolicEisenstein (s : ℂ) : HyperbolicSpace → ℂ :=
  Quotient.lift (fun g => eisenstein g s) (by
    intro g h hgh
    have hk : g⁻¹*h ∈ compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h = g*(g⁻¹*h) := by group
    rw [hh]
    exact (eisenstein_right_unitary g (g⁻¹*h) s hk).symm)

@[simp] lemma hyperbolicEisenstein_mk (s : ℂ) (g : SL(2,ℂ)) :
    hyperbolicEisenstein s (g : HyperbolicSpace) = eisenstein g s := rfl

theorem hyperbolicEisenstein_automorphy (M : levelThree) (s : ℂ) (hs : 2 < s.re)
    (w : HyperbolicSpace) :
    hyperbolicEisenstein s (complexMatrix M • w) =
      complexCharacter M * hyperbolicEisenstein s w := by
  induction w using Quotient.inductionOn with | _ g =>
    exact eisenstein_automorphy M g s hs

def upperPoint (z : ℂ) (v : ℝ) (hv : 0 < v) : HyperbolicSpace :=
  (upperSection z v hv : HyperbolicSpace)

lemma hyperbolicEisenstein_upperPoint (s : ℂ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    hyperbolicEisenstein s (upperPoint z v hv) = upperEisenstein z v hv s := rfl

def complexBottomRow (g : SL(2,ℂ)) : Fin 2 → ℂ := g 1

lemma complexBottomRow_mul (g h : SL(2,ℂ)) :
    complexBottomRow (g*h) = rowOperator h (complexBottomRow g) := by
  funext j
  simp only [complexBottomRow, rowOperator_apply, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Matrix.vecMul, dotProduct]

lemma complexBottomRow_ne_zero (g : SL(2,ℂ)) : complexBottomRow g ≠ 0 := by
  intro hz
  have hc : g 1 0 = 0 := congrFun hz 0
  have hd : g 1 1 = 0 := congrFun hz 1
  have h : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  simp only [hc, hd, mul_zero, sub_zero] at h
  exact zero_ne_one h

def liftedHeight (g : SL(2,ℂ)) : ℝ := (rowEnergy (complexBottomRow g))⁻¹

lemma liftedHeight_pos (g : SL(2,ℂ)) : 0 < liftedHeight g :=
  inv_pos.mpr (rowEnergy_pos _ (complexBottomRow_ne_zero g))

lemma liftedHeight_right_unitary (g k : SL(2,ℂ)) (hk : k ∈ compactSubgroup) :
    liftedHeight (g*k) = liftedHeight g := by
  simp only [liftedHeight, complexBottomRow_mul, rowEnergy_unitary k hk]

def hyperbolicHeight : HyperbolicSpace → ℝ :=
  Quotient.lift liftedHeight (by
    intro g h hgh
    have hk : g⁻¹*h ∈ compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h = g*(g⁻¹*h) := by group
    rw [hh]
    exact (liftedHeight_right_unitary g (g⁻¹*h) hk).symm)

@[simp] lemma hyperbolicHeight_mk (g : SL(2,ℂ)) :
    hyperbolicHeight (g : HyperbolicSpace) = liftedHeight g := rfl

lemma hyperbolicHeight_pos (w : HyperbolicSpace) : 0 < hyperbolicHeight w := by
  induction w using Quotient.inductionOn with | _ g => exact liftedHeight_pos g

theorem hyperbolicHeight_action_upperPoint (g : SL(2,ℂ)) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    hyperbolicHeight (g • upperPoint z v hv) =
      v / (‖g 1 0*z + g 1 1‖ ^ 2 + ‖g 1 0‖ ^ 2 * v ^ 2) := by
  change liftedHeight (g * upperSection z v hv) = _
  rw [liftedHeight, complexBottomRow_mul, rowEnergy_upperSection, inv_div]
  rfl

def cosetHeight (x : CuspCosets) : HyperbolicSpace → ℝ :=
  Quotient.lift (fun g : SL(2,ℂ) => (rowEnergy (rowOperator g (embeddedRow x)))⁻¹) (by
    intro g h hgh
    have hk : g⁻¹*h ∈ compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h = g*(g⁻¹*h) := by group
    rw [hh, ← rowOperator_mul, rowEnergy_unitary (g⁻¹*h) hk])

lemma cosetHeight_cosetOf (M : levelThree) (w : HyperbolicSpace) :
    cosetHeight (cosetOf M) w = hyperbolicHeight (complexMatrix M • w) := by
  induction w using Quotient.inductionOn with | _ g =>
    change (rowEnergy (rowOperator g (embeddedRow (cosetOf M))))⁻¹ =
      liftedHeight (complexMatrix M * g)
    rw [liftedHeight, complexBottomRow_mul]
    rfl

theorem hyperbolicEisenstein_eq_height_series (s : ℂ) (w : HyperbolicSpace) :
    hyperbolicEisenstein s w = ∑' x : CuspCosets,
      (cosetCharacter x)⁻¹ * (cosetHeight x w : ℂ) ^ s := by
  induction w using Quotient.inductionOn with | _ g =>
    apply tsum_congr
    intro x
    change (cosetCharacter x)⁻¹ *
      (rowEnergy (rowOperator g (embeddedRow x)) : ℂ) ^ (-s) =
      (cosetCharacter x)⁻¹ * ((rowEnergy (rowOperator g (embeddedRow x)))⁻¹ : ℝ) ^ s
    rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (rowEnergy_nonneg _),
      Complex.cpow_neg]

theorem height_series_summable_norm (s : ℂ) (hs : 2 < s.re) (w : HyperbolicSpace) :
    Summable (fun x : CuspCosets =>
      ‖(cosetCharacter x)⁻¹ * (cosetHeight x w : ℂ) ^ s‖) := by
  induction w using Quotient.inductionOn with | _ g =>
    apply (summable_norm_summand g s hs).congr
    intro x
    congr 1
    change (cosetCharacter x)⁻¹ *
      (rowEnergy (rowOperator g (embeddedRow x)) : ℂ) ^ (-s) =
      (cosetCharacter x)⁻¹ * ((rowEnergy (rowOperator g (embeddedRow x)))⁻¹ : ℝ) ^ s
    rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (rowEnergy_nonneg _),
      Complex.cpow_neg]

theorem hyperbolicEisenstein_differentiableOn (w : HyperbolicSpace) :
    DifferentiableOn ℂ (fun s : ℂ => hyperbolicEisenstein s w) {s : ℂ | 2 < s.re} := by
  induction w using Quotient.inductionOn with | _ g =>
    exact eisenstein_differentiableOn g

end

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

def upperTranslation (a : O) : levelThree := by
  let M : SL(2,O) := ⟨!![1, 3*a; 0, 1], by simp⟩
  refine ⟨M, ?_⟩
  change Matrix.SpecialLinearGroup.map (n := Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3 : O)})) M = 1
  have h3 : Ideal.Quotient.mk (Ideal.span {(3 : O)}) (3 : O) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  apply Subtype.ext
  funext i j
  change Ideal.Quotient.mk (Ideal.span {(3 : O)}) ((!![(1 : O), 3*a; 0, 1]) i j) =
    (1 : Matrix (Fin 2) (Fin 2) (O ⧸ Ideal.span {(3 : O)})) i j
  fin_cases i <;> fin_cases j <;> simp [h3, map_mul]

lemma complexCharacter_upperTranslation (a : O) : complexCharacter (upperTranslation a) = 1 := by
  change eisEmbedding (value (upperTranslation a)) = 1
  rw [value_zero_lower_left _ (by rfl), map_one]

lemma upperTranslation_section (a : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    complexMatrix (upperTranslation a) * upperSection z v hv =
      upperSection (z + 3*eisEmbedding a) v hv := by
  apply Subtype.ext
  funext i j
  change (((!![(1 : O), 3*a; 0, 1]).map eisEmbedding) *
    !![(Real.sqrt v : ℂ), z/(Real.sqrt v : ℂ); 0, (Real.sqrt v : ℂ)⁻¹]) i j =
    (!![(Real.sqrt v : ℂ), (z+3*eisEmbedding a)/(Real.sqrt v : ℂ);
      0, (Real.sqrt v : ℂ)⁻¹]) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, map_mul] ;
    norm_num only [map_ofNat] ; ring

theorem upperEisenstein_periodic (a : O) (z : ℂ) (v : ℝ) (hv : 0 < v)
    (s : ℂ) (hs : 2 < s.re) :
    upperEisenstein (z + 3*eisEmbedding a) v hv s = upperEisenstein z v hv s := by
  unfold upperEisenstein
  rw [← upperTranslation_section, eisenstein_automorphy _ _ _ hs,
    complexCharacter_upperTranslation, one_mul]

end

open MeasureTheory Set Filter
open scoped BigOperators Classical

lemma integral_radial_sq (f : ℝ → ℂ) :
    (∫ z : ℂ, f (‖z‖ ^ 2)) = (Real.pi : ℂ) * ∫ t : ℝ in Set.Ioi 0, f t := by
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  have hpolar := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => f (r^2))
  have hsub := integral_comp_rpow_Ioi (E := ℂ) f (p := 2) (by norm_num)
  norm_num [Real.rpow_two, Real.rpow_one] at hsub
  simp only [Complex.finrank_real_complex, hball, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Complex.real_smul, ] at hpolar hsub
  rw [hpolar]
  rw [← hsub]
  rw [show (fun x : ℝ => (2:ℂ)*x*f (x^2)) =
      (fun x : ℝ => (2:ℂ)*(x*f (x^2))) by funext x; ring, integral_const_mul]
  ring

lemma integrable_radial_sq_iff (f : ℝ → ℂ) :
    Integrable (fun z : ℂ => f (‖z‖ ^ 2)) ↔ IntegrableOn f (Set.Ioi 0) := by
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ) (f := fun r : ℝ => f (r^2))]
  have h := integrableOn_Ioi_comp_rpow_iff' (E := ℂ) f (p := 2) (by norm_num)
  simpa only [Complex.finrank_real_complex, Nat.reduceSub, pow_one,
    show (2:ℝ)-1=1 by norm_num, Real.rpow_one, Real.rpow_two] using h

lemma add_one_image_Ioi : (fun x : ℝ => x+1) '' Set.Ioi 0 = Set.Ioi 1 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    simp only [Set.mem_Ioi] at *
    linarith
  · intro hy
    refine ⟨y-1, ?_, by ring⟩
    simp only [Set.mem_Ioi] at *
    linarith

lemma integrable_add_one_Ioi_iff (f : ℝ → ℂ) :
    IntegrableOn (fun x : ℝ => f (x+1)) (Set.Ioi 0) ↔ IntegrableOn f (Set.Ioi 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

lemma integral_add_one_Ioi (f : ℝ → ℂ) :
    (∫ x : ℝ in Set.Ioi 0, f (x+1)) = ∫ x : ℝ in Set.Ioi 1, f x := by
  have h := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

def hyperbolicKernel (s : ℂ) (z : ℂ) : ℂ := ((1+‖z‖^2 : ℝ) : ℂ) ^ (-s)

lemma hyperbolicKernel_integrable (s : ℂ) (hs : 1 < s.re) :
    Integrable (hyperbolicKernel s) := by
  unfold hyperbolicKernel
  rw [integrable_radial_sq_iff (fun t : ℝ => ((1+t : ℝ) : ℂ)^(-s))]
  have h := (integrable_add_one_Ioi_iff (fun x : ℝ => (x : ℂ)^(-s))).mpr
    (integrableOn_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) (by norm_num : (0:ℝ)<1))
  simpa only [add_comm] using h

theorem integral_hyperbolicKernel (s : ℂ) (hs : 1 < s.re) :
    (∫ z : ℂ, hyperbolicKernel s z) = (Real.pi : ℂ) / (s-1) := by
  unfold hyperbolicKernel
  rw [integral_radial_sq (fun t : ℝ => ((1+t : ℝ) : ℂ)^(-s))]
  simp_rw [add_comm (1:ℝ)]
  rw [integral_add_one_Ioi (fun t : ℝ => (t : ℂ)^(-s))]
  rw [integral_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) (by norm_num : (0:ℝ)<1)]
  simp only [Complex.ofReal_one, Complex.one_cpow]
  have hn : (-s+1)⁻¹ = -(s-1)⁻¹ := by
    rw [show -s+1=-(s-1) by ring, inv_neg]
  simp only [div_eq_mul_inv, hn]
  ring

open MeasureTheory Set Filter
open scoped BigOperators Classical FourierTransform RealInnerProductSpace

lemma breveE_norm (z : ℂ) : ‖ShortDraftTrace.breveE z‖ = 1 := by
  change ‖Complex.exp (2 * Real.pi * Complex.I * (z + starRingEnd ℂ z))‖ = 1
  rw [Complex.norm_exp]
  have hre : (2 * Real.pi * Complex.I * (z + starRingEnd ℂ z)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

def sourceFourierKernel (s freq : ℂ) : ℂ :=
  ∫ z : ℂ, hyperbolicKernel s z * ShortDraftTrace.breveE (-freq*z)

lemma sourceFourierKernel_integrable (s freq : ℂ) (hs : 1 < s.re) :
    Integrable (fun z : ℂ => hyperbolicKernel s z * ShortDraftTrace.breveE (-freq*z)) := by
  apply (hyperbolicKernel_integrable s hs).norm.mono'
  · have hker : Continuous (hyperbolicKernel s) := by
      unfold hyperbolicKernel
      apply Continuous.cpow
      · fun_prop
      · exact continuous_const
      · intro z
        exact Complex.ofReal_mem_slitPlane.mpr (by positivity)
    have hchar : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-freq*z)) := by
      change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
        ((-freq*z)+starRingEnd ℂ (-freq*z))))
      fun_prop
    exact (hker.mul hchar).aestronglyMeasurable
  · exact Eventually.of_forall (fun z => by simp only [norm_mul, breveE_norm, mul_one, le_refl])

lemma sourceFourierKernel_zero (s : ℂ) (hs : 1 < s.re) :
    sourceFourierKernel s 0 = (Real.pi : ℂ)/(s-1) := by
  simpa only [sourceFourierKernel, neg_zero, zero_mul, AddChar.map_zero_eq_one, mul_one]
    using integral_hyperbolicKernel s hs

lemma sourceFrequency_inner (z freq : ℂ) : inner ℝ z (2*starRingEnd ℂ freq) = 2*(freq*z).re := by
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
  change ((2 * starRingEnd ℂ freq) * starRingEnd ℂ z).re = _
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma traceIntegral_eq_fourier (f : ℂ → ℂ) (freq : ℂ) :
    (∫ z : ℂ, f z * ShortDraftTrace.breveE (-freq*z)) = 𝓕 f (2*starRingEnd ℂ freq) := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [sourceFrequency_inner]
    change f z *
      Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))) = _
    simp only [smul_eq_mul]
    rw [mul_comm (f z)]
    congr 1
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring)

lemma sourceFourierKernel_eq_fourier (s freq : ℂ) :
    sourceFourierKernel s freq = 𝓕 (hyperbolicKernel s) (2*starRingEnd ℂ freq) :=
  traceIntegral_eq_fourier (hyperbolicKernel s) freq

lemma hyperbolicKernel_laplace (s : ℂ) (hs : 0 < s.re) (z : ℂ) :
    hyperbolicKernel s z * Complex.Gamma s =
      ∫ t : ℝ in Set.Ioi 0, (t : ℂ)^(s-1) *
        Complex.exp (-((1+‖z‖^2 : ℝ) : ℂ) * t) := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs
    (by positivity : 0 < 1+‖z‖^2)
  simp only [neg_mul]
  rw [h]
  congr 1
  rw [hyperbolicKernel, one_div, Complex.inv_cpow_ofReal_nonneg (by positivity),
    Complex.cpow_neg]

lemma source_gaussian_fourier (t : ℝ) (ht : 0 < t) (freq : ℂ) :
    𝓕 (fun z : ℂ => Complex.exp (-(t : ℂ)*‖z‖^2)) (2*starRingEnd ℂ freq) =
      (Real.pi : ℂ)/t * Complex.exp (-(4*Real.pi^2*‖freq‖^2 : ℝ)/t) := by
  rw [fourier_gaussian_innerProductSpace (by simpa using ht)]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat, div_self (by norm_num : (2:ℂ)≠0),
    Complex.cpow_one, norm_mul, Complex.norm_conj, Complex.norm_ofNat]
  congr 2
  push_cast
  ring

def gaussianMixture (s freq : ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  (t : ℂ)^(s-1) * Complex.exp (-t) *
    Complex.exp (-(t : ℂ)*‖z‖^2) * ShortDraftTrace.breveE (-freq*z)

lemma norm_gaussianMixture (s freq : ℂ) (t : ℝ) (ht : 0 < t) (z : ℂ) :
    ‖gaussianMixture s freq t z‖ =
      t ^ (s.re-1) * Real.exp (-t) * Real.exp (-t*‖z‖^2) := by
  simp only [gaussianMixture, norm_mul, breveE_norm, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re,
    Complex.norm_exp, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, ← Complex.ofReal_pow, Complex.neg_im, neg_zero, zero_mul, sub_zero]

lemma gaussianMixture_slice_integrable (s freq : ℂ) (t : ℝ) (ht : 0 < t) :
    Integrable (gaussianMixture s freq t) := by
  have hg : Integrable (fun z : ℂ => Complex.exp (-(t : ℂ)*‖z‖^2)) := by
    simpa only [zero_mul, add_zero] using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (by simpa using ht : 0 < (t : ℂ).re) 0 (0 : ℂ)
  apply ((hg.const_mul ((t : ℂ)^(s-1)*Complex.exp (-t))).norm).mono'
  · unfold gaussianMixture
    change AEStronglyMeasurable (fun z : ℂ => (t : ℂ)^(s-1)*Complex.exp (-t)*
      Complex.exp (-(t : ℂ)*‖z‖^2) *
      Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop
  · exact Eventually.of_forall fun z => by
      simp only [gaussianMixture, norm_mul, breveE_norm, mul_one, le_refl]

lemma integral_norm_gaussianMixture (s freq : ℂ) (t : ℝ) (ht : 0 < t) :
    (∫ z : ℂ, ‖gaussianMixture s freq t z‖) =
      Real.pi * (Real.exp (-t)*t^(s.re-2)) := by
  simp_rw [norm_gaussianMixture s freq t ht]
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm ht]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat, div_self (by norm_num : (2:ℝ)≠0),
    Real.rpow_one]
  have hp : t^(s.re-1)/t = t^(s.re-2) := by
    calc
      t^(s.re-1)/t = t^(s.re-1)/t^(1:ℝ) := by rw [Real.rpow_one]
      _ = t^((s.re-1)-1) := (Real.rpow_sub ht _ _).symm
      _ = _ := by congr 1; ring
  calc
    t^(s.re-1)*Real.exp (-t)*(Real.pi/t) = Real.pi*(Real.exp (-t)*(t^(s.re-1)/t)) := by ring
    _ = _ := by rw [hp]

theorem gaussianMixture_integrable (s freq : ℂ) (hs : 1 < s.re) :
    Integrable (fun p : ℝ × ℂ => gaussianMixture s freq p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℂ => gaussianMixture s freq p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
    unfold gaussianMixture
    change AEStronglyMeasurable (fun p : ℝ × ℂ =>
      (p.1 : ℂ)^(s-1)*Complex.exp (-p.1)*Complex.exp (-(p.1 : ℂ)*‖p.2‖^2)*
      Complex.exp (2*Real.pi*Complex.I*((-freq*p.2)+starRingEnd ℂ (-freq*p.2)))) _
    fun_prop
  apply (integrable_prod_iff hmeas).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact gaussianMixture_slice_integrable s freq t ht
  · have hgamma := (Real.GammaIntegral_convergent (by linarith : 0 < s.re-1)).const_mul Real.pi
    apply hgamma.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [integral_norm_gaussianMixture s freq t ht]
    congr 2
    ring_nf

open MeasureTheory Set Filter
open scoped BigOperators Classical FourierTransform RealInnerProductSpace

lemma gaussianMixture_laplace_form (s freq : ℂ) (t : ℝ) (z : ℂ) :
    gaussianMixture s freq t z =
      ((t : ℂ)^(s-1) * Complex.exp (-((1+‖z‖^2 : ℝ) : ℂ)*t)) *
        ShortDraftTrace.breveE (-freq*z) := by
  have he : Complex.exp (-(t : ℂ))*Complex.exp (-(t : ℂ)*‖z‖^2) =
      Complex.exp (-((1+‖z‖^2 : ℝ) : ℂ)*t) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (t : ℂ)^(s-1) * (Complex.exp (-(t : ℂ))*Complex.exp (-(t : ℂ)*‖z‖^2)) *
        ShortDraftTrace.breveE (-freq*z) := by unfold gaussianMixture; ring
    _ = _ := by rw [he]

lemma integral_gaussianMixture_t (s freq : ℂ) (hs : 0 < s.re) (z : ℂ) :
    (∫ t : ℝ in Set.Ioi 0, gaussianMixture s freq t z) =
      (hyperbolicKernel s z * Complex.Gamma s)*ShortDraftTrace.breveE (-freq*z) := by
  simp_rw [gaussianMixture_laplace_form]
  rw [integral_mul_const, ← hyperbolicKernel_laplace s hs z]

lemma integral_gaussianMixture_z (s freq : ℂ) (t : ℝ) (ht : 0 < t) :
    (∫ z : ℂ, gaussianMixture s freq t z) =
      (Real.pi : ℂ) * ((t : ℂ)^(s-2) *
        Complex.exp (-(t : ℂ) - (4*Real.pi^2*‖freq‖^2 : ℝ)/t)) := by
  have hfac : (fun z : ℂ => gaussianMixture s freq t z) =
      (fun z : ℂ => ((t : ℂ)^(s-1)*Complex.exp (-t))*
        (Complex.exp (-(t : ℂ)*‖z‖^2)*ShortDraftTrace.breveE (-freq*z))) := by
    funext z
    unfold gaussianMixture
    ring
  rw [hfac, integral_const_mul, traceIntegral_eq_fourier, source_gaussian_fourier t ht freq]
  have hp : (t : ℂ)^(s-1)/(t : ℂ) = (t : ℂ)^(s-2) := by
    calc
      _ = (t : ℂ)^(s-1)/(t : ℂ)^(1 : ℂ) := by rw [Complex.cpow_one]
      _ = (t : ℂ)^((s-1)-1) := (Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr ht.ne')).symm
      _ = _ := by congr 1; ring
  calc
    _ = (Real.pi : ℂ)*(((t : ℂ)^(s-1)/t)*
        (Complex.exp (-(t : ℂ))*Complex.exp (-(4*Real.pi^2*‖freq‖^2 : ℝ)/t))) := by ring
    _ = _ := by rw [hp, ← Complex.exp_add]; congr 2; ring_nf

theorem sourceFourierKernel_gamma (s freq : ℂ) (hs : 1 < s.re) :
    sourceFourierKernel s freq * Complex.Gamma s =
      (Real.pi : ℂ) * ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ)^(s-2) * Complex.exp (-(t : ℂ) - (4*Real.pi^2*‖freq‖^2 : ℝ)/t) := by
  have hmix := gaussianMixture_integrable s freq hs
  calc
    _ = ∫ z : ℂ, (hyperbolicKernel s z * Complex.Gamma s)*
        ShortDraftTrace.breveE (-freq*z) := by
      rw [sourceFourierKernel, ← integral_mul_const]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by ring
    _ = ∫ z : ℂ, ∫ t : ℝ in Set.Ioi 0, gaussianMixture s freq t z := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => (integral_gaussianMixture_t s freq (by linarith) z).symm
    _ = ∫ t : ℝ in Set.Ioi 0, ∫ z : ℂ, gaussianMixture s freq t z :=
      (integral_integral_swap hmix).symm
    _ = _ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact integral_gaussianMixture_z s freq t ht

def schlafliIntegral (ν : ℂ) (x : ℝ) : ℂ :=
  ∫ t : ℝ in Set.Ioi 0, (t : ℂ)^(ν-1)*
    Complex.exp (-(t : ℂ) - (x : ℂ)^2/(4*t))

lemma schlafliIntegral_integrable (ν : ℂ) (x : ℝ) (hν : 0 < ν.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^(ν-1)*
      Complex.exp (-(t : ℂ)-(x : ℂ)^2/(4*t))) (Set.Ioi 0) := by
  apply (Real.GammaIntegral_convergent hν).mono'
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hre : (-(t : ℂ)-(x : ℂ)^2/(4*t)).re = -t-x^2/(4*t) := by
      rw [show -(t : ℂ)-(x : ℂ)^2/(4*t) = ((-t-x^2/(4*t) : ℝ) : ℂ) by push_cast; rfl]
      rfl
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp, hre]
    simp only [Complex.sub_re, Complex.one_re]
    have he := Real.exp_le_exp.mpr (show -t-x^2/(4*t) ≤ -t by linarith [div_nonneg (sq_nonneg x) (show 0 ≤ 4*t by positivity)])
    have hb := mul_le_mul_of_nonneg_left he (Real.rpow_nonneg ht.le (ν.re-1))
    simpa only [mul_comm] using hb

def schlafliBesselK (ν : ℂ) (x : ℝ) : ℂ :=
  (1/2 : ℂ)*(x/2 : ℂ)^(-ν)*schlafliIntegral ν x

lemma sourceFourierKernel_gamma_schlafli (s freq : ℂ) (hs : 1 < s.re) :
    sourceFourierKernel s freq * Complex.Gamma s =
      (Real.pi : ℂ)*schlafliIntegral (s-1) (4*Real.pi*‖freq‖) := by
  rw [sourceFourierKernel_gamma s freq hs]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  rw [show s-2=(s-1)-1 by ring]
  apply congrArg (fun w : ℂ => (t : ℂ)^((s-1)-1)*Complex.exp w)
  push_cast
  ring

theorem sourceFourierKernel_bessel (s freq : ℂ) (hs : 1 < s.re) (hf : freq ≠ 0) :
    sourceFourierKernel s freq =
      (2*Real.pi : ℂ)/Complex.Gamma s *
        (2*Real.pi*‖freq‖ : ℂ)^(s-1) *
        schlafliBesselK (s-1) (4*Real.pi*‖freq‖) := by
  have hg := Complex.Gamma_ne_zero_of_re_pos (show 0 < s.re by linarith)
  have hz : (2*Real.pi*‖freq‖ : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hf))
  have hp : (2*Real.pi*‖freq‖ : ℂ)^(s-1) * (2*Real.pi*‖freq‖ : ℂ)^(-(s-1)) = 1 := by
    rw [← Complex.cpow_add _ _ hz, add_neg_cancel, Complex.cpow_zero]
  have hreorder : (2*Real.pi : ℂ)/Complex.Gamma s *
      (2*Real.pi*‖freq‖ : ℂ)^(s-1) * schlafliBesselK (s-1) (4*Real.pi*‖freq‖) =
      ((2*Real.pi : ℂ)*(2*Real.pi*‖freq‖ : ℂ)^(s-1)*
        schlafliBesselK (s-1) (4*Real.pi*‖freq‖))/Complex.Gamma s := by ring
  rw [hreorder]
  apply (eq_div_iff hg).mpr
  rw [sourceFourierKernel_gamma_schlafli s freq hs]
  unfold schlafliBesselK
  push_cast
  have hhalf : (4*(Real.pi : ℂ)*‖freq‖)/2 = 2*Real.pi*‖freq‖ := by ring
  rw [hhalf]
  linear_combination -((Real.pi : ℂ)*schlafliIntegral (s-1) (4*Real.pi*‖freq‖))*hp

theorem sourceFourierKernel_four_thirds (freq : ℂ) (hf : freq ≠ 0) :
    sourceFourierKernel (4/3 : ℂ) freq =
      (2*Real.pi : ℂ)/Complex.Gamma (4/3) *
        (2*Real.pi*‖freq‖ : ℂ)^(1/3 : ℂ) *
        schlafliBesselK (1/3) (4*Real.pi*‖freq‖) := by
  convert! sourceFourierKernel_bessel (4/3) freq (by norm_num) hf using 1 ; norm_num

end CubicEisenstein

end

end OAI

end


