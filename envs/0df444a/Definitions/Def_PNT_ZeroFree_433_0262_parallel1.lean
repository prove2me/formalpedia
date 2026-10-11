-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0262_parallel1
-- name    : PNT_ZeroFree_433_0262_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:44:04.985414+00:00
-- url     : https://prove2.me/theorems/61fe3ca8-26ac-4172-ad0e-2af856e9e2d3
-- title:
--   Zero-free region foundations: Mellin.VerticalContourShift [0262_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Mellin.VerticalContourShift
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/VerticalContourShift.lean#L80-L580

import Definitions.Def_PNT_ZeroFree_433_0020
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0057_1
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0079_1
import Definitions.Def_PNT_ZeroFree_433_0167
import Definitions.Def_PNT_ZeroFree_433_0327
import Definitions.Def_PNT_ZeroFree_433_0505

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/VerticalContourShift.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace VerticalContourShift
open Filter MeasureTheory
open scoped Classical Topology

lemma gaussian_regulator_norm (ε σ t : ℝ) :
    ‖Complex.exp ((ε:ℂ)*((σ:ℂ)+t*Complex.I)^2)‖=Real.exp (ε*(σ^2-t^2)) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [pow_two,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  ring

lemma gaussian_regulator_norm_le (ε σ t : ℝ) (hε0 : 0≤ε) (hε1 : ε≤1) :
    ‖Complex.exp ((ε:ℂ)*((σ:ℂ)+t*Complex.I)^2)‖≤Real.exp (σ^2) := by
  rw [gaussian_regulator_norm]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg σ,sq_nonneg t,mul_nonneg hε0 (sq_nonneg t),
    mul_nonneg (sub_nonneg.mpr hε1) (sq_nonneg σ)]

def gaussianRegulatorSequence (n : ℕ) : ℝ := 1/((n:ℝ)+1)

lemma gaussianRegulatorSequence_pos (n : ℕ) : 0<gaussianRegulatorSequence n := by
  unfold gaussianRegulatorSequence
  positivity

lemma gaussianRegulatorSequence_le_one (n : ℕ) : gaussianRegulatorSequence n≤1 := by
  unfold gaussianRegulatorSequence
  apply (div_le_one (by positivity)).mpr
  linarith [Nat.cast_nonneg (α:=ℝ) n]

lemma gaussianRegulatorSequence_tendsto : Tendsto gaussianRegulatorSequence atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem gaussian_regulator_integral_tendsto (g : ℝ→ℂ) (hg : Integrable g) (σ : ℝ) :
    Tendsto (fun n : ℕ=>∫t : ℝ,
      Complex.exp ((gaussianRegulatorSequence n:ℂ)*((σ:ℂ)+t*Complex.I)^2)*g t)
      atTop (𝓝 (∫t : ℝ,g t)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun t : ℝ=>Real.exp (σ^2)*‖g t‖)
  · intro n
    have hc : Continuous (fun t : ℝ=>
        Complex.exp ((gaussianRegulatorSequence n:ℂ)*((σ:ℂ)+t*Complex.I)^2)) := by fun_prop
    exact hc.aestronglyMeasurable.mul hg.aestronglyMeasurable
  · exact hg.norm.const_mul _
  · intro n
    exact Filter.Eventually.of_forall (fun t=>by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (gaussian_regulator_norm_le _ σ t (gaussianRegulatorSequence_pos n).le
          (gaussianRegulatorSequence_le_one n)) (norm_nonneg _))
  · filter_upwards with t
    have hε : Tendsto (fun n : ℕ=>(gaussianRegulatorSequence n:ℂ)) atTop (𝓝 0) :=
      by simpa only [Function.comp_def,Complex.ofReal_zero] using
        Complex.continuous_ofReal.continuousAt.tendsto.comp gaussianRegulatorSequence_tendsto
    have he := (Complex.continuous_exp.tendsto 0).comp
      (by simpa only [zero_mul] using hε.mul_const (((σ:ℂ)+t*Complex.I)^2))
    simpa only [Function.comp_def,Complex.exp_zero,one_mul] using he.mul_const (g t)

lemma rpow_between_endpoints (y a b σ : ℝ) (hy : 0<y) (ha : a≤σ) (hb : σ≤b) :
    y^σ≤y^a+y^b := by
  by_cases h1 : 1≤y
  · exact (Real.rpow_le_rpow_of_exponent_le h1 hb).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hy.le a))
  · exact (Real.rpow_le_rpow_of_exponent_ge hy (le_of_not_ge h1) ha).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hy.le b))

theorem mellin_uniform_strip_bound (f : ℝ→ℂ) (a b : ℝ)
    (ha : MellinConvergent f (a:ℂ)) (hb : MellinConvergent f (b:ℂ)) :
    ∃C : ℝ,0≤C ∧ ∀s : ℂ,a≤s.re→s.re≤b→‖mellin f s‖≤C := by
  let B : ℝ→ℝ := fun y=>‖(y:ℂ)^((a:ℂ)-1)*f y‖+‖(y:ℂ)^((b:ℂ)-1)*f y‖
  have hB : IntegrableOn B (Set.Ioi 0) := by
    exact ha.norm.add hb.norm
  refine ⟨∫y in Set.Ioi 0,B y,integral_nonneg (fun y=>add_nonneg (norm_nonneg _) (norm_nonneg _)),?_⟩
  intro s hsa hsb
  unfold mellin
  apply norm_integral_le_of_norm_le hB
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  change 0<y at hy
  have hp := rpow_between_endpoints y (a-1) (b-1) (s.re-1) hy (by linarith) (by linarith)
  change ‖(y:ℂ)^(s-1)*f y‖≤B y
  dsimp only [B]
  simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy,Complex.sub_re,
    Complex.ofReal_re,Complex.one_re]
  simpa only [add_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg (f y))

end VerticalContourShift

namespace GaussianMoment

lemma gaussian_le_inverse_quadratic (c t:ℝ) (hc:0<c) :
    Real.exp (-c*t^2)≤(1+2/c)/(1+t^2) := by
  have h0:Real.exp (-c*t^2)≤1:=by
    apply Real.exp_le_one_iff.mpr
    nlinarith [sq_nonneg t]
  have h1:t^2*Real.exp (-c*t^2)≤2/c:=by
    have hm:=gaussian_moment_term_bound (t^2) c (sq_nonneg t) hc
    have he:Real.exp (-(c*t^2/2))≤1:=by
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg t]
    exact hm.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left he (div_nonneg (by norm_num) hc.le))
  apply (le_div_iff₀ (by positivity : 0<1+t^2)).mpr
  nlinarith

lemma linear_height_young (A ε t:ℝ) (hε:0<ε) :
    A*|t|≤ε*t^2/2+A^2/(2*ε) := by
  have hs:0≤ε^2*t^2-2*ε*A*|t|+A^2:=by
    calc
      0≤(ε*|t|-A)^2:=sq_nonneg _
      _=ε^2*t^2-2*ε*A*|t|+A^2:=by rw [sub_sq,mul_pow,sq_abs];ring
  apply le_of_mul_le_mul_left (a := 2*ε) ?_
    (mul_pos (by norm_num : (0:ℝ)<2) hε)
  calc
    2*ε*(A*|t|)≤ε^2*t^2+A^2:=by nlinarith [hs]
    _=2*ε*(ε*t^2/2+A^2/(2*ε)):=by field_simp

theorem gaussian_regulator_strip_bound (a b A B ε:ℝ) (hB:0≤B) (hε:0<ε)
    (f:ℂ→ℂ)
    (hf:∀σ:ℝ,σ∈Set.Icc a b→∀t:ℝ,
      ‖f ((σ:ℂ)+(t:ℂ)*Complex.I)‖≤B*Real.exp (A*|t|))
    (σ t:ℝ) (hσ:σ∈Set.Icc a b) :
    ‖Complex.exp ((ε:ℂ)*((σ:ℂ)+(t:ℂ)*Complex.I)^2)*
        f ((σ:ℂ)+(t:ℂ)*Complex.I)‖≤
      (B*Real.exp (ε*(max |a| |b|)^2+A^2/(2*ε))*(1+4/ε))/(1+t^2) := by
  let R:ℝ:=max |a| |b|
  have hR:0≤R:=le_trans (abs_nonneg a) (le_max_left _ _)
  have hsabs:|σ|≤R:=abs_le_max_abs_abs hσ.1 hσ.2
  have hs:σ^2≤R^2:=by
    calc
      _=|σ|^2:=(sq_abs σ).symm
      _≤R^2:=pow_le_pow_left₀ (abs_nonneg σ) hsabs 2
  have hre:((ε:ℂ)*((σ:ℂ)+(t:ℂ)*Complex.I)^2).re=ε*(σ^2-t^2):=by
    simp [pow_two,Complex.mul_re,Complex.mul_im]

  have hE:ε*(σ^2-t^2)+A*|t|≤
      (ε*R^2+A^2/(2*ε))-(ε/2)*t^2:=by
    have hy:=linear_height_young A ε t hε
    nlinarith
  have hg:=gaussian_le_inverse_quadratic (ε/2) t (by positivity)
  have hg':Real.exp (-(ε/2)*t^2)≤(1+4/ε)/(1+t^2):=by
    convert! hg using 1 ;field_simp ;ring
  rw [norm_mul,Complex.norm_exp,hre]
  calc
    _≤Real.exp (ε*(σ^2-t^2))*(B*Real.exp (A*|t|)):=
      mul_le_mul_of_nonneg_left (hf σ hσ t) (Real.exp_pos _).le
    _=B*Real.exp (ε*(σ^2-t^2)+A*|t|):=by rw [Real.exp_add];ring
    _≤B*Real.exp ((ε*R^2+A^2/(2*ε))-(ε/2)*t^2):=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE) hB
    _=(B*Real.exp (ε*R^2+A^2/(2*ε)))*Real.exp (-(ε/2)*t^2):=by
      rw [Real.exp_sub,div_eq_mul_inv,←Real.exp_neg,neg_mul]
      ring
    _≤(B*Real.exp (ε*R^2+A^2/(2*ε)))*((1+4/ε)/(1+t^2)):=
      mul_le_mul_of_nonneg_left hg' (mul_nonneg hB (Real.exp_pos _).le)
    _=_:=by dsimp only [R];ring

theorem gaussian_regulator_strip_decay (a b A B ε:ℝ) (_hab:a≤b) (_hA:0≤A)
    (hB:0≤B) (hε:0<ε) (f:ℂ→ℂ)
    (hf:∀σ:ℝ,σ∈Set.Icc a b→∀t:ℝ,
      ‖f ((σ:ℂ)+(t:ℂ)*Complex.I)‖≤B*Real.exp (A*|t|)) :
    ∃K:ℝ,0≤K ∧ ∀σ:ℝ,σ∈Set.Icc a b→∀t:ℝ,
      ‖Complex.exp ((ε:ℂ)*((σ:ℂ)+(t:ℂ)*Complex.I)^2)*
        f ((σ:ℂ)+(t:ℂ)*Complex.I)‖≤K/(1+t^2) := by
  refine ⟨B*Real.exp (ε*(max |a| |b|)^2+A^2/(2*ε))*(1+4/ε),by positivity,?_⟩
  intro σ hσ t
  exact gaussian_regulator_strip_bound a b A B ε hB hε f hf σ t hσ

end GaussianMoment

namespace VerticalContourShift
open Filter MeasureTheory
open scoped Classical Topology

theorem integral_eq_of_exponential_strip_growth
    (f : ℂ→ℂ) (a b A B : ℝ) (hab : a≤b) (hA : 0≤A) (hB : 0≤B)
    (hdiff : ∀z : ℂ,a≤z.re→z.re≤b→DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ=>f ((a:ℂ)+t*Complex.I)))
    (hb : Integrable (fun t : ℝ=>f ((b:ℂ)+t*Complex.I)))
    (hbound : ∀σ∈Set.Icc a b,∀t : ℝ,‖f ((σ:ℂ)+t*Complex.I)‖≤B*Real.exp (A*|t|)) :
    (∫t : ℝ,f ((a:ℂ)+t*Complex.I))=∫t : ℝ,f ((b:ℂ)+t*Complex.I) := by
  let F : ℕ→ℂ→ℂ := fun n z=>Complex.exp ((gaussianRegulatorSequence n:ℂ)*z^2)*f z
  have hreg (n : ℕ) : Continuous (fun z : ℂ=>Complex.exp ((gaussianRegulatorSequence n:ℂ)*z^2)) := by
    fun_prop
  have hint (n : ℕ) (σ : ℝ) (hσ : Integrable (fun t : ℝ=>f ((σ:ℂ)+t*Complex.I))) :
      Integrable (fun t : ℝ=>F n ((σ:ℂ)+t*Complex.I)) := by
    apply hσ.bdd_mul (c:=Real.exp (σ^2))
    · exact ((hreg n).comp (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun t=>gaussian_regulator_norm_le _ σ t
        (gaussianRegulatorSequence_pos n).le (gaussianRegulatorSequence_le_one n))
  have heq (n : ℕ) :
      (∫t : ℝ,F n ((a:ℂ)+t*Complex.I))=∫t : ℝ,F n ((b:ℂ)+t*Complex.I) := by
    obtain ⟨K,hK,hdec⟩ := GaussianMoment.gaussian_regulator_strip_decay a b A B
      (gaussianRegulatorSequence n) hab hA hB (gaussianRegulatorSequence_pos n) f hbound
    apply integral_eq_of_strip_decay (F n) a b K hab
    · intro z hza hzb
      have hg : Differentiable ℂ (fun w : ℂ=>Complex.exp ((gaussianRegulatorSequence n:ℂ)*w^2)) := by
        fun_prop
      exact hg.differentiableAt.mul (hdiff z hza hzb)
    · exact hint n a ha
    · exact hint n b hb
    · exact hdec
  have hleft := gaussian_regulator_integral_tendsto (fun t : ℝ=>f ((a:ℂ)+t*Complex.I)) ha a
  have hright := gaussian_regulator_integral_tendsto (fun t : ℝ=>f ((b:ℂ)+t*Complex.I)) hb b
  change Tendsto (fun n=>∫t : ℝ,F n ((a:ℂ)+t*Complex.I)) atTop
    (𝓝 (∫t : ℝ,f ((a:ℂ)+t*Complex.I))) at hleft
  change Tendsto (fun n=>∫t : ℝ,F n ((b:ℂ)+t*Complex.I)) atTop
    (𝓝 (∫t : ℝ,f ((b:ℂ)+t*Complex.I))) at hright
  simp only [heq] at hleft
  exact tendsto_nhds_unique hleft hright

end VerticalContourShift

namespace CubicGammaExponential
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

lemma norm_Gamma_le_real (z : ℂ) (hz : 0<z.re) :
    ‖Complex.Gamma z‖≤Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz,Real.Gamma_eq_integral hz]
  unfold Complex.GammaIntegral
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul,Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma norm_sin_le_exp_abs_im (z : ℂ) :
    ‖Complex.sin z‖≤Real.exp |z.im| := by
  rw [Complex.sin,norm_div,norm_mul,Complex.norm_I,mul_one]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  calc
    _ ≤ ‖Complex.exp (-z*Complex.I)‖+‖Complex.exp (z*Complex.I)‖ := norm_sub_le _ _
    _ = Real.exp z.im+Real.exp (-z.im) := by simp [Complex.norm_exp]
    _ ≤ Real.exp |z.im|+Real.exp |z.im| :=
      add_le_add (Real.exp_le_exp.mpr (le_abs_self _)) (Real.exp_le_exp.mpr (neg_le_abs _))
    _ = _ := by ring

lemma Gamma_ne_zero_of_im_ne_zero (z : ℂ) (hz : z.im≠0) : Complex.Gamma z≠0 := by
  apply Complex.Gamma_ne_zero
  intro n he
  apply hz
  have h:=congrArg Complex.im he
  simpa using h

lemma inverse_Gamma_reflection (z : ℂ) (hz : z.im≠0) :
    (Complex.Gamma z)⁻¹=Complex.Gamma (1-z)*Complex.sin (Real.pi*z)/Real.pi := by
  have hg:=Gamma_ne_zero_of_im_ne_zero z hz
  have hh:=Gamma_ne_zero_of_im_ne_zero (1-z) (by simpa using hz)
  have hp : (Real.pi:ℂ)≠0:=Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : Complex.sin (Real.pi*z)≠0 := by
    intro hs
    have he:=Complex.Gamma_mul_Gamma_one_sub z
    rw [hs,div_zero] at he
    exact (mul_ne_zero hg hh) he
  apply mul_left_cancel₀ hg
  rw [mul_inv_cancel₀ hg]
  symm
  calc
    _ = (Complex.Gamma z*Complex.Gamma (1-z))*Complex.sin (Real.pi*z)/Real.pi := by ring
    _ = 1 := by
      rw [Complex.Gamma_mul_Gamma_one_sub,div_mul_cancel₀ _ hs,div_self hp]

lemma inverse_Gamma_norm_of_left (z : ℂ) (hz : z.re<1) (hi : z.im≠0) :
    ‖(Complex.Gamma z)⁻¹‖≤
      (Real.Gamma (1-z.re)/Real.pi)*Real.exp (Real.pi*|z.im|) := by
  rw [inverse_Gamma_reflection z hi,norm_div,norm_mul,
    Complex.norm_of_nonneg Real.pi_pos.le]
  have hgamma:=norm_Gamma_le_real (1-z) (by simp;linarith)
  have hsin:=norm_sin_le_exp_abs_im (Real.pi*z)
  simp only [Complex.sub_re,Complex.one_re] at hgamma
  have him : |((Real.pi:ℂ)*z).im|=Real.pi*|z.im| := by
    simp [abs_mul, abs_of_pos Real.pi_pos]
  rw [him] at hsin
  calc
    _ ≤ (Real.Gamma (1-z.re)*Real.exp (Real.pi*|z.im|))/Real.pi :=
      div_le_div_of_nonneg_right
        (mul_le_mul hgamma hsin (norm_nonneg _) (Real.Gamma_pos_of_pos (by linarith)).le)
        Real.pi_pos.le
    _ = _ := by ring

lemma inverse_Gamma_norm_le_shift_left (z : ℂ) (n : ℕ) (hi : 1≤|z.im|) :
    ‖(Complex.Gamma z)⁻¹‖≤‖(Complex.Gamma (z-n))⁻¹‖ := by
  have he:=congrArg norm (CubicReflectionKernel.inverse_Gamma_shift (z-n) n)
  simp only [sub_add_cancel,norm_mul] at he
  have hprod : 1≤‖∏k∈Finset.range n,(z-(n:ℂ)+k)‖ := by
    rw [norm_prod]
    apply Finset.one_le_prod
    intro k hk
    calc
      1 ≤ |z.im| := hi
      _ = |(z-(n:ℂ)+k).im| := by simp
      _ ≤ _ := Complex.abs_im_le_norm _
  rw [he]
  exact le_mul_of_one_le_left (norm_nonneg _) hprod

lemma real_Gamma_compact_bound (a b : ℝ) (ha : 0<a) :
    ∃C : ℝ,0<C ∧ ∀x∈Set.Icc a b,Real.Gamma x≤C := by
  have hc : ContinuousOn Real.Gamma (Set.Icc a b) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (fun x hx=>ha.trans_le hx.1)
  obtain ⟨C,hC⟩:=(isCompact_Icc : IsCompact (Set.Icc a b)).bddAbove_image hc
  refine ⟨|C|+1,by positivity,?_⟩
  intro x hx
  exact (hC (Set.mem_image_of_mem _ hx)).trans (by linarith [le_abs_self C])

lemma inverse_Gamma_compact_strip_bound (a b : ℝ) :
    ∃C : ℝ,0<C ∧ ∀σ∈Set.Icc a b,∀t∈Set.Icc (-1:ℝ) 1,
      ‖(Complex.Gamma ((σ:ℂ)+t*Complex.I))⁻¹‖≤C := by
  have hc : Continuous (fun p : ℝ×ℝ=>
      ‖(Complex.Gamma ((p.1:ℂ)+p.2*Complex.I))⁻¹‖) :=
    (Complex.differentiable_one_div_Gamma.continuous.comp (by fun_prop)).norm
  obtain ⟨C,hC⟩:=((isCompact_Icc : IsCompact (Set.Icc a b)).prod
    (isCompact_Icc : IsCompact (Set.Icc (-1:ℝ) 1))).bddAbove_image hc.continuousOn
  refine ⟨|C|+1,by positivity,?_⟩
  intro σ hσ t ht
  exact (hC ⟨(σ,t),⟨hσ,ht⟩,rfl⟩).trans (by linarith [le_abs_self C])

theorem inverse_Gamma_strip_exp_bound (a b : ℝ) :
    ∃C : ℝ,0<C ∧ ∀σ∈Set.Icc a b,∀t : ℝ,
      ‖(Complex.Gamma ((σ:ℂ)+t*Complex.I))⁻¹‖≤C*Real.exp (Real.pi*|t|) := by
  obtain ⟨n,hn⟩:=exists_nat_gt b
  obtain ⟨Cg,hCg,hg⟩:=real_Gamma_compact_bound ((n:ℝ)+1-b) ((n:ℝ)+1-a) (by linarith)
  obtain ⟨Cc,hCc,hc⟩:=inverse_Gamma_compact_strip_bound a b
  refine ⟨Cc+Cg/Real.pi,by positivity,?_⟩
  intro σ hσ t
  have hexp : 1≤Real.exp (Real.pi*|t|) := Real.one_le_exp (by positivity)
  by_cases ht:|t|≤1
  · have hsmall:=hc σ hσ t (abs_le.mp ht)
    calc
      _ ≤ Cc := hsmall
      _ ≤ Cc+Cg/Real.pi := le_add_of_nonneg_right (by positivity)
      _ ≤ (Cc+Cg/Real.pi)*Real.exp (Real.pi*|t|) :=
        le_mul_of_one_le_right (by positivity) hexp
  · have ht1 : 1 < |t| :=lt_of_not_ge ht
    have ht0 : t≠0 := by intro ht0;subst t;norm_num at ht1
    let z : ℂ := (σ:ℂ)+t*Complex.I
    let w : ℂ := z-n
    have hw : w.re<1 := by
      dsimp [w,z]
      simp only [Complex.ofReal_re,Complex.mul_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
        sub_zero,add_zero]
      linarith [hσ.2]
    have hwi : w.im≠0 := by simpa [w,z] using ht0
    have he : 1-w.re=(n:ℝ)+1-σ := by simp [w,z];ring
    have hi : w.im=t := by simp [w,z]
    have hbound:=inverse_Gamma_norm_of_left w hw hwi
    rw [he,hi] at hbound
    have hgbound:=hg ((n:ℝ)+1-σ) ⟨by linarith [hσ.2],by linarith [hσ.1]⟩
    calc
      _ ≤ ‖(Complex.Gamma w)⁻¹‖ :=
        inverse_Gamma_norm_le_shift_left z n (by simpa [z] using ht1.le)
      _ ≤ (Real.Gamma ((n:ℝ)+1-σ)/Real.pi)*Real.exp (Real.pi*|t|) := hbound
      _ ≤ (Cg/Real.pi)*Real.exp (Real.pi*|t|) := by gcongr
      _ ≤ (Cc+Cg/Real.pi)*Real.exp (Real.pi*|t|) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCc.le) (Real.exp_pos _).le

theorem inverse_Gamma_strip_exp_bound_complex (a b : ℝ) :
    ∃C : ℝ,0<C ∧ ∀z : ℂ,z.re∈Set.Icc a b →
      ‖(Complex.Gamma z)⁻¹‖≤C*Real.exp (Real.pi*|z.im|) := by
  obtain ⟨C,hC,hb⟩:=inverse_Gamma_strip_exp_bound a b
  refine ⟨C,hC,?_⟩
  intro z hz
  simpa only [Complex.re_add_im] using hb z.re hz z.im

theorem inverse_cubic_Gamma_pair_strip_bound (a b : ℝ) :
    ∃C : ℝ,0<C ∧ ∀s : ℂ,s.re∈Set.Icc a b →
      ‖(Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))⁻¹‖≤
        C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨C1,hC1,h1⟩:=inverse_Gamma_strip_exp_bound_complex (a+1/3) (b+1/3)
  obtain ⟨C2,hC2,h2⟩:=inverse_Gamma_strip_exp_bound_complex (a+2/3) (b+2/3)
  refine ⟨C1*C2,mul_pos hC1 hC2,?_⟩
  intro s hs
  have hb1:=h1 (s+1/3) (by norm_num;constructor <;> linarith [hs.1,hs.2])
  have hb2:=h2 (s+2/3) (by norm_num;constructor <;> linarith [hs.1,hs.2])
  norm_num at hb1 hb2
  rw [mul_inv_rev,norm_mul,norm_inv,norm_inv]
  calc
    _ ≤ (C2*Real.exp (Real.pi*|s.im|))*(C1*Real.exp (Real.pi*|s.im|)) :=
      mul_le_mul hb2 hb1 (by positivity) (by positivity)
    _ = C1*C2*Real.exp (2*Real.pi*|s.im|) := by
      rw [show 2*Real.pi*|s.im|=Real.pi*|s.im|+Real.pi*|s.im| by ring,Real.exp_add]
      ring

end CubicGammaExponential

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CubicEisenstein

lemma cubic_bessel_mellin_norm_scale (s : ℂ) (r : ℝ) (hr : 0<r) :
    (∫v : ℝ in Set.Ioi 0,‖(v:ℂ)^(2*s)*
      schlafliBesselK (1/3) (4*Real.pi*r*v)‖)=
    r^(-(2*s.re+1))*(∫v : ℝ in Set.Ioi 0,
      ‖(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*v)‖) := by
  let g : ℝ→ℝ := fun v=>‖(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*v)‖
  have hp (v : ℝ) (hv : 0<v) :
      ‖(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*r*v)‖=
        r^(-(2*s.re))*g (r*v) := by
    dsimp only [g]
    rw [norm_mul,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hv,
      Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hr hv)]
    simp only [show (2*s).re=2*s.re by simp]
    rw [Real.mul_rpow hr.le hv.le]
    rw [show 4*Real.pi*r*v=4*Real.pi*(r*v) by ring]
    have hc : r^(-(2*s.re))*r^(2*s.re)=1 := by
      rw [←Real.rpow_add hr]
      simp
    linear_combination -(v^(2*s.re)*‖schlafliBesselK (1/3) (4*Real.pi*(r*v))‖)*hc
  calc
    _=∫v : ℝ in Set.Ioi 0,r^(-(2*s.re))*g (r*v) :=
      setIntegral_congr_fun measurableSet_Ioi hp
    _=r^(-(2*s.re))*(r⁻¹*(∫v : ℝ in Set.Ioi 0,g v)) := by
      rw [integral_const_mul,integral_comp_mul_left_Ioi g 0 hr]
      simp
    _=_ := by
      rw [←mul_assoc,←Real.rpow_neg_one,←Real.rpow_add hr]
      congr 2
      ring

lemma weighted_cubic_bessel_integral_norm (s : ℂ) (freq a : ℂ) (hf : freq≠0) :
    (∫v : ℝ in Set.Ioi 0,‖a*((v:ℂ)^(2*s)*
      schlafliBesselK (1/3) (4*Real.pi*‖freq‖*v))‖)=
    (‖a‖*‖freq‖^(-(2*s.re+1)))*(∫v : ℝ in Set.Ioi 0,
      ‖(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*v)‖) := by
  simp only [norm_mul,integral_const_mul]
  rw [←integral_const_mul]
  have h:=cubic_bessel_mellin_norm_scale s ‖freq‖ (norm_pos_iff.mpr hf)
  simp only [norm_mul] at h
  rw [integral_const_mul,h]
  ring


end CubicEisenstein

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CubicEisenstein

lemma positive_sqrt_cpow_twice (r : ℝ) (hr : 0<r) (s : ℂ) :
    (Real.sqrt r:ℂ)^(2*s+1)=(r:ℂ)^(s+1/2) := by
  have ha : Complex.arg (Real.sqrt r:ℂ)=0 :=
    Complex.arg_ofReal_of_nonneg (Real.sqrt_nonneg r)
  have h := Complex.cpow_nat_mul' (x:=(Real.sqrt r:ℂ)) (n:=2)
    (by simpa only [ha,mul_zero] using (neg_lt_zero.mpr Real.pi_pos))
    (by simpa only [ha,mul_zero] using Real.pi_pos.le) (s+1/2)
  have hs : (Real.sqrt r:ℂ)^2=(r:ℂ) := by
    rw [←Complex.ofReal_pow,Real.sq_sqrt hr.le]
  norm_num only at h
  simpa only [hs,show (2:ℂ)*(s+1/2)=2*s+1 by ring] using h

lemma radial_bessel_coefficient_norm (r q σ : ℝ) (hr : 0<r) (hq : 0<q) (a : ℂ) :
    ‖a*(r:ℂ)‖*‖((q*Real.sqrt r:ℝ):ℂ)‖^(-(2*σ+1))=
      q^(-(2*σ+1))*(‖a‖*r^(1/2-σ)) := by
  rw [norm_mul,Complex.norm_of_nonneg hr.le,
    Complex.norm_of_nonneg (mul_pos hq (Real.sqrt_pos.mpr hr)).le,
    Real.mul_rpow hq.le (Real.sqrt_nonneg r),Real.sqrt_eq_rpow,
    ←Real.rpow_mul hr.le]
  have hp : r*r^((1/2)*(-(2*σ+1)))=r^(1/2-σ) := by
    calc
      _=r^1*r^((1/2)*(-(2*σ+1))) := by rw [Real.rpow_one]
      _=r^(1+(1/2)*(-(2*σ+1))) := (Real.rpow_add hr _ _).symm
      _=_ := by congr 1;ring
  calc
    _=q^(-(2*σ+1))*(‖a‖*(r*r^((1/2)*(-(2*σ+1))))) := by ring
    _=_ := by rw [hp]

lemma radial_bessel_coefficient_identity (r q : ℝ) (hr : 0<r) (hq : 0<q)
    (a B s : ℂ) :
    (a*(r:ℂ))*(B/((q*Real.sqrt r:ℝ):ℂ)^(2*s+1))=
      (B/(q:ℂ)^(2*s+1))*(a*(r:ℂ)^(1/2-s)) := by
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hq.le (Real.sqrt_nonneg r),
    positive_sqrt_cpow_twice r hr s]
  have hp : (r:ℂ)/(r:ℂ)^(s+1/2)=(r:ℂ)^(1/2-s) := by
    have h := Complex.cpow_sub (1:ℂ) (s+1/2) (Complex.ofReal_ne_zero.mpr hr.ne')
    rw [Complex.cpow_one] at h
    simpa only [show (1:ℂ)-(s+1/2)=1/2-s by ring] using h.symm
  calc
    _=(B/(q:ℂ)^(2*s+1))*(a*((r:ℂ)/(r:ℂ)^(s+1/2))) := by ring
    _=_ := by rw [hp]

def radialBesselProfile {α : Type*} (r : α→ℝ) (a : α→ℂ) (q v : ℝ) : ℂ :=
  ∑'i,(a i*(r i:ℂ))*(v:ℂ)*
    schlafliBesselK (1/3) (4*Real.pi*q*Real.sqrt (r i)*v)


end CubicEisenstein

end

end OAI

end


