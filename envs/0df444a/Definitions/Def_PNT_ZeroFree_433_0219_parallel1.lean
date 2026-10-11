-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0219_parallel1
-- name    : PNT_ZeroFree_433_0219_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:14:00.512311+00:00
-- url     : https://prove2.me/theorems/65ce8ac3-38d0-406d-a0cc-c98f0fe085af
-- title:
--   Zero-free region foundations: Eisenstein.ResidualFourierBounds [0219_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.ResidualFourierBounds
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ResidualFourierBounds.lean#L163-L680

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0131_parallel1
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0144_parallel1
import Definitions.Def_PNT_ZeroFree_433_0185_parallel1
import Definitions.Def_PNT_ZeroFree_433_0192_parallel1
import Definitions.Def_PNT_ZeroFree_433_0215_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0221_parallel1
import Definitions.Def_PNT_ZeroFree_433_0225_parallel1
import Definitions.Def_PNT_ZeroFree_433_0231_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ResidualFourierBounds.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O


def cuspIntervalWhittakerHeightFactor (a b : ℝ)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (h : ActualEisensteinCubic.O) : ℂ :=
  ∫v in Set.Icc a b,ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))


end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O


lemma cuspIntervalWhittakerHeightFactor_center_bessel (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h=
      cubicBesselNormalizer h*(∫v in Set.Icc a b,
        ρ v*(schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2)) := by
  rw [cuspIntervalWhittakerHeightFactor,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := ha.trans_le hv.1
  dsimp only
  rw [sourceFourierKernel_cubic_height h hh v hpos]
  ring


end


section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section

def cubicBesselDensity (x t : ℝ) : ℝ :=
  t^(-(2:ℝ)/3)*Real.exp (-t-x^2/(4*t))

lemma cubicBesselDensity_integrable (x : ℝ) :
    IntegrableOn (cubicBesselDensity x) (Set.Ioi 0) := by
  have hi := (schlafliIntegral_integrable (1/3:ℂ) x (by norm_num)).re
  apply MeasureTheory.IntegrableOn.congr_fun hi _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [show (1/3:ℂ)=((1/3:ℝ):ℂ) by norm_num,
    schlafliIntegrand_real (1/3) x t ht]
  change t^((1/3:ℝ)-1)*Real.exp (-t-x^2/(4*t))=cubicBesselDensity x t
  norm_num [cubicBesselDensity]

lemma cubicBesselDensity_nonneg (x t : ℝ) (ht : 0≤t) : 0≤cubicBesselDensity x t :=
  mul_nonneg (Real.rpow_nonneg ht _) (Real.exp_pos _).le

lemma schlafliIntegral_cubic_real (x : ℝ) :
    schlafliIntegral (1/3:ℂ) x=((∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t):ℝ) := by
  unfold schlafliIntegral
  calc
    _ = ∫t in Set.Ioi (0:ℝ),((cubicBesselDensity x t:ℝ):ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [show (1/3:ℂ)=((1/3:ℝ):ℂ) by norm_num,
        schlafliIntegrand_real (1/3) x t ht]
      norm_num [cubicBesselDensity]
    _ = _ := integral_ofReal

lemma schlafliBesselK_cubic_real (x : ℝ) (hx : 0<x) :
    schlafliBesselK (1/3:ℂ) x=
      (((1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t)):ℝ) := by
  rw [schlafliBesselK,schlafliIntegral_cubic_real]
  have hp := Complex.ofReal_cpow (show 0≤x/2 by positivity) (-(1:ℝ)/3)
  norm_num only [Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_one,
    Complex.ofReal_ofNat,neg_div] at hp
  rw [←hp]
  push_cast
  ring_nf

lemma schlafliBesselK_cubic_norm_re (x : ℝ) (hx : 0<x) :
    ‖schlafliBesselK (1/3:ℂ) x‖=(schlafliBesselK (1/3:ℂ) x).re := by
  rw [schlafliBesselK_cubic_real x hx,Complex.ofReal_re]
  apply Complex.norm_of_nonneg
  apply mul_nonneg (by positivity)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact cubicBesselDensity_nonneg x t ht.le

lemma cubicBesselDensity_upper (x t : ℝ) (ht : 0<t) :
    cubicBesselDensity x t≤Real.exp (-x/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by
  have hq : -t-x^2/(4*t)≤-x/2-t/2 := by
    have hf : x/2-t/2≤x^2/(4*t) :=
      (le_div_iff₀ (show 0<4*t by positivity)).mpr (by
        nlinarith [sq_nonneg (t-x),sq_nonneg t])
    linarith
  have he := Real.exp_le_exp.mpr hq
  unfold cubicBesselDensity
  calc
    _ ≤ t^(-(2:ℝ)/3)*Real.exp (-x/2-t/2) :=
      mul_le_mul_of_nonneg_left he (Real.rpow_nonneg ht.le _)
    _ = _ := by rw [sub_eq_add_neg,Real.exp_add]; ring_nf

lemma cubicBesselIntegral_upper (x : ℝ) :
    (∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t)≤
      Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3)) := by
  have hi : IntegrableOn (fun t : ℝ => t^(-(2:ℝ)/3)*Real.exp (-t/2)) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := -(2:ℝ)/3) (p := (1:ℝ)) (b := (1/2:ℝ)) (by norm_num) (by norm_num) (by norm_num)
    simpa only [Real.rpow_one,show ∀t : ℝ,-(1/2)*t=-t/2 by intro t;ring] using h
  have hb := setIntegral_mono_on (cubicBesselDensity_integrable x)
    (hi.const_mul (Real.exp (-x/2))) measurableSet_Ioi (fun t ht => cubicBesselDensity_upper x t ht)
  rw [integral_const_mul] at hb
  have he : (∫t in Set.Ioi (0:ℝ),t^(-(2:ℝ)/3)*Real.exp (-t/2))=
      (2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3) := by
    have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (1/3:ℝ)) (r := (1/2:ℝ)) (by norm_num) (by norm_num)
    convert! hh using 1 <;> norm_num ; congr 2 ; funext t ; ring_nf
  rw [he] at hb
  exact hb

def cubicBesselUpperConstant : ℝ :=
  (1/2:ℝ)*(1/2:ℝ)^(-(1:ℝ)/3)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))

lemma cubicBesselUpperConstant_pos : 0<cubicBesselUpperConstant := by
  unfold cubicBesselUpperConstant
  positivity

theorem schlafliBesselK_cubic_upper (x : ℝ) (hx : 1≤x) :
    ‖schlafliBesselK (1/3:ℂ) x‖≤cubicBesselUpperConstant*Real.exp (-x/2) := by
  have hxp : 0<x := by linarith
  rw [schlafliBesselK_cubic_norm_re x hxp,schlafliBesselK_cubic_real x hxp,Complex.ofReal_re]
  have hp : (x/2)^(-(1:ℝ)/3)≤(1/2:ℝ)^(-(1:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by norm_num)
  calc
    _ ≤ (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*
        (Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))) :=
      mul_le_mul_of_nonneg_left (cubicBesselIntegral_upper x) (by positivity)
    _ ≤ (1/2:ℝ)*(1/2:ℝ)^(-(1:ℝ)/3)*
        (Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) (by positivity)
    _ = _ := by unfold cubicBesselUpperConstant;ring

lemma cubicBesselDensity_lower (x t : ℝ) (hx : 0<x) (ht : t∈Set.Icc x (2*x)) :
    (2*x)^(-(2:ℝ)/3)*Real.exp (-9*x/4)≤cubicBesselDensity x t := by
  have htp : 0<t := hx.trans_le ht.1
  have hp : (2*x)^(-(2:ℝ)/3)≤t^(-(2:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos htp ht.2 (by norm_num)
  have hfrac : x^2/(4*t)≤x/4 :=
    (div_le_iff₀ (show 0<4*t by positivity)).mpr (by nlinarith [ht.1])
  have he : Real.exp (-9*x/4)≤Real.exp (-t-x^2/(4*t)) :=
    Real.exp_le_exp.mpr (by linarith [ht.2])
  exact mul_le_mul hp he (Real.exp_pos _).le (Real.rpow_nonneg htp.le _)

lemma cubicBesselIntegral_lower (x : ℝ) (hx : 0<x) :
    x*((2*x)^(-(2:ℝ)/3)*Real.exp (-9*x/4))≤
      ∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t := by
  have hsub : Set.Icc x (2*x)⊆Set.Ioi (0:ℝ) := fun t ht => hx.trans_le ht.1
  have hi := cubicBesselDensity_integrable x
  have hr := hi.mono_set hsub
  have hconstant : IntegrableOn (fun _ : ℝ => (2*x)^(-(2:ℝ)/3)*Real.exp (-9*x/4))
      (Set.Icc x (2*x)) := integrableOn_const (hs := isCompact_Icc.measure_ne_top)
  have hmono := setIntegral_mono_on hconstant hr measurableSet_Icc
    (fun t ht => cubicBesselDensity_lower x t hx ht)
  have hextend : (∫t in Set.Icc x (2*x),cubicBesselDensity x t)≤
      ∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t := by
    apply setIntegral_mono_set hi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cubicBesselDensity_nonneg x t ht.le
    · exact Eventually.of_forall hsub
  rw [setIntegral_const,Real.volume_real_Icc_of_le (by linarith),smul_eq_mul,
    show 2*x-x=x by ring] at hmono
  exact hmono.trans hextend

def cubicBesselLowerConstant : ℝ :=
  (1/2:ℝ)*(1/2:ℝ)^(-(1:ℝ)/3)*(2:ℝ)^(-(2:ℝ)/3)

lemma cubicBesselLowerConstant_pos : 0<cubicBesselLowerConstant := by
  unfold cubicBesselLowerConstant
  positivity

theorem schlafliBesselK_cubic_lower (x : ℝ) (hx : 0<x) :
    cubicBesselLowerConstant*Real.exp (-9*x/4)≤(schlafliBesselK (1/3:ℂ) x).re := by
  rw [schlafliBesselK_cubic_real x hx,Complex.ofReal_re]
  have hp := mul_le_mul_of_nonneg_left (cubicBesselIntegral_lower x hx)
    (show 0≤(1/2:ℝ)*(x/2)^(-(1:ℝ)/3) by positivity)
  have hnorm : (x/2)^(-(1:ℝ)/3)=(1/2:ℝ)^(-(1:ℝ)/3)*x^(-(1:ℝ)/3) := by
    rw [show x/2=(1/2:ℝ)*x by ring,Real.mul_rpow (by norm_num) hx.le]
  have htwo : (2*x)^(-(2:ℝ)/3)=(2:ℝ)^(-(2:ℝ)/3)*x^(-(2:ℝ)/3) :=
    Real.mul_rpow (by norm_num) hx.le
  have hxp : x^(-(1:ℝ)/3)*x*x^(-(2:ℝ)/3)=1 := by
    calc
      _ = x^(-(1:ℝ)/3)*x^(1:ℝ)*x^(-(2:ℝ)/3) := by rw [Real.rpow_one]
      _ = x^((-(1:ℝ)/3+1)+(-(2:ℝ)/3)) := by rw [←Real.rpow_add hx,←Real.rpow_add hx]
      _ = 1 := by norm_num
  have he : (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*(x*((2*x)^(-(2:ℝ)/3)*Real.exp (-9*x/4)))=
      cubicBesselLowerConstant*Real.exp (-9*x/4) := by
    rw [hnorm,htwo]
    calc
      _ = cubicBesselLowerConstant*(x^(-(1:ℝ)/3)*x*x^(-(2:ℝ)/3))*Real.exp (-9*x/4) := by
        unfold cubicBesselLowerConstant
        ring
      _ = _ := by rw [hxp,mul_one]
  rwa [he] at hp

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma exp_neg_mul_le_inverse_cube (ε r : ℝ) (hε : 0<ε) (hr : 0<r) :
    Real.exp (-ε*r)≤(6/ε^3)*r^(-3:ℝ) := by
  have hp := Real.pow_div_factorial_le_exp (ε*r) (le_of_lt (mul_pos hε hr)) 3
  norm_num only [Nat.factorial] at hp
  have hi := one_div_le_one_div_of_le (by positivity : (0:ℝ)<(ε*r)^3/6) hp
  rw [one_div,←Real.exp_neg] at hi
  rw [Real.rpow_neg hr.le]
  norm_num only [Real.rpow_ofNat]
  have halg : (6/ε^3)*(r^3)⁻¹=((ε*r)^3/6)⁻¹ := by
    field_simp
  rw [halg]
  simpa only [neg_mul,one_div] using hi

lemma summable_exp_neg_embedding_norm (ε : ℝ) (hε : 0<ε) :
    Summable (fun h : ActualEisensteinCubic.O => Real.exp (-ε*‖ConcreteTraceCRT.eisEmbedding h‖)) := by
  have hs := (summable_embedding_rpow (-3) (by norm_num)).mul_left (6/ε^3)
  have hz : Summable (fun h : ActualEisensteinCubic.O => if h=0 then (1:ℝ) else 0) :=
    (hasSum_ite_eq 0 (1:ℝ)).summable
  apply Summable.of_nonneg_of_le (fun h => (Real.exp_pos _).le) _ (hz.add hs)
  intro h
  by_cases hh : h=0
  · subst h
    norm_num [Pi.add_apply]
  · have hp : 0<‖ConcreteTraceCRT.eisEmbedding h‖ :=
      norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hh)
    simpa only [Pi.add_apply,if_neg hh,zero_add] using exp_neg_mul_le_inverse_cube ε _ hε hp

lemma summable_exp_neg_cuspFrequency_norm (ε : ℝ) (hε : 0<ε) :
    Summable (fun h : ActualEisensteinCubic.O => Real.exp (-ε*‖cuspFrequency h‖)) := by
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := by
    apply norm_pos_iff.mpr
    exact mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero
  have hs := summable_exp_neg_embedding_norm (ε/‖(3:ℂ)*ConcreteTraceCRT.eisLam‖) (div_pos hε hd)
  apply hs.congr
  intro h
  congr 1
  rw [cuspFrequency,norm_div]
  ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cubicBesselNormalizer_ne_zero (h : ActualEisensteinCubic.O) (hh : h≠0) : cubicBesselNormalizer h≠0 := by
  unfold cubicBesselNormalizer
  apply mul_ne_zero
  · exact div_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  · apply Complex.cpow_ne_zero_iff.mpr
    left
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (cuspFrequency_ne_zero h hh)))

lemma cubicBesselHeight_integrable (a b : ℝ) (ha : 0<a) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    IntegrableOn (fun v : ℝ => schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2)
      (Set.Icc a b) volume := by
  have hsource : IntegrableOn (fun v : ℝ => (v:ℂ)^(-(4/3:ℂ)-1)*
      sourceFourierKernel (4/3) (cuspFrequency h*v)) (Set.Icc a b) volume := by
    apply ContinuousOn.integrableOn_Icc
    intro v hv
    have hpos := ha.trans_le hv.1
    exact ((Complex.continuousAt_ofReal_cpow_const v (-(4/3:ℂ)-1) (Or.inr hpos.ne')).mul
      ((sourceFourierKernel_continuous_freq (4/3) (by norm_num)).continuousAt.comp
        ((Complex.continuous_ofReal.const_mul (cuspFrequency h)).continuousAt))).continuousWithinAt
  apply (hsource.div_const (cubicBesselNormalizer h)).congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  apply (div_eq_iff (cubicBesselNormalizer_ne_zero h hh)).mpr
  simpa only [mul_comm] using sourceFourierKernel_cubic_height h hh v (ha.trans_le hv.1)

lemma cubicBesselHeight_average_lower (a b : ℝ) (ha : 0<a) (hab : a<b) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    ((b-a)*cubicBesselLowerConstant/b^2)*Real.exp (-9*Real.pi*b*‖cuspFrequency h‖)≤
      ‖∫v in Set.Icc a b,schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2‖ := by
  have hb : 0<b := ha.trans hab
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  let lower : ℝ := (cubicBesselLowerConstant/b^2)*Real.exp (-9*Real.pi*b*‖cuspFrequency h‖)
  have hi := cubicBesselHeight_integrable a b ha h hh
  have hpoint (v : ℝ) (hv : v∈Set.Icc a b) : lower≤
      RCLike.re (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
    have hvp := ha.trans_le hv.1
    have hx : 0<4*Real.pi*‖cuspFrequency h‖*v := by positivity
    have hK := schlafliBesselK_cubic_lower (4*Real.pi*‖cuspFrequency h‖*v) hx
    have he : Real.exp (-9*Real.pi*b*‖cuspFrequency h‖)≤
        Real.exp (-9*(4*Real.pi*‖cuspFrequency h‖*v)/4) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hv.2
        (show 0≤9*Real.pi*‖cuspFrequency h‖ by positivity)
      nlinarith [hmul]
    have hnum : cubicBesselLowerConstant*Real.exp (-9*Real.pi*b*‖cuspFrequency h‖)≤
        (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)).re :=
      (mul_le_mul_of_nonneg_left he cubicBesselLowerConstant_pos.le).trans hK
    have hden : v^2≤b^2 := sq_le_sq₀ hvp.le hb.le |>.mpr hv.2
    change lower≤Complex.re (_/(v:ℂ)^2)
    rw [←Complex.ofReal_pow,Complex.div_ofReal_re]
    calc
      lower = (cubicBesselLowerConstant*Real.exp (-9*Real.pi*b*‖cuspFrequency h‖))/b^2 := by dsimp [lower]; ring
      _ ≤ (cubicBesselLowerConstant*Real.exp (-9*Real.pi*b*‖cuspFrequency h‖))/v^2 :=
        div_le_div_of_nonneg_left (mul_nonneg cubicBesselLowerConstant_pos.le (Real.exp_pos _).le)
          (sq_pos_of_pos hvp) hden
      _ ≤ _ := div_le_div_of_nonneg_right hnum (sq_nonneg v)
  have hmono := setIntegral_mono_on («μ» := volume)
    (f := fun _ : ℝ => lower)
    (g := fun v : ℝ => RCLike.re (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2))
    (integrableOn_const (hs := isCompact_Icc.measure_ne_top) : IntegrableOn (fun _ : ℝ => lower) (Set.Icc a b))
    hi.re measurableSet_Icc hpoint
  rw [setIntegral_const,Real.volume_real_Icc_of_le hab.le,smul_eq_mul] at hmono
  have hreal : (∫v in Set.Icc a b,RCLike.re
      (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2))=
      Complex.re (∫v in Set.Icc a b,schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) :=
    integral_re hi
  rw [hreal] at hmono
  have hfinal := hmono.trans (Complex.re_le_norm _)
  convert! hfinal using 1 ; dsimp [lower] ; ring


end CubicEisenstein

end

end OAI

end


