-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0228_parallel1_1
-- name    : PNT_ZeroFree_433_0228_parallel1_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:49:03.002889+00:00
-- url     : https://prove2.me/theorems/73934b50-46f9-4e04-8b14-e83781619192
-- title:
--   Zero-free region foundations: Eisenstein.CuspAverage [0228_parallel1_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.CuspAverage
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CuspAverage.lean#L81-L508

import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0079_1
import Definitions.Def_PNT_ZeroFree_433_0167
import Definitions.Def_PNT_ZeroFree_433_0327
import Definitions.Def_PNT_ZeroFree_433_0505

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CuspAverage.lean
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

open Filter MeasureTheory
open scoped BigOperators Classical Topology

lemma ramified_denominator_ne_zero (s : ℂ) (hs : 1<s.re) :
    (3:ℂ)^(3*s-3)-1≠0 := by
  intro he
  have hpow : (3:ℂ)^(3*s-3)=1 := sub_eq_zero.mp he
  have hnorm : 1<‖(3:ℂ)^(3*s-3)‖ := by
    rw [show (3:ℂ)=((3:ℝ):ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    apply Real.one_lt_rpow (by norm_num)
    norm_num
    linarith
  rw [hpow,norm_one] at hnorm
  exact lt_irrefl _ hnorm


section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section

lemma complex_gaussian_power_integrable (s : ℂ) (r : ℝ)
    (hs : 0<s.re) (hr : 0<r) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(s-1)*Complex.exp (-(r:ℂ)*(x:ℂ)^2))
      (Set.Ioi 0) volume := by
  have hs2 : 0<(s/(2:ℂ)).re := by simpa using half_pos hs
  have hbase : MellinConvergent (fun t : ℝ => Complex.exp (-(t:ℂ))) (s/2) := by
    simpa only [MellinConvergent,smul_eq_mul,Complex.ofReal_exp,Complex.ofReal_neg,mul_comm]
      using Complex.GammaIntegral_convergent hs2
  have hlinear := (MellinConvergent.comp_mul_left
    (f := fun t : ℝ => Complex.exp (-(t:ℂ))) (s := s/2) hr).mpr hbase
  have hgaussian := (MellinConvergent.comp_rpow
    (f := fun t : ℝ => Complex.exp (-((r*t:ℝ):ℂ))) (s := s) (a := 2)
      (by norm_num)).mpr hlinear
  simpa only [MellinConvergent,smul_eq_mul,Real.rpow_two,
    Complex.ofReal_mul,Complex.ofReal_pow,neg_mul] using hgaussian

lemma complex_gaussian_power_integral (s : ℂ) (r : ℝ)
    (hs : 0<s.re) (hr : 0<r) :
    (∫x : ℝ in Set.Ioi 0,(x:ℂ)^(s-1)*Complex.exp (-(r:ℂ)*(x:ℂ)^2)) =
      (1/2:ℂ)*((1/(r:ℂ))^(s/2)*Complex.Gamma (s/2)) := by
  have hs2 : 0<(s/(2:ℂ)).re := by simpa using half_pos hs
  have he := mellin_comp_rpow (fun t : ℝ => Complex.exp (-((r*t:ℝ):ℂ))) s 2
  simp only [mellin,smul_eq_mul,Real.rpow_two,Complex.ofReal_mul,
    Complex.ofReal_pow,Complex.real_smul] at he
  norm_num only [Complex.ofReal_ofNat] at he
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hs2 hr] at he
  simpa [neg_mul] using he

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

def cubicMellinMixture (s : ℂ) (t x : ℝ) : ℂ :=
  (t:ℂ)^(-(2:ℂ)/3)*Complex.exp (-(t:ℂ))*
    ((x:ℂ)^((s-1/3)-1)*Complex.exp (-((1/(4*t):ℝ):ℂ)*(x:ℂ)^2))

lemma cubicMellinMixture_slice_integrable (s : ℂ) (hs : 1/3<s.re)
    (t : ℝ) (ht : 0<t) :
    IntegrableOn (cubicMellinMixture s t) (Set.Ioi 0) volume := by
  apply (complex_gaussian_power_integrable (s-1/3) (1/(4*t))
    (by norm_num; linarith) (by positivity)).const_mul

lemma cubicMellinMixture_integral_x (s : ℂ) (hs : 1/3<s.re)
    (t : ℝ) (ht : 0<t) :
    (∫x : ℝ in Set.Ioi 0,cubicMellinMixture s t x) =
      ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
        ((t:ℂ)^((s+1/3)/2-1)*Complex.exp (-(t:ℂ))) := by
  simp only [cubicMellinMixture,integral_const_mul]
  rw [complex_gaussian_power_integral (s-1/3) (1/(4*t))
    (by norm_num; linarith) (by positivity)]
  have hb : (1/(((1/(4*t):ℝ):ℂ)))=(4:ℂ)*(t:ℂ) := by
    push_cast
    field_simp
  have hm : ((4:ℂ)*(t:ℂ))^((s-1/3)/2)=
      (4:ℂ)^((s-1/3)/2)*(t:ℂ)^((s-1/3)/2) := by
    simpa only [Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg (by norm_num : 0≤(4:ℝ)) ht.le ((s-1/3)/2)
  rw [hb,hm]
  have hp : (t:ℂ)^(-(2:ℂ)/3)*(t:ℂ)^((s-1/3)/2)=
      (t:ℂ)^((s+1/3)/2-1) := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
    congr 1
    ring
  calc
    _ = ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
        (((t:ℂ)^(-(2:ℂ)/3)*(t:ℂ)^((s-1/3)/2))*Complex.exp (-(t:ℂ))) := by ring
    _ = _ := by rw [hp]

lemma cubicMellinMixture_norm (s : ℂ) (t x : ℝ) (ht : 0<t) (hx : 0<x) :
    ‖cubicMellinMixture s t x‖ =
      (t^(-(2:ℝ)/3)*Real.exp (-t))*
        (x^((s.re-1/3)-1)*Real.exp (-(1/(4*t))*x^2)) := by
  have he : -((1/(4*t):ℝ):ℂ)*(x:ℂ)^2=(-(1/(4*t))*x^2:ℝ) := by
    push_cast
    rfl
  simp only [cubicMellinMixture,norm_mul,he,
    Complex.norm_cpow_eq_rpow_re_of_pos ht,Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_exp,Complex.ofReal_re,Complex.neg_re]
  norm_num

lemma real_gaussian_power_integral (sigma r : ℝ) (hs : 0<sigma) (hr : 0<r) :
    (∫x : ℝ in Set.Ioi 0,x^(sigma-1)*Real.exp (-r*x^2)) =
      r^(-sigma/2)*(1/2)*Real.Gamma (sigma/2) := by
  simpa only [Real.rpow_two,sub_add_cancel] using
    (_root_.integral_rpow_mul_exp_neg_mul_rpow (p:=2) (q:=sigma-1) (b:=r)
      (by norm_num) (by linarith) hr)

lemma cubicMellinMixture_integral_norm (s : ℂ) (hs : 1/3<s.re)
    (t : ℝ) (ht : 0<t) :
    (∫x : ℝ in Set.Ioi 0,‖cubicMellinMixture s t x‖) =
      ((1/2:ℝ)*(4:ℝ)^((s.re-1/3)/2)*Real.Gamma ((s.re-1/3)/2))*
        (t^((s.re+1/3)/2-1)*Real.exp (-t)) := by
  calc
    _ = ∫x : ℝ in Set.Ioi 0,(t^(-(2:ℝ)/3)*Real.exp (-t))*
        (x^((s.re-1/3)-1)*Real.exp (-(1/(4*t))*x^2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact cubicMellinMixture_norm s t x ht hx
    _ = _ := by
      rw [integral_const_mul,real_gaussian_power_integral (s.re-1/3) (1/(4*t))
        (by linarith) (by positivity)]
      have hpow : (1/(4*t):ℝ)^(-(s.re-1/3)/2)=(4:ℝ)^((s.re-1/3)/2)*t^((s.re-1/3)/2) := by
        rw [show -(s.re-1/3)/2=-((s.re-1/3)/2) by ring,
          Real.rpow_neg_eq_inv_rpow,one_div,inv_inv,
          Real.mul_rpow (by norm_num : 0≤(4:ℝ)) ht.le]
      rw [hpow]
      have hp : t^(-(2:ℝ)/3)*t^((s.re-1/3)/2)=t^((s.re+1/3)/2-1) := by
        rw [←Real.rpow_add ht]
        congr 1
        ring
      calc
        _ = ((1/2:ℝ)*(4:ℝ)^((s.re-1/3)/2)*Real.Gamma ((s.re-1/3)/2))*
            ((t^(-(2:ℝ)/3)*t^((s.re-1/3)/2))*Real.exp (-t)) := by ring
        _ = _ := by rw [hp]


end


end CubicEisenstein

end

end OAI

end


