-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0234_parallel1
-- name    : PNT_ZeroFree_433_0234_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:38:15.948582+00:00
-- url     : https://prove2.me/theorems/de0a430f-8b0f-4217-94ea-30da45c3b839
-- title:
--   Zero-free region foundations: Eisenstein.BesselDerivatives [0234_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.BesselDerivatives
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/BesselDerivatives.lean#L212-L636

import Definitions.Def_PNT_ZeroFree_433_0234_parallel1_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/BesselDerivatives.lean
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
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding


lemma cubicBesselDerivativeMajorant_integral :
    (∫t in Set.Ioi (0:ℝ),t^(-(2:ℝ)/3)*Real.exp (-t/2))=
      (2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3) := by
  have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (1/3:ℝ)) (r := (1/2:ℝ)) (by norm_num) (by norm_num)
  convert! hh using 1 <;> norm_num ; congr 2 ; funext t ; ring_nf

lemma cubicBesselIntegral_norm_bound (x : ℝ) :
    ‖∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t‖≤
      Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3)) := by
  have hpos : 0≤∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicBesselDensity_nonneg x t ht.le
  rw [Real.norm_of_nonneg hpos]
  exact cubicBesselIntegral_upper x

lemma cubicBesselIntegralDeriv_norm_bound (delta x : ℝ) (hdelta : 0<delta) (hx : delta≤x) :
    ‖∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t‖≤
      (4/delta)*Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3)) := by
  have hi := cubicBesselDensityDeriv_integrable x (hdelta.trans_le hx)
  have hb := integral_mono_ae hi.norm
    (cubicBesselDerivativeMajorant_integrable.const_mul ((4/delta)*Real.exp (-x/2)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cubicBesselDensityDeriv_bound delta x t hdelta hx ht)
  rw [integral_const_mul,cubicBesselDerivativeMajorant_integral] at hb
  exact (norm_integral_le_integral_norm _).trans hb

def cubicBesselDerivativeUpper (delta : ℝ) : ℝ :=
  ((1/12:ℝ)*(delta/2)^(-(4:ℝ)/3)+
    (1/2:ℝ)*(delta/2)^(-(1:ℝ)/3)*(4/delta))*
      ((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))

lemma cubicBesselDerivativeUpper_nonneg (delta : ℝ) (hdelta : 0<delta) :
    0≤cubicBesselDerivativeUpper delta := by
  unfold cubicBesselDerivativeUpper
  positivity

lemma schlafliBesselK_cubic_derivative_bound (delta x : ℝ) (hdelta : 0<delta) (hx : delta≤x) :
    ‖schlafliBesselK_cubic_derivative x‖≤cubicBesselDerivativeUpper delta*Real.exp (-x/2) := by
  have hxp : 0<x := hdelta.trans_le hx
  have hp1 : (x/2)^(-(1:ℝ)/3)≤(delta/2)^(-(1:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have hp4 : (x/2)^(-(4:ℝ)/3)≤(delta/2)^(-(4:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  rw [schlafliBesselK_cubic_derivative,Complex.norm_real,cubicBesselRealDeriv]
  calc
    _ ≤ ‖(-(1:ℝ)/12)*(x/2)^(-(4:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t)‖+
        ‖(1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t)‖ := norm_add_le _ _
    _ = (1/12:ℝ)*(x/2)^(-(4:ℝ)/3)*‖∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t‖+
        (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*‖∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t‖ := by
      have hn4 : ‖(x/2)^(-(4:ℝ)/3)‖=(x/2)^(-(4:ℝ)/3) :=
        Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)
      have hn1 : ‖(x/2)^(-(1:ℝ)/3)‖=(x/2)^(-(1:ℝ)/3) :=
        Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)
      simp only [norm_mul,hn4,hn1]
      norm_num
    _ ≤ (1/12:ℝ)*(delta/2)^(-(4:ℝ)/3)*
          (Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3)))+
        (1/2:ℝ)*(delta/2)^(-(1:ℝ)/3)*
          ((4/delta)*Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))) := by
      gcongr
      · exact cubicBesselIntegral_norm_bound x
      · exact cubicBesselIntegralDeriv_norm_bound delta x hdelta hx
    _ = _ := by unfold cubicBesselDerivativeUpper;ring

end


section

open scoped BigOperators Classical Topology
open Filter Set
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O


lemma gaussPrimeWeight_analytic (p:Eis) (hp:Prime p) (s:ℂ):
    AnalyticAt ℂ (fun z:ℂ=>(Ideal.absNorm (Ideal.span {p}):ℂ)^(-z)) s:=by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  exact Eventually.of_forall fun z=>(differentiableAt_id.neg).const_cpow (Or.inl
    (Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))))

lemma gaussPrimeWeight_center (p:Eis) (hp:Prime p):
    (Ideal.absNorm (Ideal.span {p}):ℂ)^3*
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ)))^3=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹:=by
  have hQ:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  rw [←Complex.cpow_nat_mul,←Complex.cpow_natCast _ 3,←Complex.cpow_add _ _ hQ]
  convert! Complex.cpow_neg_one (Ideal.absNorm (Ideal.span {p}):ℂ) using 1 ;congr 1 ;norm_num


end


open Filter MeasureTheory
open scoped BigOperators Classical Topology ComplexConjugate

def inverseCuspPath (c d : ℂ) (v : ℝ) (direction : ℂ) (t : ℝ) : ℂ×ℝ :=
  (-d/c-(t:ℂ)*star direction/(c^2*((v^2+t^2*‖direction‖^2:ℝ):ℂ)),
    v/(‖c‖^2*(v^2+t^2*‖direction‖^2)))

lemma inverseCuspPath_zero (c d : ℂ) (v : ℝ) (direction : ℂ)
    (hc : c≠0) (hv : 0<v) :
    inverseCuspPath c d v direction 0=(-d/c,1/(‖c‖^2*v)) := by
  unfold inverseCuspPath
  simp only [Complex.ofReal_zero,zero_pow (by decide : 2≠0),zero_mul,add_zero,zero_div,sub_zero]
  congr 1
  field_simp [norm_ne_zero_iff.mpr hc,hv.ne']

theorem inverseCuspPath_hasDerivAt (c d : ℂ) (v : ℝ) (direction : ℂ)
    (hc : c≠0) (hv : 0<v) :
    HasDerivAt (inverseCuspPath c d v direction)
      (-(star direction)/(c^2*(v:ℂ)^2),0) 0 := by
  have hn : ‖c‖≠0 := norm_ne_zero_iff.mpr hc
  have hvc : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hden : HasDerivAt (fun t : ℝ=>v^2+t^2*‖direction‖^2) 0 0 := by
    convert! (((hasDerivAt_id (0:ℝ)).pow 2).mul_const (‖direction‖^2)).const_add (v^2) using 1 <;> norm_num
  have hnum : HasDerivAt (fun t : ℝ=>(t:ℂ)*star direction) (star direction) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const (star direction))
  have hdenC := hden.ofReal_comp.const_mul (c^2)
  have hdenR := hden.const_mul (‖c‖^2)
  have hcz : c^2*((v^2+(0:ℝ)^2*‖direction‖^2:ℝ):ℂ)≠0 := by
    simpa using mul_ne_zero (pow_ne_zero 2 hc) (pow_ne_zero 2 hvc)
  have hrz : ‖c‖^2*(v^2+(0:ℝ)^2*‖direction‖^2)≠0 := by positivity
  have hz : HasDerivAt
      (fun t : ℝ=>-d/c-(t:ℂ)*star direction/(c^2*((v^2+t^2*‖direction‖^2:ℝ):ℂ)))
      (-(star direction)/(c^2*(v:ℂ)^2)) 0 := by
    convert! (hnum.div hdenC hcz).const_sub (-d/c) using 1 ;
      simp only [zero_pow (by decide : 2≠0),zero_mul,add_zero,Complex.ofReal_pow,
        Complex.ofReal_zero,mul_zero,sub_zero]
    field_simp

  have hvd : HasDerivAt (fun t : ℝ=>v/(‖c‖^2*(v^2+t^2*‖direction‖^2))) 0 0 := by
    convert! (hasDerivAt_const (0:ℝ) v).div hdenR hrz using 1 ; simp
  exact hz.prodMk hvd

theorem inverseCuspPath_comp_hasDerivAt (c d : ℂ) (v : ℝ) (direction : ℂ)
    (hc : c≠0) (hv : 0<v) (F : ℂ×ℝ→ℂ) (A : (ℂ×ℝ)→L[ℝ]ℂ)
    (hF : HasFDerivAt F A (-d/c,1/(‖c‖^2*v))) :
    HasDerivAt (fun t=>F (inverseCuspPath c d v direction t))
      (A (-(star direction)/(c^2*(v:ℂ)^2),0)) 0 := by
  have hf : HasFDerivAt F A (inverseCuspPath c d v direction 0) := by
    rwa [inverseCuspPath_zero c d v direction hc hv]
  exact hf.comp_hasDerivAt 0 (inverseCuspPath_hasDerivAt c d v direction hc hv)

end CubicEisenstein

end

end OAI

end


