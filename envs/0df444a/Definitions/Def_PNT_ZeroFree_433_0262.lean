-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0262
-- name    : PNT_ZeroFree_433_0262
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:47:30.80198+00:00
-- url     : https://prove2.me/theorems/8583e6e9-3bea-4e6f-a83a-f506d63604ad
-- title:
--   Zero-free region foundations: Mellin.VerticalContourShift [0262]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Mellin.VerticalContourShift
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/VerticalContourShift.lean#L80-L628

import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0100
import Definitions.Def_PNT_ZeroFree_433_0101
import Definitions.Def_PNT_ZeroFree_433_0148_parallel2
import Definitions.Def_PNT_ZeroFree_433_0221_parallel2
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0229_parallel2
import Definitions.Def_PNT_ZeroFree_433_0262_parallel1

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


open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CubicEisenstein


theorem cubic_bessel_series_mellin {α : Type*} [Countable α]
    (freq a : α→ℂ) (hf : ∀i,freq i≠0) (s : ℂ) (hs : -(1/3)<s.re)
    (ha : Summable (fun i=>‖a i‖*‖freq i‖^(-(2*s.re+1)))) :
    (∫v : ℝ in Set.Ioi 0,∑'i,a i*((v:ℂ)^(2*s)*
      schlafliBesselK (1/3) (4*Real.pi*‖freq i‖*v)))=
    ∑'i,a i*(((2:ℂ)^(2*s-1)*Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))/
      ((4*Real.pi*‖freq i‖:ℝ):ℂ)^(2*s+1)) := by
  have hi (i : α) := (source_cubic_bessel_mellin_integrable s (freq i) hs (hf i)).const_mul (a i)
  have hsum : Summable (fun i=>∫v : ℝ in Set.Ioi 0,
      ‖a i*((v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*‖freq i‖*v))‖) := by
    simp only [weighted_cubic_bessel_integral_norm s _ _ (hf _)]
    exact ha.mul_right _
  rw [←integral_tsum_of_summable_integral_norm hi hsum]
  apply tsum_congr
  intro i
  rw [integral_const_mul,source_cubic_bessel_mellin s (freq i) hs (hf i)]

end CubicEisenstein

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CubicEisenstein


theorem radialBesselProfile_mellin {α : Type*} [Countable α]
    (r : α→ℝ) (hr : ∀i,0<r i) (a : α→ℂ) (q : ℝ) (hq : 0<q)
    (s : ℂ) (hs : -(1/3)<s.re)
    (ha : Summable (fun i=>‖a i‖*(r i)^(1/2-s.re))) :
    mellin (radialBesselProfile r a q) (2*s)=
      (((2:ℂ)^(2*s-1)*Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))/
        ((4*Real.pi*q:ℝ):ℂ)^(2*s+1))*(∑'i,a i*(r i:ℂ)^(1/2-s)) := by
  let f : α→ℂ := fun i=>((q*Real.sqrt (r i):ℝ):ℂ)
  have hf (i : α) : f i≠0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos hq (Real.sqrt_pos.mpr (hr i))).ne'
  have has : Summable (fun i=>‖a i*(r i:ℂ)‖*‖f i‖^(-(2*s.re+1))) := by
    simp only [f,radial_bessel_coefficient_norm _ q s.re (hr _) hq]
    exact ha.mul_left _
  have hid := cubic_bessel_series_mellin f (fun i=>a i*(r i:ℂ)) hf s hs has
  calc
    _=(∫v : ℝ in Set.Ioi 0,∑'i,(a i*(r i:ℂ))*((v:ℂ)^(2*s)*
        schlafliBesselK (1/3) (4*Real.pi*‖f i‖*v))) := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only [radialBesselProfile]
      simp only [smul_eq_mul]
      rw [←tsum_mul_left]
      apply tsum_congr
      intro i
      have hp : (v:ℂ)^(2*s-1)*(v:ℂ)=(v:ℂ)^(2*s) := by
        calc
          _=(v:ℂ)^(2*s-1)*(v:ℂ)^1 := by rw [Complex.cpow_one]
          _=(v:ℂ)^((2*s-1)+1) :=
            (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne')).symm
          _=_ := by rw [sub_add_cancel]
      have hn : ‖f i‖=q*Real.sqrt (r i) :=
        Complex.norm_of_nonneg (mul_pos hq (Real.sqrt_pos.mpr (hr i))).le
      rw [hn]
      have hk : 4*Real.pi*q*Real.sqrt (r i)*v=4*Real.pi*(q*Real.sqrt (r i))*v := by ring
      rw [hk]
      change (v:ℂ)^(2*s-1)*_=_
      linear_combination (a i*(r i:ℂ))*schlafliBesselK (1/3) (4*Real.pi*(q*Real.sqrt (r i))*v)*hp
    _=_ := by
      rw [hid,←tsum_mul_left]
      apply tsum_congr
      intro i
      have hn : ‖f i‖=q*Real.sqrt (r i) :=
        Complex.norm_of_nonneg (mul_pos hq (Real.sqrt_pos.mpr (hr i))).le
      rw [hn,show 4*Real.pi*(q*Real.sqrt (r i))=(4*Real.pi*q)*Real.sqrt (r i) by ring]
      exact radial_bessel_coefficient_identity (r i) (4*Real.pi*q) (hr i)
        (by positivity) (a i) _ s

end CubicEisenstein

end

end OAI

end


