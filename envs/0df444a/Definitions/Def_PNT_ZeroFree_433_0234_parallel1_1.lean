-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0234_parallel1_1
-- name    : PNT_ZeroFree_433_0234_parallel1_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:32:30.177582+00:00
-- url     : https://prove2.me/theorems/1c2554b5-48ff-48f6-a405-ad2791c6d220
-- title:
--   Zero-free region foundations: Eisenstein.BesselDerivatives [0234_parallel1_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.BesselDerivatives
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/BesselDerivatives.lean#L83-L210

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0094
import Definitions.Def_PNT_ZeroFree_433_0123_parallel1
import Definitions.Def_PNT_ZeroFree_433_0126_parallel1
import Definitions.Def_PNT_ZeroFree_433_0132_parallel1
import Definitions.Def_PNT_ZeroFree_433_0143_parallel1
import Definitions.Def_PNT_ZeroFree_433_0148_parallel1
import Definitions.Def_PNT_ZeroFree_433_0219_parallel1
import Definitions.Def_PNT_ZeroFree_433_0222_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0241_parallel1
import Definitions.Def_PNT_ZeroFree_433_0506_parallel1

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

def cubicBesselDensityDeriv (x t : ℝ) : ℝ := -(x/(2*t))*cubicBesselDensity x t

lemma cubicBesselDensity_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun y : ℝ => cubicBesselDensity y t) (cubicBesselDensityDeriv x t) x := by
  have he := ((((hasDerivAt_id x).pow 2).div_const (4*t)).const_sub (-t)).exp.const_mul (t^(-(2:ℝ)/3))
  simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,mul_one] at he
  convert! he using 1
  all_goals unfold cubicBesselDensityDeriv cubicBesselDensity
  all_goals norm_num
  all_goals ring

lemma cubic_exp_damping (y : ℝ) : y*Real.exp (-y)≤1 := by
  have hy : y≤Real.exp y := by linarith [Real.add_one_le_exp y]
  calc
    _ ≤ Real.exp y*Real.exp (-y) := mul_le_mul_of_nonneg_right hy (Real.exp_pos _).le
    _ = 1 := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]

lemma cubicBesselDensityDeriv_bound (delta x t : ℝ)
    (hdelta : 0<delta) (hx : delta≤x) (ht : 0<t) :
    ‖cubicBesselDensityDeriv x t‖≤
      (4/delta)*Real.exp (-x/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by
  have hxp : 0<x := hdelta.trans_le hx
  have hdamp : (x/(2*t))*Real.exp (-(x^2/(8*t)))≤4/x := by
    have hrewrite : x/(2*t)=(4/x)*(x^2/(8*t)) := by field_simp;ring
    rw [hrewrite,mul_assoc]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (cubic_exp_damping (x^2/(8*t))) (by positivity : 0≤4/x)
  have hyoung : x/2-t/2≤x^2/(8*t) :=
    (le_div_iff₀ (show 0<8*t by positivity)).mpr (by nlinarith [sq_nonneg (x-2*t)])
  have he : Real.exp (-t-x^2/(4*t))≤
      Real.exp (-x/2)*Real.exp (-t/2)*Real.exp (-(x^2/(8*t))) := by
    rw [←Real.exp_add,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsplit : x^2/(4*t)=2*(x^2/(8*t)) := by ring
    rw [hsplit]
    linarith
  have hnorm : ‖cubicBesselDensityDeriv x t‖=
      (x/(2*t))*t^(-(2:ℝ)/3)*Real.exp (-t-x^2/(4*t)) := by
    unfold cubicBesselDensityDeriv cubicBesselDensity
    rw [norm_mul,norm_neg,Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by positivity)]
    ring
  rw [hnorm]
  calc
    _ ≤ (x/(2*t))*t^(-(2:ℝ)/3)*
        (Real.exp (-x/2)*Real.exp (-t/2)*Real.exp (-(x^2/(8*t)))) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = ((x/(2*t))*Real.exp (-(x^2/(8*t))))*
        Real.exp (-x/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by ring
    _ ≤ (4/x)*Real.exp (-x/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by
      gcongr
    _ ≤ _ := by
      gcongr

lemma cubicBesselDerivativeMajorant_integrable :
    IntegrableOn (fun t : ℝ => t^(-(2:ℝ)/3)*Real.exp (-t/2)) (Set.Ioi 0) volume := by
  have hh := integrableOn_rpow_mul_exp_neg_mul_rpow (s:=-(2:ℝ)/3) (p:=1) (b:=1/2)
    (by norm_num) (by norm_num) (by norm_num)
  apply hh.congr
  filter_upwards with t
  rw [Real.rpow_one]
  congr 1
  congr 1
  ring

lemma cubicBesselDensityDeriv_integrable (x : ℝ) (hx : 0<x) :
    IntegrableOn (cubicBesselDensityDeriv x) (Set.Ioi 0) volume := by
  apply (cubicBesselDerivativeMajorant_integrable.const_mul ((4/x)*Real.exp (-x/2))).mono'
  · unfold cubicBesselDensityDeriv cubicBesselDensity
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicBesselDensityDeriv_bound x x t hx le_rfl ht

lemma cubicBesselIntegral_hasDerivAt (x : ℝ) (hx : 0<x) :
    HasDerivAt (fun y : ℝ => ∫t in Set.Ioi (0:ℝ),cubicBesselDensity y t)
      (∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t) x := by
  let delta := x/2
  have hdelta : 0<delta := half_pos hx
  have hU : Set.Ioi delta∈𝓝 x := isOpen_Ioi.mem_nhds (by
    change delta<x
    dsimp [delta]
    linarith)
  have hbound : ∀ᵐt ∂volume.restrict (Set.Ioi (0:ℝ)),∀y∈Set.Ioi delta,
      ‖cubicBesselDensityDeriv y t‖≤(4/delta)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htp : 0<t := ht
    intro y hy
    have hyp : 0<y := hdelta.trans hy
    calc
      _ ≤ (4/delta)*Real.exp (-y/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) :=
        cubicBesselDensityDeriv_bound delta y t hdelta hy.le ht
      _ ≤ _ := by
        have he : Real.exp (-y/2)≤1 := Real.exp_le_one_iff.mpr (by linarith)
        calc
          _ ≤ (4/delta)*1*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by gcongr
          _ = _ := by ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := volume.restrict (Set.Ioi (0:ℝ)))
    (F := cubicBesselDensity) (F' := cubicBesselDensityDeriv)
    (bound := fun t => (4/delta)*(t^(-(2:ℝ)/3)*Real.exp (-t/2))) hU
    (Eventually.of_forall (fun y => by unfold cubicBesselDensity;fun_prop))
    (cubicBesselDensity_integrable x)
    (by unfold cubicBesselDensityDeriv cubicBesselDensity;fun_prop)
    hbound (cubicBesselDerivativeMajorant_integrable.const_mul (4/delta))
    (Eventually.of_forall (fun t y _ => cubicBesselDensity_hasDerivAt y t))
  exact h.2

def cubicBesselRealDeriv (x : ℝ) : ℝ :=
  (-(1:ℝ)/12)*(x/2)^(-(4:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t)+
    (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t)

def schlafliBesselK_cubic_derivative (x : ℝ) : ℂ := (cubicBesselRealDeriv x:ℂ)

lemma schlafliBesselK_cubic_hasDerivAt (x : ℝ) (hx : 0<x) :
    HasDerivAt (fun y : ℝ => schlafliBesselK (1/3) y)
      (schlafliBesselK_cubic_derivative x) x := by
  have hp : HasDerivAt (fun y : ℝ => (1/2:ℝ)*(y/2)^(-(1:ℝ)/3))
      ((-(1:ℝ)/12)*(x/2)^(-(4:ℝ)/3)) x := by
    have hh := (((hasDerivAt_id x).div_const 2).rpow_const
      (p:=-(1:ℝ)/3) (Or.inl (by positivity : x/2≠0))).const_mul (1/2:ℝ)
    convert! hh using 1 <;> norm_num ; ring
  have hr := hp.mul (cubicBesselIntegral_hasDerivAt x hx)
  have hreal : HasDerivAt (fun y : ℝ => (1/2:ℝ)*(y/2)^(-(1:ℝ)/3)*
      (∫t in Set.Ioi (0:ℝ),cubicBesselDensity y t)) (cubicBesselRealDeriv x) x := by
    exact hr
  apply hreal.ofReal_comp.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact schlafliBesselK_cubic_real y hy


end


end CubicEisenstein

end

end OAI

end


