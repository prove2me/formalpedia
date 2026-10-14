-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0240_parallel2
-- name    : PNT_ZeroFree_433_0240_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:35:59.069881+00:00
-- url     : https://prove2.me/theorems/2b78db81-9229-4f60-90d6-4c481cee9675
-- title:
--   Zero-free region foundations: Eisenstein.CuspDilation [0240_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.CuspDilation
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CuspDilation.lean#L294-L381

import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0117_1
import Definitions.Def_PNT_ZeroFree_433_0131
import Definitions.Def_PNT_ZeroFree_433_0132
import Definitions.Def_PNT_ZeroFree_433_0140_parallel1
import Definitions.Def_PNT_ZeroFree_433_0159_parallel1
import Definitions.Def_PNT_ZeroFree_433_0178_parallel1
import Definitions.Def_PNT_ZeroFree_433_0189_parallel1
import Definitions.Def_PNT_ZeroFree_433_0194_parallel1
import Definitions.Def_PNT_ZeroFree_433_0196_parallel1
import Definitions.Def_PNT_ZeroFree_433_0199_parallel1
import Definitions.Def_PNT_ZeroFree_433_0215_parallel2
import Definitions.Def_PNT_ZeroFree_433_0227_parallel2
import Definitions.Def_PNT_ZeroFree_433_0230_parallel1
import Definitions.Def_PNT_ZeroFree_433_0232_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0236_parallel1
import Definitions.Def_PNT_ZeroFree_433_0243_parallel2
import Definitions.Def_PNT_ZeroFree_433_0248_parallel1
import Definitions.Def_PNT_ZeroFree_433_0253_parallel1
import Definitions.Def_PNT_ZeroFree_433_0263_parallel2
import Definitions.Def_PNT_ZeroFree_433_0266_parallel1
import Definitions.Def_PNT_ZeroFree_433_0270_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CuspDilation.lean
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

open scoped BigOperators Classical


open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma cuspTransition_dilate (A : ℝ) (hA : A≠0) :
    cuspTransition A (2*A)=fun v => cuspTransition 1 2 (v/A) := by
  funext v
  unfold cuspTransition
  congr 1
  field_simp

lemma cuspTransition_dilate_deriv (A v : ℝ) (hA : A≠0) :
    deriv (cuspTransition A (2*A)) v=deriv (cuspTransition 1 2) (v/A)/A := by
  rw [cuspTransition_dilate A hA]
  have hd := (((cuspTransition_contDiff 1 2).differentiable (by simp) (v/A)).hasDerivAt).comp v
    ((hasDerivAt_id v).div_const A)
  simpa [Function.comp_def,id_eq,div_eq_mul_inv] using hd.deriv

lemma cuspTransition_dilate_second (A v : ℝ) (hA : A≠0) :
    deriv (deriv (cuspTransition A (2*A))) v=
      deriv (deriv (cuspTransition 1 2)) (v/A)/A^2 := by
  have he : deriv (cuspTransition A (2*A))=
      fun x => deriv (cuspTransition 1 2) (x/A)/A := by
    funext x
    exact cuspTransition_dilate_deriv A x hA
  rw [he]
  have hc := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff 1 2)).2
  have hd := (((hc.differentiable (by simp) (v/A)).hasDerivAt).comp v
    ((hasDerivAt_id v).div_const A)).div_const A
  simp only [Function.comp_def,id_eq] at hd
  convert! hd.deriv using 1; field_simp

def cuspBaseDefectFactor (s : ℂ) (x : ℝ) : ℂ :=
  (x:ℂ)^2*(deriv (deriv (cuspTransition 1 2)) x:ℝ)+
    (2*s-1)*(x:ℂ)*(deriv (cuspTransition 1 2) x:ℝ)

lemma cuspBaseDefectFactor_continuous (s : ℂ) : Continuous (cuspBaseDefectFactor s) := by
  have h1 := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff 1 2)).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  unfold cuspBaseDefectFactor
  exact ((Complex.continuous_ofReal.pow 2).mul (Complex.continuous_ofReal.comp h2.continuous)).add
    ((continuous_const.mul Complex.continuous_ofReal).mul (Complex.continuous_ofReal.comp h1.continuous))

lemma cuspBaseDefectFactor_compact (s : ℂ) : HasCompactSupport (cuspBaseDefectFactor s) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Set.Icc (1:ℝ) 2))
  intro x hx
  by_contra hn
  have hout : x<1 ∨ 2<x := by simpa only [Set.mem_Icc,not_and_or,not_le] using hn
  obtain ⟨h1,h2⟩ := cuspTransition_derivatives 1 2 x (by norm_num) hout
  exact hx (by simp [cuspBaseDefectFactor,h1,h2])

lemma cuspSeedDefectProfile_dilate (A v : ℝ) (hA : A≠0) (s : ℂ) :
    cuspSeedDefectProfile A (2*A) s v=
      positiveHeightPower s v*cuspBaseDefectFactor s (v/A) := by
  rw [cuspSeedDefectProfile,cuspTransition_dilate_deriv A v hA,cuspTransition_dilate_second A v hA]
  unfold cuspBaseDefectFactor
  push_cast
  field_simp

theorem cuspSeedDefectProfile_dilate_bound :
    ∃C : ℝ,0≤C ∧ ∀A : ℝ,1≤A → ∀v : ℝ,
      ‖cuspSeedDefectProfile A (2*A) (4/3) v‖≤C*A^2 := by
  obtain ⟨B,hB⟩ := (cuspBaseDefectFactor_compact (4/3)).exists_bound_of_continuous
    (cuspBaseDefectFactor_continuous (4/3))
  let C := max B 0
  have hC : 0≤C := le_max_right _ _
  have hbound (x : ℝ) : ‖cuspBaseDefectFactor (4/3) x‖≤C := (hB x).trans (le_max_left _ _)
  refine ⟨4*C,by positivity,fun A hA v => ?_⟩
  have hApos : 0<A := lt_of_lt_of_le zero_lt_one hA
  by_cases hv : v∈Set.Icc A (2*A)
  · have hv1 : 1≤v := hA.trans hv.1
    have hvpos : 0<v := hApos.trans_le hv.1
    have hp : ‖positiveHeightPower (4/3) v‖≤v^2 := by
      rw [positiveHeightPower_eq_cpow _ _ hvpos,Complex.norm_cpow_eq_rpow_re_of_pos hvpos]
      norm_num
      have hh := Real.rpow_le_rpow_of_exponent_le hv1 (show (4/3:ℝ)≤2 by norm_num)
      simpa using hh
    rw [cuspSeedDefectProfile_dilate A v hApos.ne',norm_mul]
    have hm := mul_le_mul hp (hbound (v/A)) (norm_nonneg _) (sq_nonneg v)
    calc
      _ ≤ v^2*C := hm
      _ ≤ (2*A)^2*C := mul_le_mul_of_nonneg_right (sq_le_sq₀ hvpos.le (by positivity) |>.mpr hv.2) hC
      _ = (4*C)*A^2 := by ring
  · have hout : v<A ∨ 2*A<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using hv
    rw [cuspSeedDefectProfile_zero A (2*A) (4/3) v (by linarith) hout,norm_zero]
    positivity

theorem smoothCuspSeedDefect_dilate_bound :
    ∃C : ℝ,0≤C ∧ ∀A : ℝ,1≤A → ∀w : HyperbolicSpace,
      ‖smoothCuspSeedDefect A (2*A) (4/3) w‖≤C*A^2 := by
  obtain ⟨C,hC,hbound⟩ := cuspSeedDefectProfile_dilate_bound
  exact ⟨C,hC,fun A hA w => cuspCutoffCorrection_norm_le _ _ (by positivity) (hbound A hA) w⟩


end CubicEisenstein


end

end OAI

end


