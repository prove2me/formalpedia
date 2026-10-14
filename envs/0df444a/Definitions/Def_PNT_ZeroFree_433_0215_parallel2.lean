-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0215_parallel2
-- name    : PNT_ZeroFree_433_0215_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:26:38.935427+00:00
-- url     : https://prove2.me/theorems/2874431c-9b53-44d6-8a47-0cacf6fa3fbf
-- title:
--   Zero-free region foundations: Eisenstein.ScatteringCoefficients [0215_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.ScatteringCoefficients
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ScatteringCoefficients.lean#L359-L731

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0147_parallel1
import Definitions.Def_PNT_ZeroFree_433_0151_parallel2
import Definitions.Def_PNT_ZeroFree_433_0155_parallel1
import Definitions.Def_PNT_ZeroFree_433_0215_parallel1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ScatteringCoefficients.lean
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
open scoped BigOperators Classical

open ActualEisensteinCubic ConcreteTraceCRT

lemma arithmeticDirichletTerm_differentiable (h : ActualEisensteinCubic.O) (c : LevelLower) :
    Differentiable ℂ (fun s : ℂ => arithmeticDirichletTerm s h c) := by
  by_cases hc : c.1=0
  · simp only [arithmeticDirichletTerm,if_pos hc]
    exact differentiable_const _
  · have hq : ((‖eisEmbedding c.1‖^2:ℝ):ℂ)≠0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc)))
    simp only [arithmeticDirichletTerm,if_neg hc]
    exact (differentiable_id.neg.const_cpow (Or.inl hq)).mul_const _

lemma arithmeticDirichletTerm_norm_mono (h : ActualEisensteinCubic.O)
    (a : ℝ) (s : ℂ) (ha : a≤s.re) (c : LevelLower) :
    ‖arithmeticDirichletTerm s h c‖≤‖arithmeticDirichletTerm (a:ℂ) h c‖ := by
  by_cases hc : c.1=0
  · simp only [arithmeticDirichletTerm,if_pos hc,norm_zero,le_refl]
  · have hpos : 0<‖eisEmbedding c.1‖^2 := sq_pos_of_pos
      (norm_pos_iff.mpr (eisEmbedding_ne_zero hc))
    have hq : 1≤‖eisEmbedding c.1‖^2 := by
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))
    simp only [arithmeticDirichletTerm,if_neg hc,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos,Complex.neg_re,Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg ha))
      (norm_nonneg _)

theorem arithmeticDirichletSeries_differentiableAt (h : ActualEisensteinCubic.O)
    (s : ℂ) (hs : 2<s.re) :
    DifferentiableAt ℂ (fun z => arithmeticDirichletSeries z h) s := by
  let a : ℝ := (2+s.re)/2
  have ha : 2<a := by dsimp [a]; linarith
  have has : a<s.re := by dsimp [a]; linarith
  have hsum := arithmeticDirichletTerm_summable_norm (a:ℂ) (by simpa using ha) h
  have hopen : IsOpen {z : ℂ | a<z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun z => arithmeticDirichletSeries z h) {z : ℂ | a<z.re} := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun c => (arithmeticDirichletTerm_differentiable h c).differentiableOn) hopen
    intro c z hz
    exact arithmeticDirichletTerm_norm_mono h a z hz.le c
  exact (hd s has).differentiableAt (hopen.mem_nhds has)

theorem scatteringCoefficient_differentiableAt (h : ActualEisensteinCubic.O)
    (s : ℂ) (hs : 2<s.re) :
    DifferentiableAt ℂ (fun z => scatteringCoefficient z h) s :=
  (arithmeticDirichletSeries_differentiableAt h s hs).div_const _

theorem scatteringCoefficient_analyticOnNhd (h : ActualEisensteinCubic.O) :
    AnalyticOnNhd ℂ (fun z => scatteringCoefficient z h) {z : ℂ | 2<z.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    exact (scatteringCoefficient_differentiableAt h z hz).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re

end


section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

local notation "O" => ActualEisensteinCubic.O


def cuspWhittakerHeightFactor (s : ℂ) (h : ActualEisensteinCubic.O) : ℂ :=
  ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v)


lemma cuspWhittakerHeightFactor_bessel (s : ℂ) (hs : 1<s.re) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    cuspWhittakerHeightFactor s h=
      ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1)*
        ((2*Real.pi:ℂ)/Complex.Gamma s*
          (2*Real.pi*‖cuspFrequency h*v‖:ℂ)^(s-1)*
          schlafliBesselK (s-1) (4*Real.pi*‖cuspFrequency h*v‖)) := by
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
  dsimp only
  rw [sourceFourierKernel_bessel s _ hs
    (mul_ne_zero (cuspFrequency_ne_zero h hh) (Complex.ofReal_ne_zero.mpr hpos.ne'))]


end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

local notation "O" => ActualEisensteinCubic.O


lemma cuspWhittakerHeightFactor_integrable (s : ℂ) (hs : 1<s.re) (h : ActualEisensteinCubic.O) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))
      (Set.Icc (5:ℝ) 6) volume := by
  apply ContinuousOn.integrableOn_Icc
  intro v hv
  have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
  exact ((Complex.continuousAt_ofReal_cpow_const v (-s-1) (Or.inr hpos.ne')).mul
    ((sourceFourierKernel_continuous_freq s hs).continuousAt.comp
      ((Complex.continuous_ofReal.const_mul (cuspFrequency h)).continuousAt))).continuousWithinAt

lemma cuspWhittakerHeightFactor_real_re_pos (sigma : ℝ) (hsigma : 1<sigma) (h : ActualEisensteinCubic.O) :
    0<(cuspWhittakerHeightFactor (sigma:ℂ) h).re := by
  let f : ℝ→ℂ := fun v => (v:ℂ)^(-(sigma:ℂ)-1)*sourceFourierKernel (sigma:ℂ) (cuspFrequency h*v)
  have hi : IntegrableOn f (Set.Icc (5:ℝ) 6) volume :=
    cuspWhittakerHeightFactor_integrable (sigma:ℂ) hsigma h
  have hp (v : ℝ) (hv : v∈Set.Icc (5:ℝ) 6) : 0<(f v).re := by
    have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
    have he := Complex.ofReal_cpow hpos.le (-sigma-1)
    simp only [Complex.ofReal_sub,Complex.ofReal_neg,Complex.ofReal_one] at he
    change 0<((v:ℂ)^(-(sigma:ℂ)-1)*sourceFourierKernel (sigma:ℂ) (cuspFrequency h*v)).re
    rw [←he,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact mul_pos (Real.rpow_pos_of_pos hpos _) (sourceFourierKernel_real_re_pos sigma hsigma _)
  change 0<RCLike.re (∫v in Set.Icc (5:ℝ) 6,f v)
  rw [←integral_re hi]
  apply (integral_pos_iff_support_of_nonneg_ae ?_ hi.re).mpr
  · have heq : Function.support (fun v => RCLike.re (f v))=ᵐ[volume.restrict (Set.Icc (5:ℝ) 6)] Set.univ := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      apply propext
      change RCLike.re (f v) ≠ 0 ↔ True
      exact iff_true_intro (hp v hv).ne'
    rw [measure_congr heq,Measure.restrict_apply_univ]
    norm_num
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (hp v hv).le

lemma cuspWhittakerHeightFactor_center_ne_zero (h : ActualEisensteinCubic.O) :
    cuspWhittakerHeightFactor (4/3:ℂ) h≠0 := by
  intro he
  have hh := cuspWhittakerHeightFactor_real_re_pos (4/3:ℝ) (by norm_num) h
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hh
  rw [he,Complex.zero_re] at hh
  exact lt_irrefl 0 hh

end CubicEisenstein

end

end OAI

end


