-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0213_parallel1
-- name    : PNT_ZeroFree_433_0213_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:19:40.942627+00:00
-- url     : https://prove2.me/theorems/34e00d21-2cc3-4c7a-a59f-4cf12fc8509f
-- title:
--   Zero-free region foundations: Eisenstein.CuspResidues [0213_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.CuspResidues
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CuspResidues.lean#L82-L668

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0098
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0109
import Definitions.Def_PNT_ZeroFree_433_0130_parallel1
import Definitions.Def_PNT_ZeroFree_433_0131_parallel1
import Definitions.Def_PNT_ZeroFree_433_0138_parallel1
import Definitions.Def_PNT_ZeroFree_433_0185_parallel2
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1
import Definitions.Def_PNT_ZeroFree_433_0260_parallel2_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CuspResidues.lean
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
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups Matrix

lemma levelThree_integral_eq_translation (M : CubicKubota.levelThree)
    (hc : (M : SL(2,ActualEisensteinCubic.O)) 1 0=0) :
    integralComplexMatrix M.1=complexTranslation (ConcreteTraceCRT.eisEmbedding ((M : SL(2,ActualEisensteinCubic.O)) 0 1)) := by
  have hr := row_eq_one_of_lower_left_zero M hc
  have hd : (M : SL(2,ActualEisensteinCubic.O)) 1 1=1 := by
    simpa [row,Matrix.one_apply] using congrFun hr 1
  have ha : (M : SL(2,ActualEisensteinCubic.O)) 0 0=1 := by
    have hh : (M : SL(2,ActualEisensteinCubic.O)) 0 0 * (M : SL(2,ActualEisensteinCubic.O)) 1 1-
      (M : SL(2,ActualEisensteinCubic.O)) 0 1 * (M : SL(2,ActualEisensteinCubic.O)) 1 0=1 := by
      simpa only [Matrix.det_fin_two] using (M : SL(2,ActualEisensteinCubic.O)).property
    simpa only [hc,hd,mul_zero,mul_one,sub_zero] using hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTranslation,ha,hc,hd]

lemma periodDomain_unique_translate (z w t : ℂ) (hz : z∈periodDomain) (hw : w∈periodDomain)
    (ht : t∈periodLattice) (he : z=w+t) : z=w := by
  have hf := ZSpan.fract_add_ZSpan periodBasis w ht
  rw [←he,(ZSpan.fract_eq_self (b := periodBasis)).mpr hz,
    (ZSpan.fract_eq_self (b := periodBasis)).mpr hw] at hf
  exact hf


end

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups


section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups Matrix

def spatialComplexSplit : EuclideanSpatial ≃ᵐ ℝ × ℂ :=
  spatialHeightSplit.trans ((MeasurableEquiv.refl ℝ).prodCongr Complex.measurableEquivPi.symm)

lemma spatialComplexSplit_fst (p : EuclideanSpatial) : (spatialComplexSplit p).1=p 2 := rfl
lemma spatialComplexSplit_snd (p : EuclideanSpatial) :
    (spatialComplexSplit p).2=(p 0:ℂ)+(p 1:ℂ)*Complex.I := rfl

lemma spatialComplexSplit_preserves_volume : MeasurePreserving spatialComplexSplit volume volume :=
  ((MeasurePreserving.id volume).prod Complex.volume_preserving_equiv_pi.symm).comp
    spatialHeightSplit_preserves_volume


def cuspEuclideanStrip : Set EuclideanSpatial :=
  spatialComplexSplit ⁻¹' (Set.Icc (5:ℝ) 6 ×ˢ periodDomain)

lemma cuspEuclideanStrip_measurable : MeasurableSet cuspEuclideanStrip :=
  spatialComplexSplit.measurable (measurableSet_Icc.prod periodDomain_measurable)

lemma cuspEuclideanStrip_positive : cuspEuclideanStrip⊆euclideanUpperHalf := by
  intro p hp
  have hh : 5≤p 2 := hp.1.1
  change 0<p 2
  linarith


lemma spatialComplexSplit_symm_eq (q : ℝ × ℂ) :
    spatialComplexSplit.symm q=WithLp.toLp 2 ![q.2.re,q.2.im,q.1] := by
  apply spatialComplexSplit.injective
  rw [spatialComplexSplit.apply_symm_apply]
  apply Prod.ext
  · rfl
  · exact (Complex.re_add_im q.2).symm

lemma spatialComplexSplit_symm_continuous : Continuous spatialComplexSplit.symm := by
  change Continuous (fun q : ℝ × ℂ => spatialComplexSplit.symm q)
  simp_rw [spatialComplexSplit_symm_eq]
  fun_prop


end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

def cuspMainHeightFactor (s : ℂ) : ℂ :=
  ((6:ℂ)^(s-2)-(5:ℂ)^(s-2))/(s-2)

def cuspScatterHeightFactor (s : ℂ) : ℂ :=
  ((5:ℂ)^(-s)-(6:ℂ)^(-s))/s

lemma cuspHeightPower_integrable (s : ℂ) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^s) (Set.Icc (5:ℝ) 6) volume := by
  apply ContinuousOn.integrableOn_Icc
  intro v hv
  exact (Complex.continuousAt_ofReal_cpow_const v s (Or.inr (by linarith [hv.1]))).continuousWithinAt

lemma cuspMainHeightFactor_integral (s : ℂ) (hs : s≠2) :
    (∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(s-3))=cuspMainHeightFactor s := by
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (5:ℝ)≤6)]
  have hr : s-3≠(-1:ℂ) := by intro h; apply hs; linear_combination h
  rw [integral_cpow (Or.inr ⟨hr,by norm_num⟩)]
  change ((6:ℂ)^(s-3+1)-(5:ℂ)^(s-3+1))/(s-3+1)=_
  have he : s-3+1=s-2 := by ring
  rw [he]
  rfl

lemma cuspScatterHeightFactor_integral (s : ℂ) (hs : s≠0) :
    (∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1))=cuspScatterHeightFactor s := by
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (5:ℝ)≤6)]
  have hr : -s-1≠(-1:ℂ) := by intro h; apply hs; linear_combination -h
  rw [integral_cpow (Or.inr ⟨hr,by norm_num⟩)]
  change ((6:ℂ)^(-s-1+1)-(5:ℂ)^(-s-1+1))/(-s-1+1)=_
  have he : -s-1+1=-s := by ring
  rw [he,cuspScatterHeightFactor]
  ring

lemma cuspMainHeightFactor_differentiableAt (s : ℂ) (hs : s≠2) :
    DifferentiableAt ℂ cuspMainHeightFactor s := by
  have hd : DifferentiableAt ℂ (fun z : ℂ => z-2) s := differentiableAt_id.sub_const 2
  exact ((hd.const_cpow (Or.inl (by norm_num))).sub
    (hd.const_cpow (Or.inl (by norm_num)))).div hd (sub_ne_zero.mpr hs)

lemma cuspScatterHeightFactor_differentiableAt (s : ℂ) (hs : s≠0) :
    DifferentiableAt ℂ cuspScatterHeightFactor s := by
  have hd : DifferentiableAt ℂ (fun z : ℂ => -z) s := differentiableAt_id.neg
  exact ((hd.const_cpow (Or.inl (by norm_num))).sub
    (hd.const_cpow (Or.inl (by norm_num)))).div differentiableAt_id hs

def cuspConstantAverage (s : ℂ) : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*(cuspMainHeightFactor s+
    ((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0*cuspScatterHeightFactor s)


lemma cuspConstantAverage_differentiableAt (s : ℂ) (hs : 4/3<s.re) (hs2 : s≠2) :
    DifferentiableAt ℂ cuspConstantAverage s := by
  have hs0 : s≠0 := by intro he; subst s; norm_num at hs
  have hs1 : s≠1 := by intro he; subst s; norm_num at hs
  have hsc : DifferentiableAt ℂ (fun z : ℂ => scatteringCoefficient z 0) s :=
    (arithmeticDirichletSeries_zero_differentiableAt s hs).div_const _
  exact ((cuspMainHeightFactor_differentiableAt s hs2).add
    ((((differentiableAt_const (Real.pi:ℂ)).div (differentiableAt_id.sub_const 1)
      (sub_ne_zero.mpr hs1)).mul hsc).mul
      (cuspScatterHeightFactor_differentiableAt s hs0))).const_mul _

lemma cuspScatterHeightFactor_center_re_pos :
    0<(cuspScatterHeightFactor (4/3:ℂ)).re := by
  have h5 := Complex.ofReal_cpow (by norm_num : (0:ℝ)≤5) (-(4/3:ℝ))
  have h6 := Complex.ofReal_cpow (by norm_num : (0:ℝ)≤6) (-(4/3:ℝ))
  norm_num only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat] at h5 h6
  have he : cuspScatterHeightFactor (4/3:ℂ)=
      (((5:ℝ)^(-(4/3:ℝ))-(6:ℝ)^(-(4/3:ℝ)))/(4/3:ℝ):ℝ) := by
    rw [cuspScatterHeightFactor,←h5,←h6]
    push_cast
    rfl
  rw [he,Complex.ofReal_re]
  apply div_pos
  · exact sub_pos.mpr (Real.rpow_lt_rpow_of_neg (by norm_num) (by norm_num) (by norm_num))
  · norm_num

def cuspConstantAverageResidue : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*(3*(Real.pi:ℂ))*constantArithmeticResidue*
    cuspScatterHeightFactor (4/3:ℂ)

lemma cuspConstantAverageResidue_ne_zero : cuspConstantAverageResidue≠0 := by
  apply mul_ne_zero
  · exact mul_ne_zero (mul_ne_zero cusp_volume_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      constantArithmeticResidue_ne_zero
  · intro he
    have hh := cuspScatterHeightFactor_center_re_pos
    rw [he,Complex.zero_re] at hh
    exact lt_irrefl 0 hh

lemma cuspConstantAverage_oneSidedResidue :
    Tendsto (fun x : ℝ => ((x:ℂ)-(4/3:ℂ))*cuspConstantAverage (x:ℂ))
      (𝓝[>] (4/3:ℝ)) (𝓝 cuspConstantAverageResidue) := by
  have harg : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] (4/3:ℝ)) (𝓝 (4/3:ℂ)) := by
    convert! Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 ; norm_num
  have hlinear := harg.sub_const (4/3:ℂ)
  norm_num only [sub_self] at hlinear
  have hm := (cuspMainHeightFactor_differentiableAt (4/3:ℂ) (by norm_num)).continuousAt.tendsto.comp harg
  have hh := (cuspScatterHeightFactor_differentiableAt (4/3:ℂ) (by norm_num)).continuousAt.tendsto.comp harg
  have hpi : Tendsto (fun x : ℝ => (Real.pi:ℂ)/((x:ℂ)-1))
      (𝓝[>] (4/3:ℝ)) (𝓝 (3*(Real.pi:ℂ))) := by
    convert! tendsto_const_nhds.div (harg.sub_const 1) (by norm_num : (4/3:ℂ)-1≠0) using 1 ; ring_nf
  have hall := ((hlinear.mul hm).add
    ((hpi.mul scatteringCoefficient_zero_oneSidedResidue).mul hh)).const_mul
      ((9*Real.sqrt 3/2:ℝ):ℂ)
  convert! hall using 1
  · ext x
    dsimp only [cuspConstantAverage,Function.comp_def]
    ring
  · simp only [zero_mul,zero_add,cuspConstantAverageResidue]
    ring_nf

open Filter MeasureTheory
open scoped BigOperators Classical Topology


def cuspUpperParameterRegion : Set ℂ := {s | (4/3:ℝ)<s.re ∧ 0<s.im}

lemma cuspUpperParameterRegion_isOpen : IsOpen cuspUpperParameterRegion :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)

lemma cuspUpperParameterRegion_convex : Convex ℝ cuspUpperParameterRegion :=
  ((convex_Ioi (4/3:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)

lemma cuspConstantAverage_analyticOn_upper : AnalyticOnNhd ℂ cuspConstantAverage cuspUpperParameterRegion := by
  apply (Complex.analyticOnNhd_iff_differentiableOn cuspUpperParameterRegion_isOpen).mpr
  intro s hs
  apply (cuspConstantAverage_differentiableAt s hs.1 ?_).differentiableWithinAt
  intro he
  subst s
  norm_num [cuspUpperParameterRegion] at hs


lemma realAbove_tendsto_complex_punctured :
    Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] (4/3:ℝ)) (𝓝[≠] (4/3:ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · convert! Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 ; norm_num
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change (4/3:ℝ)<x at hx
    change (x:ℂ)≠(4/3:ℂ)
    intro he
    have hh := congrArg Complex.re he
    norm_num at hh
    linarith [hx]


end CubicEisenstein

end

end OAI

end


