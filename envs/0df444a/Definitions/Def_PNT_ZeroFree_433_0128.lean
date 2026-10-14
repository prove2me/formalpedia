-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0128
-- name    : PNT_ZeroFree_433_0128
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:49:33.378398+00:00
-- url     : https://prove2.me/theorems/14cfac5f-bd09-49a0-8e9e-e1c6b30c4c82
-- title:
--   Zero-free region foundations: CubicSieve.ScaleCaps [0128]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.ScaleCaps
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ScaleCaps.lean#L83-L796

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0054
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0059
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0087
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0102
import Definitions.Def_PNT_ZeroFree_433_0103
import Definitions.Def_PNT_ZeroFree_433_0107
import Definitions.Def_PNT_ZeroFree_433_0109
import Definitions.Def_PNT_ZeroFree_433_0110
import Definitions.Def_PNT_ZeroFree_433_0111
import Definitions.Def_PNT_ZeroFree_433_0118_parallel1
import Definitions.Def_PNT_ZeroFree_433_0119
import Definitions.Def_PNT_ZeroFree_433_0119_parallel1
import Definitions.Def_PNT_ZeroFree_433_0120_parallel1
import Definitions.Def_PNT_ZeroFree_433_0121_parallel1
import Definitions.Def_PNT_ZeroFree_433_0123
import Definitions.Def_PNT_ZeroFree_433_0124_parallel1
import Definitions.Def_PNT_ZeroFree_433_0128_parallel1
import Definitions.Def_PNT_ZeroFree_433_0128_parallel2
import Definitions.Def_PNT_ZeroFree_433_0131_parallel2
import Definitions.Def_PNT_ZeroFree_433_0136_parallel2
import Definitions.Def_PNT_ZeroFree_433_0144_parallel2
import Definitions.Def_PNT_ZeroFree_433_0149_parallel2
import Definitions.Def_PNT_ZeroFree_433_0151_parallel1
import Definitions.Def_PNT_ZeroFree_433_0158_parallel2
import Definitions.Def_PNT_ZeroFree_433_0226_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ScaleCaps.lean
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

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct bit parity retained b0Exponent aLabel jLabel j2Label squarefreeLabel b0Label)

variable {ι : Type*} [DecidableEq ι]


variable (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]


omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondOfBlock_label (B A₀ C D : Finset ι)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i∈B,0 < v₁ i+v₂ i) (x : SecondExpansionData ι) :
    globalSecondLabel p (globalSecondOfBlock B A₀ C D v₁ v₂ ε₁ ε₂ x) =
      secondSupportLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x) := by
  have h := cubeCoordinatesOfBlock_primeProduct p B v₁ v₂ ε₁ ε₂ hv
    (fun a b e₁ e₂ => bit (retained (parity (a+b)) e₁ e₂))
  unfold globalSecondLabel globalSecondOfBlock secondSupportLabel
  dsimp only [expansionSupportData]
  rw [show jLabel p (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).support
      (fun i => (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).leftExponent i+
        (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).rightExponent i)
      (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).leftBit (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).rightBit =
      jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂ from h]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)


end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap


open scoped BigOperators Classical
namespace SecondPassArithmetic


open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

private theorem five_factor_bounds (a b c d e : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 1 ≤ e) :
    a ≤ a*b*c*d*e ∧ b ≤ a*b*c*d*e ∧ c ≤ a*b*c*d*e ∧ d ≤ a*b*c*d*e ∧ e ≤ a*b*c*d*e := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · calc
      a = a*1*1*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      b = 1*b*1*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      c = 1*1*c*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      d = 1*1*1*d*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      e = 1*1*1*1*e := by ring
      _ ≤ _ := by gcongr

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSupported_small_norms (ell M : ℝ) (_hell : 0 < ell) (side : Bool)
    (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source) :
    primeProductNorm p (x.cube.sideDivisor side) ≤ ell*Real.exp M ∧
    primeProductNorm p x.common ≤ ell*Real.exp M ∧
    primeProductNorm p x.firstCommon ≤ ell*Real.exp M ∧
    primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ ell*Real.exp M ∧
    primeProductNorm p x.source.divisor ≤ ell*Real.exp M ∧
    primeProductNorm p x.source.overlap ≤ ell*Real.exp M := by
  have ha := primeProductNorm_ge_one p hp (x.cube.sideDivisor side)
  have hc := primeProductNorm_ge_one p hp x.common
  have ht := primeProductNorm_ge_one p hp x.firstCommon
  have hg := primeProductNorm_ge_one p hp x.source.sourceCommon
  have hv := primeProductNorm_ge_one p hp x.source.overlap
  have hden : 0 < primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.common*primeProductNorm p x.firstCommon := by positivity
  have heq : (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon)*Real.exp M =
      (ell*Real.exp M)/(primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.common*primeProductNorm p x.firstCommon) := by
    unfold globalFirstColumnScale
    ring
  have hprod := (le_div_iff₀ hden).mp (hs.2.trans_eq heq)
  have hprod' : primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.common*
      primeProductNorm p x.firstCommon*primeProductNorm p x.source.sourceCommon*primeProductNorm p x.source.overlap ≤ ell*Real.exp M := by
    convert! hprod using 1 ; ring
  obtain ⟨ha',hc',ht',hg',hv'⟩ := five_factor_bounds _ _ _ _ _ ha hc ht hg hv
  refine ⟨ha'.trans hprod',hc'.trans hprod',ht'.trans hprod',?_,?_,hv'.trans hprod'⟩
  · exact (primeProductNorm_mono p hp Finset.sdiff_subset).trans (hg'.trans hprod')
  · exact (primeProductNorm_mono p hp hx.2.1).trans (hg'.trans hprod')


include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSupported_divisor_bound (ell B M : ℝ) (hell : 0 < ell) (hB : 0 ≤ B)
    (side : Bool) (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    primeProductNorm p x.firstDivisor ≤ (ell*Real.exp M)*B^2 := by
  have hC := (globalSupported_small_norms p hp ell M hell side x hx hs).2.1
  have hrad := globalCube_radical_bound p hp B hB x hb₁ hb₂
  calc
    _ ≤ primeProductNorm p (x.common∪x.cube.support) := primeProductNorm_mono p hp hx.2.2.2
    _ = primeProductNorm p x.common*primeProductNorm p x.cube.support :=
      FirstPassCubeLabels.primeProductNorm_union p _ _ hx.2.2.1
    _ ≤ _ := mul_le_mul hC hrad (FirstPassCubeLabels.primeProductNorm_pos p hp _).le (by positivity)

include hp in

theorem globalSupported_cutoff_row_bound (ell B Y M Z : ℝ) (hell : 0 < ell) (hB : 0 ≤ B)
    (hY : 0 < Y) (hZ : 0 ≤ Z) (side : Bool) (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hk : x.source.frequency ∈ firstCoreSecondCutoff p x.firstCommon (globalFirstColumnScale p ell x side)
      Y M Z x.source.sourceCommon x.source.divisor) :
    ‖eisEmbedding (SecondPassFiber.newRow (globalSecondTuple p x))‖^2 ≤
      3*(ell*Real.exp M)^2*B^2*((⌈Z*(ell*Real.exp M)^2/Y⌉₊ : ℝ)+1)^2 := by
  let X := globalFirstColumnScale p ell x side
  let U := (X/primeProductNorm p x.firstCommon)*Real.exp M
  let lengthScale := ell*Real.exp M
  have hsmall := globalSupported_small_norms p hp ell M hell side x hx hs
  have hD := globalSupported_divisor_bound p hp ell B M hell hB side x hx hs hb₁ hb₂
  have ha := primeProductNorm_ge_one p hp (x.cube.sideDivisor side)
  have hc := primeProductNorm_ge_one p hp x.common
  have ht := primeProductNorm_ge_one p hp x.firstCommon
  have hX : X ≤ ell := by
    exact div_le_self hell.le (one_le_mul_of_one_le_of_one_le ha hc)
  have hU : U ≤ lengthScale := mul_le_mul_of_nonneg_right
    ((div_le_self (globalFirstColumnScale_pos p hp ell hell x side).le ht).trans hX) (Real.exp_pos M).le
  have hU0 : 0 ≤ U := by
    exact (mul_pos (div_pos (globalFirstColumnScale_pos p hp ell hell x side)
      (FirstPassCubeLabels.primeProductNorm_pos p hp _)) (Real.exp_pos M)).le
  have hden : primeProductNorm p x.source.divisor *
      (((X/primeProductNorm p x.firstCommon)/primeProductNorm p x.source.sourceCommon)*Real.exp M)^2 ≤ lengthScale^2 := by
    rw [show ((X/primeProductNorm p x.firstCommon)/primeProductNorm p x.source.sourceCommon)*Real.exp M =
      U/primeProductNorm p x.source.sourceCommon by dsimp [U];ring]
    exact (supported_cutoff_denominator _ _ _ (primeProductNorm_mono p hp hx.2.1)
      (primeProductNorm_ge_one p hp _)).trans (pow_le_pow_left₀ hU0 hU 2)
  have hr : Z/(Y/(primeProductNorm p x.source.divisor *
      (((X/primeProductNorm p x.firstCommon)/primeProductNorm p x.source.sourceCommon)*Real.exp M)^2)) ≤ Z*lengthScale^2/Y := by
    rw [div_div_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hden hZ) hY.le
  have hceil : (⌈Z/(Y/(primeProductNorm p x.source.divisor *
      (((X/primeProductNorm p x.firstCommon)/primeProductNorm p x.source.sourceCommon)*Real.exp M)^2))⌉₊ : ℝ) ≤
      (⌈Z*lengthScale^2/Y⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_mono hr
  have hf := secondFrequencyCutoff_norm_sq_le _ Z x.source.frequency hk
  simp only [primeSubsetGenerator_norm_eq_productNorm] at hf
  have hf' : ‖eisEmbedding x.source.frequency‖^2 ≤ 3*((⌈Z*lengthScale^2/Y⌉₊ : ℝ)+1)^2 := by
    apply hf.trans
    gcongr
  change ‖eisEmbedding (actualSecondRow p x.firstDivisor x.source.divisor x.source.frequency)‖^2 ≤ _
  simp only [actualSecondRow,map_mul,norm_mul,mul_pow,primeSubsetGenerator_norm_eq_productNorm]
  calc
    _ ≤ (lengthScale*B^2)*lengthScale*(3*((⌈Z*lengthScale^2/Y⌉₊ : ℝ)+1)^2) := by
      exact mul_le_mul (mul_le_mul hD hsmall.2.2.2.2.1 (FirstPassCubeLabels.primeProductNorm_pos p hp _).le (by positivity))
        hf' (sq_nonneg _) (by dsimp [lengthScale]; positivity)
    _ = _ := by dsimp [lengthScale];ring_nf


include hp in
theorem globalScaleVector_le_caps (ell B Y M Z : ℝ) (hell : 0 < ell) (hB : 0 ≤ B)
    (hY : 0 < Y) (hZ : 0 ≤ Z) (side : Bool) (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hk : x.source.frequency ∈ firstCoreSecondCutoff p x.firstCommon (globalFirstColumnScale p ell x side)
      Y M Z x.source.sourceCommon x.source.divisor) :
    ∀ i,globalScaleVector p side x i ≤ globalNormCaps ell B Y M Z i := by
  obtain ⟨ha,hc,ht,hr,he,hv⟩ := globalSupported_small_norms p hp ell M hell side x hx hs
  have hd := globalSupported_divisor_bound p hp ell B M hell hB side x hx hs hb₁ hb₂
  have hrow := globalSupported_cutoff_row_bound p hp ell B Y M Z hell hB hY hZ side x hx hs hb₁ hb₂ hk
  have hJ := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos B hB hb₁ hb₂).1
  have hrad := globalCube_radical_bound p hp B hB x hb₁ hb₂
  have hactive : (globalCubeActiveRoot p x)^2 ≤ B^2 :=
    (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans hrad
  intro i
  fin_cases i
  · exact ha
  · exact hc
  · exact ht
  · exact hr
  · exact hJ
  · exact hd
  · exact he
  · exact hv
  · exact hrow
  · exact hactive

include hp in

theorem globalScaleIndex_mem_concrete_box (ell B Y M Z : ℝ) (hell : 0 < ell) (hB : 0 ≤ B)
    (hY : 0 < Y) (hZ : 0 ≤ Z) (side : Bool) (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hk0 : x.source.frequency ≠ 0)
    (hk : x.source.frequency ∈ firstCoreSecondCutoff p x.firstCommon (globalFirstColumnScale p ell x side)
      Y M Z x.source.sourceCommon x.source.divisor) :
    globalScaleIndex p side x∈globalLogBox (globalNormCaps ell B Y M Z) :=
  globalScaleIndex_mem_box p hp side x hk0 _
    (globalScaleVector_le_caps p hp ell B Y M Z hell hB hY hZ side x hx hs hb₁ hb₂ hk)

end SecondPassArithmetic

end

end OAI

end


