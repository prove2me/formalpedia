-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0149
-- name    : PNT_ZeroFree_433_0149
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:12:25.426294+00:00
-- url     : https://prove2.me/theorems/06dbe5bf-9b13-4c19-8f8e-a0ee70f47d6d
-- title:
--   Zero-free region foundations: MeanSquare.LogarithmicBins [0149]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.MeanSquare.LogarithmicBins
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/LogarithmicBins.lean#L84-L653

import Definitions.Def_PNT_ZeroFree_433_0146
import Definitions.Def_PNT_ZeroFree_433_0148
import Definitions.Def_PNT_ZeroFree_433_0149_parallel1
import Definitions.Def_PNT_ZeroFree_433_0149_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/LogarithmicBins.lean
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

namespace InitialMeanSquare


open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm)
open SecondPassIntegration (elementNorm)


theorem initial_log_box_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ U V K : ℝ,1≤U → 0<V → 0<K → V≤U → K≤U →
      ((secondLogBinBox V K).card:ℝ)≤C*U^ε := by
  obtain ⟨C,hC,hpow⟩ := globalLogFactor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro U V K hU hV hK hVU hKU
  have hv := normLogBin_le_log_upper V U hV hVU hU
  have hk := normLogBin_le_log_upper K U hK hKU hU
  have hlog := Real.log_nonneg hU
  let B := 1+Real.log 27+22*Real.log U
  have h27 : 0≤Real.log 27 := Real.log_nonneg (by norm_num)
  have hB : 1≤B := by dsimp [B]; linarith
  have hvB : (normLogBin V:ℝ)+1≤B := by dsimp [B]; linarith
  have hkB : (normLogBin K:ℝ)+1≤B := by dsimp [B]; linarith
  have hh : ((secondLogBinBox V K).card:ℝ)≤B^3 := by
    rw [secondLogBinBox_card,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_add,Nat.cast_one]
    calc
      _ ≤ B^2*B := mul_le_mul (pow_le_pow_left₀ (by positivity) hvB 2) hkB
        (by positivity) (sq_nonneg B)
      _ = B^3 := by ring
  exact hh.trans ((pow_le_pow_right₀ hB (by decide : 3≤10)).trans (hpow U hU))

end InitialMeanSquare

namespace SecondPassArithmetic


section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel dilationLabel jLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)


variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem globalFirstRowScale_le_pooled (K ell B F : ℝ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (b : GlobalCubeBlock ι) :
    globalFirstRowScale p K ell B F ((b.withCommon ∅).append ⟨∅,∅,∅,1⟩) ≤
      globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by
  let x := (b.withCommon ∅).append (⟨∅,∅,∅,1⟩ : SecondExpansionData ι)
  let j := globalScaleIndex p true x
  have hbds := globalScaleIndex_bounds p hp true x (by exact one_ne_zero)
  have hd := (hbds 5).2
  have hc := (hbds 1).1
  have hJ := (hbds 4).1
  change primeProductNorm p b.firstDivisor≤globalLogRep j 5*Real.exp 1 at hd
  change globalLogRep j 1≤primeProductNorm p b.common at hc
  change globalLogRep j 4≤globalCubeJNorm p x at hJ
  change ell^2*B^4*F^2*primeProductNorm p b.firstDivisor/
      (K*(primeProductNorm p b.common)^2*globalCubeJNorm p x) ≤
    Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4)
  have hdpos := (FirstPassCubeLabels.primeProductNorm_pos p hp b.firstDivisor).le
  have h5 := (globalLogRep_pos j 5).le
  apply div_le_div₀ (by positivity)
  · calc
      _ ≤ ell^2*B^4*F^2*(globalLogRep j 5*Real.exp 1) := by gcongr
      _ = _ := by ring
  · exact mul_pos (mul_pos hK (sq_pos_of_pos (globalLogRep_pos j 1))) (globalLogRep_pos j 4)
  · exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (globalLogRep_pos j 1).le hc 2) hK.le)
      hJ (globalLogRep_pos j 4).le (by positivity)

include hp in

theorem first_row_enlargement (b : GlobalCubeBlock ι) (x : Ideal O × O)
    (K ell B F : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (hb₁ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B)
    (hf : (Ideal.absNorm x.1 : ℝ)≤F)
    (hh : ‖eisEmbedding x.2‖^2 ≤
      ell^2*primeProductNorm p (cubeActiveSupport b.cube.support
        (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit)*
      primeProductNorm p b.firstDivisor/
      (K*‖eisEmbedding (aLabel p b.cube.support b.cube.leftBit)‖^2*
        ‖eisEmbedding (aLabel p b.cube.support b.cube.rightBit)‖^2*(primeProductNorm p b.common)^2)) :
    ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
        b.cube.leftBit b.cube.rightBit) x)‖^2 ≤
      globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by
  let active := cubeActiveSupport b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
  let e := dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
  let j := jLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
  let a1 := aLabel p b.cube.support b.cube.leftBit
  let a2 := aLabel p b.cube.support b.cube.rightBit
  have hpos (v : ι → ℕ) : 0<‖eisEmbedding (primeProduct p b.cube.support v)‖^2 :=
    zero_lt_one.trans_le (element_norm_ge_one _ (primeProduct_ne_zero p hp _ _))
  have hcon := first_conductor_norm_bound p hp b.cube.support b.cube.leftExponent b.cube.rightExponent
    b.cube.leftBit b.cube.rightBit b.cube.support_pos B hB.le hb₁ hb₂
  have hnum := first_row_numeric_bound (primeProductNorm p active) (‖eisEmbedding e‖^2) (‖eisEmbedding j‖^2)
    (‖eisEmbedding a1‖^2) (‖eisEmbedding a2‖^2) (primeProductNorm p b.common) (primeProductNorm p b.firstDivisor)
    (‖eisEmbedding x.2‖^2) (Ideal.absNorm x.1) ell K B F
    (FirstPassCubeLabels.primeProductNorm_pos p hp active).le (sq_nonneg _) (hpos _) (hpos _) (hpos _)
    (FirstPassCubeLabels.primeProductNorm_pos p hp b.common) (FirstPassCubeLabels.primeProductNorm_pos p hp b.firstDivisor).le
    (sq_nonneg _) (Nat.cast_nonneg _) hell hK hB hF hcon hh hf
  have hgen : ‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator x.1)‖^2=(Ideal.absNorm x.1 : ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,ConcretePrimeRowBridge.span_idealGenerator]
  have hrow : ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap e x)‖^2 =
      ‖eisEmbedding x.2‖^2*(Ideal.absNorm x.1 : ℝ)^2*‖eisEmbedding e‖^2 := by
    simp only [DescentWeightedCauchy.firstElementRowMap,map_mul,map_pow,norm_mul,norm_pow,mul_pow]
    rw [show (‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator x.1)‖^2)^2 =
        (Ideal.absNorm x.1 : ℝ)^2 by rw [hgen]]
  rw [hrow]
  exact hnum.trans (globalFirstRowScale_le_pooled p hp K ell B F hK hell hB hF b)

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel dilationLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalFirstFrequencyScale (K ell : ℝ) (b : GlobalCubeBlock ι) : ℝ :=
  ell^2*primeProductNorm p (cubeActiveSupport b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit)*
    primeProductNorm p b.firstDivisor/
    (K*‖eisEmbedding (aLabel p b.cube.support b.cube.leftBit)‖^2*
      ‖eisEmbedding (aLabel p b.cube.support b.cube.rightBit)‖^2*(primeProductNorm p b.common)^2)

def globalCubeFirstTargets (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O)) : Finset O :=
  s.image (DescentWeightedCauchy.firstElementRowMap
    (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
      b.cube.leftBit b.cube.rightBit))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalCubeFirstTargets_mem (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O))
    (x : Ideal O × O) (hx : x∈s) :
    DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
        b.cube.leftBit b.cube.rightBit) x∈globalCubeFirstTargets p b s :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalCubeFirstTargets_ne_zero (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O))
    (hsf : ∀ x∈s,Squarefree x.1) (hs0 : ∀ x∈s,x.2≠0)
    (z : O) (hz : z∈globalCubeFirstTargets p b s) : z≠0 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  apply mul_ne_zero
  · apply mul_ne_zero (hs0 x hx)
    exact pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero _ (by simpa using (hsf x hx).ne_zero))
  · exact primeProduct_ne_zero p hp _ _

include hp in
theorem globalCubeFirstTargets_norm_bound (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O))
    (K ell B F : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (hb₁ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B)
    (hf : ∀ x∈s,(Ideal.absNorm x.1 : ℝ)≤F)
    (hh : ∀ x∈s,‖eisEmbedding x.2‖^2≤globalFirstFrequencyScale p K ell b)
    (z : O) (hz : z∈globalCubeFirstTargets p b s) :
    (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  rw [← eisEmbedding_norm_sq_eq_absNorm_span]
  exact first_row_enlargement p hp b x K ell B F hK hell hB hF hb₁ hb₂ (hf x hx) (hh x hx)

end SecondPassArithmetic

end

end OAI

end


