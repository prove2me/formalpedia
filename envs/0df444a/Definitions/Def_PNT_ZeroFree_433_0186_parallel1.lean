-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0186_parallel1
-- name    : PNT_ZeroFree_433_0186_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:30:57.883624+00:00
-- url     : https://prove2.me/theorems/f3b4abe2-6020-4206-ad75-7ab3cd2ce132
-- title:
--   Zero-free region foundations: CubicSieve.CanonicalLogEnergy [0186_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.CanonicalLogEnergy
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/CanonicalLogEnergy.lean#L144-L591

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0051
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0073
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0086
import Definitions.Def_PNT_ZeroFree_433_0087
import Definitions.Def_PNT_ZeroFree_433_0096
import Definitions.Def_PNT_ZeroFree_433_0102
import Definitions.Def_PNT_ZeroFree_433_0110
import Definitions.Def_PNT_ZeroFree_433_0130
import Definitions.Def_PNT_ZeroFree_433_0130_parallel1
import Definitions.Def_PNT_ZeroFree_433_0158_parallel1
import Definitions.Def_PNT_ZeroFree_433_0174_parallel1
import Definitions.Def_PNT_ZeroFree_433_0182_parallel1
import Definitions.Def_PNT_ZeroFree_433_0183_parallel1
import Definitions.Def_PNT_ZeroFree_433_0185_parallel2
import Definitions.Def_PNT_ZeroFree_433_0223_parallel1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel2
import Definitions.Def_PNT_ZeroFree_433_0246_parallel1
import Definitions.Def_PNT_ZeroFree_433_0249_parallel1
import Definitions.Def_PNT_ZeroFree_433_0255_parallel1
import Definitions.Def_PNT_ZeroFree_433_0259_parallel1
import Definitions.Def_PNT_ZeroFree_433_0275_parallel2
import Definitions.Def_PNT_ZeroFree_433_0280_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/CanonicalLogEnergy.lean
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


namespace CanonicalRowCompletion

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

section
open ActualEisensteinCubic
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
open CanonicalCubeSeparation JointLogSeparation

variable {ι : Type*} [DecidableEq ι]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem fixedChildRow_coefficient_expansion
    (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (H : Finset ι → ℂ) :
    fixedChildRow p hp hcop hg pool Ψ m H f z =
      ∑ T ∈ pool.powerset,
        canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z * H T := by
  unfold fixedChildRow
  apply Finset.sum_congr rfl
  intro T hT
  simp only [secondChildColumn, canonicalSourceCoefficient]
  ring


end

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
open CanonicalCubeSeparation JointLogSeparation


theorem cubeIdeal_row (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀ I ∈ F, Admissible I)
    (v : primePool F →₀ ℕ) (z : ActualEisensteinCubic.O) :
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    idealRowHom z (cubeIdeal F v) =
      multiplicityRow (fun i => Ideal.span {poolPrimary F i}) (poolPrimary_good F hF)
        Finset.univ v z := by
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have hprod : cubeIdeal F v = ∏ i : primePool F, (Ideal.span {poolPrimary F i}) ^ v i := by
    unfold cubeIdeal
    exact Finset.prod_congr rfl (fun i _ => by rw [poolPrimary_span F hF i])
  rw [hprod, idealRowHom_prime_powers]


end

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O

theorem fixedChildRow_zero_of_subunit {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ)
    (b X : ℝ) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t ≤ b) (hsub : b*X < 1) :
    fixedChildRow p hp hcop hg pool Ψ m
      (fun T => W (primeProductNorm p T/X)) f z = 0 := by
  unfold fixedChildRow
  apply Finset.sum_eq_zero
  intro T hT
  have hw : W (primeProductNorm p T/X) = 0 := by
    by_contra hne
    have hh := (div_le_iff₀ hX).mp (hW _ hne)
    have hone := primeProductNorm_ge_one p hp T
    linarith
  simp only [secondChildColumn,hw,mul_zero]


end

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O


def cubeLogRange (b X : ℝ) : Finset ℕ :=
  Finset.range (normLogBin (max 1 (b*X)) + 1)


theorem cubeLogRange_card (b X : ℝ) :
    (cubeLogRange b X).card = normLogBin (max 1 (b*X)) + 1 := by
  exact Finset.card_range _


end CanonicalRowCompletion

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels


def canonicalTerminalConstant (A M : ℝ) : ℝ :=
  2*128^4*SchwartzMap.seminorm ℝ 0 0 rowMajorant*(Real.exp A*M)^2

theorem canonicalTerminalConstant_nonneg (A M : ℝ) : 0≤canonicalTerminalConstant A M := by
  unfold canonicalTerminalConstant
  positivity

theorem fixedDepthRank_zero_iff (Z K : ℝ) (hZ : 1<Z) (hK : 0<K) :
    fixedDepthRank Z K=0 ↔ K≤1 := by
  rw [fixedDepthRank,Nat.ceil_eq_zero]
  constructor
  · intro h
    have hm := (div_le_iff₀ (Real.log_pos hZ)).mp h
    apply (Real.log_nonpos_iff hK.le).mp
    nlinarith
  · intro h
    apply (div_le_iff₀ (Real.log_pos hZ)).mpr
    have hm := (Real.log_nonpos_iff hK.le).mpr h
    nlinarith

theorem smallColumn_row_le_label (m : ActualEisensteinCubic.O) (hm : m≠0) (X F K : ℝ)
    (hX : X≤1) (hF : 0≤F) (hK : 0≤K)
    (hinv : K*‖eisEmbedding m‖^2≤X*F) : K≤F := by
  have hn := element_norm_ge_one m hm
  have h1 := mul_le_mul_of_nonneg_left hn hK
  have h2 := mul_le_mul_of_nonneg_right hX hF
  nlinarith

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})


theorem canonicalLogEnergy_subunit (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ → ℂ) (X K A : ℝ) (hX : 0<X)
    (hV : ∀s,V s≠0→|s|≤A) (hsmall : X*Real.exp A<1) :
    canonicalLogEnergy p hp hcop hg pool Ψ m labels V X K=0 := by
  have hcol (S : Finset ι) : V (columnLog p X S)=0 := by
    by_contra hn
    have hupper := columnLog_norm_upper p hp X A hX S ((le_abs_self _).trans (hV _ hn))
    have hlower := primeProductNorm_ge_one p hp S
    linarith
  have hrow (f y : ActualEisensteinCubic.O) : fixedChildRow p hp hcop hg pool Ψ m
      (fun S=>V (columnLog p X S)) f y=0 := by
    unfold fixedChildRow
    apply Finset.sum_eq_zero
    intro S hS
    simp only [secondChildColumn,hcol,mul_zero]
  simp only [canonicalLogEnergy,canonicalSmoothedEnergy,nonzeroRowMajorantSum,hrow,norm_zero,
    zero_pow (by decide : (2:ℕ)≠0),Complex.ofReal_zero,mul_zero,ite_self,tsum_zero,
    Finset.sum_const_zero,Complex.zero_re]


end SecondPassArithmetic

end

end OAI

end


