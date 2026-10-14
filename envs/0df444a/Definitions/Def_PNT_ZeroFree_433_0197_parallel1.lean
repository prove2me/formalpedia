-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0197_parallel1
-- name    : PNT_ZeroFree_433_0197_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:05:44.959812+00:00
-- url     : https://prove2.me/theorems/4cda9fb6-7b7e-4a5c-8ae4-4ac37a4118d8
-- title:
--   Zero-free region foundations: CubicSieve.ReopeningBounds [0197_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.ReopeningBounds
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ReopeningBounds.lean#L345-L614

import Definitions.Def_PNT_ZeroFree_433_0105
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1
import Definitions.Def_PNT_ZeroFree_433_0224_parallel1_1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ReopeningBounds.lean
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


namespace SecondPassArithmetic


def reopeningScaleConstant (A M : ℝ) : ℝ := 1+Real.exp (A+1)+Real.exp M

def reopeningAuxiliaryScale (A M κ Z : ℝ) : ℝ := reopeningScaleConstant A M*Z^(κ+3)

lemma reopeningScaleConstant_one (A M : ℝ) : 1≤reopeningScaleConstant A M := by
  unfold reopeningScaleConstant
  linarith [Real.exp_pos (A+1),Real.exp_pos M]

lemma reopeningScaleConstant_exp (A M : ℝ) : Real.exp A≤reopeningScaleConstant A M := by
  have h : Real.exp A≤Real.exp (A+1) := Real.exp_le_exp.mpr (by linarith)
  unfold reopeningScaleConstant
  linarith [Real.exp_pos M]

theorem globalFirstRowCap_reopening (Z η X F Ksrc B : ℝ)
    (hZ : 0<Z) (hK : 0<Ksrc) (hB : 0<B) :
    globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F =
      (Real.exp 1)^8*X^2*F^2*Z^η/Ksrc := by
  unfold globalFirstRowCap
  field_simp

theorem globalFirstRowCap_reopening_bound (Z η X F Ksrc B : ℝ)
    (hZ : 1≤Z) (_hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B) :
    globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F ≤ (Real.exp 1)^8*Z^13 := by
  rw [globalFirstRowCap_reopening Z η X F Ksrc B (by linarith) (by linarith) (by linarith)]
  have hηZ : Z^η≤Z := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ hη1
  calc
    _ ≤ (Real.exp 1)^8*X^2*F^2*Z^η := div_le_self (by positivity) hK
    _ ≤ (Real.exp 1)^8*(Z^3)^2*(Z^3)^2*Z := by gcongr
    _ = _ := by ring

theorem globalFirstRowCap_reopening_small_power (Z η X F Ksrc B deltaLoss : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B) (hδ : 0≤deltaLoss) :
    (max 1 (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F))^deltaLoss ≤
      ((Real.exp 1)^8)^deltaLoss*Z^(13*deltaLoss) := by
  have he : 1≤Real.exp (1:ℝ) := Real.one_le_exp (by norm_num)
  have hb := globalFirstRowCap_reopening_bound Z η X F Ksrc B hZ hη hη1 hX hXZ hF hFZ hK hB
  have hmax : max 1 (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)≤(Real.exp 1)^8*Z^13 :=
    max_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ he) (one_le_pow₀ hZ)) hb
  apply (Real.rpow_le_rpow (by positivity) hmax hδ).trans_eq
  rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_natCast_mul (by linarith : 0≤Z)]
  norm_num

theorem reopeningAuxiliaryScale_bounds (A M κ Z η X F Ksrc B : ℝ)
    (hκ : 0≤κ) (hZ : 1≤Z) (hη : 0≤η)
    (hX : 1≤X) (hXZ : X≤Z^3) (_hF : 1≤F) (hFZ : F≤Z^3)
    (hK : 1≤Ksrc) (hKZ : Ksrc≤Z^3) (hB : 1≤B) (hactive : B^3≤Real.exp A*X) :
    let U := reopeningAuxiliaryScale A M κ Z
    1≤U ∧ Ksrc/Z^η≤U ∧ X/B^3≤U ∧ Real.exp 1*B≤U ∧ F≤U ∧ Z^κ≤U ∧
      Real.exp M≤U ∧ (X/B^3)*Real.exp M≤U ∧ (X/B^3)⁻¹≤U := by
  let C := reopeningScaleConstant A M
  have hC : 1≤C := reopeningScaleConstant_one A M
  have hCZ : C≤C*Z^(κ+3) := le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hZ (by linarith))
  have hZ3 : Z^3≤Z^(κ+3) := by
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by norm_num; linarith)
  have hZκ : Z^κ≤Z^(κ+3) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hbase : Z^(κ+3)≤C*Z^(κ+3) := le_mul_of_one_le_left (by positivity) hC
  have hKcut : Ksrc/Z^η≤Z^3 :=
    (div_le_self (by linarith) (Real.one_le_rpow hZ hη)).trans hKZ
  have hell : X/B^3≤X := div_le_self (by linarith) (one_le_pow₀ hB)
  have hB3 : B≤B^3 := by nlinarith [sq_nonneg (B-1)]
  have hBsup : Real.exp 1*B≤Real.exp (A+1)*Z^3 := by
    calc
      _ ≤ Real.exp 1*B^3 := mul_le_mul_of_nonneg_left hB3 (Real.exp_pos _).le
      _ ≤ Real.exp 1*(Real.exp A*X) := mul_le_mul_of_nonneg_left hactive (Real.exp_pos _).le
      _ ≤ Real.exp 1*(Real.exp A*Z^3) := by gcongr
      _ = _ := by rw [Real.exp_add]; ring
  have hCA : Real.exp (A+1)≤C := by dsimp [C,reopeningScaleConstant]; linarith [Real.exp_pos M]
  have hCM : Real.exp M≤C := by dsimp [C,reopeningScaleConstant]; linarith [Real.exp_pos (A+1)]
  have hinv : (X/B^3)⁻¹≤Real.exp A := by
    rw [inv_div]
    exact (div_le_iff₀ (by linarith : 0<X)).mpr hactive
  change 1≤C*Z^(κ+3) ∧ _
  refine ⟨hC.trans hCZ,hKcut.trans (hZ3.trans hbase),
    (hell.trans hXZ).trans (hZ3.trans hbase),?_,hFZ.trans (hZ3.trans hbase),
    hZκ.trans hbase,hCM.trans hCZ,?_,hinv.trans ((reopeningScaleConstant_exp A M).trans hCZ)⟩
  · exact hBsup.trans (mul_le_mul hCA hZ3 (by positivity) (by linarith))
  · calc
      _ ≤ Z^3*Real.exp M := mul_le_mul_of_nonneg_right (hell.trans hXZ) (Real.exp_pos _).le
      _ ≤ Z^(κ+3)*C := mul_le_mul hZ3 hCM (Real.exp_pos _).le (by positivity)
      _ = _ := mul_comm _ _


lemma reopening_cutoff_ratio (Z η Ksrc : ℝ) (hZ : 0<Z) (hK : 0<Ksrc) :
    Ksrc/(Ksrc/Z^η)=Z^η := by field_simp

lemma globalFirstRowCap_reopening_rpow (Z η X F Ksrc B deltaLoss : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B) (hδ : 0≤deltaLoss) :
    (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss ≤
      ((Real.exp 1)^8)^deltaLoss*Z^(13*deltaLoss) := by
  have hcap : 0≤globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F := by
    unfold globalFirstRowCap
    positivity
  exact (Real.rpow_le_rpow hcap (le_max_right 1 _) hδ).trans
    (globalFirstRowCap_reopening_small_power Z η X F Ksrc B deltaLoss hZ hη hη1 hX hXZ hF hFZ hK hB hδ)

lemma reopening_cube_bound (A M Z X B : ℝ) (hZ : 1≤Z) (_hX : 1≤X)
    (hXZ : X≤Z^3) (hB : 1≤B) (hactive : B^3≤Real.exp A*X) :
    Real.exp 1*B≤reopeningScaleConstant A M*Z^3 := by
  have hB3 : B≤B^3 := by nlinarith [sq_nonneg (B-1)]
  have hC : Real.exp (A+1)≤reopeningScaleConstant A M := by
    unfold reopeningScaleConstant
    linarith [Real.exp_pos M]
  calc
    _ ≤ Real.exp 1*B^3 := mul_le_mul_of_nonneg_left hB3 (Real.exp_pos _).le
    _ ≤ Real.exp 1*(Real.exp A*X) := mul_le_mul_of_nonneg_left hactive (Real.exp_pos _).le
    _ ≤ Real.exp 1*(Real.exp A*Z^3) := by gcongr
    _ = Real.exp (A+1)*Z^3 := by rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (by positivity)

theorem reopening_diagonal_monomial (A M Z η X F Ksrc B deltaLoss ε : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B)
    (hactive : B^3≤Real.exp A*X) (hδ : 0≤deltaLoss) (hε : 0≤ε) :
    (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss *
      ((Real.exp 1*B)*(reopeningScaleConstant A M*Z^4))^ε ≤
      (((Real.exp 1)^8)^deltaLoss*(reopeningScaleConstant A M^2)^ε)*Z^(13*deltaLoss+7*ε) := by
  let C := reopeningScaleConstant A M
  have hC : 1≤C := reopeningScaleConstant_one A M
  have hb := reopening_cube_bound A M Z X B hZ hX hXZ hB hactive
  have hprod : (Real.exp 1*B)*(C*Z^4)≤C^2*Z^7 := by
    calc
      _ ≤ (C*Z^3)*(C*Z^4) := mul_le_mul_of_nonneg_right hb (by positivity)
      _ = _ := by ring
  have hpow : ((Real.exp 1*B)*(C*Z^4))^ε≤(C^2)^ε*Z^(7*ε) := by
    apply (Real.rpow_le_rpow (by positivity) hprod hε).trans_eq
    rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_natCast_mul (by linarith : 0≤Z)]
    norm_num
  have hcap := globalFirstRowCap_reopening_rpow Z η X F Ksrc B deltaLoss hZ hη hη1 hX hXZ hF hFZ hK hB hδ
  calc
    _ ≤ (((Real.exp 1)^8)^deltaLoss*Z^(13*deltaLoss))*((C^2)^ε*Z^(7*ε)) :=
      mul_le_mul hcap hpow (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = _ := by rw [Real.rpow_add (by linarith : 0<Z)]; dsimp [C]; ring

theorem reopening_recursive_monomial (A M Z η X F Ksrc B deltaLoss ε : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B)
    (hδ : 0≤deltaLoss) (_hε : 0≤ε) :
    (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss *
      (reopeningScaleConstant A M*Z^4)^(deltaLoss+8*ε) ≤
      (((Real.exp 1)^8)^deltaLoss*(reopeningScaleConstant A M)^(deltaLoss+8*ε))*Z^(17*deltaLoss+32*ε) := by
  have hC : 0<reopeningScaleConstant A M := lt_of_lt_of_le zero_lt_one (reopeningScaleConstant_one A M)
  have he : (reopeningScaleConstant A M*Z^4)^(deltaLoss+8*ε)=
      reopeningScaleConstant A M^(deltaLoss+8*ε)*Z^(4*deltaLoss+32*ε) := by
    rw [Real.mul_rpow hC.le (by positivity),←Real.rpow_natCast_mul (by linarith : 0≤Z)]
    congr 2
    ring
  rw [he]
  have hcap := globalFirstRowCap_reopening_rpow Z η X F Ksrc B deltaLoss hZ hη hη1 hX hXZ hF hFZ hK hB hδ
  calc
    _ ≤ (((Real.exp 1)^8)^deltaLoss*Z^(13*deltaLoss))*
      (reopeningScaleConstant A M^(deltaLoss+8*ε)*Z^(4*deltaLoss+32*ε)) :=
      mul_le_mul_of_nonneg_right hcap (by positivity)
    _ = _ := by
      have hh : 17*deltaLoss+32*ε=13*deltaLoss+(4*deltaLoss+32*ε) := by ring
      rw [hh]
      simp only [Real.rpow_add (by linarith : 0<Z)]
      ring

theorem reopening_diagonal_with_ratio (A M Z η X F Ksrc B deltaLoss ε : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B)
    (hactive : B^3≤Real.exp A*X) (hδ : 0≤deltaLoss) (hε : 0≤ε) :
    (Ksrc/(Ksrc/Z^η))*((globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss *
      ((Real.exp 1*B)*(reopeningScaleConstant A M*Z^4))^ε) ≤
      (((Real.exp 1)^8)^deltaLoss*(reopeningScaleConstant A M^2)^ε)*Z^(η+13*deltaLoss+7*ε) := by
  rw [reopening_cutoff_ratio Z η Ksrc (by linarith) (by linarith)]
  apply (mul_le_mul_of_nonneg_left (reopening_diagonal_monomial A M Z η X F Ksrc B deltaLoss ε
    hZ hη hη1 hX hXZ hF hFZ hK hB hactive hδ hε) (by positivity)).trans_eq
  rw [show η+13*deltaLoss+7*ε=η+(13*deltaLoss+7*ε) by ring]
  simp only [Real.rpow_add (by linarith : 0<Z)]
  ring

theorem reopening_recursive_with_ratio (A M Z η X F Ksrc B deltaLoss ε : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B)
    (hδ : 0≤deltaLoss) (hε : 0≤ε) :
    (Ksrc/(Ksrc/Z^η))*((globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss *
      (reopeningScaleConstant A M*Z^4)^(deltaLoss+8*ε)) ≤
      (((Real.exp 1)^8)^deltaLoss*(reopeningScaleConstant A M)^(deltaLoss+8*ε))*Z^(η+17*deltaLoss+32*ε) := by
  rw [reopening_cutoff_ratio Z η Ksrc (by linarith) (by linarith)]
  apply (mul_le_mul_of_nonneg_left (reopening_recursive_monomial A M Z η X F Ksrc B deltaLoss ε
    hZ hη hη1 hX hXZ hF hFZ hK hB hδ hε) (by positivity)).trans_eq
  rw [show η+17*deltaLoss+32*ε=η+(17*deltaLoss+32*ε) by ring]
  simp only [Real.rpow_add (by linarith : 0<Z)]
  ring

end SecondPassArithmetic

end

end OAI

end


