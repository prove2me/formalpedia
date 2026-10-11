-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0034
-- name    : PNT_ZeroFree_433_0034
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T14:02:28.429837+00:00
-- url     : https://prove2.me/theorems/a1e9b54c-8eaf-4f48-9126-e5e301fdc36e
-- title:
--   Zero-free region foundations: Mellin.CompactWeights [0034]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Mellin.CompactWeights
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/CompactWeights.lean#L56-L595

import Definitions.Def_PNT_ZeroFree_433_0033

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/CompactWeights.lean#L56-L595
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Mellin.CompactWeights
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

namespace CompactScaleBridge

section

open ConcretePrimeRowBridge ShortDraftHeckeBridge FiniteSFactor

theorem outsideCoeff_baseChange_zero
    {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal O)) :
    outsideCoeff S (baseChangeWeight χ) 0 = 0 := by
  classical
  unfold outsideCoeff
  apply Finset.sum_eq_zero
  intro I hI
  have hnorm : Ideal.absNorm I = 0 := mem_fiber.mp hI
  have hbot : I = ⊥ := Ideal.absNorm_eq_zero_iff.mp hnorm
  subst I
  have hz : baseChangeWeight χ (⊥ : Ideal O) = 0 := by
    rw [baseChangeWeight]
    have hμ : UniqueFactorizationMonoid.moebius (⊥ : Ideal O) = 0 := by
      simpa only [Ideal.zero_eq_bot] using
        (UniqueFactorizationMonoid.moebius_zero (α := Ideal O))
    rw [hμ]
    simp
  by_cases hgood : ∀ P ∈ S, ¬P ∣ (⊥ : Ideal O) <;>
    simp [outsideWeight,  hz]

theorem outsideCoeff_compact_hasSum
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (W : ℝ → ℂ) (D : ℝ)
    (hD : 0 < D) (hSupp : ∀ y : ℝ, 2 ≤ y → W y = 0) :
    HasSum (fun n : ℕ =>
      outsideCoeff S (baseChangeWeight χ) n * W ((n : ℝ) / D))
      (realCompactOutsideSum χ S W D) := by
  classical
  let N : ℕ := 2 * Nat.ceil D
  have hNreal : 2 * D ≤ (N : ℝ) := by
    dsimp [N]
    push_cast
    nlinarith [Nat.le_ceil D]
  have hterm (n : ℕ) (hn : n ∉ Finset.Icc 1 N) :
      outsideCoeff S (baseChangeWeight χ) n * W ((n : ℝ) / D) = 0 := by
    by_cases hn0 : n = 0
    · subst n
      rw [outsideCoeff_baseChange_zero]
      simp
    · have hn_gt : N < n := by
        simp only [Finset.mem_Icc] at hn
        omega
      have hnreal : (N : ℝ) < n := by exact_mod_cast hn_gt
      have hratio : 2 ≤ (n : ℝ) / D := by
        apply (le_div_iff₀ hD).2
        nlinarith
      simp [hSupp _ hratio]
  have hs : HasSum (fun n : ℕ =>
      outsideCoeff S (baseChangeWeight χ) n * W ((n : ℝ) / D))
      (∑ n ∈ Finset.Icc 1 N,
        outsideCoeff S (baseChangeWeight χ) n * W ((n : ℝ) / D)) :=
    hasSum_sum_of_ne_finset_zero hterm
  change HasSum _ (∑ I ∈ outsideIdealsUpTo S N,
      baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D))
  rw [outsideIdealSum_eq_outsideCoeff_sum S N (baseChangeWeight χ)
    (fun n : ℕ => W ((n : ℝ) / D))]
  exact hs

end

open ConcretePrimeRowBridge ShortDraftHeckeBridge Filter Asymptotics

theorem realCompactOutsideSum_eq_outsideCompactSum
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (W : ℝ → ℂ) (D : ℝ)
    (hD : 0 < D) (hSupp : ∀ y : ℝ, 2 ≤ y → W y = 0) :
    realCompactOutsideSum χ S W D =
      CompactMellinBridge.outsideCompactSum χ S W D⁻¹ := by
  have hs := outsideCoeff_compact_hasSum χ S W D hD hSupp
  have h := hs.tsum_eq
  simpa only [CompactMellinBridge.outsideCompactSum, div_eq_mul_inv] using h.symm

theorem zero_free_of_fixedTestPrimeMSConstants
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O))
    (hSprime : ∀ P ∈ S, Prime P)
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (hSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hSupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0)
    (hBoundW : ∀ y : ℝ, ‖W y‖ ≤ 1)
    (ε η Cmean Ccount : ℝ) (m₀ : ℕ)
    (hε : 0 ≤ ε) (hη : 0 < η) (hCcount : 0 < Ccount)
    (hMS : ∀ m : ℕ, m₀ ≤ m →
      FixedTestPrimeMSConstants χ S hSbad W m ε Cmean Ccount)
    (ρ : ℂ) (hσρ : (23 / 24 : ℝ) + (ε + η) < ρ.re)
    (hρone : ρ.re < 1) (hWρ : mellin W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 := by
  obtain ⟨LipC, hLipC, hLip⟩ :=
    smooth_supported_hasLipschitzConstant W hSmooth hSupp
  have hFinite := realCompactOutsideSum_isBigO_of_fixedTestPrimeMSConstants
    χ S hSbad W LipC ε η Cmean Ccount m₀
    hLipC hLip hε hη hCcount hBoundW hMS
  have hEq :
      (fun D : ℝ => CompactMellinBridge.outsideCompactSum χ S W D⁻¹) =ᶠ[atTop]
      (realCompactOutsideSum χ S W) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
    exact (realCompactOutsideSum_eq_outsideCompactSum χ S W D hD
      (fun y hy => hSupp y (Or.inr hy))).symm
  have hTop :
      (fun D : ℝ => CompactMellinBridge.outsideCompactSum χ S W D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ ((23 / 24 : ℝ) + (ε + η))) :=
    hFinite.congr' hEq.symm Filter.EventuallyEq.rfl
  exact CompactMellinBridge.baseChange_outsideCompact_zero_free
    χ S hSprime W hSmooth hSupp ((23 / 24 : ℝ) + (ε + η)) hTop
    ρ hσρ hρone hWρ

end CompactScaleBridge

open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ConcreteCompactWeight

noncomputable def bumpData : ContDiffBump (3 / 2 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

noncomputable def bump (y : ℝ) : ℝ := bumpData y

theorem bump_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) bump := by
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (bumpData : ℝ → ℝ)
  exact bumpData.contDiff (n := ⊤)

theorem bump_nonneg (y : ℝ) : 0 ≤ bump y := bumpData.nonneg

theorem bump_one : bump (3 / 2 : ℝ) = 1 := by
  change bumpData (3 / 2 : ℝ) = 1
  exact bumpData.one_of_mem_closedBall (by
    simp only [Metric.mem_closedBall, dist_self]
    exact bumpData.rIn_pos.le)

theorem bump_support (y : ℝ) (hy : y ≤ 1 ∨ 2 ≤ y) : bump y = 0 := by
  change bumpData y = 0
  apply bumpData.zero_of_le_dist
  rw [Real.dist_eq]
  change (1 / 4 : ℝ) ≤ |y - 3 / 2|
  rcases hy with h | h
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith

theorem bump_compact : HasCompactSupport bump := bumpData.hasCompactSupport

noncomputable def positiveExtension (y : ℝ) : ℝ :=
  1 + (y - 1) * Real.smoothTransition (2 * y - 1)

theorem positiveExtension_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) positiveExtension := by
  unfold positiveExtension
  have ht : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => 2 * y - 1) := by fun_prop
  exact contDiff_const.add
    ((contDiff_id.sub contDiff_const).mul
      ((Real.smoothTransition.contDiff (n := ⊤)).comp ht))

theorem positiveExtension_pos (y : ℝ) : 0 < positiveExtension y := by
  unfold positiveExtension
  by_cases hhalf : y ≤ 1 / 2
  · have ht : 2 * y - 1 ≤ 0 := by linarith
    rw [Real.smoothTransition.zero_of_nonpos ht]
    norm_num
  · by_cases hone : 1 ≤ y
    · have ht : 1 ≤ 2 * y - 1 := by linarith
      rw [Real.smoothTransition.one_of_one_le ht]
      linarith
    · have hle := Real.smoothTransition.le_one (2 * y - 1)
      have hnonneg := Real.smoothTransition.nonneg (2 * y - 1)
      have hprod : (1 - y) * Real.smoothTransition (2 * y - 1) ≤ 1 - y := by
        exact (mul_le_mul_of_nonneg_left hle (by linarith)).trans_eq (mul_one _)
      nlinarith

theorem positiveExtension_eq (y : ℝ) (hy : 1 ≤ y) :
    positiveExtension y = y := by
  unfold positiveExtension
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 * y - 1)]
  ring

noncomputable def weight (ρ : ℂ) (y : ℝ) : ℂ :=
  (bump y : ℂ) * Complex.exp ((Real.log (positiveExtension y) : ℂ) * (-ρ))

theorem weight_smooth (ρ : ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (weight ρ) := by
  have hb : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => (bump y : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp bump_smooth
  have hlog : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun y : ℝ => Real.log (positiveExtension y)) :=
    positiveExtension_smooth.log (fun y => ne_of_gt (positiveExtension_pos y))
  have hc : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun y : ℝ => (Real.log (positiveExtension y) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp hlog
  have hexp : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun y : ℝ => Complex.exp ((Real.log (positiveExtension y) : ℂ) * (-ρ))) :=
    (hc.mul contDiff_const).cexp
  exact hb.mul hexp

theorem weight_support (ρ : ℂ) (y : ℝ)
    (hy : y ≤ 1 ∨ 2 ≤ y) : weight ρ y = 0 := by
  simp [weight, bump_support y hy]

theorem weight_eq_cpow (ρ : ℂ) (y : ℝ) (hy : 0 < y) :
    weight ρ y = (y : ℂ) ^ (-ρ) * (bump y : ℂ) := by
  by_cases hy1 : y ≤ 1
  · simp [weight, bump_support y (Or.inl hy1)]
  · have hgy : positiveExtension y = y :=
      positiveExtension_eq y (le_of_lt (lt_of_not_ge hy1))
    rw [weight, hgy, Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (ne_of_gt hy))]
    rw [← Complex.ofReal_log hy.le]
    ring

theorem weight_mellin_eq_bump (ρ : ℂ) :
    mellin (weight ρ) ρ = mellin (fun y : ℝ => (bump y : ℂ)) 0 := by
  have hpoint : Set.EqOn (weight ρ)
      (fun y : ℝ => (y : ℂ) ^ (-ρ) * (bump y : ℂ)) (Set.Ioi 0) := by
    intro y hy
    exact weight_eq_cpow ρ y hy
  rw [mellin]
  have heq :
      (∫ y : ℝ in Set.Ioi 0, (y : ℂ) ^ (ρ - 1) * weight ρ y) =
      mellin (fun y : ℝ => (y : ℂ) ^ (-ρ) * (bump y : ℂ)) ρ := by
    rw [mellin]
    exact setIntegral_congr_fun measurableSet_Ioi (fun y hy => by
      simp only [smul_eq_mul]
      rw [hpoint hy])
  simp only [smul_eq_mul]
  rw [heq]
  simpa only [smul_eq_mul, add_neg_cancel] using
    (mellin_cpow_smul (fun y : ℝ => (bump y : ℂ)) ρ (-ρ))

noncomputable def weightedBump (y : ℝ) : ℝ :=
  bump y / positiveExtension y

theorem weightedBump_continuous : Continuous weightedBump := by
  exact bump_smooth.continuous.div positiveExtension_smooth.continuous
    (fun y => ne_of_gt (positiveExtension_pos y))

theorem weightedBump_compact : HasCompactSupport weightedBump := by
  change HasCompactSupport (fun y : ℝ => bump y * (positiveExtension y)⁻¹)
  exact bump_compact.mul_right

theorem weightedBump_nonneg (y : ℝ) : 0 ≤ weightedBump y := by
  exact div_nonneg (bump_nonneg y) (positiveExtension_pos y).le

theorem weightedBump_nonzero : weightedBump (3 / 2 : ℝ) ≠ 0 := by
  simp [weightedBump, bump_one, positiveExtension_eq (3 / 2) (by norm_num)]

theorem weightedBump_integral_pos :
    0 < ∫ y : ℝ, weightedBump y := by
  exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    weightedBump_continuous weightedBump_compact weightedBump_nonneg
    weightedBump_nonzero

theorem weightedBump_eq_zero_of_nonpos (y : ℝ) (hy : y ≤ 0) :
    weightedBump y = 0 := by
  simp [weightedBump, bump_support y (Or.inl (by linarith))]

theorem mellin_bump_zero_eq_integral_weightedBump :
    mellin (fun y : ℝ => (bump y : ℂ)) 0 =
      (∫ y : ℝ, weightedBump y : ℝ) := by
  rw [mellin]
  have hpoint : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ ((0 : ℂ) - 1) • (bump y : ℂ) =
        (weightedBump y : ℂ) := by
    intro y hy
    by_cases hy1 : y ≤ 1
    · simp [weightedBump, bump_support y (Or.inl hy1)]
    · have hgy : positiveExtension y = y :=
        positiveExtension_eq y (le_of_lt (lt_of_not_ge hy1))
      simp [weightedBump, hgy, Complex.cpow_neg_one, smul_eq_mul,
        div_eq_mul_inv, mul_comm]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => hpoint y hy)]
  rw [integral_complex_ofReal]
  congr 1
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
    exact weightedBump_eq_zero_of_nonpos y (le_of_not_gt hy))

theorem weight_mellin_ne_zero (ρ : ℂ) : mellin (weight ρ) ρ ≠ 0 := by
  rw [weight_mellin_eq_bump, mellin_bump_zero_eq_integral_weightedBump]
  exact Complex.ofReal_ne_zero.mpr weightedBump_integral_pos.ne'

theorem weight_norm_le_one (ρ : ℂ) (hρ : 0 ≤ ρ.re) (y : ℝ) :
    ‖weight ρ y‖ ≤ 1 := by
  by_cases hylo : y ≤ 1
  · rw [weight_support ρ y (Or.inl hylo)]
    simp
  by_cases hyhi : 2 ≤ y
  · rw [weight_support ρ y (Or.inr hyhi)]
    simp
  have hy1 : 1 ≤ y := le_of_lt (lt_of_not_ge hylo)
  have hypos : 0 < y := by linarith
  rw [weight_eq_cpow ρ y hypos, Complex.norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hypos,
    Complex.neg_re, Complex.norm_of_nonneg (bump_nonneg y)]
  have hpow : y ^ (-ρ.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith)
  have hpowpos : 0 ≤ y ^ (-ρ.re) := Real.rpow_nonneg hypos.le _
  have hb : bump y ≤ 1 := bumpData.le_one
  nlinarith

end ConcreteCompactWeight

namespace CompactScaleBridge

section

open ConcreteCompactWeight

theorem zero_free_of_fixedTestPrimeMSConstants_concrete
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hSprime : ∀ P ∈ S, Prime P)
    (hSbad : ∀ P : Ideal ActualEisensteinCubic.O, P.IsMaximal →
      ConcretePrimeRowBridge.goodLambda ∈ P → P ∈ S)
    (ρ : ℂ)
    (ε η Cmean Ccount : ℝ) (m₀ : ℕ)
    (hε : 0 ≤ ε) (hη : 0 < η) (hCcount : 0 < Ccount)
    (hMS : ∀ m : ℕ, m₀ ≤ m →
      FixedTestPrimeMSConstants χ S hSbad (weight ρ) m ε Cmean Ccount)
    (hσρ : (23 / 24 : ℝ) + (ε + η) < ρ.re)
    (hρone : ρ.re < 1) :
    χ.LFunction ρ ≠ 0 := by
  have hρnonneg : 0 ≤ ρ.re := by linarith
  exact zero_free_of_fixedTestPrimeMSConstants
    χ S hSprime hSbad (weight ρ)
    (weight_smooth ρ) (weight_support ρ)
    (weight_norm_le_one ρ hρnonneg)
    ε η Cmean Ccount m₀ hε hη hCcount hMS
    ρ hσρ hρone (weight_mellin_ne_zero ρ)

end

theorem dirichletTarget_of_fixedTestPrimeMSConstants_concrete
    (hMS : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (ρ : ℂ), (23 / 24 : ℝ) < ρ.re → ρ.re < 1 →
      ∃ S : Finset (Ideal ActualEisensteinCubic.O),
      ∃ _hSprime : ∀ P ∈ S, Prime P,
      ∃ hSbad : ∀ P : Ideal ActualEisensteinCubic.O,
        P.IsMaximal → ConcretePrimeRowBridge.goodLambda ∈ P → P ∈ S,
      ∃ ε η Cmean Ccount : ℝ, ∃ m₀ : ℕ,
      ∃ _hmean : ∀ m : ℕ, m₀ ≤ m →
          FixedTestPrimeMSConstants χ S hSbad
            (ConcreteCompactWeight.weight ρ) m ε Cmean Ccount,
        0 ≤ ε ∧ 0 < η ∧ 0 < Ccount ∧
        (23 / 24 : ℝ) + (ε + η) < ρ.re) :
    ShortDraft.DirichletTarget := by
  intro q _ χ ρ h23 hprincipal
  by_cases hρone : ρ.re < 1
  · obtain ⟨S, hSprime, hSbad, ε, η, Cmean, Ccount, m₀,
      hmean, hε, hη, hCcount, hgap⟩ := hMS q χ ρ h23 hρone
    exact zero_free_of_fixedTestPrimeMSConstants_concrete
      χ S hSprime hSbad ρ ε η Cmean Ccount m₀
      hε hη hCcount hmean hgap hρone
  · exact ShortDraft.dirichlet_target_of_one_le_re q χ ρ
      (le_of_not_gt hρone) hprincipal

end CompactScaleBridge

namespace ActualEisensteinCubic

open ShortDraftCusp

theorem A3_unramified_fixed_denominator_local_character
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (a b c d : O) (hdet : a * d - b * c = 1)
    (hd : d ∈ P) :
    cubicChar P hgood (Ideal.Quotient.mk P (-b)) *
      cubicChar P hgood (Ideal.Quotient.mk P c) = 1 := by
  have hd0 : Ideal.Quotient.mk P d = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hd
  have hrel := congrArg (Ideal.Quotient.mk P)
    (A3_unramified_det_relation a b c d hdet)
  simp only [map_mul, map_sub, map_one, hd0, mul_zero, sub_zero] at hrel
  have hh := congrArg (cubicChar P hgood) hrel
  simpa only [map_mul, map_one] using hh

end ActualEisensteinCubic

namespace TwoPassProfiles

theorem first_poisson_profile
    (K h d f E t c x₁ x₂ : ℝ)
    (hd : d ≠ 0) (hf : f ≠ 0) (hE : E ≠ 0)
    (ht : t ≠ 0) (hc : c ≠ 0)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) :
    K * h / (d * (t * x₁) * (t * x₂) * c) =
      K * (h * f ^ 2 * E) /
        (d * f ^ 2 * E * t ^ 2 * c * x₁ * x₂) := by
  field_simp

theorem second_poisson_profile
    (Y k'' d e v n₁ n₂ : ℝ)
    (hd : d ≠ 0) (he : e ≠ 0) (hv : v ≠ 0)
    (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0) :
    Y * k'' / (e * (v * n₁) * (v * n₂)) =
      Y * (d * e * k'') / (d * e ^ 2 * v ^ 2 * n₁ * n₂) := by
  field_simp

theorem child_column_profile
    (Lᵢ g v n : ℝ)
    (hLᵢ : Lᵢ ≠ 0) (hg : g ≠ 0) (hv : v ≠ 0) :
    (g * v * n) / Lᵢ = n / (Lᵢ / (g * v)) := by
  field_simp

theorem first_profile_logshape
    (K y d f E t c x₁ x₂ : ℝ)
    (hK : 0 < K) (hy : 0 < y) (hd : 0 < d)
    (hf : 0 < f) (hE : 0 < E) (ht : 0 < t)
    (hc : 0 < c) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) :
    Real.log (K * y / (d * f ^ 2 * E * t ^ 2 * c * x₁ * x₂)) =
      Real.log K + Real.log y - Real.log d -
      2 * Real.log f - Real.log E - 2 * Real.log t -
      Real.log c - Real.log x₁ - Real.log x₂ := by
  have hden : 0 < d * f ^ 2 * E * t ^ 2 * c * x₁ * x₂ := by positivity
  rw [Real.log_div (by positivity) (ne_of_gt hden)]
  rw [Real.log_mul (ne_of_gt hK) (ne_of_gt hy)]
  rw [Real.log_mul (ne_of_gt (by positivity : 0 < d * f ^ 2 * E * t ^ 2 * c * x₁)) (ne_of_gt hx₂)]
  rw [Real.log_mul (ne_of_gt (by positivity : 0 < d * f ^ 2 * E * t ^ 2 * c)) (ne_of_gt hx₁)]
  rw [Real.log_mul (ne_of_gt (by positivity : 0 < d * f ^ 2 * E * t ^ 2)) (ne_of_gt hc)]
  rw [Real.log_mul (ne_of_gt (by positivity : 0 < d * f ^ 2 * E)) (ne_of_gt (by positivity : 0 < t ^ 2))]
  rw [Real.log_mul (ne_of_gt (by positivity : 0 < d * f ^ 2)) (ne_of_gt hE)]
  rw [Real.log_mul (ne_of_gt hd) (ne_of_gt (by positivity : 0 < f ^ 2))]
  rw [Real.log_pow, Real.log_pow]
  ring

theorem second_profile_logshape
    (Y k d e v n₁ n₂ : ℝ)
    (hY : 0 < Y) (hk : 0 < k) (hd : 0 < d)
    (he : 0 < e) (hv : 0 < v)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    Real.log (Y * k / (d * e ^ 2 * v ^ 2 * n₁ * n₂)) =
      Real.log Y + Real.log k - Real.log d -
      2 * Real.log e - 2 * Real.log v -
      Real.log n₁ - Real.log n₂ := by
  have hden : 0 < d * e ^ 2 * v ^ 2 * n₁ * n₂ := by positivity
  rw [Real.log_div (by positivity) (ne_of_gt hden)]
  rw [Real.log_mul (ne_of_gt hY) (ne_of_gt hk)]
  rw [Real.log_mul (ne_of_gt (by positivity : 0 < d * e ^ 2 * v ^ 2 * n₁)) (ne_of_gt hn₂)]
  rw [Real.log_mul (ne_of_gt (by positivity : 0 < d * e ^ 2 * v ^ 2)) (ne_of_gt hn₁)]
  rw [Real.log_mul (ne_of_gt (by positivity : 0 < d * e ^ 2)) (ne_of_gt (by positivity : 0 < v ^ 2))]
  rw [Real.log_mul (ne_of_gt hd) (ne_of_gt (by positivity : 0 < e ^ 2))]
  rw [Real.log_pow, Real.log_pow]
  ring

private def firstCoeff : Fin 9 → ℝ
  | 0 => 1 | 1 => 1 | 2 => -1 | 3 => -2 | 4 => -1
  | 5 => -2 | 6 => -1 | 7 => -1 | 8 => -1

private noncomputable def firstLogs (K y d f E t c x₁ x₂ : ℝ) : Fin 9 → ℝ
  | 0 => Real.log K | 1 => Real.log y | 2 => Real.log d
  | 3 => Real.log f | 4 => Real.log E | 5 => Real.log t
  | 6 => Real.log c | 7 => Real.log x₁ | 8 => Real.log x₂

theorem first_logsum
    (K y d f E t c x₁ x₂ : ℝ) :
    (∑ j : Fin 9, firstCoeff j * firstLogs K y d f E t c x₁ x₂ j) =
      Real.log K + Real.log y - Real.log d -
      2 * Real.log f - Real.log E - 2 * Real.log t -
      Real.log c - Real.log x₁ - Real.log x₂ := by
  simp [Fin.sum_univ_succ, firstCoeff, firstLogs]
  ring

private def secondCoeff : Fin 7 → ℝ
  | 0 => 1 | 1 => 1 | 2 => -1 | 3 => -2
  | 4 => -2 | 5 => -1 | 6 => -1

private noncomputable def secondLogs (Y k d e v n₁ n₂ : ℝ) : Fin 7 → ℝ
  | 0 => Real.log Y | 1 => Real.log k | 2 => Real.log d
  | 3 => Real.log e | 4 => Real.log v
  | 5 => Real.log n₁ | 6 => Real.log n₂

theorem second_logsum
    (Y k d e v n₁ n₂ : ℝ) :
    (∑ j : Fin 7, secondCoeff j * secondLogs Y k d e v n₁ n₂ j) =
      Real.log Y + Real.log k - Real.log d -
      2 * Real.log e - 2 * Real.log v -
      Real.log n₁ - Real.log n₂ := by
  simp [Fin.sum_univ_succ, secondCoeff, secondLogs]
  ring

theorem first_profile_exp
    (K y d f E t c x₁ x₂ : ℝ)
    (hK : 0 < K) (hy : 0 < y) (hd : 0 < d)
    (hf : 0 < f) (hE : 0 < E) (ht : 0 < t)
    (hc : 0 < c) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) :
    K * y / (d * f ^ 2 * E * t ^ 2 * c * x₁ * x₂) =
      Real.exp (∑ j : Fin 9,
        firstCoeff j * firstLogs K y d f E t c x₁ x₂ j) := by
  rw [first_logsum, ← first_profile_logshape K y d f E t c x₁ x₂
    hK hy hd hf hE ht hc hx₁ hx₂]
  exact (Real.exp_log (by positivity)).symm

theorem second_profile_exp
    (Y k d e v n₁ n₂ : ℝ)
    (hY : 0 < Y) (hk : 0 < k) (hd : 0 < d)
    (he : 0 < e) (hv : 0 < v)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    Y * k / (d * e ^ 2 * v ^ 2 * n₁ * n₂) =
      Real.exp (∑ j : Fin 7,
        secondCoeff j * secondLogs Y k d e v n₁ n₂ j) := by
  rw [second_logsum, ← second_profile_logshape Y k d e v n₁ n₂
    hY hk hd he hv hn₁ hn₂]
  exact (Real.exp_log (by positivity)).symm

theorem first_dyadic_profile
    (K₀ y₀ d₀ f₀ E₀ t₀ c₀ x₁₀ x₂₀
      k y d f E t c x₁ x₂ : ℝ)
    (hK₀ : K₀ ≠ 0) (hy₀ : y₀ ≠ 0) (hd₀ : d₀ ≠ 0)
    (hf₀ : f₀ ≠ 0) (hE₀ : E₀ ≠ 0) (ht₀ : t₀ ≠ 0)
    (hc₀ : c₀ ≠ 0) (hx₁₀ : x₁₀ ≠ 0) (hx₂₀ : x₂₀ ≠ 0)
    (hk : 0 < k) (hy : 0 < y) (hd : 0 < d)
    (hf : 0 < f) (hE : 0 < E) (ht : 0 < t)
    (hc : 0 < c) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) :
    (K₀ * k) * (y₀ * y) /
      ((d₀ * d) * (f₀ * f) ^ 2 * (E₀ * E) *
        (t₀ * t) ^ 2 * (c₀ * c) * (x₁₀ * x₁) * (x₂₀ * x₂)) =
      (K₀ * y₀ /
        (d₀ * f₀ ^ 2 * E₀ * t₀ ^ 2 * c₀ * x₁₀ * x₂₀)) *
        Real.exp (∑ j : Fin 9,
          firstCoeff j * firstLogs k y d f E t c x₁ x₂ j) := by
  rw [← first_profile_exp k y d f E t c x₁ x₂
    hk hy hd hf hE ht hc hx₁ hx₂]
  field_simp

theorem second_dyadic_profile
    (Y₀ k₀ d₀ e₀ v₀ n₁₀ n₂₀
      y k d e v n₁ n₂ : ℝ)
    (hY₀ : Y₀ ≠ 0) (hk₀ : k₀ ≠ 0) (hd₀ : d₀ ≠ 0)
    (he₀ : e₀ ≠ 0) (hv₀ : v₀ ≠ 0)
    (hn₁₀ : n₁₀ ≠ 0) (hn₂₀ : n₂₀ ≠ 0)
    (hy : 0 < y) (hk : 0 < k) (hd : 0 < d)
    (he : 0 < e) (hv : 0 < v)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    (Y₀ * y) * (k₀ * k) /
      ((d₀ * d) * (e₀ * e) ^ 2 * (v₀ * v) ^ 2 *
        (n₁₀ * n₁) * (n₂₀ * n₂)) =
      (Y₀ * k₀ /
        (d₀ * e₀ ^ 2 * v₀ ^ 2 * n₁₀ * n₂₀)) *
        Real.exp (∑ j : Fin 7,
          secondCoeff j * secondLogs y k d e v n₁ n₂ j) := by
  rw [← second_profile_exp y k d e v n₁ n₂
    hy hk hd he hv hn₁ hn₂]
  field_simp

end TwoPassProfiles

end

end OAI

end


