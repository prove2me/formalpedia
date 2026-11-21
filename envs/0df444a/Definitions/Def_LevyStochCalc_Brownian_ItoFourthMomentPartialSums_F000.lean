-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F000
-- name    : LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:53:45.86381+00:00
-- url     : https://prove2.me/theorems/fcb84c78-dfc9-4374-9254-fe8368f4374d
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoFourthMomentPartialSums
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoFourthMomentPartialSums. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F002
import Definitions.Def_SourceProof_2f34208c7b9f4e759c37de78
import Definitions.Def_SourceProof_abcff24ab5778ee51e37f41d

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second and fourth moments of the elementary Brownian integral

The moment recursion over the partial sums of the elementary integral of a simple integrand: one
step adds the second moment of the new tile, and in the fourth-moment recursion the odd-power
cross terms drop out because a coefficient measurable before an increment is independent of it.
Iterating gives `𝔼|∫_0^T H dW|⁴ ≤ (6 + c)·C⁴·T²` for an integrand bounded by `C`, where `c` is
the fourth moment of the standard Gaussian, and the sharper form
`𝔼|∫_0^T H dW|⁴ ≤ (6 + c)·(∑_j c_j² Δ_j)²` against a per-tile coefficient bound `c`, which for a
coefficient vanishing off a subinterval sees only that subinterval's length.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

namespace SimplePredictable

variable {T : ℝ} (G : SimplePredictable Ω T)
  {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

omit [IsProbabilityMeasure P] in
/-- A real random variable in `Lᵐ` has an integrable `m`-th power. -/
private theorem integrable_pow_of_memLp {f : Ω → ℝ} {m : ℕ} (hm : m ≠ 0)
    {p : ℝ≥0∞} (hp : p = (m : ℝ≥0∞)) (h : MemLp f p P) : Integrable (fun ω => f ω ^ m) P := by
  subst hp
  refine (h.integrable_norm_pow hm).mono ((continuous_pow m).comp_aestronglyMeasurable h.1)
    (Filter.Eventually.of_forall fun ω => ?_)
  simp
section Moments

/-- One step of a second-moment recursion. -/
private theorem integral_add_mul_increment_sq
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {S ξ : Ω → ℝ}
    (hS2 : MemLp S 2 P) (hSm : Measurable S)
    (hSad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) S)
    (hξm : Measurable ξ) (hξad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) ξ)
    {C : ℝ} (hC0 : 0 ≤ C) (hCξ : ∀ ω, |ξ ω| ≤ C) :
    ∫ ω, (S ω + ξ ω * (W.W b ω - W.W a ω)) ^ 2 ∂P
      = (∫ ω, S ω ^ 2 ∂P) + (∫ ω, ξ ω ^ 2 ∂P) * (b - a) := by
  have hDm : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have hD2 : MemLp (fun ω => W.W b ω - W.W a ω) 2 P := memLp_increment W ha hab 2 (by simp)
  have hSD : Integrable (fun ω => |S ω| * |W.W b ω - W.W a ω|) P := by
    have h := (hS2.abs).integrable_mul (hD2.abs)
    exact h
  have hD2int : Integrable (fun ω => (W.W b ω - W.W a ω) ^ 2) P :=
    integrable_pow_of_memLp (m := 2) (by norm_num) (by simp) hD2
  have hi1 : Integrable (fun ω => S ω ^ 2) P :=
    integrable_pow_of_memLp (m := 2) (by norm_num) (by simp) hS2
  have hi2 : Integrable (fun ω => (2 * (S ω * ξ ω)) * (W.W b ω - W.W a ω) ^ 1) P := by
    refine (hSD.const_mul (2 * C)).mono
      (((measurable_const.mul (hSm.mul hξm)).mul (hDm.pow_const 1)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    have h1 := hCξ ω
    have h2 := abs_nonneg (S ω)
    have h3 := abs_nonneg (W.W b ω - W.W a ω)
    rw [pow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * C * (|S ω| * |W.W b ω - W.W a ω|))]
    have h4 : |(2 : ℝ)| = 2 := by norm_num
    rw [h4]
    nlinarith [mul_nonneg (mul_nonneg h2 h3) (sub_nonneg.mpr h1)]
  have hi3 : Integrable (fun ω => ξ ω ^ 2 * (W.W b ω - W.W a ω) ^ 2) P := by
    refine (hD2int.const_mul (C ^ 2)).mono
      (((hξm.pow_const 2).mul (hDm.pow_const 2)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    have h1 := hCξ ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow, abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ C ^ 2 * (W.W b ω - W.W a ω) ^ 2)]
    have h2 : |W.W b ω - W.W a ω| ^ 2 = (W.W b ω - W.W a ω) ^ 2 := by
      rw [← abs_pow, abs_of_nonneg (sq_nonneg _)]
    rw [h2]
    nlinarith [sq_nonneg (W.W b ω - W.W a ω),
      mul_le_mul h1 h1 (abs_nonneg (ξ ω)) hC0]
  have hexp : ∀ ω, (S ω + ξ ω * (W.W b ω - W.W a ω)) ^ 2
      = S ω ^ 2 + (2 * (S ω * ξ ω)) * (W.W b ω - W.W a ω) ^ 1
        + ξ ω ^ 2 * (W.W b ω - W.W a ω) ^ 2 := fun ω => by ring
  have hξ2ad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) (fun ω => ξ ω ^ 2) := by
    have hfun : (fun ω => ξ ω ^ 2) = ξ * ξ := by funext ω; rw [pow_two]; rfl
    rw [hfun]; exact hξad.mul hξad
  have hi12 : Integrable
      (fun ω => S ω ^ 2 + (2 * (S ω * ξ ω)) * (W.W b ω - W.W a ω) ^ 1) P := hi1.add hi2
  simp_rw [hexp]
  rw [integral_add hi12 hi3, integral_add hi1 hi2,
    _root_.Prove2MeSourceProof.h_2f34208c7b9f4e759c37de78 W ℱ hℱ ha hab (Y := fun ω => 2 * (S ω * ξ ω))
      (MeasureTheory.stronglyMeasurable_const.mul (hSad.mul hξad))
      (measurable_const.mul (hSm.mul hξm)) 1,
    integral_increment_pow_odd W ha hab odd_one, mul_zero, add_zero,
    _root_.Prove2MeSourceProof.h_2f34208c7b9f4e759c37de78 W ℱ hℱ ha hab (Y := fun ω => ξ ω ^ 2)
      hξ2ad (hξm.pow_const 2) 2,
    integral_increment_sq W ha hab]
/-- One step of a fourth-moment recursion. -/
private theorem integral_add_mul_increment_pow_four
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {S ξ : Ω → ℝ}
    (hS4 : MemLp S 4 P) (hSm : Measurable S)
    (hSad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) S)
    (hξm : Measurable ξ) (hξad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) ξ)
    {C : ℝ} (hC0 : 0 ≤ C) (hCξ : ∀ ω, |ξ ω| ≤ C) :
    ∫ ω, (S ω + ξ ω * (W.W b ω - W.W a ω)) ^ 4 ∂P
      = (∫ ω, S ω ^ 4 ∂P)
        + 6 * ((∫ ω, S ω ^ 2 * ξ ω ^ 2 ∂P) * (b - a))
        + (∫ ω, ξ ω ^ 4 ∂P) * ((b - a) ^ 2 * gaussianFourthMoment) := by
  have hDm : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have hD4 : MemLp (fun ω => W.W b ω - W.W a ω) 4 P := memLp_increment W ha hab 4 (by simp)
  have hU4 : Integrable
      (fun ω => (|S ω| + |W.W b ω - W.W a ω|) ^ 4) P :=
    integrable_pow_of_memLp (m := 4) (by norm_num) (by simp) (hS4.abs.add hD4.abs)
  have hpow : ∀ (i j : ℕ), i + j = 4 → ∀ ω,
      |S ω| ^ i * |W.W b ω - W.W a ω| ^ j ≤ (|S ω| + |W.W b ω - W.W a ω|) ^ 4 := by
    intro i j hij ω
    have hx : |S ω| ≤ |S ω| + |W.W b ω - W.W a ω| := by
      linarith [abs_nonneg (W.W b ω - W.W a ω)]
    have hy : |W.W b ω - W.W a ω| ≤ |S ω| + |W.W b ω - W.W a ω| := by
      linarith [abs_nonneg (S ω)]
    calc |S ω| ^ i * |W.W b ω - W.W a ω| ^ j
        ≤ (|S ω| + |W.W b ω - W.W a ω|) ^ i * (|S ω| + |W.W b ω - W.W a ω|) ^ j :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx i)
            (pow_le_pow_left₀ (abs_nonneg _) hy j) (by positivity) (by positivity)
      _ = (|S ω| + |W.W b ω - W.W a ω|) ^ 4 := by rw [← pow_add, hij]
  have key : ∀ (K : ℝ), 0 ≤ K → ∀ (A : Ω → ℝ), Measurable A → ∀ (i j : ℕ), i + j = 4 →
      (∀ ω, |A ω| ≤ K * |S ω| ^ i) →
      Integrable (fun ω => A ω * (W.W b ω - W.W a ω) ^ j) P := by
    intro K hK A hAm i j hij hA
    refine (hU4.const_mul K).mono ((hAm.mul (hDm.pow_const j)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow, abs_mul, abs_of_nonneg hK,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (|S ω| + |W.W b ω - W.W a ω|) ^ 4)]
    calc |A ω| * |W.W b ω - W.W a ω| ^ j
        ≤ (K * |S ω| ^ i) * |W.W b ω - W.W a ω| ^ j :=
          mul_le_mul_of_nonneg_right (hA ω) (by positivity)
      _ = K * (|S ω| ^ i * |W.W b ω - W.W a ω| ^ j) := by ring
      _ ≤ K * (|S ω| + |W.W b ω - W.W a ω|) ^ 4 :=
          mul_le_mul_of_nonneg_left (hpow i j hij ω) hK
  have hi1 : Integrable (fun ω => S ω ^ 4) P :=
    integrable_pow_of_memLp (m := 4) (by norm_num) (by simp) hS4
  have hi2 : Integrable
      (fun ω => (4 * (S ω ^ 3 * ξ ω)) * (W.W b ω - W.W a ω) ^ 1) P := by
    refine key (4 * C) (by positivity) (fun ω => 4 * (S ω ^ 3 * ξ ω))
      (measurable_const.mul ((hSm.pow_const 3).mul hξm)) 3 1 rfl fun ω => ?_
    rw [abs_mul, abs_mul, abs_pow, show |(4 : ℝ)| = 4 from by norm_num]
    have := hCξ ω
    nlinarith [pow_nonneg (abs_nonneg (S ω)) 3, abs_nonneg (ξ ω)]
  have hi3 : Integrable
      (fun ω => (6 * (S ω ^ 2 * ξ ω ^ 2)) * (W.W b ω - W.W a ω) ^ 2) P := by
    refine key (6 * C ^ 2) (by positivity) (fun ω => 6 * (S ω ^ 2 * ξ ω ^ 2))
      (measurable_const.mul ((hSm.pow_const 2).mul (hξm.pow_const 2))) 2 2 rfl fun ω => ?_
    rw [abs_mul, abs_mul, abs_pow, abs_pow, show |(6 : ℝ)| = 6 from by norm_num]
    have h := hCξ ω
    nlinarith [pow_nonneg (abs_nonneg (S ω)) 2, abs_nonneg (ξ ω),
      mul_le_mul h h (abs_nonneg (ξ ω)) hC0]
  have hi4 : Integrable
      (fun ω => (4 * (S ω * ξ ω ^ 3)) * (W.W b ω - W.W a ω) ^ 3) P := by
    refine key (4 * C ^ 3) (by positivity) (fun ω => 4 * (S ω * ξ ω ^ 3))
      (measurable_const.mul (hSm.mul (hξm.pow_const 3))) 1 3 rfl fun ω => ?_
    rw [abs_mul, abs_mul, abs_pow, show |(4 : ℝ)| = 4 from by norm_num, pow_one]
    have h3 : |ξ ω| ^ 3 ≤ C ^ 3 := pow_le_pow_left₀ (abs_nonneg _) (hCξ ω) 3
    nlinarith [mul_nonneg (abs_nonneg (S ω)) (sub_nonneg.mpr h3)]
  have hi5 : Integrable (fun ω => ξ ω ^ 4 * (W.W b ω - W.W a ω) ^ 4) P := by
    refine key (C ^ 4) (by positivity) (fun ω => ξ ω ^ 4) (hξm.pow_const 4) 0 4 rfl fun ω => ?_
    rw [abs_pow, pow_zero, mul_one]
    exact pow_le_pow_left₀ (abs_nonneg _) (hCξ ω) 4
  have hexp : ∀ ω, (S ω + ξ ω * (W.W b ω - W.W a ω)) ^ 4
      = S ω ^ 4 + (4 * (S ω ^ 3 * ξ ω)) * (W.W b ω - W.W a ω) ^ 1
        + (6 * (S ω ^ 2 * ξ ω ^ 2)) * (W.W b ω - W.W a ω) ^ 2
        + (4 * (S ω * ξ ω ^ 3)) * (W.W b ω - W.W a ω) ^ 3
        + ξ ω ^ 4 * (W.W b ω - W.W a ω) ^ 4 := fun ω => by ring
  have hi12 : Integrable
      (fun ω => S ω ^ 4 + (4 * (S ω ^ 3 * ξ ω)) * (W.W b ω - W.W a ω) ^ 1) P := hi1.add hi2
  have hi123 : Integrable
      (fun ω => S ω ^ 4 + (4 * (S ω ^ 3 * ξ ω)) * (W.W b ω - W.W a ω) ^ 1
        + (6 * (S ω ^ 2 * ξ ω ^ 2)) * (W.W b ω - W.W a ω) ^ 2) P := hi12.add hi3
  have hi1234 : Integrable
      (fun ω => S ω ^ 4 + (4 * (S ω ^ 3 * ξ ω)) * (W.W b ω - W.W a ω) ^ 1
        + (6 * (S ω ^ 2 * ξ ω ^ 2)) * (W.W b ω - W.W a ω) ^ 2
        + (4 * (S ω * ξ ω ^ 3)) * (W.W b ω - W.W a ω) ^ 3) P := hi123.add hi4
  have hS3ξ : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a)
      (fun ω => 4 * (S ω ^ 3 * ξ ω)) := by
    have h3 : (fun ω => S ω ^ 3) = S * S * S := by funext ω; simp only [Pi.mul_apply]; ring
    exact MeasureTheory.stronglyMeasurable_const.mul ((h3 ▸ ((hSad.mul hSad).mul hSad)).mul hξad)
  have hS2ξ2 : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a)
      (fun ω => 6 * (S ω ^ 2 * ξ ω ^ 2)) := by
    have h2 : (fun ω => S ω ^ 2) = S * S := by funext ω; simp only [Pi.mul_apply]; ring
    have h2' : (fun ω => ξ ω ^ 2) = ξ * ξ := by funext ω; simp only [Pi.mul_apply]; ring
    exact MeasureTheory.stronglyMeasurable_const.mul
      ((h2 ▸ (hSad.mul hSad)).mul (h2' ▸ (hξad.mul hξad)))
  have hSξ3 : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a)
      (fun ω => 4 * (S ω * ξ ω ^ 3)) := by
    have h3 : (fun ω => ξ ω ^ 3) = ξ * ξ * ξ := by funext ω; simp only [Pi.mul_apply]; ring
    exact MeasureTheory.stronglyMeasurable_const.mul (hSad.mul (h3 ▸ ((hξad.mul hξad).mul hξad)))
  have hξ4 : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) (fun ω => ξ ω ^ 4) := by
    have h4 : (fun ω => ξ ω ^ 4) = ξ * ξ * ξ * ξ := by funext ω; simp only [Pi.mul_apply]; ring
    exact h4 ▸ (((hξad.mul hξad).mul hξad).mul hξad)
  simp_rw [hexp]
  rw [integral_add hi1234 hi5, integral_add hi123 hi4, integral_add hi12 hi3,
    integral_add hi1 hi2,
    _root_.Prove2MeSourceProof.h_2f34208c7b9f4e759c37de78 W ℱ hℱ ha hab (Y := fun ω => 4 * (S ω ^ 3 * ξ ω)) hS3ξ
      (measurable_const.mul ((hSm.pow_const 3).mul hξm)) 1,
    integral_increment_pow_odd W ha hab odd_one, mul_zero, add_zero,
    _root_.Prove2MeSourceProof.h_2f34208c7b9f4e759c37de78 W ℱ hℱ ha hab (Y := fun ω => 6 * (S ω ^ 2 * ξ ω ^ 2)) hS2ξ2
      (measurable_const.mul ((hSm.pow_const 2).mul (hξm.pow_const 2))) 2,
    integral_increment_sq W ha hab,
    _root_.Prove2MeSourceProof.h_2f34208c7b9f4e759c37de78 W ℱ hℱ ha hab (Y := fun ω => 4 * (S ω * ξ ω ^ 3)) hSξ3
      (measurable_const.mul (hSm.mul (hξm.pow_const 3))) 3,
    integral_increment_pow_odd W ha hab (by decide : Odd 3), mul_zero, add_zero,
    _root_.Prove2MeSourceProof.h_2f34208c7b9f4e759c37de78 W ℱ hℱ ha hab (Y := fun ω => ξ ω ^ 4) hξ4
      (hξm.pow_const 4) 4,
    integral_increment_pow_four W ha hab]
  rw [integral_const_mul]
  ring
variable (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)

include hℱ h_adapt hC0 hC in
/-- One step of the second-moment recursion for the partial sums. -/
theorem integral_partialSum_sq_succ {k : ℕ} (hk : k < G.N) :
    ∫ ω, (G.partialSum W (k + 1) ω) ^ 2 ∂P
      = (∫ ω, (G.partialSum W k ω) ^ 2 ∂P)
        + (∫ ω, (G.ξ ⟨k, hk⟩ ω) ^ 2 ∂P)
          * (G.partition (⟨k, hk⟩ : Fin G.N).succ
            - G.partition (⟨k, hk⟩ : Fin G.N).castSucc) := by
  have hrw : ∀ ω, G.partialSum W (k + 1) ω
      = G.partialSum W k ω + G.ξ ⟨k, hk⟩ ω
        * (W.W (G.partition (⟨k, hk⟩ : Fin G.N).succ) ω
          - W.W (G.partition (⟨k, hk⟩ : Fin G.N).castSucc) ω) := fun ω => by
    rw [G.partialSum_succ W k ω, term, dif_pos hk]
  simp_rw [hrw]
  exact integral_add_mul_increment_sq W ℱ hℱ (G.partition_nonneg _)
    (G.partition_strictMono Fin.castSucc_lt_succ)
    (G.memLp_partialSum W hC 2 (by simp) k) (G.measurable_partialSum W k)
    ((_root_.Prove2MeSourceProof.h_abcff24ab5778ee51e37f41d G) W ℱ hℱ h_adapt hk.le)
    (G.ξ_measurable _) (h_adapt ⟨k, hk⟩) hC0 (hC ⟨k, hk⟩)
end Moments

end SimplePredictable

end LevyStochCalc.Brownian.Ito


