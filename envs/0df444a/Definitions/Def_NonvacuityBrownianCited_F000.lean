-- Prove2me | Definitions.Def_NonvacuityBrownianCited_F000
-- name    : NonvacuityBrownianCited_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:43:31.948479+00:00
-- url     : https://prove2.me/theorems/b52a8c88-2bd0-4377-8bac-434a29c4947d
-- title:
--   Source declarations: NonvacuityBrownianCited
-- statement:
--   Source-preserving extracted declarations from NonvacuityBrownianCited. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F003
import Definitions.Def_NonvacuityContract_F000
import Definitions.Def_SourceProof_4090f5760db323e17cd5fcca

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Continuous modification and right-continuous martingale property of a Brownian motion

A Brownian motion satisfies the Kolmogorov moment condition with exponents `(4, 2)` and the
constant `𝔼[Z⁴]` of the standard Gaussian, so it carries a continuous modification; it is a
martingale for the right-continuation of its natural filtration, and that filtration and the
modification are distinct from the trivial σ-algebra and from the zero process.

## Main statements

* `lintegral_nnnorm_pow_four_increment` — `𝔼‖W_b − W_a‖⁴ = (b − a)² · 𝔼[Z⁴]`, and
  `lintegral_nnnorm_pow_four_brownian_sub` for arbitrary nonnegative times.
* `isKolmogorovProcess_brownian` — the Kolmogorov condition for `W` with exponents `(4, 2)`
  and constant `𝔼[Z⁴]`, which is positive (`gaussianFourthMoment_pos`,
  `gaussianFourthMoment_toNNReal_pos`).
* `exists_continuous_modification_brownian` — a continuous modification of `W`, with second
  moment `1` at time `1` (`exists_continuous_modification_brownian_moment`).
* `prob_brownian_unit_pos` — `P(W₁ > 0) = 1 / 2`, whence
  `naturalFiltration_brownian_unit_ne_bot` and
  `rightCont_naturalFiltration_brownian_unit_ne_bot`.
* `martingale_brownian_rightCont_cited` — `W` is a martingale for the right-continuation of
  its natural filtration.
* `exists_brownianMotion_cited` — the same statements on a probability space delivered by the
  existence theorem.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §2.2, §2.7.
* Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, 2016, §2.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

universe u

section KolmogorovCondition

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The fourth moment of a Brownian increment over `(a, b]` is `(b − a)²` times the fourth
moment of the standard Gaussian. -/
theorem lintegral_nnnorm_pow_four_increment (W : Brownian.BrownianMotion P)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫⁻ ω, (‖W.W b ω - W.W a ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      = ENNReal.ofReal ((b - a) ^ 2 * Brownian.Ito.gaussianFourthMoment) := by
  have hnorm : ∀ x : ℝ, ‖x‖ ^ 4 = x ^ 4 := fun x => by
    rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity)]
  have hmem : MemLp (fun ω => W.W b ω - W.W a ω) ((4 : ℕ) : ℝ≥0∞) P := by
    simpa using Brownian.Ito.memLp_increment W ha hab 4 (by simp)
  have hint : Integrable (fun ω => (W.W b ω - W.W a ω) ^ 4) P := by
    refine (hmem.integrable_norm_pow (by norm_num)).congr
      (Filter.Eventually.of_forall fun ω => hnorm _)
  rw [← Brownian.Ito.integral_increment_pow_four W ha hab,
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => by positivity)]
  refine lintegral_congr fun ω => ?_
  rw [show ((‖W.W b ω - W.W a ω‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖W.W b ω - W.W a ω‖ from
      (ofReal_norm _).symm, ← ENNReal.ofReal_pow (norm_nonneg _), hnorm]
/-- A Brownian motion agrees almost surely with its value at the time clipped to `[0, ∞)`. -/
theorem brownian_ae_eq_clip (W : Brownian.BrownianMotion P) (t : ℝ) :
    ∀ᵐ ω ∂P, W.W t ω = W.W (max t 0) ω := by
  rcases le_or_gt 0 t with ht | ht
  · rw [max_eq_left ht]
    exact Filter.Eventually.of_forall fun _ => rfl
  · rw [max_eq_right ht.le]
    filter_upwards [W.negative_zero t ht, W.initial_zero] with ω h1 h2
    rw [h1, h2]
/-- The fourth moment of the difference of the values of a Brownian motion at two nonnegative
times is the square of their distance times the fourth moment of the standard Gaussian. -/
theorem lintegral_nnnorm_pow_four_brownian_sub (W : Brownian.BrownianMotion P)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫⁻ ω, (‖W.W a ω - W.W b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      = ENNReal.ofReal ((a - b) ^ 2 * Brownian.Ito.gaussianFourthMoment) := by
  rcases lt_trichotomy a b with h | h | h
  · have hswap : ∀ ω : Ω, (‖W.W a ω - W.W b ω‖₊ : ℝ≥0∞)
        = (‖W.W b ω - W.W a ω‖₊ : ℝ≥0∞) := fun ω => by rw [← nnnorm_neg, neg_sub]
    simp_rw [hswap]
    rw [lintegral_nnnorm_pow_four_increment W ha h]
    congr 1
    ring
  · subst h
    simp
  · rw [lintegral_nnnorm_pow_four_increment W hb h]
/-- A Brownian motion satisfies the Kolmogorov moment condition with exponents `(4, 2)` and
constant the fourth moment of the standard Gaussian. -/
theorem isKolmogorovProcess_brownian (W : Brownian.BrownianMotion P) :
    ProbabilityTheory.IsKolmogorovProcess (fun t ω => W.W t ω) P 4 2
      Brownian.Ito.gaussianFourthMoment.toNNReal := by
  have hc0 : (0 : ℝ) ≤ Brownian.Ito.gaussianFourthMoment :=
    Brownian.Ito.gaussianFourthMoment_nonneg
  refine ProbabilityTheory.IsKolmogorovProcess.mk_of_secondCountableTopology
    (fun t => W.measurable_eval t) (fun s t => ?_) (by norm_num) (by norm_num)
  have hae : (fun ω => edist (W.W s ω) (W.W t ω) ^ (4 : ℝ))
      =ᵐ[P] fun ω => (‖W.W (max s 0) ω - W.W (max t 0) ω‖₊ : ℝ≥0∞) ^ (4 : ℕ) := by
    filter_upwards [brownian_ae_eq_clip W s, brownian_ae_eq_clip W t] with ω h1 h2
    rw [h1, h2, show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast,
      Brownian.Ito.edist_eq_coe_nnnorm_sub]
  have hedist : edist s t ^ (2 : ℝ) = ENNReal.ofReal (|s - t| ^ 2) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, edist_dist,
      Real.dist_eq, ← ENNReal.ofReal_pow (abs_nonneg _)]
  rw [lintegral_congr_ae hae,
    lintegral_nnnorm_pow_four_brownian_sub W (le_max_right s 0) (le_max_right t 0), hedist,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
    Real.coe_toNNReal _ hc0]
  refine ENNReal.ofReal_le_ofReal ?_
  have hdiff : |max s 0 - max t 0| ≤ |s - t| := abs_max_sub_max_le_abs s t 0
  have h1 : (max s 0 - max t 0) ^ 2 ≤ (s - t) ^ 2 := by
    rw [← sq_abs (max s 0 - max t 0), ← sq_abs (s - t)]
    exact pow_le_pow_left₀ (abs_nonneg _) hdiff 2
  nlinarith [sq_abs (s - t), hc0, h1]
/-- The fourth moment of the standard Gaussian is positive. -/
theorem gaussianFourthMoment_pos : 0 < Brownian.Ito.gaussianFourthMoment := by
  rcases Brownian.Ito.gaussianFourthMoment_nonneg.lt_or_eq with h | h
  · exact h
  obtain ⟨Ω, _, P, _, ⟨W⟩⟩ := _root_.Prove2MeSourceProof.h_c83c751666c401b491a738db.{0}
  exfalso
  have h0 : ∫⁻ ω, (‖W.W 1 ω - W.W 0 ω‖₊ : ℝ≥0∞) ^ 4 ∂P = 0 := by
    rw [lintegral_nnnorm_pow_four_increment W le_rfl zero_lt_one, ← h]
    simp
  have hmeas : AEMeasurable (fun ω => (‖W.W 1 ω - W.W 0 ω‖₊ : ℝ≥0∞) ^ 4) P :=
    ((((W.measurable_eval 1).sub (W.measurable_eval 0)).nnnorm.coe_nnreal_ennreal).pow_const
      4).aemeasurable
  rw [lintegral_eq_zero_iff' hmeas] at h0
  refine brownian_not_ae_zero W zero_lt_one ?_
  filter_upwards [h0, W.initial_zero] with ω hω h1
  have hz : W.W 1 ω - W.W 0 ω = 0 := by simpa using hω
  rw [h1, sub_zero] at hz
  exact hz
/-- The constant of the Kolmogorov condition of a Brownian motion is positive. -/
theorem gaussianFourthMoment_toNNReal_pos :
    0 < Brownian.Ito.gaussianFourthMoment.toNNReal :=
  Real.toNNReal_pos.mpr gaussianFourthMoment_pos
end KolmogorovCondition

section ContinuousModification

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A Brownian motion admits a modification with continuous paths. -/
theorem exists_continuous_modification_brownian (W : Brownian.BrownianMotion P) :
    ∃ Y : ℝ → Ω → ℝ, (∀ᵐ ω ∂P, Continuous fun t => Y t ω) ∧
      ∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = W.W t ω :=
  _root_.Prove2MeSourceProof.h_00d6535be52148842f88e973 P (fun t ω => W.W t ω)
    (isKolmogorovProcess_brownian W) (by norm_num)
/-- A Brownian motion admits a modification with continuous paths whose value at time `1` has
second moment `1` and is not almost surely `0`. -/
theorem exists_continuous_modification_brownian_moment (W : Brownian.BrownianMotion P) :
    ∃ Y : ℝ → Ω → ℝ, (∀ᵐ ω ∂P, Continuous fun t => Y t ω) ∧
      (∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = W.W t ω) ∧
      ∫⁻ ω, (‖Y 1 ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 ∧
      ¬ (fun ω => Y 1 ω) =ᵐ[P] fun _ => (0 : ℝ) := by
  obtain ⟨Y, hcont, hmod⟩ := exists_continuous_modification_brownian W
  have hae : (fun ω => (‖Y 1 ω‖₊ : ℝ≥0∞) ^ 2)
      =ᵐ[P] fun ω => (‖W.W 1 ω‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [hmod 1] with ω hω
    rw [hω]
  refine ⟨Y, hcont, hmod, ?_, ?_⟩
  · rw [lintegral_congr_ae hae, _root_.Prove2MeSourceProof.h_bfc6836a0f0c399780ee75a6 W zero_lt_one]
    simp
  · intro h
    refine brownian_not_ae_zero W zero_lt_one ?_
    filter_upwards [h, hmod 1] with ω h1 h2
    rw [← h2]
    exact h1
end ContinuousModification

section RightContinuousMartingale

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A σ-algebra carrying an event of probability `1 / 2` is not trivial. -/
theorem measurableSpace_ne_bot_of_prob_half {m : MeasurableSpace Ω} {S : Set Ω}
    (hS : MeasurableSet[m] S) (hP : P S = 1 / 2) : m ≠ ⊥ := by
  intro h
  rw [h] at hS
  rcases MeasurableSpace.measurableSet_bot_iff.mp hS with h0 | h1
  · rw [h0, measure_empty, one_div] at hP
    exact (ENNReal.inv_ne_zero.mpr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)) hP.symm
  · rw [h1, measure_univ, one_div, eq_comm, ENNReal.inv_eq_one] at hP
    norm_num at hP
/-- The probability that a Brownian motion is positive at time `1` is `1 / 2`. -/
theorem prob_brownian_unit_pos (W : Brownian.BrownianMotion P) :
    P {ω | 0 < W.W 1 ω} = 1 / 2 := by
  rw [← prob_increment_unit_pos W]
  refine measure_congr ?_
  filter_upwards [W.initial_zero] with ω hω
  show (0 < W.W 1 ω) = (0 < W.W 1 ω - W.W 0 ω)
  rw [hω, sub_zero]
/-- The event that a Brownian motion is positive at time `1` belongs to the σ-algebra generated
by its value at time `1`. -/
theorem measurableSet_brownian_unit_pos (W : Brownian.BrownianMotion P) :
    MeasurableSet[MeasurableSpace.comap (W.W 1) inferInstance] {ω | 0 < W.W 1 ω} :=
  ⟨Set.Ioi 0, measurableSet_Ioi, rfl⟩
/-- The σ-algebra generated by a Brownian motion at a time `t ≤ s` is contained in its natural
filtration at time `s`. -/
theorem comap_brownian_le_naturalFiltration (W : Brownian.BrownianMotion P) {s t : ℝ}
    (hts : t ≤ s) :
    MeasurableSpace.comap (W.W t) inferInstance
      ≤ Brownian.Martingale.naturalFiltration W s :=
  le_iSup₂ (f := fun j (_ : j ≤ s) =>
    MeasurableSpace.comap (W.W j) (inferInstance : MeasurableSpace ℝ)) t hts
/-- The natural filtration of a Brownian motion at time `1` is not trivial. -/
theorem naturalFiltration_brownian_unit_ne_bot (W : Brownian.BrownianMotion P) :
    Brownian.Martingale.naturalFiltration W 1 ≠ ⊥ :=
  measurableSpace_ne_bot_of_prob_half
    (comap_brownian_le_naturalFiltration W (le_refl (1 : ℝ)) _
      (measurableSet_brownian_unit_pos W))
    (prob_brownian_unit_pos W)
/-- The right-continuation of the natural filtration of a Brownian motion is not trivial at
time `1`. -/
theorem rightCont_naturalFiltration_brownian_unit_ne_bot (W : Brownian.BrownianMotion P) :
    (Brownian.Martingale.naturalFiltration W).rightCont 1 ≠ ⊥ :=
  measurableSpace_ne_bot_of_prob_half
    (Filtration.le_rightCont _ 1 _
      (comap_brownian_le_naturalFiltration W (le_refl (1 : ℝ)) _
        (measurableSet_brownian_unit_pos W)))
    (prob_brownian_unit_pos W)
/-- A Brownian motion is a martingale for the right-continuation of its natural filtration. -/
theorem martingale_brownian_rightCont_cited (W : Brownian.BrownianMotion P) :
    Martingale (fun t : ℝ => W.W t)
      (Brownian.Martingale.naturalFiltration W).rightCont P :=
  _root_.Prove2MeSourceProof.h_4090f5760db323e17cd5fcca W
end RightContinuousMartingale

section Capstone

/-- Some probability space carries a Brownian motion with a continuous modification whose value
at time `1` is not almost surely `0`, which is a martingale for the right-continuation of its
natural filtration, that filtration being nontrivial at time `1`, and whose value at time `1`
has second moment `1` while its value at time `0` vanishes almost surely. -/
theorem exists_brownianMotion_cited :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : Brownian.BrownianMotion P),
      (∃ Y : ℝ → Ω → ℝ, (∀ᵐ ω ∂P, Continuous fun t => Y t ω) ∧
          (∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = W.W t ω) ∧
          ¬ (fun ω => Y 1 ω) =ᵐ[P] fun _ => (0 : ℝ)) ∧
        Martingale (fun t : ℝ => W.W t)
          (Brownian.Martingale.naturalFiltration W).rightCont P ∧
        (Brownian.Martingale.naturalFiltration W).rightCont 1 ≠ ⊥ ∧
        (fun ω => W.W 0 ω) =ᵐ[P] (fun _ => (0 : ℝ)) ∧
        ∫⁻ ω, (‖W.W 1 ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 := by
  obtain ⟨Ω, _, P, _, ⟨W⟩⟩ := _root_.Prove2MeSourceProof.h_c83c751666c401b491a738db.{0}
  obtain ⟨Y, hcont, hmod, -, hY0⟩ := exists_continuous_modification_brownian_moment W
  refine ⟨Ω, inferInstance, P, inferInstance, W, ⟨Y, hcont, hmod, hY0⟩,
    martingale_brownian_rightCont_cited W,
    rightCont_naturalFiltration_brownian_unit_ne_bot W, W.initial_zero, ?_⟩
  rw [_root_.Prove2MeSourceProof.h_bfc6836a0f0c399780ee75a6 W zero_lt_one]
  simp
end Capstone

end LevyStochCalc.Examples.Nonvacuity


