-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionComplexCubicBound
-- name    : CK_GeneralCK_ReflectionComplexCubicBound
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T12:27:38.632613+00:00
-- url     : https://prove2.me/theorems/ee70898d-c55e-4031-aec8-a83491b9a472
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionComplexCubicBound` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionComplexCubicBound` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionComplexCubicBound` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionComplexCubicBound (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionComplexCubicBound.lean)

import Definitions.Def_CK_GeneralCK_ReflectionComplexContactFactor

-- ===== source module GeneralCK.ReflectionComplexCubicBound =====
section

/-!
# Quantitative cubic bound for the complex contact germ

This file turns the qualitative cubic factorization into an explicit norm
estimate.  The main input is a quadratic entropy-loss estimate on the closed
`4/5` contact disc.
-/

namespace GeneralCK.Reflection.ComplexCubicBound

open Set Filter Function
open scoped Topology
open ComplexEntropy ComplexFixedPoint ComplexContactGerm ComplexContactFactor

private lemma entropyTaylor_three (c : ℂ) :
    ((1 + c) * Complex.logTaylor 3 c +
      (1 - c) * Complex.logTaylor 3 (-c)) / 2 = c ^ 2 / 2 := by
  simp [Complex.logTaylor, Finset.sum_range_succ]
  ring

/-- Quadratic entropy loss on the verified contact disc. -/
theorem norm_entropyExt_sub_logTwo_le {c : ℂ}
    (hc : ‖c‖ ≤ (4 / 5 : ℝ)) :
    ‖entropyExt c - (Real.log 2 : ℂ)‖ ≤ 3 * ‖c‖ ^ 2 := by
  have hc1 : ‖c‖ < 1 := hc.trans_lt (by norm_num)
  have hp := Complex.norm_log_sub_logTaylor_le 2 hc1
  have hm := Complex.norm_log_sub_logTaylor_le 2 (z := -c) (by simpa using hc1)
  norm_num at hp hm
  have hinv : (1 - ‖c‖)⁻¹ ≤ (5 : ℝ) := by
    rw [inv_le_comm₀ (sub_pos.mpr hc1) (by norm_num : (0 : ℝ) < 5)]
    linarith
  have hid : entropyExt c - (Real.log 2 : ℂ) =
      -(c ^ 2 / 2 +
        ((1 + c) * (Complex.log (1 + c) - Complex.logTaylor 3 c) +
          (1 - c) * (Complex.log (1 - c) - Complex.logTaylor 3 (-c))) / 2) := by
    unfold entropyExt
    rw [← entropyTaylor_three c]
    ring
  rw [hid, norm_neg]
  calc
    ‖c ^ 2 / 2 +
        ((1 + c) * (Complex.log (1 + c) - Complex.logTaylor 3 c) +
          (1 - c) * (Complex.log (1 - c) - Complex.logTaylor 3 (-c))) / 2‖
        ≤ ‖c‖ ^ 2 / 2 +
          ((1 + ‖c‖) * (‖c‖ ^ 3 * (1 - ‖c‖)⁻¹ / 3) +
            (1 + ‖c‖) * (‖c‖ ^ 3 * (1 - ‖c‖)⁻¹ / 3)) / 2 := by
      calc
        _ ≤ ‖c ^ 2 / 2‖ +
            ‖((1 + c) * (Complex.log (1 + c) - Complex.logTaylor 3 c) +
              (1 - c) * (Complex.log (1 - c) - Complex.logTaylor 3 (-c))) / 2‖ :=
          norm_add_le _ _
        _ ≤ _ := by
          have hplus :
              ‖(1 + c) * (Complex.log (1 + c) - Complex.logTaylor 3 c)‖ ≤
                (1 + ‖c‖) * (‖c‖ ^ 3 * (1 - ‖c‖)⁻¹ / 3) :=
            (norm_mul_le _ _).trans <| mul_le_mul
              (by simpa using norm_add_le (1 : ℂ) c) hp
              (norm_nonneg _) (by positivity)
          have hminus :
              ‖(1 - c) * (Complex.log (1 - c) - Complex.logTaylor 3 (-c))‖ ≤
                (1 + ‖c‖) * (‖c‖ ^ 3 * (1 - ‖c‖)⁻¹ / 3) :=
            (norm_mul_le _ _).trans <| mul_le_mul
              (by simpa using norm_sub_le (1 : ℂ) c)
              (by simpa only [sub_eq_add_neg, norm_neg] using hm)
              (norm_nonneg _) (by positivity)
          rw [norm_div, norm_pow, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num,
            norm_div, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
          gcongr
          exact (norm_add_le _ _).trans (add_le_add hplus hminus)
    _ ≤ ‖c‖ ^ 2 / 2 +
        ((1 + (4 / 5 : ℝ)) * (‖c‖ ^ 3 * 5 / 3) +
          (1 + (4 / 5 : ℝ)) * (‖c‖ ^ 3 * 5 / 3)) / 2 := by
      gcongr
    _ ≤ 3 * ‖c‖ ^ 2 := by
      have hn := norm_nonneg c
      have hc3 : ‖c‖ ^ 3 ≤ (4 / 5 : ℝ) * ‖c‖ ^ 2 := by
        calc
          ‖c‖ ^ 3 = ‖c‖ * ‖c‖ ^ 2 := by ring
          _ ≤ (4 / 5 : ℝ) * ‖c‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      nlinarith

/-- Any contact-disc solution obeys a cubic deviation estimate from its
linear approximation. -/
theorem norm_contact_sub_linear_le {tau c : ℂ}
    (hc : c ∈ Metric.closedBall 0 (4 / 5 : ℝ))
    (hfix : c = tau * entropyExt c) :
    ‖c - (Real.log 2 : ℂ) * tau‖ ≤ 3 * ‖tau‖ * ‖c‖ ^ 2 := by
  have hcNorm : ‖c‖ ≤ (4 / 5 : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hc
  rw [show c - (Real.log 2 : ℂ) * tau =
      tau * entropyExt c - (Real.log 2 : ℂ) * tau from
        congrArg (fun z => z - (Real.log 2 : ℂ) * tau) hfix]
  have hid : tau * entropyExt c - (Real.log 2 : ℂ) * tau =
      tau * (entropyExt c - (Real.log 2 : ℂ)) := by ring
  rw [hid, norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_entropyExt_sub_logTwo_le hcNorm)
    (norm_nonneg tau)).trans_eq (by ring)

/-- Combining the entropy bound with the uniform entropy norm estimate gives
an entirely parameter-based cubic bound. -/
theorem norm_contact_sub_linear_le_tau {tau c : ℂ}
    (hc : c ∈ Metric.closedBall 0 (4 / 5 : ℝ))
    (hfix : c = tau * entropyExt c) :
    ‖c - (Real.log 2 : ℂ) * tau‖ ≤ (15 / 4 : ℝ) * ‖tau‖ ^ 3 := by
  have hcTau : ‖c‖ ≤ (1103 / 1000 : ℝ) * ‖tau‖ := by
    rw [hfix, norm_mul]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (entropyExt_uniformBound c hc) (norm_nonneg tau)
  calc
    ‖c - (Real.log 2 : ℂ) * tau‖ ≤ 3 * ‖tau‖ * ‖c‖ ^ 2 :=
      norm_contact_sub_linear_le hc hfix
    _ ≤ 3 * ‖tau‖ * ((1103 / 1000 : ℝ) * ‖tau‖) ^ 2 := by
      gcongr
    _ ≤ (15 / 4 : ℝ) * ‖tau‖ ^ 3 := by
      have hn := norm_nonneg tau
      nlinarith [sq_nonneg ‖tau‖]

/-- Quantitative cubic approximation for the chosen Banach fixed point on
the full verified parameter disc. -/
theorem norm_fixedPoint_sub_linear_le {tau : ℂ}
    (htau : ‖tau‖ ≤ (7 / 10 : ℝ)) :
    ‖fixedPoint tau htau - (Real.log 2 : ℂ) * tau‖ ≤
      (15 / 4 : ℝ) * ‖tau‖ ^ 3 := by
  have hmem := Metric.ball_subset_closedBall (fixedPoint_mem_ball htau)
  have hfix := fixedPoint_isFixedPt htau
  change IsFixedPt (ComplexDiscElementary.contactMap entropyExt tau)
    (fixedPoint tau htau) at hfix
  unfold IsFixedPt ComplexDiscElementary.contactMap at hfix
  exact norm_contact_sub_linear_le_tau hmem hfix.symm

/-- A chosen analytic cubic remainder from the parity factorization. -/
noncomputable def cubicRemainder : ℂ → ℂ :=
  Classical.choose exists_contactGerm_cubicRemainder

theorem analyticAt_cubicRemainder : AnalyticAt ℂ cubicRemainder 0 :=
  (Classical.choose_spec exists_contactGerm_cubicRemainder).1

theorem eventually_contactGerm_cubicRemainder :
    contactGerm =ᶠ[𝓝 0]
      fun tau => (Real.log 2 : ℂ) * tau + tau ^ 3 * cubicRemainder tau :=
  (Classical.choose_spec exists_contactGerm_cubicRemainder).2

/-- The analytic cubic remainder has the uniform punctured-neighborhood bound
`15/4`. -/
theorem eventually_norm_cubicRemainder_le :
    ∀ᶠ tau in 𝓝 (0 : ℂ), tau ≠ 0 → ‖cubicRemainder tau‖ ≤ (15 / 4 : ℝ) := by
  filter_upwards [eventually_contactGerm_cubicRemainder,
      eventually_contactGerm_fixed, eventually_contactGerm_mem_ball]
    with tau hrem hfix hball
  intro htau
  have hbound := norm_contact_sub_linear_le_tau
    (Metric.ball_subset_closedBall hball) hfix
  have hid : contactGerm tau - (Real.log 2 : ℂ) * tau =
      tau ^ 3 * cubicRemainder tau := by rw [hrem]; ring
  rw [hid, norm_mul, norm_pow] at hbound
  have hpos : 0 < ‖tau‖ ^ 3 := pow_pos (norm_pos_iff.mpr htau) _
  nlinarith

theorem norm_cubicRemainder_zero_le :
    ‖cubicRemainder 0‖ ≤ (15 / 4 : ℝ) := by
  have hbound : ∀ᶠ tau in 𝓝[≠] (0 : ℂ),
      ‖cubicRemainder tau‖ ≤ (15 / 4 : ℝ) := by
    have hlocal : ∀ᶠ tau in 𝓝[≠] (0 : ℂ),
        tau ≠ 0 → ‖cubicRemainder tau‖ ≤ (15 / 4 : ℝ) :=
      Filter.Eventually.filter_mono inf_le_left eventually_norm_cubicRemainder_le
    filter_upwards [hlocal, self_mem_nhdsWithin] with tau hbound htau
    exact hbound (by simpa using htau)
  have htend : Tendsto (fun tau : ℂ => ‖cubicRemainder tau‖)
      (𝓝[≠] 0) (𝓝 ‖cubicRemainder 0‖) :=
    analyticAt_cubicRemainder.continuousAt.norm.tendsto.mono_left inf_le_left
  exact le_of_tendsto htend hbound

theorem eventually_norm_cubicRemainder_le_all :
    ∀ᶠ tau in 𝓝 (0 : ℂ), ‖cubicRemainder tau‖ ≤ (15 / 4 : ℝ) := by
  filter_upwards [eventually_norm_cubicRemainder_le] with tau hbound
  by_cases htau : tau = 0
  · simpa only [htau] using norm_cubicRemainder_zero_le
  · exact hbound htau

/-- There is a genuine positive analytic radius on which the cubic remainder
is analytic at every point and obeys the explicit `15/4` norm bound. -/
theorem exists_cubicRemainder_radius :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ tau : ℂ, ‖tau‖ < rho →
        AnalyticAt ℂ cubicRemainder tau ∧
          ‖cubicRemainder tau‖ ≤ (15 / 4 : ℝ) := by
  have hlocal : ∀ᶠ tau in 𝓝 (0 : ℂ),
      AnalyticAt ℂ cubicRemainder tau ∧
        ‖cubicRemainder tau‖ ≤ (15 / 4 : ℝ) :=
    analyticAt_cubicRemainder.eventually_analyticAt.and
      eventually_norm_cubicRemainder_le_all
  obtain ⟨rho, hrho, hball⟩ := Metric.eventually_nhds_iff_ball.mp hlocal
  refine ⟨rho, hrho, ?_⟩
  intro tau htau
  exact hball tau (by simpa only [Metric.mem_ball, dist_zero_right] using htau)

end GeneralCK.Reflection.ComplexCubicBound

end


