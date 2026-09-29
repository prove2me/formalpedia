-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionComplexEntropy
-- name    : CK_GeneralCK_ReflectionComplexEntropy
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:20:13.219481+00:00
-- url     : https://prove2.me/theorems/5720d715-20c1-47a5-b2bc-b7cafcceb59a
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionComplexEntropy` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionComplexEntropy` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionComplexEntropy` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionComplexEntropy (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionComplexEntropy.lean)

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_CK_GeneralCK_ReflectionComplexDiscElementary
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface

-- ===== source module GeneralCK.ReflectionComplexEntropy =====
section

/-!
# The complex entropy on the small-bias disc

This is the natural-logarithm entropy extension used in the small-bias
Taylor--Cauchy argument.  The logarithms are on their principal branch; on
the open unit disc both `1 + c` and `1 - c` lie in `Complex.slitPlane`.
-/

namespace GeneralCK.Reflection.ComplexEntropy

open Set











private lemma one_add_mem_slitPlane {c : ℂ} (hc : ‖c‖ < 1) :
    1 + c ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_of_norm_lt_one hc

private lemma one_sub_mem_slitPlane {c : ℂ} (hc : ‖c‖ < 1) :
    1 - c ∈ Complex.slitPlane := by
  simpa only [sub_eq_add_neg, norm_neg] using
    (Complex.mem_slitPlane_of_norm_lt_one (z := -c) (by simpa using hc))
























private lemma logTaylor_five_sub_neg (c : ℂ) :
    Complex.logTaylor 5 c - Complex.logTaylor 5 (-c) = 2 * (c + c ^ 3 / 3) := by
  simp [Complex.logTaylor, Finset.sum_range_succ]
  ring

/-- A fourth-order logarithm expansion gives an explicit derivative majorant
valid throughout the open unit disc. -/
theorem norm_entropyDeriv_le {c : ℂ} (hc : ‖c‖ < 1) :
    ‖entropyDeriv c‖ ≤
      ‖c‖ + ‖c‖ ^ 3 / 3 + ‖c‖ ^ 5 * (1 - ‖c‖)⁻¹ / 5 := by
  have hp := Complex.norm_log_sub_logTaylor_le 4 hc
  have hm := Complex.norm_log_sub_logTaylor_le 4 (z := -c) (by simpa using hc)
  norm_num at hp hm
  have hid : entropyDeriv c =
      -((Complex.log (1 + c) - Complex.logTaylor 5 c) +
        (Complex.logTaylor 5 c - Complex.logTaylor 5 (-c)) +
        (Complex.logTaylor 5 (-c) - Complex.log (1 - c))) / 2 := by
    simp only [entropyDeriv]
    ring
  rw [hid, norm_div, norm_neg, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  calc
    ‖Complex.log (1 + c) - Complex.logTaylor 5 c +
          (Complex.logTaylor 5 c - Complex.logTaylor 5 (-c)) +
          (Complex.logTaylor 5 (-c) - Complex.log (1 - c))‖ / 2
        ≤ (‖Complex.log (1 + c) - Complex.logTaylor 5 c‖ +
          ‖Complex.logTaylor 5 c - Complex.logTaylor 5 (-c)‖ +
          ‖Complex.logTaylor 5 (-c) - Complex.log (1 - c)‖) / 2 := by
            exact div_le_div_of_nonneg_right norm_add₃_le (by norm_num)
    _ =
    (‖Complex.log (1 + c) - Complex.logTaylor 5 c‖ +
        2 * ‖c + c ^ 3 / 3‖ +
        ‖Complex.logTaylor 5 (-c) - Complex.log (1 - c)‖) / 2 := by
          rw [logTaylor_five_sub_neg, norm_mul]
          norm_num
    _ ≤ (‖c‖ ^ 5 * (1 - ‖c‖)⁻¹ / 5 +
          2 * (‖c‖ + ‖c‖ ^ 3 / 3) +
          ‖c‖ ^ 5 * (1 - ‖c‖)⁻¹ / 5) / 2 := by
            gcongr
            · exact (norm_add_le c (c ^ 3 / 3)).trans (by
                rw [norm_div, norm_pow, show ‖(3 : ℂ)‖ = (3 : ℝ) by norm_num])
            · rw [norm_sub_rev]
              simpa only [sub_eq_add_neg] using hm
    _ = ‖c‖ + ‖c‖ ^ 3 / 3 + ‖c‖ ^ 5 * (1 - ‖c‖)⁻¹ / 5 := by ring

/-- The derivative is uniformly bounded by `7/5` on the closed `4/5` disc. -/
theorem norm_entropyDeriv_le_seven_fifths {c : ℂ}
    (hc : ‖c‖ ≤ (4 / 5 : ℝ)) : ‖entropyDeriv c‖ ≤ (7 / 5 : ℝ) := by
  have hc1 : ‖c‖ < 1 := hc.trans_lt (by norm_num)
  have hinv : (1 - ‖c‖)⁻¹ ≤ (5 : ℝ) := by
    rw [inv_le_comm₀ (sub_pos.mpr hc1) (by norm_num : (0 : ℝ) < 5)]
    linarith
  calc
    ‖entropyDeriv c‖ ≤ ‖c‖ + ‖c‖ ^ 3 / 3 + ‖c‖ ^ 5 * (1 - ‖c‖)⁻¹ / 5 :=
      norm_entropyDeriv_le hc1
    _ ≤ (4 / 5 : ℝ) + (4 / 5 : ℝ) ^ 3 / 3 +
        (4 / 5 : ℝ) ^ 5 * 5 / 5 := by
      gcongr
    _ ≤ (7 / 5 : ℝ) := by norm_num

/-- The complex entropy is `7/5`-Lipschitz on the closed `4/5` disc, proving
one of the two analytic premises of the elementary contraction package. -/
theorem entropyExt_lipschitzOnWith :
    LipschitzOnWith (7 / 5 : NNReal) entropyExt
      (Metric.closedBall 0 (4 / 5 : ℝ)) := by
  apply (convex_closedBall (0 : ℂ) (4 / 5 : ℝ)).lipschitzOnWith_of_nnnorm_deriv_le
  · intro c hc
    have hc' : ‖c‖ ≤ (4 / 5 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hc
    exact (hasDerivAt_entropyExt (hc'.trans_lt (by norm_num))).differentiableAt
  · intro c hc
    have hc' : ‖c‖ ≤ (4 / 5 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hc
    rw [(hasDerivAt_entropyExt (hc'.trans_lt (by norm_num))).deriv]
    exact_mod_cast norm_entropyDeriv_le_seven_fifths hc'

private noncomputable def entropyTaylor (c : ℂ) : ℂ :=
  (c ^ 2 / 2 + c ^ 4 / 12 + c ^ 6 / 30 + c ^ 8 / 56) +
    (c ^ 10 / 90 + c ^ 12 / 132 + c ^ 14 / 182)

private lemma entropyTaylor_identity (c : ℂ) :
    ((1 + c) * Complex.logTaylor 15 c +
      (1 - c) * Complex.logTaylor 15 (-c)) / 2 = entropyTaylor c := by
  simp [Complex.logTaylor, Finset.sum_range_succ, entropyTaylor]
  ring

private lemma norm_entropyTaylor_le (c : ℂ) :
    ‖entropyTaylor c‖ ≤
      (‖c‖ ^ 2 / 2 + ‖c‖ ^ 4 / 12 + ‖c‖ ^ 6 / 30 + ‖c‖ ^ 8 / 56) +
      (‖c‖ ^ 10 / 90 + ‖c‖ ^ 12 / 132 + ‖c‖ ^ 14 / 182) := by
  unfold entropyTaylor
  refine (norm_add_le _ _).trans (add_le_add norm_add₄_le norm_add₃_le) |>.trans_eq ?_
  simp only [norm_div, norm_pow]
  norm_num

private lemma norm_entropyRemainder_le {c : ℂ} (hc : ‖c‖ < 1) :
    ‖((1 + c) * (Complex.log (1 + c) - Complex.logTaylor 15 c) +
      (1 - c) * (Complex.log (1 - c) - Complex.logTaylor 15 (-c))) / 2‖ ≤
      (1 + ‖c‖) * (‖c‖ ^ 15 * (1 - ‖c‖)⁻¹ / 15) := by
  have hp := Complex.norm_log_sub_logTaylor_le 14 hc
  have hm := Complex.norm_log_sub_logTaylor_le 14 (z := -c) (by simpa using hc)
  norm_num at hp hm
  rw [norm_div, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  calc
    ‖(1 + c) * (Complex.log (1 + c) - Complex.logTaylor 15 c) +
        (1 - c) * (Complex.log (1 - c) - Complex.logTaylor 15 (-c))‖ / 2
        ≤ (‖(1 + c) * (Complex.log (1 + c) - Complex.logTaylor 15 c)‖ +
          ‖(1 - c) * (Complex.log (1 - c) - Complex.logTaylor 15 (-c))‖) / 2 := by
            gcongr
            exact norm_add_le _ _
    _ ≤ ((1 + ‖c‖) * (‖c‖ ^ 15 * (1 - ‖c‖)⁻¹ / 15) +
          (1 + ‖c‖) * (‖c‖ ^ 15 * (1 - ‖c‖)⁻¹ / 15)) / 2 := by
            gcongr
            · rw [norm_mul]
              have hone : ‖(1 + c : ℂ)‖ ≤ 1 + ‖c‖ := by
                simpa using norm_add_le (1 : ℂ) c
              exact mul_le_mul hone hp (norm_nonneg _) (by positivity)
            · rw [norm_mul]
              have hone : ‖(1 - c : ℂ)‖ ≤ 1 + ‖c‖ := by
                simpa using norm_sub_le (1 : ℂ) c
              refine mul_le_mul hone ?_ (norm_nonneg _) (by positivity)
              simpa only [sub_eq_add_neg] using hm
    _ = (1 + ‖c‖) * (‖c‖ ^ 15 * (1 - ‖c‖)⁻¹ / 15) := by ring

/-- The natural complex entropy stays below `1103/1000` on the closed
`4/5` disc, proving the second analytic premise of the elementary package. -/
theorem norm_entropyExt_le {c : ℂ} (hc : ‖c‖ ≤ (4 / 5 : ℝ)) :
    ‖entropyExt c‖ ≤ (1103 / 1000 : ℝ) := by
  have hc1 : ‖c‖ < 1 := hc.trans_lt (by norm_num)
  have hinv : (1 - ‖c‖)⁻¹ ≤ (5 : ℝ) := by
    rw [inv_le_comm₀ (sub_pos.mpr hc1) (by norm_num : (0 : ℝ) < 5)]
    linarith
  have hid :
      ((1 + c) * Complex.log (1 + c) + (1 - c) * Complex.log (1 - c)) / 2 =
        entropyTaylor c +
          ((1 + c) * (Complex.log (1 + c) - Complex.logTaylor 15 c) +
            (1 - c) * (Complex.log (1 - c) - Complex.logTaylor 15 (-c))) / 2 := by
    rw [← entropyTaylor_identity c]
    ring
  rw [entropyExt, hid]
  calc
    ‖(Real.log 2 : ℂ) -
        (entropyTaylor c +
          ((1 + c) * (Complex.log (1 + c) - Complex.logTaylor 15 c) +
            (1 - c) * (Complex.log (1 - c) - Complex.logTaylor 15 (-c))) / 2)‖
        ≤ ‖(Real.log 2 : ℂ)‖ + ‖entropyTaylor c‖ +
          ‖((1 + c) * (Complex.log (1 + c) - Complex.logTaylor 15 c) +
            (1 - c) * (Complex.log (1 - c) - Complex.logTaylor 15 (-c))) / 2‖ := by
              calc
                _ ≤ ‖(Real.log 2 : ℂ)‖ +
                    ‖entropyTaylor c +
                      ((1 + c) * (Complex.log (1 + c) - Complex.logTaylor 15 c) +
                        (1 - c) * (Complex.log (1 - c) - Complex.logTaylor 15 (-c))) / 2‖ :=
                  norm_sub_le _ _
                _ ≤ ‖(Real.log 2 : ℂ)‖ +
                    (‖entropyTaylor c‖ +
                      ‖((1 + c) * (Complex.log (1 + c) - Complex.logTaylor 15 c) +
                        (1 - c) * (Complex.log (1 - c) - Complex.logTaylor 15 (-c))) / 2‖) :=
                  add_le_add_right
                    (norm_add_le (entropyTaylor c)
                      (((1 + c) * (Complex.log (1 + c) - Complex.logTaylor 15 c) +
                        (1 - c) * (Complex.log (1 - c) - Complex.logTaylor 15 (-c))) / 2)) _
                _ = _ := by ring
    _ ≤ (7 / 10 : ℝ) +
        (((4 / 5 : ℝ) ^ 2 / 2 + (4 / 5 : ℝ) ^ 4 / 12 +
          (4 / 5 : ℝ) ^ 6 / 30 + (4 / 5 : ℝ) ^ 8 / 56) +
          ((4 / 5 : ℝ) ^ 10 / 90 + (4 / 5 : ℝ) ^ 12 / 132 +
            (4 / 5 : ℝ) ^ 14 / 182)) +
        (1 + (4 / 5 : ℝ)) * ((4 / 5 : ℝ) ^ 15 * 5 / 15) := by
      have hlog : ‖(Real.log 2 : ℂ)‖ ≤ (7 / 10 : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.log_pos (by norm_num))]
        exact (Real.log_two_lt_d9.trans (by norm_num)).le
      have hpoly : ‖entropyTaylor c‖ ≤
          (((4 / 5 : ℝ) ^ 2 / 2 + (4 / 5 : ℝ) ^ 4 / 12 +
            (4 / 5 : ℝ) ^ 6 / 30 + (4 / 5 : ℝ) ^ 8 / 56) +
            ((4 / 5 : ℝ) ^ 10 / 90 + (4 / 5 : ℝ) ^ 12 / 132 +
              (4 / 5 : ℝ) ^ 14 / 182)) := by
        calc
          ‖entropyTaylor c‖ ≤
              (‖c‖ ^ 2 / 2 + ‖c‖ ^ 4 / 12 + ‖c‖ ^ 6 / 30 + ‖c‖ ^ 8 / 56) +
              (‖c‖ ^ 10 / 90 + ‖c‖ ^ 12 / 132 + ‖c‖ ^ 14 / 182) :=
            norm_entropyTaylor_le c
          _ ≤ _ := by gcongr
      have hrem :
          ‖((1 + c) * (Complex.log (1 + c) - Complex.logTaylor 15 c) +
            (1 - c) * (Complex.log (1 - c) - Complex.logTaylor 15 (-c))) / 2‖ ≤
            (1 + (4 / 5 : ℝ)) * ((4 / 5 : ℝ) ^ 15 * 5 / 15) := by
        calc
          _ ≤ (1 + ‖c‖) * (‖c‖ ^ 15 * (1 - ‖c‖)⁻¹ / 15) :=
            norm_entropyRemainder_le hc1
          _ ≤ _ := by gcongr
      gcongr
    _ ≤ (1103 / 1000 : ℝ) := by norm_num

/-- The entropy extension maps the contact disc into the norm ball required
by the elementary self-map theorem. -/
theorem entropyExt_uniformBound :
    ∀ c ∈ Metric.closedBall (0 : ℂ) (4 / 5 : ℝ),
      ‖entropyExt c‖ ≤ (1103 / 1000 : ℝ) := by
  intro c hc
  apply norm_entropyExt_le
  simpa only [Metric.mem_closedBall, dist_zero_right] using hc

/-- The verified entropy estimate supplies the Lipschitz half of the
elementary contact-map contraction package. -/
theorem entropyContactMap_lipschitzOnWith {tau : ℂ}
    (htau : ‖tau‖ ≤ (7 / 10 : ℝ)) :
    LipschitzOnWith (49 / 50 : NNReal)
      (ComplexDiscElementary.contactMap entropyExt tau)
      (Metric.closedBall 0 (4 / 5 : ℝ)) :=
  ComplexDiscElementary.contactMap_lipschitzOnWith htau entropyExt_lipschitzOnWith

/-- The contact map in fact lands strictly inside the `4/5` disc. -/
theorem entropyContactMap_mapsTo_ball {tau : ℂ}
    (htau : ‖tau‖ ≤ (7 / 10 : ℝ)) :
    MapsTo (ComplexDiscElementary.contactMap entropyExt tau)
      (Metric.closedBall 0 (4 / 5 : ℝ)) (Metric.ball 0 (4 / 5 : ℝ)) :=
  ComplexDiscElementary.contactMap_mapsTo_ball htau entropyExt_uniformBound

/-- Both analytic entropy estimates instantiate the complete elementary
self-map and contraction package. -/
theorem entropyContactMap_contractionPackage {tau : ℂ}
    (htau : ‖tau‖ ≤ (7 / 10 : ℝ)) :
    MapsTo (ComplexDiscElementary.contactMap entropyExt tau)
        (Metric.closedBall 0 (4 / 5 : ℝ)) (Metric.closedBall 0 (4 / 5 : ℝ)) ∧
      LipschitzOnWith (49 / 50 : NNReal)
        (ComplexDiscElementary.contactMap entropyExt tau)
        (Metric.closedBall 0 (4 / 5 : ℝ)) :=
  ComplexDiscElementary.contactMap_contractionPackage
    htau entropyExt_uniformBound entropyExt_lipschitzOnWith

end GeneralCK.Reflection.ComplexEntropy

end


