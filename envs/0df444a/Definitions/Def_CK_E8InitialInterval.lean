-- Prove2me | Definitions.Def_CK_E8InitialInterval
-- name    : CK_E8InitialInterval
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:24:03.92506+00:00
-- url     : https://prove2.me/theorems/06850d3f-9415-40d2-9360-6df05f051999
-- title:
--   Courtade–Kumar proof module `E8InitialInterval` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `E8InitialInterval` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `E8InitialInterval` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module E8InitialInterval (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/E8InitialInterval.lean)

import Definitions.Def_CK_E8QuadraticThreshold

-- ===== source module E8InitialInterval =====
section

namespace GeneralCK.E8RatioMonotonicity

open Set
open Certificates.E8TAxisStableScalar
open Certificates.E8HistoricalLogConvexityBridge

theorem stable_r_le_parameter {a : ℝ} (ha : 0 ≤ a) : r a ≤ a := by
  rcases ha.eq_or_lt with rfl | ha
  · norm_num [r, z]
  · have h := SmallMean.A_lower (r_pos ha).le (r_lt_one a)
    rwa [A_r] at h

theorem stable_ell_upper {a : ℝ} (ha : 0 ≤ a) :
    ell a ≤ Real.log 2 + a ^ 2 / 2 := by
  let f : ℝ → ℝ := fun x => x ^ 2 / 2 - ell x
  have hd (x : ℝ) : HasDerivAt f (x - r x) x := by
    have h := (((hasDerivAt_id x).pow 2).div_const 2).sub (hasDerivAt_ell x)
    convert! h using 1 <;> simp [f] <;> ring
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd x).hasDerivWithinAt
    · intro x hx
      exact sub_nonneg.mpr (stable_r_le_parameter (interior_subset hx))
  have hh := hm (show (0 : ℝ) ∈ Ici 0 by simp) ha ha
  dsimp [f] at hh
  norm_num [ell, l1, z] at hh
  simpa only [ell, l1, z, neg_mul, add_comm] using hh

private theorem compactFactor_third_lower {k t : ℝ}
    (hk : 1 / 2 ≤ k) (hk1 : k ≤ 3 / 4)
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / 16) (hgap : 1 ≤ 2 * k - t) :
    3 ≤ compactFactor k t (1 / 3) := by
  let w := t / (2 * k - t)
  let s := 1 / k
  have hk0 : 0 < k := by linarith
  have hw : 0 ≤ w := div_nonneg ht (by linarith)
  have hw1 : w ≤ 1 / 16 := by
    apply (div_le_iff₀ (by linarith : 0 < 2 * k - t)).2
    nlinarith
  have hs : 4 / 3 ≤ s := by
    apply (le_div_iff₀ hk0).2
    linarith
  have hs1 : s ≤ 2 := by
    apply (div_le_iff₀ hk0).2
    linarith
  have hcross : (4 + 10 * w) * s ≤ 37 / 4 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 - s) (by linarith : 0 ≤ 4 + 10 * w)]
  let b := 4 / 3 + 4 / 3 * w + 8 * w ^ 2 - (4 + 10 * w) * s + 3 * s ^ 2
  have hb : -(37 / 4 : ℝ) ≤ b := by dsimp [b]; nlinarith [sq_nonneg w, sq_nonneg s]
  have htb := mul_le_mul_of_nonneg_left hb ht
  have hqw : (1 - t) * w ≤ 1 / 16 := by nlinarith [mul_nonneg ht hw]
  have hid : compactFactor k t (1 / 3) = 6 * s - 4 - 6 * (1 - t) * w + t * b := by
    dsimp [compactFactor, s, w, b]
    ring
  rw [hid]
  nlinarith

/-- A proved initial interval: no numerical witness or finite ledger is used. -/
theorem stableL_ge_three_initial {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 4) :
    (3 : ℝ) ≤ stableL a := by
  have hr := r_pos ha
  have hra := stable_r_le_parameter ha.le
  have ht : r a ^ 2 ≤ 1 / 16 := by nlinarith
  have hk := ell_ge_half_one_add_sq ha
  have hk0 : 1 / 2 ≤ ell a := by nlinarith [sq_nonneg (r a)]
  have hk1 : ell a ≤ 3 / 4 := by
    have hu := stable_ell_upper ha.le
    have hlog := Certificates.PilotData.log_two.2
    norm_num only [div_one] at hlog
    nlinarith
  have hbase := compactFactor_third_lower hk0 hk1 (sq_nonneg _) ht (by linarith [hk])
  rw [stableL_eq_compactFactor ha]
  exact hbase.trans (actual_compactFactor_mono ha (by simp)
    (entropyQuotient_ge_third ha) (entropyQuotient_ge_third ha))

theorem stable_numerator_nonneg_initial {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 4) :
    0 ≤ e8LogDerivativeJetNumerator (Y a) :=
  (stable_numerator_nonneg_iff_L_nonneg ha).mpr (by linarith [stableL_ge_three_initial ha ha1])

#print axioms stable_r_le_parameter
#print axioms stable_ell_upper
#print axioms stableL_ge_three_initial
#print axioms stable_numerator_nonneg_initial

end GeneralCK.E8RatioMonotonicity

end


