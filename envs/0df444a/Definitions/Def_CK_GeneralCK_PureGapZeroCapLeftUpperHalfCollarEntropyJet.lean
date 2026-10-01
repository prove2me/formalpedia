-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarEntropyJet
-- name    : CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarEntropyJet
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:35:32.761012+00:00
-- url     : https://prove2.me/theorems/0df7413b-56b9-4301-957e-daaeba00a0f1
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarEntropyJet` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarEntropyJet` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarEntropyJet` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftUpperHalfCollarEntropyJet (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftUpperHalfCollarEntropyJet.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarLogJets

-- ===== source module GeneralCK.PureGapZeroCapLeftUpperHalfCollarEntropyJet =====
section

/-! Actual entropy quartic remainder obtained by integrating the accepted
slope error through a derivative comparison; no logarithm series premise. -/

namespace GeneralCK

private theorem sixth_barrier {f f' : ℝ → ℝ} {q : ℝ} (hq : 0 ≤ q)
    (hzero : f 0 = 0)
    (hd : ∀ t ∈ Set.Icc 0 q, HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ Set.Icc 0 q, |f' t| ≤ 25 * t ^ 5) :
    |f q| ≤ (25 / 6 : ℝ) * q ^ 6 := by
  have hB (t : ℝ) : HasDerivAt (fun x : ℝ => (25 / 6 : ℝ) * x ^ 6)
      (25 * t ^ 5) t := by
    convert! (hasDerivAt_pow 6 t).const_mul (25 / 6 : ℝ) using 1 <;> norm_num <;> ring
  have hc : ContinuousOn f (Set.Icc 0 q) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hBc : ContinuousOn (fun x : ℝ => (25 / 6 : ℝ) * x ^ 6) (Set.Icc 0 q) :=
    fun t _ => (hB t).continuousAt.continuousWithinAt
  have hupper := image_le_of_deriv_right_le_deriv_boundary hc
    (fun t ht => (hd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
    (show f 0 ≤ (25 / 6 : ℝ) * (0 : ℝ) ^ 6 by simp [hzero]) hBc
    (fun t _ => (hB t).hasDerivWithinAt)
    (fun t ht => (abs_le.mp (hb t ⟨ht.1, ht.2.le⟩)).2)
    (show q ∈ Set.Icc 0 q from ⟨hq, le_rfl⟩)
  have hlower := image_le_of_deriv_right_le_deriv_boundary hc.neg
    (fun t ht => (hd t ⟨ht.1, ht.2.le⟩).neg.hasDerivWithinAt)
    (show -f 0 ≤ (25 / 6 : ℝ) * (0 : ℝ) ^ 6 by simp [hzero]) hBc
    (fun t _ => (hB t).hasDerivWithinAt)
    (fun t ht => (neg_le_iff_add_nonneg).2
      (by linarith [(abs_le.mp (hb t ⟨ht.1, ht.2.le⟩)).1]))
    (show q ∈ Set.Icc 0 q from ⟨hq, le_rfl⟩)
  change -f q ≤ _ at hlower
  exact abs_le.mpr ⟨by linarith, hupper⟩

theorem leftUpper_entropy_half_bias_quartic_remainder {q : ℝ}
    (hq : 0 ≤ q) (hqmax : q ≤ 1 / 64) :
    |1 - H (1 / 2 - q) - (2 * q ^ 2 / Real.log 2 +
        4 * q ^ 4 / (3 * Real.log 2))| ≤ (25 / 6 : ℝ) * q ^ 6 := by
  let E : ℝ → ℝ := fun t => 1 - H (1 / 2 - t) -
    (2 * t ^ 2 / Real.log 2 + 4 * t ^ 4 / (3 * Real.log 2))
  change |E q| ≤ _
  apply sixth_barrier hq (f' := fun t => J (1 / 2 - t) -
    (4 * t / Real.log 2 + 16 * t ^ 3 / (3 * Real.log 2)))
  · norm_num [E, H_half]
  · intro t ht
    have hdH := (Comparison.hasDerivAt_H
      (show 0 < 1 / 2 - t by linarith [ht.2])
      (show 1 / 2 - t < 1 by linarith [ht.1])).comp t
        ((hasDerivAt_id t).const_sub (1 / 2 : ℝ))
    have hd2 := ((hasDerivAt_pow 2 t).const_mul 2).div_const (Real.log 2)
    have hd4 := ((hasDerivAt_pow 4 t).const_mul 4).div_const (3 * Real.log 2)
    convert! (hdH.const_sub 1).sub (hd2.add hd4) using 1 <;> simp [E] <;> ring
  · intro t ht
    exact leftUpper_J_half_bias_cubic_remainder ht.1 (ht.2.trans hqmax)

#print axioms leftUpper_entropy_half_bias_quartic_remainder

end GeneralCK

end


