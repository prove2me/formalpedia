-- Prove2me | Definitions.Def_CK_GeneralCK_PsiOppositeCornerDomain
-- name    : CK_GeneralCK_PsiOppositeCornerDomain
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:38:43.208905+00:00
-- url     : https://prove2.me/theorems/d1aafcc3-888d-48db-87b7-1428dfec99be
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiOppositeCornerDomain` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiOppositeCornerDomain` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiOppositeCornerDomain` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiOppositeCornerDomain (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiOppositeCornerDomain.lean)

import Definitions.Def_CK_GeneralCK_PsiRegionLedger
import Definitions.Def_CK_GeneralCK_PsiRetainedChildBridge_v2

-- ===== source module GeneralCK.PsiOppositeCornerDomain =====
section

/-!
# Physical domain of the opposite deterministic corner

Entropy feasibility and the small total distance from the deterministic
corners put every tuple in the ratio-eight analytic domain. The numerical
entropy bound is proved by elementary logarithmic inequalities.
-/

namespace GeneralCK.PsiOppositeCornerDomain
open Set

theorem entropy_dyadic_corner : H (1 / 16384 : ℝ) ≤ 1 / 1024 := by
  have hL : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog : Real.log ((1 / 16384 : ℝ)⁻¹) = 14 * Real.log 2 := by
    norm_num
    rw [show (16384 : ℝ) = 2 ^ (14 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hupper : H (1 / 16384 : ℝ) * Real.log 2 ≤
      (1 / 16384) * Real.log ((1 / 16384 : ℝ)⁻¹) + 1 / 16384 := by
    have hc : (0 : ℝ) < 1 - 1 / 16384 := by norm_num
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hc)
    have hm := mul_le_mul_of_nonneg_left h hc.le
    norm_num at hm
    rw [H, div_mul_cancel₀ _ log_two_pos.ne', Real.binEntropy]
    norm_num
    linarith
  rw [hlog] at hupper
  nlinarith

theorem entropy_of_corner_width {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hc : μ.a + 1 - μ.b ≤ 1 / 8192) : μ.meanEntropy ≤ 1 / 1024 := by
  have ha : μ.a ∈ Icc (0 : ℝ) 1 := ⟨μ.a_interior.1.le, μ.a_interior.2.le⟩
  have hb : 1 - μ.b ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [μ.b_interior.1, μ.b_interior.2]
  have hf : μ.f ≤ H (1 - μ.b) := by rw [H_complement]; exact μ.f_le_cap
  have hmean := PsiRetainedChildBridge.entropy_mean_le_parent_cap ha hb μ.e_le_cap hf
  have hm : (μ.a + (1 - μ.b)) / 2 ∈ Icc (0 : ℝ) (1 / 2) := by
    constructor <;> linarith [μ.a_interior.1, μ.b_interior.2]
  have hbound := H_strictMonoOn.monotoneOn hm
    (show (1 / 16384 : ℝ) ∈ Icc (0 : ℝ) (1 / 2) by norm_num)
    (show (μ.a + (1 - μ.b)) / 2 ≤ 1 / 16384 by linarith)
  exact hmean.trans (hbound.trans entropy_dyadic_corner)

/-- The complete small-corner geometry needed by the corrected analytic
owner. Positive entropy is retained and all comparisons are weak at faces. -/
theorem corner_domain {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hc : μ.a + 1 - μ.b ≤ 1 / 8192) :
    0 ≤ 1 - μ.a - μ.b ∧ 1 - μ.a - μ.b ≤ 1 / 10 ∧
      0 < μ.meanEntropy ∧ μ.meanEntropy ≤ 1 / 1024 ∧
      8 * μ.meanEntropy ≤ μ.b - μ.a ∧ μ.a ≤ 1 / 2 ∧ 1 / 2 ≤ μ.b := by
  have hE := entropy_of_corner_width μ hc
  have ha := μ.a_interior.1
  have hb := μ.b_interior.2
  have hEpos : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  exact ⟨by linarith, by linarith, hEpos, hE,
    by linarith, by linarith, by linarith⟩

#print axioms entropy_dyadic_corner
#print axioms entropy_of_corner_width
#print axioms corner_domain

end GeneralCK.PsiOppositeCornerDomain

end


