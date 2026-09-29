-- Prove2me | Definitions.Def_CK_GeneralCK_DeterministicCap
-- name    : CK_GeneralCK_DeterministicCap
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:28:07.592973+00:00
-- url     : https://prove2.me/theorems/b9d27b97-f9e3-485e-9dd4-66c3840f6861
-- title:
--   Courtade–Kumar proof module `GeneralCK.DeterministicCap` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.DeterministicCap` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.DeterministicCap` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.DeterministicCap (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/DeterministicCap.lean)

import Definitions.Def_CK_GeneralCK_ProfileConvexity
import Definitions.Def_CK_GeneralCK_InformationIdentity
import Definitions.Def_CK_GeneralCK_FiniteLaw

namespace GeneralCK

private theorem binEntropy_split (a b : ℝ) (hs : a + b ≠ 0) :
    (a + b) * Real.binEntropy (a / (a + b)) =
      Real.negMulLog a + Real.negMulLog b - Real.negMulLog (a + b) := by
  have h := Information.scaled_binary_entropy (a + b) (a / (a + b))
  have hp : (a + b) * (a / (a + b)) = a := mul_div_cancel₀ a hs
  have hq : (a + b) * (1 - a / (a + b)) = b := by field_simp; ring
  rw [hp, hq] at h
  linarith

/-- Entropy chain rule for the two posterior Bernoulli parameters. -/
theorem deterministic_entropy_chain {a b : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hb : 0 < b) (hb' : b < 1) :
    H ((a + b) / 2) - (H a + H b) / 2 =
      ((a + b) / 2) * (1 - H (a / (a + b))) +
      (1 - (a + b) / 2) * (1 - H ((1 - b) / (2 - a - b))) := by
  have hs : a + b ≠ 0 := by linarith
  have ht : (1 - b) + (1 - a) ≠ 0 := by linarith
  have h₁ := binEntropy_split a b hs
  have h₂ := binEntropy_split (1 - b) (1 - a) ht
  have h₃ := Information.scaled_binary_entropy 2 ((a + b) / 2)
  have heqa : 2 * ((a + b) / 2) = a + b := by ring
  have heqb : 2 * (1 - (a + b) / 2) = 2 - a - b := by ring
  have heqc : (1 - b) + (1 - a) = 2 - a - b := by ring
  rw [heqc] at h₂
  rw [heqa, heqb] at h₃
  have h₄ := Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub a
  have h₅ := Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub b
  have htwo : Real.negMulLog 2 = -2 * Real.log 2 := by simp [Real.negMulLog]
  rw [htwo] at h₃
  unfold H
  field_simp
  nlinarith

private theorem eta_H_lower_closed {p : ℝ} (hp : 0 < p) (hp' : p ≤ 1 / 2) :
    eta (H p) = (1 - 2 * p) * J p := by
  rw [eta_eq_profile (H_nonneg hp.le (by linarith)) (H_le_one p),
    entropyInverse_H_lower hp.le hp']

private theorem deterministic_cost_chain_ordered {a b : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hb : 0 < b) (hb' : b < 1) (hab : a ≤ b) :
    interiorCost a b =
      ((a + b) / 2) * Scalar.P (1 - H (a / (a + b))) +
      (1 - (a + b) / 2) * Scalar.P (1 - H ((1 - b) / (2 - a - b))) := by
  have hs : 0 < a + b := by linarith
  have ht : 0 < 2 - a - b := by linarith
  have hp : 0 < a / (a + b) := div_pos ha hs
  have hp' : a / (a + b) ≤ 1 / 2 := (div_le_iff₀ hs).2 (by linarith)
  have hq : 0 < (1 - b) / (2 - a - b) := div_pos (by linarith) ht
  have hq' : (1 - b) / (2 - a - b) ≤ 1 / 2 := (div_le_iff₀ ht).2 (by linarith)
  have hpj : (1 - a / (a + b)) / (a / (a + b)) = b / a := by field_simp; ring
  have hqj : (1 - (1 - b) / (2 - a - b)) / ((1 - b) / (2 - a - b)) =
      (1 - a) / (1 - b) := by field_simp; ring
  simp only [Scalar.P, sub_sub_cancel, eta_H_lower_closed hp hp', eta_H_lower_closed hq hq']
  unfold interiorCost J
  rw [hpj, hqj]
  rw [Real.log_div (by linarith : 1 - a ≠ 0) ha.ne',
    Real.log_div (by linarith : 1 - b ≠ 0) hb.ne', Real.log_div hb.ne' ha.ne',
    Real.log_div (by linarith : 1 - a ≠ 0) (by linarith : 1 - b ≠ 0)]
  field_simp
  ring

/-- The deterministic-cap inequality, obtained by convexity of the production
profile and the two binary entropy chain identities. -/
theorem deterministic_cap_bound {a b : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hb : 0 < b) (hb' : b < 1) :
    Scalar.P (H ((a + b) / 2) - (H a + H b) / 2) ≤ interiorCost a b := by
  suffices hordered : ∀ (a b : ℝ), 0 < a → a < 1 → 0 < b → b < 1 → a ≤ b →
      Scalar.P (H ((a + b) / 2) - (H a + H b) / 2) ≤ interiorCost a b by
    rcases le_total a b with hab | hba
    · exact hordered a b ha ha' hb hb' hab
    · simpa only [add_comm, interiorCost_comm b a] using hordered b a hb hb' ha ha' hba
  intro a b ha ha' hb hb' hab
  have hs : 0 < a + b := by linarith
  have ht : 0 < 2 - a - b := by linarith
  have hp : 0 < a / (a + b) := div_pos ha hs
  have hp' : a / (a + b) < 1 := (div_lt_one hs).2 (by linarith)
  have hq : 0 < (1 - b) / (2 - a - b) := div_pos (by linarith) ht
  have hq' : (1 - b) / (2 - a - b) < 1 := (div_lt_one ht).2 (by linarith)
  have h := Scalar.P_convexOn.2
    (show 1 - H (a / (a + b)) ∈ Set.Ico (0 : ℝ) 1 from
      ⟨by linarith [H_le_one (a / (a + b))], by linarith [H_pos hp hp']⟩)
    (show 1 - H ((1 - b) / (2 - a - b)) ∈ Set.Ico (0 : ℝ) 1 from
      ⟨by linarith [H_le_one ((1 - b) / (2 - a - b))], by linarith [H_pos hq hq']⟩)
    (show 0 ≤ (a + b) / 2 by linarith) (show 0 ≤ 1 - (a + b) / 2 by linarith)
    (show (a + b) / 2 + (1 - (a + b) / 2) = 1 by ring)
  rw [deterministic_entropy_chain ha ha' hb hb', deterministic_cost_chain_ordered ha ha' hb hb' hab]
  exact h

end GeneralCK


