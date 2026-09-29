-- Prove2me | Definitions.Def_CK_CKLaneA3W_FinalLemmas
-- name    : CK_CKLaneA3W_FinalLemmas
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T16:12:28.995125+00:00
-- url     : https://prove2.me/theorems/88de6b08-ef09-41aa-ab0f-6813d78e5f3a
-- title:
--   Courtade–Kumar proof module `CKLaneA3W.FinalLemmas` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA3W.FinalLemmas` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA3W.FinalLemmas` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA3W.FinalLemmas (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3W/FinalLemmas.lean)

import Definitions.Def_CK_CKLaneA3W_Positivity
import Definitions.Def_CK_CKLaneA3W_Formula

/-!
# CKLaneA3W.FinalLemmas — generic final positivity lemmas and minors-from-positivity bridge
-/

namespace CKLaneA3W

open GeneralCK GeneralCK.Correction

def rho2S : SPoly := [(0, [(0, 1 / 4)]), (1, [(0, 1)]), (2, [(0, 1)])]

theorem rho2S_eval (σ L : ℝ) : SPoly.eval σ L rho2S = (σ + 1 / 2) ^ 2 := by
  simp [rho2S, SPoly.eval_cons, SPoly.eval_nil, LPoly.eval_cons, LPoly.eval_nil]; ring

/-- positivity of a TM-enclosed function with valuation 5 split as `ρ² A0 + t² B`. -/
theorem pos_of_TM_split {f : ℝ → ℝ → ℝ} {D : TMd} (hf : Good f D) (Q0 A0 : SPoly) (B : TPoly)
    (hn : 7 ≤ D.n) (hz : zeroPrefix D.P 5 = true)
    (hQ : TPoly.drop D.P 5 = Q0 :: [] :: B)
    (hQ0 : Q0 = SPoly.mul rho2S A0)
    (mA mB : ℕ) (hmA : 0 < mA) (hmB : 0 < mB)
    (hA : allBoxes (fun a b => decide (0 < (sBox a b A0).1)) mA = true)
    (hB : allBoxes (fun a b => decide (D.r * Tq ^ (D.n - 7) < (tBox 0 Tq a b B).1)) mB = true) :
    ∀ t ρ, Dom t ρ → 0 < f t ρ := by
  intro t ρ hd
  have ht := hd.1
  have hσ := hd.sigma
  have hL : Real.log 2 ≠ 0 := by positivity
  have h1 := hf.1 t ρ hd
  unfold ev at h1
  set σ := ρ - 1 / 2 with hσdef
  have hev : TPoly.eval t σ (Real.log 2) D.P =
      t ^ 5 * (SPoly.eval σ (Real.log 2) Q0 + t * (0 + t * TPoly.eval t σ (Real.log 2) B)) := by
    rw [zeroPrefix_eval t σ _ D.P 5 hz, hQ, TPoly.eval_cons, TPoly.eval_cons, SPoly.eval_nil]
  have hQ0e : SPoly.eval σ (Real.log 2) Q0 = ρ ^ 2 * SPoly.eval σ (Real.log 2) A0 := by
    rw [hQ0, SPoly.eval_mul σ _ hL, rho2S_eval]; rw [hσdef]; ring
  -- A0 lower bound
  obtain ⟨a, b, hab, ha, hb⟩ := allBoxes_cover _ mA hmA hA hσ
  have hAlo : (0 : ℝ) < SPoly.eval σ (Real.log 2) A0 := by
    have h := (sBox_spec ha hb A0).1
    have : (0 : ℚ) < (sBox a b A0).1 := by simpa using hab
    have : (0 : ℝ) < (sBox a b A0).1 := by exact_mod_cast this
    linarith
  -- B lower bound
  obtain ⟨a', b', hab', ha', hb'⟩ := allBoxes_cover _ mB hmB hB hσ
  have hBlo : (D.r : ℝ) * t ^ (D.n - 7) < TPoly.eval t σ (Real.log 2) B := by
    have h := (tBox_spec (t0 := 0) (t1 := Tq) (by simp; exact ht.le) hd.2.1 ha' hb' B).1
    have hq : D.r * Tq ^ (D.n - 7) < (tBox 0 Tq a' b' B).1 := by simpa using hab'
    have hq' : (D.r : ℝ) * (Tq : ℝ) ^ (D.n - 7) < ((tBox 0 Tq a' b' B).1 : ℝ) := by exact_mod_cast hq
    have hr : (0 : ℝ) ≤ D.r := by exact_mod_cast hf.2
    have hpow : t ^ (D.n - 7) ≤ (Tq : ℝ) ^ (D.n - 7) := pow_le_pow_left₀ ht.le hd.2.1 _
    have : (D.r : ℝ) * t ^ (D.n - 7) ≤ D.r * (Tq : ℝ) ^ (D.n - 7) := mul_le_mul_of_nonneg_left hpow hr
    linarith
  have hsplit : (D.r : ℝ) * t ^ D.n = t ^ 5 * (t * t * ((D.r : ℝ) * t ^ (D.n - 7))) := by
    have : D.n = (D.n - 7) + 7 := by omega
    conv_lhs => rw [this]
    ring
  have hlow : t ^ 5 * (ρ ^ 2 * SPoly.eval σ (Real.log 2) A0 +
      t * t * (TPoly.eval t σ (Real.log 2) B - D.r * t ^ (D.n - 7))) ≤ f t ρ := by
    have h2 := neg_abs_le (f t ρ - TPoly.eval t σ (Real.log 2) D.P)
    rw [hsplit] at h1
    have key : TPoly.eval t σ (Real.log 2) D.P - t ^ 5 * (t * t * ((D.r : ℝ) * t ^ (D.n - 7))) =
        t ^ 5 * (ρ ^ 2 * SPoly.eval σ (Real.log 2) A0 +
          t * t * (TPoly.eval t σ (Real.log 2) B - D.r * t ^ (D.n - 7))) := by
      rw [hev, hQ0e]; ring
    linarith
  have hpos : 0 < t ^ 5 * (ρ ^ 2 * SPoly.eval σ (Real.log 2) A0 +
      t * t * (TPoly.eval t σ (Real.log 2) B - D.r * t ^ (D.n - 7))) := by
    have h3 := hd.2.2.1
    have hBpos : 0 < TPoly.eval t σ (Real.log 2) B - D.r * t ^ (D.n - 7) := by linarith
    positivity
  linarith

/-- positivity of a TM-enclosed function with valuation 2 (single t-box per σ-box). -/
theorem pos_of_TM_val2 {f : ℝ → ℝ → ℝ} {D : TMd} (hf : Good f D) (hn : 2 ≤ D.n)
    (hz : zeroPrefix D.P 2 = true) (m : ℕ) (hm : 0 < m)
    (hB : allBoxes (fun a b => decide (D.r * Tq ^ (D.n - 2) < (tBox 0 Tq a b (TPoly.drop D.P 2)).1)) m = true) :
    ∀ t ρ, Dom t ρ → 0 < f t ρ := by
  intro t ρ hd
  have ht := hd.1
  have hσ := hd.sigma
  have h1 := hf.1 t ρ hd
  unfold ev at h1
  set σ := ρ - 1 / 2 with hσdef
  have hev := zeroPrefix_eval t σ (Real.log 2) D.P 2 hz
  obtain ⟨a, b, hab, ha, hb⟩ := allBoxes_cover _ m hm hB hσ
  have hBlo : (D.r : ℝ) * t ^ (D.n - 2) < TPoly.eval t σ (Real.log 2) (TPoly.drop D.P 2) := by
    have h := (tBox_spec (t0 := 0) (t1 := Tq) (by simp; exact ht.le) hd.2.1 ha hb (TPoly.drop D.P 2)).1
    have hq : D.r * Tq ^ (D.n - 2) < (tBox 0 Tq a b (TPoly.drop D.P 2)).1 := by simpa using hab
    have hq' : (D.r : ℝ) * (Tq : ℝ) ^ (D.n - 2) < ((tBox 0 Tq a b (TPoly.drop D.P 2)).1 : ℝ) := by
      exact_mod_cast hq
    have hr : (0 : ℝ) ≤ D.r := by exact_mod_cast hf.2
    have hpow : t ^ (D.n - 2) ≤ (Tq : ℝ) ^ (D.n - 2) := pow_le_pow_left₀ ht.le hd.2.1 _
    have : (D.r : ℝ) * t ^ (D.n - 2) ≤ D.r * (Tq : ℝ) ^ (D.n - 2) := mul_le_mul_of_nonneg_left hpow hr
    linarith
  have hsplit : (D.r : ℝ) * t ^ D.n = t ^ 2 * ((D.r : ℝ) * t ^ (D.n - 2)) := by
    have : D.n = (D.n - 2) + 2 := by omega
    conv_lhs => rw [this]
    ring
  have h2 := neg_abs_le (f t ρ - TPoly.eval t σ (Real.log 2) D.P)
  rw [hsplit] at h1
  have hpos : 0 < t ^ 2 * (TPoly.eval t σ (Real.log 2) (TPoly.drop D.P 2) - D.r * t ^ (D.n - 2)) := by
    have : 0 < TPoly.eval t σ (Real.log 2) (TPoly.drop D.P 2) - D.r * t ^ (D.n - 2) := by linarith
    positivity
  have key : TPoly.eval t σ (Real.log 2) D.P - t ^ 2 * ((D.r : ℝ) * t ^ (D.n - 2)) =
      t ^ 2 * (TPoly.eval t σ (Real.log 2) (TPoly.drop D.P 2) - D.r * t ^ (D.n - 2)) := by
    rw [hev]; ring
  linarith

/-- actual ratio minors from positivity of `m11` and `kdet` (as in `actualHighU_of_scaledOwner`). -/
theorem minors_of_pos {u rho : ℝ} (hu0 : 0 < u) (huhalf : u < 1 / 2) (hr : 0 < rho) (hr1 : rho < 1)
    (hm' : 0 < Natural.m11 u (u + rho * (1 / 2 - u)))
    (hk' : 0 < Natural.kdet u (u + rho * (1 / 2 - u))) : ActualRatioMinorsPositive u rho := by
  obtain ⟨huw, hw⟩ := Natural.ratio_point_interior (sub_pos.mpr huhalf) hr hr1
  have heq := Natural.kernel_eq_actual_ratio hu0 (sub_pos.mpr huhalf) hr hr1
  have hw0 : 0 < H (u + rho * (1 / 2 - u)) := H_pos (hu0.trans huw) (by linarith [hw])
  have hw1 : H (u + rho * (1 / 2 - u)) < 1 := by
    have hs := H_strictMonoOn ⟨(hu0.trans huw).le, hw.le⟩
      (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc 0 (1 / 2)) hw
    simpa only [H_half] using hs
  unfold ActualRatioMinorsPositive
  refine ⟨heq.1 ▸ hm', ?_⟩
  exact (Mdet_pos_iff_Kfactored_pos hw0 hw1).2 (heq.2 ▸ hk')

end CKLaneA3W


