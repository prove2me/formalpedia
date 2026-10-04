-- Prove2me | Definitions.Def_CK_CKLaneN1_DBSound
-- name    : CK_CKLaneN1_DBSound
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T13:15:44.217585+00:00
-- url     : https://prove2.me/theorems/dc323f7a-7cf9-48b7-a2f5-df7289a91f56
-- title:
--   Courtade–Kumar proof module `CKLaneN1.DBSound` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.DBSound` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.DBSound` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.DBSound (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/DBSound.lean)

import Definitions.Def_CK_CKLaneN1_DBChecker

-- ===== source module CKLaneN1.DBSound =====
section

/-!
# Lane N1: soundness of the NO_SEP §6 leaf kernel, in the row form `NoSepA_ModerateRest`
-/

namespace CKLaneN1

open GeneralCK GeneralCK.Scalar CKLaneE.FP Set

/-- Common consequences of `dbBase` and box membership. -/
structure DBFacts {k : ℕ} (B : B3) (μ : InteriorLaw (Fin k)) : Prop where
  hE_le : μ.meanEntropy ≤ ((dbEup B : ℚ) : ℝ)
  hI_le : H ((μ.a + μ.b) / 2) - μ.meanEntropy ≤ ((dbIup B : ℚ) : ℝ)
  hI_ge : ((dbIlo B : ℚ) : ℝ) ≤ H ((μ.a + μ.b) / 2) - μ.meanEntropy
  hdrop : H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 ≤ ((dbK B : ℚ) : ℝ) * (μ.b - μ.a) ^ 2
  hK0 : 0 ≤ ((dbK B : ℚ) : ℝ)
  hV : LogSum.V μ.a μ.b ≤ ((((1 + DD) ^ 2 - B.a0 ^ 2) / 4 : ℚ) : ℝ)
  hus_a : ((((1 - dbRmax B) / 2 : ℚ)) : ℝ) ≤ μ.a

set_option maxHeartbeats 2000000 in
theorem dbFacts_of {B : B3} (hb : dbBase B = true) {k : ℕ} (μ : InteriorLaw (Fin k))
    (hab : μ.a < μ.b) (hsum : μ.a + μ.b ≤ 1) (ha : 1 / 10 ≤ μ.a) (hd : μ.b - μ.a ≤ 1 / 50)
    (hin : InDB B μ) : DBFacts B μ := by
  simp only [dbBase, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨hbox, hp0⟩, hp1⟩, hp2⟩, hp3⟩, hHE⟩ := hb
  obtain ⟨hq0, hq01, hq1D, ht0, ht01, ht1⟩ := hbox
  obtain ⟨hqa0, hqa1, hE0, hE1⟩ := hin
  have haI := μ.a_interior
  have hbI := μ.b_interior
  set q := 1 - μ.a - μ.b with hq_def
  set d := μ.b - μ.a with hd_def
  have hdpos : 0 < d := by rw [hd_def]; linarith
  have hq0R : (0 : ℝ) ≤ (B.a0 : ℝ) := by exact_mod_cast hq0
  have ht0R : (0 : ℝ) ≤ (B.b0 : ℝ) := by exact_mod_cast ht0
  have ht01R : (B.b0 : ℝ) ≤ (B.b1 : ℝ) := by exact_mod_cast ht01
  have ht1R : (B.b1 : ℝ) ≤ 1 := by exact_mod_cast ht1
  have hq1DR : (B.a1 : ℝ) + (DD : ℝ) < 1 := by exact_mod_cast hq1D
  have hDD : (DD : ℝ) = 1 / 50 := by simp [DD]
  have hEM : (EM : ℝ) = 11 / 200 := by simp [EM]
  have hqpos : 0 ≤ q := hq0R.trans hqa0
  have hmid : (μ.a + μ.b) / 2 = (1 - q) / 2 := by rw [hq_def]; ring
  -- H(m) bounds
  have hHmU : H ((μ.a + μ.b) / 2) ≤ ((dbHpU B : ℚ) : ℝ) := by
    rw [hmid]
    have h1 : H ((1 - q) / 2) ≤ H ((1 - (B.a0 : ℝ)) / 2) :=
      CKLaneD.H_mono_left (by linarith) (by linarith) (by linarith)
    have h2 := H_le_Hhi hp0
    simp only [dbHpU]
    push_cast at h2 ⊢
    linarith
  have hHmL : ((dbHpL B : ℚ) : ℝ) ≤ H ((μ.a + μ.b) / 2) := by
    rw [hmid]
    have h1 : H ((1 - (B.a1 : ℝ)) / 2) ≤ H ((1 - q) / 2) :=
      CKLaneD.H_mono_left (by linarith) (by linarith) (by linarith)
    have h2 := H_ge_Hlo hp1
    simp only [dbHpL]
    push_cast at h2 ⊢
    linarith
  have hr0 : 1 - 2 * μ.a ≤ ((dbRmax B : ℚ) : ℝ) := by
    simp only [dbRmax]
    push_cast
    apply le_min
    · have : 1 - 2 * μ.a = q + d := by rw [hq_def, hd_def]; ring
      rw [this, hDD]; linarith
    · linarith
  have hr1 : ((dbRmax B : ℚ) : ℝ) < 1 := by
    simp only [dbRmax]; push_cast
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hK1 := drop_le_Aup haI.1 hab hbI.2 hsum hr0 hr1
  have hK2 : H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 ≤ ((dbK2 B : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 := by
    rw [entropyDrop_eq_secondDiff]
    have h1 := drop_le_K2 (q := q) (d := d) (q₁ := (B.a1 : ℝ)) (D := (DD : ℝ)) hqpos hqa1 hq1DR
      hdpos (by rw [hDD]; exact hd)
    have hsd : secondDiff (B.a1 : ℝ) (DD : ℝ) ≤
        ((Cup (B.a1 + DD) : ℚ) : ℝ) + ((Cup (|B.a1 - DD|) : ℚ) : ℝ) - 2 * ((Clo B.a1 : ℚ) : ℝ) := by
      unfold secondDiff
      have e1 := C_le_Cup hp2
      have e2 := C_le_Cup hp3
      have e3 := Clo_le_C hp1
      push_cast at e1 e2 e3
      have hc2 : Cf ((B.a1 : ℝ) - (DD : ℝ)) = 1 - H ((1 - |(B.a1 : ℝ) - (DD : ℝ)|) / 2) := by
        rw [← Cf_abs]; rfl
      unfold Cf at hc2 ⊢
      rw [hc2]
      linarith
    have hD2 : (0 : ℝ) < 2 * (DD : ℝ) ^ 2 := by rw [hDD]; norm_num
    have hK2eq : ((dbK2 B : ℚ) : ℝ) = (((Cup (B.a1 + DD) : ℚ) : ℝ) + ((Cup (|B.a1 - DD|) : ℚ) : ℝ) -
        2 * ((Clo B.a1 : ℚ) : ℝ)) / (2 * (DD : ℝ) ^ 2) := by
      simp only [dbK2]; push_cast; ring
    have h2 : secondDiff (B.a1 : ℝ) (DD : ℝ) / (2 * (DD : ℝ) ^ 2) * d ^ 2 ≤
        ((dbK2 B : ℚ) : ℝ) * d ^ 2 := by
      rw [hK2eq]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg d)
      exact div_le_div_of_nonneg_right hsd hD2.le
    exact h1.trans h2
  have hΔ0 : 0 ≤ H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 := by
    have := μ.entropyDrop_nonneg
    unfold InteriorLaw.entropyDrop InteriorLaw.midpoint at this
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- E ≤ Eup
    simp only [dbEup]
    push_cast
    have := mul_le_mul_of_nonneg_left (show H ((μ.a + μ.b) / 2) - EM ≤ ((dbHpU B : ℚ) : ℝ) - EM by
      linarith) (show (0 : ℝ) ≤ (B.b1 : ℝ) by linarith)
    linarith
  · -- I ≤ Iup
    simp only [dbIup]
    push_cast
    have h1 : H ((μ.a + μ.b) / 2) - μ.meanEntropy ≤ (1 - (B.b0 : ℝ)) * (H ((μ.a + μ.b) / 2) - EM) := by
      linarith
    have h2 := mul_le_mul_of_nonneg_left (show H ((μ.a + μ.b) / 2) - EM ≤ ((dbHpU B : ℚ) : ℝ) - EM by
      linarith) (show (0 : ℝ) ≤ 1 - (B.b0 : ℝ) by linarith)
    linarith
  · -- Ilo ≤ I
    simp only [dbIlo]
    push_cast
    have h1 : (1 - (B.b1 : ℝ)) * (H ((μ.a + μ.b) / 2) - EM) ≤ H ((μ.a + μ.b) / 2) - μ.meanEntropy := by
      linarith
    have h2 := mul_le_mul_of_nonneg_left (show ((dbHpL B : ℚ) : ℝ) - EM ≤ H ((μ.a + μ.b) / 2) - EM by
      linarith) (show (0 : ℝ) ≤ 1 - (B.b1 : ℝ) by linarith)
    linarith
  · -- Δ ≤ K d²
    have hmin : ((dbK B : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 =
        min (((AupOf (dbRmax B) : ℚ) : ℝ) * (μ.b - μ.a) ^ 2) (((dbK2 B : ℚ) : ℝ) * (μ.b - μ.a) ^ 2) := by
      simp only [dbK]
      push_cast
      exact min_mul_of_nonneg _ _ (sq_nonneg _)
    rw [hmin]
    exact le_min hK1 hK2
  · -- K ≥ 0
    have hA := (Aup_pos (le_trans (by linarith [haI.2]) hr0) hr1).le
    have hK2nn : 0 ≤ ((dbK2 B : ℚ) : ℝ) := by
      by_contra hc
      have hneg : ((dbK2 B : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 < 0 :=
        mul_neg_of_neg_of_pos (lt_of_not_ge hc) (by positivity)
      linarith
    simp only [dbK]
    push_cast
    exact le_min hA hK2nn
  · -- V ≤ V*
    have hV : LogSum.V μ.a μ.b = μ.b * (1 - μ.a) := by
      unfold LogSum.V
      rw [max_eq_right hab.le, min_eq_left hab.le]
    rw [hV]
    push_cast
    have e : μ.b * (1 - μ.a) = ((1 + d) ^ 2 - q ^ 2) / 4 := by rw [hq_def, hd_def]; ring
    rw [e]
    have h1 : (1 + d) ^ 2 ≤ (1 + (DD : ℝ)) ^ 2 := by
      apply pow_le_pow_left₀ (by linarith)
      rw [hDD]; linarith
    have h2 : (B.a0 : ℝ) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hq0R hqa0 2
    linarith
  · -- u* ≤ a
    simp only [dbRmax]
    push_cast
    have : (1 : ℝ) - 2 * μ.a ≤ min ((B.a1 : ℝ) + (DD : ℝ)) (4 / 5) := by
      apply le_min
      · have : 1 - 2 * μ.a = q + d := by rw [hq_def, hd_def]; ring
        rw [this, hDD]; linarith
      · linarith
    linarith

end CKLaneN1

end


