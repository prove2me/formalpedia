-- Prove2me | Definitions.Def_CK_CKLaneN4_SplitKernel
-- name    : CK_CKLaneN4_SplitKernel
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:09:58.363397+00:00
-- url     : https://prove2.me/theorems/f5ab60b2-72a4-4a2c-8006-86f8b3d47b68
-- title:
--   Courtade–Kumar proof module `CKLaneN4.SplitKernel` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.SplitKernel` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.SplitKernel` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.SplitKernel (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/SplitKernel.lean)

import Definitions.Def_CK_CKLaneN4_EightKernel
import Definitions.Def_CK_GeneralCK_PsiChildEntropyCoupling

-- ===== source module CKLaneN4.SplitKernel =====
section

/-!
# Lane N4: the cap-free split-loss bound of the global eight-ratio theorem

Archive: `reduction/eight_global/GLOBAL_SPLIT.py` and `GLOBAL_EIGHT_PROOF.md` §2–§3.
With `C = 13/6`, `c0(q) = 1/L - C/2 + (C/2 - 1/(2L)) q` and `C_n = capacity`,

  `E · 2 c0(q) C_n(C q / (2 c0(q))) / q^2 < 1/5`  for `E ≤ 11/200`, `0 ≤ q ≤ 11/25`,

i.e. `2 c0(q) C_n(C q/(2 c0(q))) ≤ (40/11) q^2`, proved on the archived two-leaf partition
`[0, 11/50] ∪ [11/50, 11/25]` by the archive's acceptance inequality
`(11/200) C^2/(2 c0(q_-)) · C_n(z)/z^2 |_{z ≥ z0(q_+)} < 1/5` (`C_n(z)/z^2` increasing, `c0`, `z0`
increasing), with rational enclosures (`checkSplit_sound`, unconditional).

`split_term_lower`: the signed split term of `PsiChildEntropyCoupling.retained_child_decomposition`
is `≥ -(1/5) q^2/E` whenever `d + q ≤ 1` (so the endpoint coefficient is `≥ c0(q)`).
-/

namespace CKLaneN4

open GeneralCK CKLaneD Set PsiSignedSplit

/-- `c0(q) = 1/L - 13/12 + (13/12 - 1/(2L)) q`. -/
noncomputable def c0 (q : ℝ) : ℝ := 1 / Real.log 2 - 13 / 12 + (13 / 12 - 1 / (2 * Real.log 2)) * q

/-- Rational lower bound of `c0` (uses `log 2 ≤ L1`). -/
def c0lo (q : ℚ) : ℚ := (1 / L1) * (1 - q / 2) - 13 / 12 + 13 * q / 12

/-- The rational upper bound `z_r ≥ z0(q_+)`. -/
def zrOf (qh : ℚ) : ℚ := 13 * qh / (12 * c0lo qh)

theorem log_two_bounds_simple : (69 / 100 : ℝ) < Real.log 2 ∧ Real.log 2 < 7 / 10 := by
  have h1 := Certificates.PilotData.log_two.1
  have h2 := Certificates.PilotData.log_two.2
  norm_num at h1 h2
  constructor <;> linarith

theorem c0_alpha_pos : 0 < 1 / Real.log 2 - 13 / 12 := by
  have hL := log_two_bounds_simple
  have hLpos : 0 < Real.log 2 := log_two_pos
  rw [sub_pos, lt_div_iff₀ hLpos]
  linarith [hL.2]

theorem c0_beta_pos : 0 < 13 / 12 - 1 / (2 * Real.log 2) := by
  have hL := log_two_bounds_simple
  have hLpos : 0 < Real.log 2 := log_two_pos
  rw [sub_pos, div_lt_iff₀ (by positivity)]
  linarith [hL.1]

theorem c0_pos {q : ℝ} (hq : 0 ≤ q) : 0 < c0 q := by
  unfold c0
  have := mul_nonneg c0_beta_pos.le hq
  linarith [c0_alpha_pos]

theorem c0_mono {q q' : ℝ} (h : q ≤ q') : c0 q ≤ c0 q' := by
  unfold c0
  have := mul_le_mul_of_nonneg_left h c0_beta_pos.le
  linarith

theorem c0lo_le {q : ℚ} (hq : (q : ℝ) ≤ 2) : (c0lo q : ℝ) ≤ c0 (q : ℝ) := by
  have hL := log2_bounds
  have hLpos : 0 < Real.log 2 := log_two_pos
  have hinv : 1 / (L1 : ℝ) ≤ 1 / Real.log 2 := one_div_le_one_div_of_le hLpos hL.2
  have hm := mul_le_mul_of_nonneg_right hinv (show (0 : ℝ) ≤ 1 - (q : ℝ) / 2 by linarith)
  unfold c0lo c0
  push_cast
  have e : 1 / Real.log 2 - 13 / 12 + (13 / 12 - 1 / (2 * Real.log 2)) * (q : ℝ) =
      1 / Real.log 2 * (1 - (q : ℝ) / 2) - 13 / 12 + 13 * (q : ℝ) / 12 := by
    field_simp
    ring
  rw [e]
  linarith

/-- `z0(q) = 13 q / (12 c0(q))` increases. -/
theorem z0_mono {q q' : ℝ} (hq : 0 ≤ q) (h : q ≤ q') :
    13 * q / (12 * c0 q) ≤ 13 * q' / (12 * c0 q') := by
  have h0 := c0_pos hq
  have h0' := c0_pos (hq.trans h)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hα := c0_alpha_pos
  have key : q * c0 q' - q' * c0 q = (1 / Real.log 2 - 13 / 12) * (q - q') := by
    unfold c0; ring
  nlinarith

/-- The split checker on `[ql, qh]` (the archive's `GLOBAL_SPLIT.upper`, directed). -/
def checkSplit (ql qh : ℚ) (cp cm : LogCert) : Bool :=
  decide (0 ≤ ql ∧ ql ≤ qh ∧ qh ≤ 2 ∧ 0 < c0lo ql ∧ 0 < c0lo qh ∧ 0 < zrOf qh ∧ zrOf qh < 1) &&
  checkLogCert (1 + zrOf qh) cp && checkLogCert (1 - zrOf qh) cm &&
  decide (169 / (72 * c0lo ql) * (((1 + zrOf qh) * cp.hi + (1 - zrOf qh) * cm.hi) / 2) /
    zrOf qh ^ 2 ≤ 40 / 11)

theorem capacity_zero : capacity 0 = 0 := by simp [capacity]

theorem checkSplit_sound {ql qh : ℚ} {cp cm : LogCert} (h : checkSplit ql qh cp cm = true)
    {q : ℝ} (hql : (ql : ℝ) ≤ q) (hqh : q ≤ qh) :
    13 * q / 6 < 2 * c0 q ∧ 2 * c0 q * capacity ((13 * q / 6) / (2 * c0 q)) ≤ (40 / 11) * q ^ 2 := by
  unfold checkSplit at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hcp⟩, hcm⟩, hacc⟩ := h
  have r1 : (0 : ℝ) ≤ ql := by exact_mod_cast h1
  have r3 : (qh : ℝ) ≤ 2 := by exact_mod_cast h3
  have r4 : (0 : ℝ) < c0lo ql := by exact_mod_cast h4
  have r5 : (0 : ℝ) < c0lo qh := by exact_mod_cast h5
  have hq : 0 ≤ q := r1.trans hql
  set zr : ℚ := zrOf qh with hzr
  have r6 : (0 : ℝ) < zr := by exact_mod_cast h6
  have r7 : (zr : ℝ) < 1 := by exact_mod_cast h7
  have hc0q := c0_pos hq
  have hc0l : (c0lo ql : ℝ) ≤ c0 q := (c0lo_le (by linarith)).trans (c0_mono hql)
  have hc0h : (c0lo qh : ℝ) ≤ c0 (qh : ℝ) := c0lo_le r3
  have ezr : (zr : ℝ) = 13 * (qh : ℝ) / (12 * (c0lo qh : ℝ)) := by
    rw [hzr]; unfold zrOf; push_cast; ring
  have hz_eq : (13 * q / 6) / (2 * c0 q) = 13 * q / (12 * c0 q) := by field_simp; ring
  have hzle : 13 * q / (12 * c0 q) ≤ (zr : ℝ) := by
    refine (z0_mono hq hqh).trans ?_
    rw [ezr]
    apply div_le_div_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hz0 : 0 ≤ 13 * q / (12 * c0 q) := by positivity
  have hzlt : 13 * q / (12 * c0 q) < 1 := hzle.trans_lt r7
  refine ⟨?_, ?_⟩
  · rw [div_lt_one (by positivity)] at hzlt
    linarith
  rw [hz_eq]
  rcases hq.eq_or_lt with hq0 | hqpos
  · rw [← hq0]; simp [capacity_zero]
  set z := 13 * q / (12 * c0 q) with hzdef
  have hzpos : 0 < z := by positivity
  have hcapz : capacity z = SmallMean.Cn z := capacity_eq_Cn (by rw [abs_of_pos hzpos]; exact hzlt)
  have hcapr : capacity (zr : ℝ) = SmallMean.Cn (zr : ℝ) :=
    capacity_eq_Cn (by rw [abs_of_pos r6]; exact r7)
  have hratio : SmallMean.Cn z / z ^ 2 ≤ SmallMean.Cn (zr : ℝ) / (zr : ℝ) ^ 2 :=
    Cn_ratio_strictMonoOn.monotoneOn ⟨hzpos, hzlt.le⟩ ⟨r6, r7.le⟩ hzle
  -- upper enclosure of C_n(z_r)
  obtain ⟨_, hp2⟩ := checkLogCert_sound hcp
  obtain ⟨_, hm2⟩ := checkLogCert_sound hcm
  push_cast at hp2 hm2
  have hK : SmallMean.Cn (zr : ℝ) ≤
      ((1 + (zr : ℝ)) * (cp.hi : ℝ) + (1 - (zr : ℝ)) * (cm.hi : ℝ)) / 2 := by
    rw [← hcapr]
    unfold capacity
    have a1 := mul_le_mul_of_nonneg_left hp2 (show (0 : ℝ) ≤ 1 + zr by linarith)
    have a2 := mul_le_mul_of_nonneg_left hm2 (show (0 : ℝ) ≤ 1 - zr by linarith)
    linarith
  have racc : 169 / (72 * (c0lo ql : ℝ)) *
      (((1 + (zr : ℝ)) * (cp.hi : ℝ) + (1 - (zr : ℝ)) * (cm.hi : ℝ)) / 2) / (zr : ℝ) ^ 2 ≤
      40 / 11 := by
    have := (Rat.cast_le (K := ℝ)).mpr hacc
    push_cast at this
    linarith
  have hCnz0 : 0 ≤ SmallMean.Cn z := (SmallMean.Cn_ge_half_sq hzpos.le hzlt.le).trans' (by positivity)
  have hR0 : 0 ≤ SmallMean.Cn (zr : ℝ) / (zr : ℝ) ^ 2 :=
    div_nonneg ((SmallMean.Cn_ge_half_sq r6.le r7.le).trans' (by positivity)) (sq_nonneg _)
  have hsq : 2 * c0 q * z ^ 2 = 169 * q ^ 2 / (72 * c0 q) := by
    rw [hzdef]; field_simp; ring
  have hsq_le : 169 * q ^ 2 / (72 * c0 q) ≤ 169 * q ^ 2 / (72 * (c0lo ql : ℝ)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  calc 2 * c0 q * capacity z = 2 * c0 q * z ^ 2 * (SmallMean.Cn z / z ^ 2) := by
        rw [hcapz]; field_simp
    _ ≤ 2 * c0 q * z ^ 2 * (SmallMean.Cn (zr : ℝ) / (zr : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ 169 * q ^ 2 / (72 * (c0lo ql : ℝ)) * (SmallMean.Cn (zr : ℝ) / (zr : ℝ) ^ 2) := by
        rw [hsq]; exact mul_le_mul_of_nonneg_right hsq_le hR0
    _ ≤ 169 * q ^ 2 / (72 * (c0lo ql : ℝ)) *
        ((((1 + (zr : ℝ)) * (cp.hi : ℝ) + (1 - (zr : ℝ)) * (cm.hi : ℝ)) / 2) / (zr : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hK (sq_nonneg _)) (by positivity)
    _ = q ^ 2 * (169 / (72 * (c0lo ql : ℝ)) *
        (((1 + (zr : ℝ)) * (cp.hi : ℝ) + (1 - (zr : ℝ)) * (cm.hi : ℝ)) / 2) / (zr : ℝ) ^ 2) := by
        ring
    _ ≤ q ^ 2 * (40 / 11) := mul_le_mul_of_nonneg_left racc (sq_nonneg q)
    _ = (40 / 11) * q ^ 2 := by ring

end CKLaneN4

end


