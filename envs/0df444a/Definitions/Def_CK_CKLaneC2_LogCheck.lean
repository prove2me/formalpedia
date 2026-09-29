-- Prove2me | Definitions.Def_CK_CKLaneC2_LogCheck
-- name    : CK_CKLaneC2_LogCheck
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:29:59.047304+00:00
-- url     : https://prove2.me/theorems/55c1950e-c433-4bfd-be7f-d199584008ae
-- title:
--   Courtade–Kumar proof module `CKLaneC2.LogCheck` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2.LogCheck` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2.LogCheck` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2.LogCheck (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2/LogCheck.lean)

import Definitions.Def_CK_CKLaneC2_QI

-- ===== source module CKLaneC2.LogCheck =====
section
/-
Lane C2 — verified rational enclosures of `Real.log`.

`atSum w n = Σ_{i<n} w^(2i+1)/(2i+1)` (structural recursion, kernel-evaluable).
Mathlib gives, for `0 ≤ w < 1`,
    atSum w n ≤ (1/2) log((1+w)/(1-w)) ≤ atSum w n + w^(2n+1)/(1-w^2).
`logChk Llo Lhi q k n lo hi` accepts iff, with `q' = q/2^k ≥ 1` and `w = (q'-1)/(q'+1)`,
    lo ≤ k·Llo + 2·atSum w n   and   k·Lhi + 2·atSum w n + 2 w^(2n+1)/(1-w^2) ≤ hi.
Given `Llo ≤ log 2 ≤ Lhi` this certifies `lo ≤ log q ≤ hi` (`logChk_sound`).
The `log 2` enclosure itself is certified from `w = 1/3` (`log2_mem`).
-/

set_option autoImplicit false

namespace CKLaneC2

/-- `Σ_{i<n} w^(2i+1)/(2i+1)`. -/
def atSum (w : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => atSum w n + w ^ (2 * n + 1) / (2 * n + 1)

theorem atSum_cast (w : ℚ) (n : ℕ) :
    ((atSum w n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (w : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1) := by
  induction n with
  | zero => simp [atSum]
  | succ n ih =>
      rw [atSum, Finset.sum_range_succ, ← ih]
      push_cast
      ring

/-- Two-sided enclosure of `log((1+w)/(1-w))` for rational `0 ≤ w < 1`. -/
theorem log_artanh_bounds {w : ℚ} (hw0 : 0 ≤ w) (hw1 : w < 1) (n : ℕ) :
    2 * ((atSum w n : ℚ) : ℝ) ≤ Real.log ((1 + (w : ℝ)) / (1 - (w : ℝ))) ∧
    Real.log ((1 + (w : ℝ)) / (1 - (w : ℝ))) ≤
      2 * ((atSum w n : ℚ) : ℝ) + 2 * ((w : ℝ) ^ (2 * n + 1) / (1 - (w : ℝ) ^ 2)) := by
  have h0 : (0 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw0
  have h1 : (w : ℝ) < 1 := by exact_mod_cast hw1
  have lo := Real.sum_range_le_log_div h0 h1 n
  have hi := Real.log_div_le_sum_range_add h0 h1 n
  rw [atSum_cast]
  constructor <;> linarith

/-- The rational log checker (range reduction by `2^k`, `q ≥ 1` only). -/
def logChk (Llo Lhi q : ℚ) (k n : ℕ) (lo hi : ℚ) : Bool :=
  decide (1 ≤ q / 2 ^ k ∧
    lo ≤ (k : ℚ) * Llo + 2 * atSum ((q / 2 ^ k - 1) / (q / 2 ^ k + 1)) n ∧
    (k : ℚ) * Lhi + 2 * atSum ((q / 2 ^ k - 1) / (q / 2 ^ k + 1)) n +
      2 * (((q / 2 ^ k - 1) / (q / 2 ^ k + 1)) ^ (2 * n + 1) /
        (1 - ((q / 2 ^ k - 1) / (q / 2 ^ k + 1)) ^ 2)) ≤ hi)

theorem logChk_sound {Llo Lhi q lo hi : ℚ} {k n : ℕ}
    (hL : (Llo : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (Lhi : ℝ))
    (h : logChk Llo Lhi q k n lo hi = true) :
    (lo : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (hi : ℝ) := by
  unfold logChk at h
  obtain ⟨hq, hlo, hhi⟩ := of_decide_eq_true h
  set q' : ℚ := q / 2 ^ k with hq'
  set w : ℚ := (q' - 1) / (q' + 1) with hw
  have hq'pos : (0 : ℚ) < q' + 1 := by linarith
  have hw0 : 0 ≤ w := by rw [hw]; apply div_nonneg <;> linarith
  have hw1 : w < 1 := by rw [hw, div_lt_one hq'pos]; linarith
  obtain ⟨b1, b2⟩ := log_artanh_bounds hw0 hw1 n
  -- (1+w)/(1-w) = q'
  have hratio : (1 + (w : ℝ)) / (1 - (w : ℝ)) = (q' : ℝ) := by
    have hq'posR : (0 : ℝ) < (q' : ℝ) + 1 := by exact_mod_cast hq'pos
    rw [hw]; push_cast
    field_simp
    ring
  rw [hratio] at b1 b2
  -- q = 2^k * q'
  have hqeq : (q : ℝ) = (2 : ℝ) ^ k * (q' : ℝ) := by
    rw [hq']; push_cast; field_simp
  have hq'posR : (0 : ℝ) < (q' : ℝ) := by
    have : (1 : ℝ) ≤ (q' : ℝ) := by exact_mod_cast hq
    linarith
  have hlog : Real.log (q : ℝ) = (k : ℝ) * Real.log 2 + Real.log (q' : ℝ) := by
    rw [hqeq, Real.log_mul (by positivity) hq'posR.ne', Real.log_pow]
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hkL1 : (k : ℝ) * (Llo : ℝ) ≤ (k : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left hL.1 hk0
  have hkL2 : (k : ℝ) * Real.log 2 ≤ (k : ℝ) * (Lhi : ℝ) := mul_le_mul_of_nonneg_left hL.2 hk0
  have hloR : (lo : ℝ) ≤ (k : ℝ) * (Llo : ℝ) + 2 * ((atSum w n : ℚ) : ℝ) := by exact_mod_cast hlo
  have hhiR : (k : ℝ) * (Lhi : ℝ) + 2 * ((atSum w n : ℚ) : ℝ) +
      2 * ((w : ℝ) ^ (2 * n + 1) / (1 - (w : ℝ) ^ 2)) ≤ (hi : ℝ) := by exact_mod_cast hhi
  rw [hlog]
  constructor <;> linarith

/-- The certified `log 2` enclosure (from `w = 1/3`, 40 terms). -/
def Llo : ℚ := 2 * atSum (1 / 3) 40
def Lhi : ℚ := 2 * atSum (1 / 3) 40 + 2 * ((1 / 3 : ℚ) ^ 81 / (1 - (1 / 3 : ℚ) ^ 2))

theorem log2_bounds : (Llo : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (Lhi : ℝ) := by
  have h := log_artanh_bounds (w := 1 / 3) (by norm_num) (by norm_num) 40
  have e : (1 + ((1 / 3 : ℚ) : ℝ)) / (1 - ((1 / 3 : ℚ) : ℝ)) = 2 := by norm_num
  rw [e] at h
  unfold Llo Lhi
  push_cast
  push_cast at h
  constructor <;> linarith [h.1, h.2]

theorem log2_mem : QI.Mem (Real.log 2) ⟨Llo, Lhi⟩ := log2_bounds

/-- Positive control: a genuine enclosure of `log 3` is accepted ... -/
theorem logChk_pos_control : logChk Llo Lhi 3 1 20 (10986122886 / 10000000000) (10986122887 / 10000000000) = true := by
  decide +kernel

/-- ... and a corrupted one (upper end below `log 3 = 1.0986122886681...`) is rejected. -/
theorem logChk_neg_control : logChk Llo Lhi 3 1 20 (10986122886 / 10000000000) (10986122885 / 10000000000) = false := by
  decide +kernel

end CKLaneC2

end


