-- Prove2me | Definitions.Def_CK_CKLaneD_LogCert
-- name    : CK_CKLaneD_LogCert
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:50:19.558916+00:00
-- url     : https://prove2.me/theorems/a4936df1-f198-4032-bb94-51ed0e44c300
-- title:
--   Courtade–Kumar proof module `CKLaneD.LogCert` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneD.LogCert` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneD.LogCert` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneD.LogCert (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneD/LogCert.lean)

import Definitions.Def_CK_GeneralCK_Certificates_LogBounds

-- ===== source module CKLaneD.LogCert =====
section

/-!
# Lane D: exact rational logarithm certificates

`checkLogCert x c` certifies `c.lo ≤ log x ≤ c.hi` for a rational `0 < x`, using the
range reduction `x * 2^k = r` and the atanh series of `GeneralCK.Certificates` at
`w = |r - 1| / (r + 1)`.  Everything is exact rational arithmetic.
-/

namespace CKLaneD

open GeneralCK.Certificates

/-- Rational lower bound for `log 2`. -/
def L0 : ℚ := 6864597183463434168892683891 / 9903520314283042199192993792
/-- Rational upper bound for `log 2`. -/
def L1 : ℚ := 878668439483319573618263538049 / 1267650600228229401496703205376

theorem checkLog_two : checkLog (1 / 3) 40 L0 L1 = true := by decide +kernel

theorem log2_bounds : (L0 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (L1 : ℝ) := by
  have h := checkLog_sound checkLog_two
  have h2 : (1 + ((1 / 3 : ℚ) : ℝ)) / (1 - ((1 / 3 : ℚ) : ℝ)) = 2 := by norm_num
  rw [h2] at h
  exact h

theorem L0_pos : (0 : ℚ) < L0 := by decide +kernel

theorem L0_pos_real : (0 : ℝ) < (L0 : ℝ) := by exact_mod_cast L0_pos

/-- A logarithm certificate: range-reduction exponent, series length, claimed bounds. -/
structure LogCert where
  k : ℕ
  n : ℕ
  lo : ℚ
  hi : ℚ
  deriving Repr, DecidableEq

/-- The atanh argument for a ratio `r > 0`. -/
def logW (r : ℚ) : ℚ := if 1 ≤ r then (r - 1) / (r + 1) else (1 - r) / (1 + r)

/-- The certified lower bound for `log x` computed from the certificate data. -/
def certLo (x : ℚ) (c : LogCert) : ℚ :=
  if 1 ≤ x * 2 ^ c.k then -(c.k : ℚ) * L1 + logLower (logW (x * 2 ^ c.k)) c.n
  else -(c.k : ℚ) * L1 - logUpper (logW (x * 2 ^ c.k)) c.n

/-- The certified upper bound for `log x` computed from the certificate data. -/
def certHi (x : ℚ) (c : LogCert) : ℚ :=
  if 1 ≤ x * 2 ^ c.k then -(c.k : ℚ) * L0 + logUpper (logW (x * 2 ^ c.k)) c.n
  else -(c.k : ℚ) * L0 - logLower (logW (x * 2 ^ c.k)) c.n

/-- Executable acceptance test for a logarithm certificate. -/
def checkLogCert (x : ℚ) (c : LogCert) : Bool :=
  decide (0 < x) && decide (c.lo ≤ certLo x c) && decide (certHi x c ≤ c.hi)

theorem logW_nonneg {r : ℚ} (hr : 0 < r) : 0 ≤ logW r := by
  unfold logW
  split_ifs with h
  · exact div_nonneg (by linarith) (by linarith)
  · exact div_nonneg (by linarith) (by linarith)

theorem logW_lt_one {r : ℚ} (hr : 0 < r) : logW r < 1 := by
  unfold logW
  split_ifs with h
  · rw [div_lt_one (by linarith)]; linarith
  · rw [div_lt_one (by linarith)]; linarith

/-- `log ((1+w)/(1-w))` recovers `log r` (resp. `-log r`) for the two branches. -/
theorem log_ratio_logW {r : ℚ} (hr : 0 < r) :
    Real.log ((1 + ((logW r : ℚ) : ℝ)) / (1 - ((logW r : ℚ) : ℝ))) =
      if 1 ≤ r then Real.log (r : ℝ) else -Real.log (r : ℝ) := by
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  unfold logW
  split_ifs with h
  · push_cast
    have h1 : (1 : ℝ) + ((r : ℝ) - 1) / ((r : ℝ) + 1) = 2 * r / (r + 1) := by
      field_simp; ring
    have h2 : (1 : ℝ) - ((r : ℝ) - 1) / ((r : ℝ) + 1) = 2 / (r + 1) := by
      field_simp; ring
    rw [h1, h2]
    congr 1
    field_simp
  · push_cast
    have h1 : (1 : ℝ) + (1 - (r : ℝ)) / (1 + (r : ℝ)) = 2 / (1 + r) := by
      field_simp; ring
    have h2 : (1 : ℝ) - (1 - (r : ℝ)) / (1 + (r : ℝ)) = 2 * r / (1 + r) := by
      field_simp; ring
    rw [h1, h2]
    have h3 : (2 : ℝ) / (1 + r) / (2 * r / (1 + r)) = (r : ℝ)⁻¹ := by
      field_simp
    rw [h3, Real.log_inv]

theorem series_bounds (w : ℚ) (n : ℕ) (hw0 : 0 ≤ w) (hw1 : w < 1) :
    ((logLower w n : ℚ) : ℝ) ≤ Real.log ((1 + (w : ℝ)) / (1 - (w : ℝ))) ∧
      Real.log ((1 + (w : ℝ)) / (1 - (w : ℝ))) ≤ ((logUpper w n : ℚ) : ℝ) := by
  apply checkLog_sound
  unfold checkLog
  simp only [decide_eq_true_eq]
  exact ⟨hw0, hw1, le_rfl, le_rfl⟩

theorem checkLogCert_sound {x : ℚ} {c : LogCert} (h : checkLogCert x c = true) :
    (c.lo : ℝ) ≤ Real.log (x : ℝ) ∧ Real.log (x : ℝ) ≤ (c.hi : ℝ) := by
  unfold checkLogCert at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hx, hlo⟩, hhi⟩ := h
  set r : ℚ := x * 2 ^ c.k with hr_def
  have hr : 0 < r := by positivity
  have hw0 := logW_nonneg hr
  have hw1 := logW_lt_one hr
  have hs := series_bounds (logW r) c.n hw0 hw1
  have hlr := log_ratio_logW hr
  have hxr : Real.log (x : ℝ) = Real.log (r : ℝ) - (c.k : ℝ) * Real.log 2 := by
    have hx' : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    rw [hr_def]
    push_cast
    rw [Real.log_mul hx'.ne' (by positivity), Real.log_pow]
    ring
  have hL := log2_bounds
  have hk : (0 : ℝ) ≤ (c.k : ℝ) := Nat.cast_nonneg _
  have hk1 : (c.k : ℝ) * (L0 : ℝ) ≤ (c.k : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left hL.1 hk
  have hk2 : (c.k : ℝ) * Real.log 2 ≤ (c.k : ℝ) * (L1 : ℝ) := mul_le_mul_of_nonneg_left hL.2 hk
  unfold certLo at hlo
  unfold certHi at hhi
  rw [← hr_def] at hlo hhi
  by_cases h1 : 1 ≤ r
  · rw [if_pos h1] at hlr hlo hhi
    rw [hlr] at hs
    have hlo' : (c.lo : ℝ) ≤ -(c.k : ℝ) * (L1 : ℝ) + ((logLower (logW r) c.n : ℚ) : ℝ) := by
      exact_mod_cast hlo
    have hhi' : -(c.k : ℝ) * (L0 : ℝ) + ((logUpper (logW r) c.n : ℚ) : ℝ) ≤ (c.hi : ℝ) := by
      exact_mod_cast hhi
    constructor <;> nlinarith [hs.1, hs.2]
  · rw [if_neg h1] at hlr hlo hhi
    rw [hlr] at hs
    have hlo' : (c.lo : ℝ) ≤ -(c.k : ℝ) * (L1 : ℝ) - ((logUpper (logW r) c.n : ℚ) : ℝ) := by
      exact_mod_cast hlo
    have hhi' : -(c.k : ℝ) * (L0 : ℝ) - ((logLower (logW r) c.n : ℚ) : ℝ) ≤ (c.hi : ℝ) := by
      exact_mod_cast hhi
    constructor <;> nlinarith [hs.1, hs.2]

end CKLaneD

end


