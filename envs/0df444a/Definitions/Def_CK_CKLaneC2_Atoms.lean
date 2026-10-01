-- Prove2me | Definitions.Def_CK_CKLaneC2_Atoms
-- name    : CK_CKLaneC2_Atoms
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:14:00.163832+00:00
-- url     : https://prove2.me/theorems/85829135-6a62-46bc-8304-c1553df7e510
-- title:
--   Courtade–Kumar proof module `CKLaneC2.Atoms` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2.Atoms` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2.Atoms` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2.Atoms (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2/Atoms.lean)

import Definitions.Def_CK_CKLaneC2_LogCheck
import Definitions.Def_CK_GeneralCK_PureGapE8AnalyticRealBridge

-- ===== source module CKLaneC2.Atoms =====
section
/-
Lane C2 — the four transcendental atoms of the contact parametrisation and their facts.

For `c ∈ (0,1)` (the contact coordinate `c = 1 - 2 v`):
    Af c = log((1+c)/(1-c)),   Bf c = -log(1-c^2),
    Kf c = log 2 + Bf c/2  (= corpus `biasB c`),   Ef c = Kf c - c·Af c/2  (= corpus `biasE c`),
    a1f c = (Af c - 2c)/c^3,   b1f c = (Bf c - c^2)/c^4   (pre-cancelled atoms, → 2/3, 1/2 at 0).
Facts: monotonicity (a1f, b1f via Mathlib's log power series), derivatives, identification with
the corpus functions, and rational point enclosures from `logChk`.
-/

set_option autoImplicit false

namespace CKLaneC2

open GeneralCK Set

noncomputable def Af (c : ℝ) : ℝ := Real.log ((1 + c) / (1 - c))
noncomputable def Bf (c : ℝ) : ℝ := -Real.log (1 - c ^ 2)
noncomputable def Kf (c : ℝ) : ℝ := Real.log 2 + Bf c / 2
noncomputable def Ef (c : ℝ) : ℝ := Real.log 2 + Bf c / 2 - c * Af c / 2
noncomputable def a1f (c : ℝ) : ℝ := (Af c - 2 * c) / c ^ 3
noncomputable def b1f (c : ℝ) : ℝ := (Bf c - c ^ 2) / c ^ 4

theorem log_two_pos' : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

/-! ### identification with corpus functions -/

theorem Kf_eq_biasB (c : ℝ) : Kf c = Certificates.Reflection.biasB c := by
  unfold Kf Bf Certificates.Reflection.biasB
  rw [sq]; ring

theorem Ef_eq_biasE {c : ℝ} (h0 : -1 < c) (h1 : c < 1) :
    Ef c = Certificates.Reflection.biasE c := by
  have hp : (0 : ℝ) < 1 + c := by linarith
  have hm : (0 : ℝ) < 1 - c := by linarith
  unfold Ef Bf Af Certificates.Reflection.biasE
  rw [show (1 : ℝ) - c ^ 2 = (1 + c) * (1 - c) by ring, Real.log_mul hp.ne' hm.ne',
    Real.log_div hp.ne' hm.ne']
  ring

theorem Af_eq_two_A (c : ℝ) : Af c = 2 * SmallMean.A c := by
  unfold Af SmallMean.A; ring

/-! ### positivity -/

theorem Bf_nonneg {c : ℝ} (h0 : 0 ≤ c) (h1 : c < 1) : 0 ≤ Bf c := by
  unfold Bf
  have hpos : (0 : ℝ) < 1 - c ^ 2 := by nlinarith
  have hle : 1 - c ^ 2 ≤ 1 := by nlinarith
  have := Real.log_nonpos hpos.le hle
  linarith

theorem Kf_pos {c : ℝ} (h0 : 0 ≤ c) (h1 : c < 1) : 0 < Kf c := by
  unfold Kf; have := Bf_nonneg h0 h1; have := log_two_pos'; linarith

theorem Ef_pos {c : ℝ} (h0 : 0 ≤ c) (h1 : c < 1) : 0 < Ef c := by
  rw [Ef_eq_biasE (by linarith) h1]
  exact GeneralCK.Reflection.biasE_pos_wide (by linarith) h1

theorem two_Kf_sub_pos {c : ℝ} (h0 : 0 ≤ c) (h1 : c < 1) : 0 < 2 * Kf c - c ^ 2 := by
  have hB := Bf_nonneg h0 h1
  have hL : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  unfold Kf
  nlinarith

/-! ### monotonicity -/

theorem Af_mono {x y : ℝ} (hx : -1 < x) (hxy : x ≤ y) (hy : y < 1) : Af x ≤ Af y := by
  unfold Af
  have h1 : (0 : ℝ) < 1 - x := by linarith
  have h2 : (0 : ℝ) < 1 - y := by linarith
  apply Real.log_le_log (div_pos (by linarith) h1)
  rw [div_le_div_iff₀ h1 h2]
  nlinarith

theorem Bf_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) : Bf x ≤ Bf y := by
  unfold Bf
  have h2 : (0 : ℝ) < 1 - y ^ 2 := by nlinarith
  have := Real.log_le_log h2 (show 1 - y ^ 2 ≤ 1 - x ^ 2 by nlinarith)
  linarith

theorem Kf_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) : Kf x ≤ Kf y := by
  unfold Kf; have := Bf_mono hx hxy hy; linarith

theorem Ef_anti {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) : Ef y ≤ Ef x := by
  rw [Ef_eq_biasE (c := x) (by linarith) (by linarith), Ef_eq_biasE (c := y) (by linarith) hy]
  exact Certificates.Reflection.biasE_antitone ⟨hx, by linarith⟩ ⟨by linarith, hy.le⟩ hxy

/-- Power series of the pre-cancelled atom `a1f`. -/
theorem hasSum_a1f {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => 2 / (2 * (n : ℝ) + 3) * x ^ (2 * n)) (a1f x) := by
  have habs : |x| < 1 := by rw [abs_lt]; constructor <;> linarith
  have h := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have h1 := (hasSum_nat_add_iff' 1).mpr h
  have hA : Real.log (1 + x) - Real.log (1 - x) = Af x := by
    unfold Af; rw [Real.log_div (by linarith) (by linarith)]
  rw [hA] at h1
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, zero_add,
    div_one, pow_one, mul_one] at h1
  have h2 := h1.div_const (x ^ 3)
  have hfun : (fun n : ℕ => 2 * (1 / (2 * ((n + 1 : ℕ) : ℝ) + 1)) * x ^ (2 * (n + 1) + 1) / x ^ 3)
      = (fun n : ℕ => 2 / (2 * (n : ℝ) + 3) * x ^ (2 * n)) := by
    funext n
    have hx3 : x ^ 3 ≠ 0 := by positivity
    rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring, pow_add]
    push_cast
    field_simp
    ring
  rw [hfun] at h2
  simpa [a1f] using h2

theorem a1f_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) : a1f x ≤ a1f y := by
  refine hasSum_le (fun n => ?_) (hasSum_a1f hx (lt_of_le_of_lt hxy hy)) (hasSum_a1f (lt_of_lt_of_le hx hxy) hy)
  apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.le hxy _)
  positivity

/-- Power series of the pre-cancelled atom `b1f`. -/
theorem hasSum_b1f {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => (x ^ 2) ^ n / ((n : ℝ) + 2)) (b1f x) := by
  have habs : |x ^ 2| < 1 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith
  have h := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have h1 := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_add, div_one,
    pow_one] at h1
  have h2 := h1.div_const (x ^ 4)
  have hfun : (fun n : ℕ => (x ^ 2) ^ (n + 1 + 1) / (((n + 1 : ℕ) : ℝ) + 1) / x ^ 4)
      = (fun n : ℕ => (x ^ 2) ^ n / ((n : ℝ) + 2)) := by
    funext n
    have hx4 : x ^ 4 ≠ 0 := by positivity
    rw [show (x ^ 2) ^ (n + 1 + 1) = (x ^ 2) ^ n * x ^ 4 by ring]
    push_cast
    field_simp
    ring
  rw [hfun] at h2
  simpa [b1f, Bf] using h2

theorem b1f_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) : b1f x ≤ b1f y := by
  refine hasSum_le (fun n => ?_) (hasSum_b1f hx (lt_of_le_of_lt hxy hy)) (hasSum_b1f (lt_of_lt_of_le hx hxy) hy)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hx.le hxy 2) _

/-! ### derivatives -/

theorem hasDerivAt_Af {c : ℝ} (h0 : -1 < c) (h1 : c < 1) :
    HasDerivAt Af (2 / (1 - c ^ 2)) c := by
  have hp : (0 : ℝ) < 1 + c := by linarith
  have hm : (0 : ℝ) < 1 - c := by linarith
  have hne1 : (1 : ℝ) - c ≠ 0 := hm.ne'
  have hne2 : (1 : ℝ) + c ≠ 0 := hp.ne'
  have hne3 : (1 : ℝ) - c ^ 2 ≠ 0 := by nlinarith
  have hnum : HasDerivAt (fun y : ℝ => 1 + y) 1 c := (hasDerivAt_id c).const_add 1
  have hden : HasDerivAt (fun y : ℝ => 1 - y) (-1) c := by
    simpa using (hasDerivAt_id c).const_sub 1
  have hq : HasDerivAt (fun y : ℝ => (1 + y) / (1 - y))
      ((1 * (1 - c) - (1 + c) * (-1)) / (1 - c) ^ 2) c := hnum.div hden hm.ne'
  have hl : HasDerivAt (fun y : ℝ => Real.log ((1 + y) / (1 - y)))
      (((1 * (1 - c) - (1 + c) * (-1)) / (1 - c) ^ 2) / ((1 + c) / (1 - c))) c :=
    hq.log (div_pos hp hm).ne'
  refine hl.congr_deriv ?_
  field_simp
  ring

theorem hasDerivAt_Bf {c : ℝ} (h0 : -1 < c) (h1 : c < 1) :
    HasDerivAt Bf (2 * c / (1 - c ^ 2)) c := by
  have hpos : (0 : ℝ) < 1 - c ^ 2 := by nlinarith
  have hin : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * c)) c := by
    simpa using ((hasDerivAt_pow 2 c).const_sub 1)
  have hl : HasDerivAt (fun y : ℝ => -Real.log (1 - y ^ 2)) (-((-(2 * c)) / (1 - c ^ 2))) c :=
    (hin.log hpos.ne').neg
  exact hl.congr_deriv (by ring)

theorem hasDerivAt_Kf {c : ℝ} (h0 : -1 < c) (h1 : c < 1) :
    HasDerivAt Kf (c / (1 - c ^ 2)) c := by
  have h : HasDerivAt (fun y => Real.log 2 + Bf y / 2) (2 * c / (1 - c ^ 2) / 2) c :=
    ((hasDerivAt_Bf h0 h1).div_const 2).const_add _
  exact h.congr_deriv (by ring)

theorem hasDerivAt_Ef {c : ℝ} (h0 : -1 < c) (h1 : c < 1) :
    HasDerivAt Ef (-(Af c) / 2) c := by
  have hB : HasDerivAt (fun y => Bf y / 2) (2 * c / (1 - c ^ 2) / 2) c :=
    (hasDerivAt_Bf h0 h1).div_const 2
  have hA : HasDerivAt (fun y => y * Af y / 2) ((1 * Af c + c * (2 / (1 - c ^ 2))) / 2) c :=
    (HasDerivAt.mul (hasDerivAt_id' (x := c)) (hasDerivAt_Af h0 h1)).div_const 2
  have h : HasDerivAt (fun y => Real.log 2 + Bf y / 2 - y * Af y / 2)
      (2 * c / (1 - c ^ 2) / 2 - (1 * Af c + c * (2 / (1 - c ^ 2))) / 2) c :=
    (hB.const_add _).sub hA
  exact h.congr_deriv (by ring)

/-! ### rational point enclosures -/

theorem Af_bounds {c : ℚ} (h0 : 0 < c) (h1 : c < 1) {k n : ℕ} {lo hi : ℚ}
    (h : logChk Llo Lhi ((1 + c) / (1 - c)) k n lo hi = true) :
    (lo : ℝ) ≤ Af c ∧ Af c ≤ (hi : ℝ) := by
  have := logChk_sound log2_bounds h
  unfold Af
  push_cast at this
  exact this

theorem Bf_bounds {c : ℚ} (h0 : 0 < c) (h1 : c < 1) {k n : ℕ} {lo hi : ℚ}
    (h : logChk Llo Lhi (1 / (1 - c ^ 2)) k n lo hi = true) :
    (lo : ℝ) ≤ Bf c ∧ Bf c ≤ (hi : ℝ) := by
  have := logChk_sound log2_bounds h
  unfold Bf
  push_cast at this
  rw [one_div, Real.log_inv] at this
  exact this

end CKLaneC2

end


