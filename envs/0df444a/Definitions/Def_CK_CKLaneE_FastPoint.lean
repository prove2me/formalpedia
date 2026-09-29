-- Prove2me | Definitions.Def_CK_CKLaneE_FastPoint
-- name    : CK_CKLaneE_FastPoint
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:02:13.566268+00:00
-- url     : https://prove2.me/theorems/9bf9c6b2-dfcb-4023-b720-0fb44d9430dd
-- title:
--   Courtade–Kumar proof module `CKLaneE.FastPoint` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.FastPoint` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.FastPoint` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.FastPoint (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/FastPoint.lean)

import Definitions.Def_CK_CKLaneE_FastLog
import Definitions.Def_CK_CKLaneE_SlopeBounds

-- ===== source module CKLaneE.FastPoint =====
section

/-!
# Lane E: fast rational-point enclosures of `log`, `H`, slope anchors and `J`

`log (num/den)` for `0 < num ≤ den`: with `e` such that `num·2^e ≤ den`, put
`u = den - num·2^e`, `v = den + num·2^e`, `x = u/v ∈ [0,1)`; then
`log(num/den) = -e·log 2 - log((1+x)/(1-x))`, both terms enclosed by `CKLaneE.FL`.
All executable values are integers over the fixed scale `T = 2^48`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE.FP

open GeneralCK CKLaneE.FL

/-- Literal bounds for `serLo 1 3 L2n` / `serHi 1 3 L2n` (verified once by the kernel). -/
def L2lo : ℕ := 97551793252578
def L2hi : ℕ := 97551793252610

theorem L2lo_le : L2lo ≤ serLo 1 3 L2n := by decide +kernel
theorem L2hi_ge : serHi 1 3 L2n ≤ L2hi := by decide +kernel

theorem log_two_fp : 2 * (L2lo : ℝ) / T ≤ Real.log 2 ∧ Real.log 2 ≤ 2 * (L2hi : ℝ) / T := by
  obtain ⟨h1, h2⟩ := log_two_bounds
  have hT : (0 : ℝ) < T := by exact_mod_cast T_pos
  have a1 : (L2lo : ℝ) ≤ serLo 1 3 L2n := by exact_mod_cast L2lo_le
  have a2 : (serHi 1 3 L2n : ℝ) ≤ L2hi := by exact_mod_cast L2hi_ge
  constructor
  · calc 2 * (L2lo : ℝ) / T ≤ 2 * (serLo 1 3 L2n : ℝ) / T := by
          apply div_le_div_of_nonneg_right _ hT.le; linarith
      _ ≤ _ := h1
  · calc Real.log 2 ≤ 2 * (serHi 1 3 L2n : ℝ) / T := h2
      _ ≤ 2 * (L2hi : ℝ) / T := by apply div_le_div_of_nonneg_right _ hT.le; linarith

def redExp : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, e => e
  | fuel + 1, num, den, e =>
      if num * 2 ^ (e + 1) ≤ den then redExp fuel num den (e + 1) else e

def expOf (num den : ℕ) : ℕ := redExp 64 num den 0

def nterms : ℕ := 12

/-- Fixed-point (over `T`) lower bound of `log(num/den)`. -/
def logLoZ (num den : ℕ) : ℤ :=
  -((expOf num den : ℤ) * (2 * (L2hi : ℤ)) +
    2 * (serHi (den - num * 2 ^ expOf num den) (den + num * 2 ^ expOf num den) nterms : ℤ))

/-- Fixed-point (over `T`) upper bound of `log(num/den)`. -/
def logHiZ (num den : ℕ) : ℤ :=
  -((expOf num den : ℤ) * (2 * (L2lo : ℤ)) +
    2 * (serLo (den - num * 2 ^ expOf num den) (den + num * 2 ^ expOf num den) nterms : ℤ))

def logOk (num den : ℕ) : Bool := decide (0 < num ∧ num * 2 ^ expOf num den ≤ den)

theorem log_bounds {num den : ℕ} (h : logOk num den = true) :
    (logLoZ num den : ℝ) / T ≤ Real.log ((num : ℝ) / den) ∧
      Real.log ((num : ℝ) / den) ≤ (logHiZ num den : ℝ) / T := by
  simp only [logOk, decide_eq_true_eq] at h
  obtain ⟨hnum, hle⟩ := h
  simp only [logLoZ, logHiZ]
  set e := expOf num den with he
  set u := den - num * 2 ^ e with hu
  set v := den + num * 2 ^ e with hv
  have hpow : 0 < num * 2 ^ e := Nat.mul_pos hnum (by positivity)
  have hden : 0 < den := lt_of_lt_of_le hpow hle
  have huv : u < v := by omega
  obtain ⟨s1, s2⟩ := ser_bounds huv nterms
  obtain ⟨l1, l2⟩ := log_two_fp
  have hT : (0 : ℝ) < T := by exact_mod_cast T_pos
  have hucast : (u : ℝ) = den - num * 2 ^ e := by rw [hu]; push_cast [Nat.cast_sub hle]; ring
  have hvcast : (v : ℝ) = den + num * 2 ^ e := by rw [hv]; push_cast; ring
  have hnumR : (0 : ℝ) < num := by exact_mod_cast hnum
  have hdenR : (0 : ℝ) < den := by exact_mod_cast hden
  have hp2 : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  have hratio : (1 + (u : ℝ) / v) / (1 - (u : ℝ) / v) = (den : ℝ) / (num * 2 ^ e) := by
    rw [hucast, hvcast]
    have hne : (den : ℝ) + num * 2 ^ e ≠ 0 := by positivity
    field_simp
    ring
  rw [hratio] at s1 s2
  have hlog : Real.log ((num : ℝ) / den) =
      -((e : ℝ) * Real.log 2 + Real.log ((den : ℝ) / (num * 2 ^ e))) := by
    rw [Real.log_div hnumR.ne' hdenR.ne', Real.log_div hdenR.ne' (by positivity),
      Real.log_mul hnumR.ne' hp2.ne', Real.log_pow]
    ring
  rw [hlog]
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  -- scaled forms
  have s1' : (serLo u v nterms : ℝ) ≤ 1 / 2 * Real.log ((den : ℝ) / (num * 2 ^ e)) * T := by
    rw [div_le_iff₀ hT] at s1; exact s1
  have s2' : 1 / 2 * Real.log ((den : ℝ) / (num * 2 ^ e)) * T ≤ (serHi u v nterms : ℝ) := by
    rw [le_div_iff₀ hT] at s2; exact s2
  have l1' : 2 * (L2lo : ℝ) ≤ Real.log 2 * T := by rw [div_le_iff₀ hT] at l1; exact l1
  have l2' : Real.log 2 * T ≤ 2 * (L2hi : ℝ) := by rw [le_div_iff₀ hT] at l2; exact l2
  have m1 := mul_le_mul_of_nonneg_left l1' he0
  have m2 := mul_le_mul_of_nonneg_left l2' he0
  constructor
  · rw [div_le_iff₀ hT]
    push_cast
    nlinarith [m2, s2']
  · rw [le_div_iff₀ hT]
    push_cast
    nlinarith [m1, s1']

/-! ## Rational points `q ∈ (0,1)` -/

def ptOk (q : ℚ) : Bool :=
  decide (0 < q ∧ q < 1) && logOk q.num.toNat q.den && logOk (q.den - q.num.toNat) q.den

def lLo (q : ℚ) : ℚ := (logLoZ q.num.toNat q.den : ℚ) / T
def lHi (q : ℚ) : ℚ := (logHiZ q.num.toNat q.den : ℚ) / T
def l1Lo (q : ℚ) : ℚ := (logLoZ (q.den - q.num.toNat) q.den : ℚ) / T
def l1Hi (q : ℚ) : ℚ := (logHiZ (q.den - q.num.toNat) q.den : ℚ) / T

theorem ptOk_pos {q : ℚ} (h : ptOk q = true) : 0 < q ∧ q < 1 := by
  simp only [ptOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem cast_num_toNat {q : ℚ} (hq : 0 < q) : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
  have h0 : 0 ≤ q.num := (Rat.num_pos.mpr hq).le
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]

theorem num_toNat_le_den {q : ℚ} (hq : 0 < q) (hq1 : q < 1) : q.num.toNat ≤ q.den := by
  have h0 : 0 ≤ q.num := (Rat.num_pos.mpr hq).le
  have hlt : q.num < q.den := Rat.num_lt_denom_iff.mpr hq1
  omega

theorem toQ_cast (z : ℤ) : (((z : ℚ) / T : ℚ) : ℝ) = (z : ℝ) / T := by push_cast; ring

theorem ptOk_sound {q : ℚ} (h : ptOk q = true) :
    ((lLo q : ℚ) : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ ((lHi q : ℚ) : ℝ) ∧
    ((l1Lo q : ℚ) : ℝ) ≤ Real.log (1 - (q : ℝ)) ∧ Real.log (1 - (q : ℝ)) ≤ ((l1Hi q : ℚ) : ℝ) := by
  have hq := ptOk_pos h
  simp only [ptOk, Bool.and_eq_true] at h
  have h1 := log_bounds h.1.2
  have h2 := log_bounds h.2
  have hq_eq : (q : ℝ) = ((q.num.toNat : ℕ) : ℝ) / q.den := by
    rw [cast_num_toNat hq.1, Rat.cast_def]
  have hq1_eq : 1 - (q : ℝ) = (((q.den - q.num.toNat : ℕ) : ℕ) : ℝ) / q.den := by
    have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    rw [Nat.cast_sub (num_toNat_le_den hq.1 hq.2), cast_num_toNat hq.1, Rat.cast_def]
    field_simp
  rw [← hq_eq] at h1
  rw [← hq1_eq] at h2
  simp only [lLo, lHi, l1Lo, l1Hi, toQ_cast]
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

/-! ## Binary entropy -/

/-- Rational bounds on `log 2` (derived from the fixed-point constants). -/
def LqLo : ℚ := 2 * (L2lo : ℚ) / T
def LqHi : ℚ := 2 * (L2hi : ℚ) / T

theorem log_two_mem : ((LqLo : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((LqHi : ℚ) : ℝ) := by
  obtain ⟨h1, h2⟩ := log_two_fp
  constructor
  · simp only [LqLo]; push_cast; exact h1
  · simp only [LqHi]; push_cast; exact h2

theorem LqLo_pos : (0 : ℝ) < ((LqLo : ℚ) : ℝ) := by
  have : (0 : ℚ) < LqLo := by decide +kernel
  exact_mod_cast this

def HnumLo (q : ℚ) : ℚ := -(q * lHi q) - (1 - q) * l1Hi q
def HnumHi (q : ℚ) : ℚ := -(q * lLo q) - (1 - q) * l1Lo q
def Hlo (q : ℚ) : ℚ := if 0 ≤ HnumLo q then HnumLo q / LqHi else 0
def Hhi (q : ℚ) : ℚ := HnumHi q / LqLo

theorem H_bounds {q : ℚ} (h : ptOk q = true) :
    ((Hlo q : ℚ) : ℝ) ≤ H (q : ℝ) ∧ H (q : ℝ) ≤ ((Hhi q : ℚ) : ℝ) := by
  have hq := ptOk_pos h
  obtain ⟨h1, h2, h3, h4⟩ := ptOk_sound h
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.1
  have hq1 : (q : ℝ) < 1 := by exact_mod_cast hq.2
  obtain ⟨hL1, hL2⟩ := log_two_mem
  have hL : 0 < Real.log 2 := log_two_pos
  have hLlo := LqLo_pos
  set N : ℝ := -((q : ℝ) * Real.log q) - (1 - (q : ℝ)) * Real.log (1 - q) with hN
  have hHN : H (q : ℝ) = N / Real.log 2 := by rw [H_eq_logs]
  have hNlo : ((HnumLo q : ℚ) : ℝ) ≤ N := by
    simp only [HnumLo]; push_cast
    have a1 := mul_le_mul_of_nonneg_left h2 hq0.le
    have a2 := mul_le_mul_of_nonneg_left h4 (by linarith : (0 : ℝ) ≤ 1 - q)
    linarith
  have hNhi : N ≤ ((HnumHi q : ℚ) : ℝ) := by
    simp only [HnumHi]; push_cast
    have a1 := mul_le_mul_of_nonneg_left h1 hq0.le
    have a2 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 1 - q)
    linarith
  have hHnn : 0 ≤ H (q : ℝ) := H_nonneg hq0.le hq1.le
  have hNnn : 0 ≤ N := by
    have := hHnn; rw [hHN] at this
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hL))
  constructor
  · simp only [Hlo]
    split_ifs with hc
    · push_cast
      rw [hHN]
      have hc' : (0 : ℝ) ≤ ((HnumLo q : ℚ) : ℝ) := by exact_mod_cast hc
      calc ((HnumLo q : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) ≤ ((HnumLo q : ℚ) : ℝ) / Real.log 2 :=
            div_le_div_of_nonneg_left hc' hL hL2
        _ ≤ N / Real.log 2 := div_le_div_of_nonneg_right hNlo hL.le
    · simpa using hHnn
  · simp only [Hhi]; push_cast
    rw [hHN]
    have hhnn : (0 : ℝ) ≤ ((HnumHi q : ℚ) : ℝ) := hNnn.trans hNhi
    calc N / Real.log 2 ≤ ((HnumHi q : ℚ) : ℝ) / Real.log 2 := div_le_div_of_nonneg_right hNhi hL.le
      _ ≤ ((HnumHi q : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) := div_le_div_of_nonneg_left hhnn hLlo hL1

/-! ## Slope anchors and `J` bounds -/

/-- Lower bound of `log((1-v)/v)`. -/
def lamLo (v : ℚ) : ℚ := l1Lo v - lHi v
/-- Upper bound of `log((1-v)/v)`. -/
def lamHi (v : ℚ) : ℚ := l1Hi v - lLo v
def P1up (v : ℚ) : ℚ := 2 + (1 - 2 * v) / (v * (1 - v) * lamLo v)

def anchorOk (v y : ℚ) : Bool :=
  ptOk v && decide (v < 1 / 2 ∧ 0 < lamLo v ∧ Hhi v ≤ 1 - y)

theorem lam_bounds {v : ℚ} (h : ptOk v = true) :
    ((lamLo v : ℚ) : ℝ) ≤ Real.log ((1 - (v : ℝ)) / v) ∧
      Real.log ((1 - (v : ℝ)) / v) ≤ ((lamHi v : ℚ) : ℝ) := by
  have hv := ptOk_pos h
  obtain ⟨h1, h2, h3, h4⟩ := ptOk_sound h
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv.1
  have hv1 : (v : ℝ) < 1 := by exact_mod_cast hv.2
  rw [Real.log_div (by linarith) hv0.ne']
  simp only [lamLo, lamHi]; push_cast
  constructor <;> linarith

theorem anchorOk_sound {v y : ℚ} (h : anchorOk v y = true) {x : ℝ} (hx0 : 0 ≤ x)
    (hxy : x ≤ (y : ℝ)) : Scalar.P1 x ≤ ((P1up v : ℚ) : ℝ) := by
  simp only [anchorOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hpt, hv2, hlam, hH⟩ := h
  have hv := ptOk_pos hpt
  obtain ⟨_, hHhi⟩ := H_bounds hpt
  obtain ⟨hlog, _⟩ := lam_bounds hpt
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv.1
  have hv12 : (v : ℝ) < 1 / 2 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hv2
    push_cast at h
    linarith
  have hHq : ((Hhi v : ℚ) : ℝ) ≤ 1 - (y : ℝ) := by exact_mod_cast hH
  have hxv : x ≤ 1 - H (v : ℝ) := by linarith
  have hA := P1_le_anchor hv0 hv12 hx0 hxv
  have hlamR : (0 : ℝ) < ((lamLo v : ℚ) : ℝ) := by exact_mod_cast hlam
  have hvv : (0 : ℝ) < (v : ℝ) * (1 - v) := by nlinarith
  have hnum : (0 : ℝ) ≤ 1 - 2 * (v : ℝ) := by linarith
  have hfrac : (1 - 2 * (v : ℝ)) / ((v : ℝ) * (1 - v) * Real.log ((1 - v) / v)) ≤
      (1 - 2 * (v : ℝ)) / ((v : ℝ) * (1 - v) * ((lamLo v : ℚ) : ℝ)) := by
    apply div_le_div_of_nonneg_left hnum (by positivity)
    exact mul_le_mul_of_nonneg_left hlog hvv.le
  have heq : ((P1up v : ℚ) : ℝ) =
      2 + (1 - 2 * (v : ℝ)) / ((v : ℝ) * (1 - v) * ((lamLo v : ℚ) : ℝ)) := by
    simp only [P1up]; push_cast; ring
  rw [heq]
  linarith

end CKLaneE.FP

#check @CKLaneE.FP.log_bounds
#check @CKLaneE.FP.ptOk_sound
#check @CKLaneE.FP.H_bounds
#check @CKLaneE.FP.lam_bounds
#check @CKLaneE.FP.anchorOk_sound
#print axioms CKLaneE.FP.log_bounds
#print axioms CKLaneE.FP.H_bounds
#print axioms CKLaneE.FP.anchorOk_sound

end


