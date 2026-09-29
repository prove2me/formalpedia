-- Prove2me | Definitions.Def_CK_CKLaneP_FastLog
-- name    : CK_CKLaneP_FastLog
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:10:21.946675+00:00
-- url     : https://prove2.me/theorems/db583ff6-24a7-4d2e-a9bf-8d3dcf461bcc
-- title:
--   Courtade–Kumar proof module `CKLaneP.FastLog` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.FastLog` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.FastLog` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.FastLog (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/FastLog.lean)

import Definitions.Def_CK_CKLaneP_LogCheck

-- ===== source module CKLaneP.FastLog =====
section
/-
Lane P — fast certified logarithms of dyadic rationals by fixed-point Nat arithmetic.

`lnDy P Q n N = (lo, hi)` with `lo / 2^Q ≤ log (N / 2^P) ≤ hi / 2^Q` (for `N ≥ 1`), computed by
range reduction `N = 2^k · y`, `y ∈ [1,2)`, and the artanh series
    log y = 2·Σ_{j<n} w^(2j+1)/(2j+1) + tail,   w = (N - 2^k)/(N + 2^k),
evaluated with floor (lower) / ceiling (upper) fixed-point iterates at scale `2^Q`.
All arithmetic is `Nat` multiplication/division (GMP-accelerated in the kernel); there is no
`gcd` normalisation in the inner loop.  Soundness: `lnDy_sound`.
-/

set_option autoImplicit false

namespace CKLaneP

open Finset

/-- Real artanh partial sum `Σ_{i<n} w^(2i+1)/(2i+1)`. -/
noncomputable def atR (w : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, w ^ (2 * i + 1) / (2 * (i : ℝ) + 1)

theorem atR_succ (w : ℝ) (n : ℕ) :
    atR w (n + 1) = atR w n + w ^ (2 * n + 1) / (2 * (n : ℝ) + 1) := by
  unfold atR; rw [sum_range_succ]

/-- Largest `k ≤ fuel` with `2^k ≤ N` (returns 0 if none). -/
def blen (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 => if 2 ^ (fuel + 1) ≤ N then fuel + 1 else blen N fuel

theorem blen_spec (N : ℕ) (hN : 1 ≤ N) (fuel : ℕ) : 2 ^ blen N fuel ≤ N := by
  induction fuel with
  | zero => simpa [blen] using hN
  | succ f ih =>
      unfold blen
      split_ifs with h
      · exact h
      · exact ih

/-- Lower fixed-point loop: state `(j, p, acc)`; `p ≈ 2^Q w^(2j+1)` rounded down. -/
def atLo (A2 B2 : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | fuel + 1, j, p, acc => atLo A2 B2 fuel (j + 1) (p * A2 / B2) (acc + p / (2 * j + 1))

/-- Upper fixed-point loop: returns `(final q, acc)`; `q ≈ 2^Q w^(2j+1)` rounded up. -/
def atHi (A2 B2 : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, _, q, acc => (q, acc)
  | fuel + 1, j, q, acc =>
      atHi A2 B2 fuel (j + 1) ((q * A2 + B2 - 1) / B2) (acc + (q + 2 * j) / (2 * j + 1))

theorem natdiv_le_real (a b : ℕ) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := Nat.cast_div_le

theorem real_le_natceil (a b : ℕ) (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ (((a + b - 1) / b : ℕ) : ℝ) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hbR]
  have h := Nat.lt_div_mul_add hb (a := a + b - 1)
  -- a + b - 1 < (a + b - 1) / b * b + b  ⇒  a ≤ (a+b-1)/b * b
  have h2 : a ≤ (a + b - 1) / b * b := by omega
  exact_mod_cast h2

theorem atLo_sound (A2 B2 : ℕ) (w : ℝ) (Qs : ℝ) (hw2 : (A2 : ℝ) / (B2 : ℝ) = w ^ 2)
    (_hw0 : 0 ≤ w) (_hQs : 0 ≤ Qs) :
    ∀ (fuel j p acc : ℕ), (p : ℝ) ≤ Qs * w ^ (2 * j + 1) → (acc : ℝ) ≤ Qs * atR w j →
      (atLo A2 B2 fuel j p acc : ℝ) ≤ Qs * atR w (j + fuel) := by
  intro fuel
  induction fuel with
  | zero => intro j p acc _ hacc; simpa [atLo] using hacc
  | succ f ih =>
      intro j p acc hp hacc
      unfold atLo
      have hj : (0 : ℝ) < 2 * (j : ℝ) + 1 := by positivity
      have hp' : ((p * A2 / B2 : ℕ) : ℝ) ≤ Qs * w ^ (2 * (j + 1) + 1) := by
        calc ((p * A2 / B2 : ℕ) : ℝ) ≤ ((p * A2 : ℕ) : ℝ) / (B2 : ℝ) := natdiv_le_real _ _
          _ = (p : ℝ) * ((A2 : ℝ) / (B2 : ℝ)) := by push_cast; ring
          _ = (p : ℝ) * w ^ 2 := by rw [hw2]
          _ ≤ Qs * w ^ (2 * j + 1) * w ^ 2 := mul_le_mul_of_nonneg_right hp (by positivity)
          _ = Qs * w ^ (2 * (j + 1) + 1) := by ring
      have hacc' : ((acc + p / (2 * j + 1) : ℕ) : ℝ) ≤ Qs * atR w (j + 1) := by
        rw [atR_succ]
        have h1 : ((p / (2 * j + 1) : ℕ) : ℝ) ≤ (p : ℝ) / (2 * (j : ℝ) + 1) := by
          have := natdiv_le_real p (2 * j + 1); push_cast at this; exact this
        have h2 : (p : ℝ) / (2 * (j : ℝ) + 1) ≤ Qs * w ^ (2 * j + 1) / (2 * (j : ℝ) + 1) :=
          div_le_div_of_nonneg_right hp hj.le
        push_cast
        have e : Qs * (atR w j + w ^ (2 * j + 1) / (2 * (j : ℝ) + 1)) =
            Qs * atR w j + Qs * w ^ (2 * j + 1) / (2 * (j : ℝ) + 1) := by ring
        rw [e]
        linarith
      have := ih (j + 1) (p * A2 / B2) (acc + p / (2 * j + 1)) hp' hacc'
      rw [show j + 1 + f = j + (f + 1) by ring] at this
      exact this

theorem atHi_sound (A2 B2 : ℕ) (hB2 : 0 < B2) (w : ℝ) (Qs : ℝ) (hw2 : (A2 : ℝ) / (B2 : ℝ) = w ^ 2)
    (_hw0 : 0 ≤ w) (_hQs : 0 ≤ Qs) :
    ∀ (fuel j q acc : ℕ), Qs * w ^ (2 * j + 1) ≤ (q : ℝ) → Qs * atR w j ≤ (acc : ℝ) →
      Qs * w ^ (2 * (j + fuel) + 1) ≤ ((atHi A2 B2 fuel j q acc).1 : ℝ) ∧
      Qs * atR w (j + fuel) ≤ ((atHi A2 B2 fuel j q acc).2 : ℝ) := by
  intro fuel
  induction fuel with
  | zero => intro j q acc hq hacc; simpa [atHi] using And.intro hq hacc
  | succ f ih =>
      intro j q acc hq hacc
      unfold atHi
      have hj : (0 : ℝ) < 2 * (j : ℝ) + 1 := by positivity
      have hq' : Qs * w ^ (2 * (j + 1) + 1) ≤ (((q * A2 + B2 - 1) / B2 : ℕ) : ℝ) := by
        calc Qs * w ^ (2 * (j + 1) + 1) = Qs * w ^ (2 * j + 1) * w ^ 2 := by ring
          _ ≤ (q : ℝ) * w ^ 2 := mul_le_mul_of_nonneg_right hq (by positivity)
          _ = ((q * A2 : ℕ) : ℝ) / (B2 : ℝ) := by rw [← hw2]; push_cast; ring
          _ ≤ _ := real_le_natceil _ _ hB2
      have hacc' : Qs * atR w (j + 1) ≤ ((acc + (q + 2 * j) / (2 * j + 1) : ℕ) : ℝ) := by
        rw [atR_succ]
        have h1 : (q : ℝ) / (2 * (j : ℝ) + 1) ≤ (((q + 2 * j) / (2 * j + 1) : ℕ) : ℝ) := by
          have := real_le_natceil q (2 * j + 1) (by omega)
          have e : q + (2 * j + 1) - 1 = q + 2 * j := by omega
          rw [e] at this
          push_cast at this
          exact this
        have h2 : Qs * w ^ (2 * j + 1) / (2 * (j : ℝ) + 1) ≤ (q : ℝ) / (2 * (j : ℝ) + 1) :=
          div_le_div_of_nonneg_right hq hj.le
        push_cast
        have e : Qs * (atR w j + w ^ (2 * j + 1) / (2 * (j : ℝ) + 1)) =
            Qs * atR w j + Qs * w ^ (2 * j + 1) / (2 * (j : ℝ) + 1) := by ring
        rw [e]
        linarith
      have := ih (j + 1) ((q * A2 + B2 - 1) / B2) (acc + (q + 2 * j) / (2 * j + 1)) hq' hacc'
      rw [show j + 1 + f = j + (f + 1) by ring] at this
      exact this

/-- Bounds (scaled by `2^Q`) for `log y`, `y = N / 2^k`, using `n` series terms.
Returns `(lo, hi)` with `lo ≤ 2^Q log y ≤ hi` (when `2^k ≤ N`). -/
def lnY (Q n N k : ℕ) : ℕ × ℕ :=
  let A := N - 2 ^ k
  let B := N + 2 ^ k
  let A2 := A * A
  let B2 := B * B
  let lo := 2 * atLo A2 B2 n 0 (2 ^ Q * A / B) 0
  let r := atHi A2 B2 n 0 ((2 ^ Q * A + B - 1) / B) 0
  let tail := (r.1 * B2 + (B2 - A2) - 1) / (B2 - A2)
  (lo, 2 * (r.2 + tail))

theorem lnY_sound {Q n N k : ℕ} (hk : 2 ^ k ≤ N) :
    ((lnY Q n N k).1 : ℝ) ≤ 2 ^ Q * Real.log ((N : ℝ) / 2 ^ k) ∧
      2 ^ Q * Real.log ((N : ℝ) / 2 ^ k) ≤ ((lnY Q n N k).2 : ℝ) := by
  set A := N - 2 ^ k with hA
  set B := N + 2 ^ k with hB
  have hpk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hBpos : 0 < B := by omega
  have hAB : A < B := by omega
  have hAR : (A : ℝ) = (N : ℝ) - 2 ^ k := by
    rw [hA]; push_cast [Nat.cast_sub hk]; ring
  have hBR : (B : ℝ) = (N : ℝ) + 2 ^ k := by rw [hB]; push_cast; ring
  set w : ℝ := (A : ℝ) / (B : ℝ) with hw
  have hBRpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hBpos
  have hw0 : 0 ≤ w := div_nonneg (Nat.cast_nonneg _) hBRpos.le
  have hw1 : w < 1 := by
    rw [hw, div_lt_one hBRpos]; exact_mod_cast hAB
  have hw2 : ((A * A : ℕ) : ℝ) / ((B * B : ℕ) : ℝ) = w ^ 2 := by
    rw [hw]; push_cast; ring
  have hB2pos : 0 < B * B := Nat.mul_pos hBpos hBpos
  have hQs : (0 : ℝ) ≤ 2 ^ Q := by positivity
  -- ratio identity
  have hpkR : (0 : ℝ) < 2 ^ k := by positivity
  have hratio : (1 + w) / (1 - w) = (N : ℝ) / 2 ^ k := by
    rw [hw, hAR, hBR]
    have hNpos : (0 : ℝ) < (N : ℝ) + 2 ^ k := by positivity
    field_simp
    ring
  obtain ⟨b1, b2⟩ := (show 2 * atR w n ≤ Real.log ((1 + w) / (1 - w)) ∧
      Real.log ((1 + w) / (1 - w)) ≤ 2 * atR w n + 2 * (w ^ (2 * n + 1) / (1 - w ^ 2)) from by
    have lo := Real.sum_range_le_log_div hw0 hw1 n
    have hi := Real.log_div_le_sum_range_add hw0 hw1 n
    unfold atR
    constructor <;> linarith)
  rw [hratio] at b1 b2
  -- lower
  have hp0 : ((2 ^ Q * A / B : ℕ) : ℝ) ≤ 2 ^ Q * w ^ (2 * 0 + 1) := by
    calc ((2 ^ Q * A / B : ℕ) : ℝ) ≤ ((2 ^ Q * A : ℕ) : ℝ) / (B : ℝ) := natdiv_le_real _ _
      _ = 2 ^ Q * w ^ (2 * 0 + 1) := by rw [hw]; push_cast; ring
  have hlo := atLo_sound (A * A) (B * B) w (2 ^ Q) hw2 hw0 hQs n 0 _ 0 hp0
    (by simp [atR])
  rw [zero_add] at hlo
  -- upper
  have hq0 : 2 ^ Q * w ^ (2 * 0 + 1) ≤ (((2 ^ Q * A + B - 1) / B : ℕ) : ℝ) := by
    calc 2 ^ Q * w ^ (2 * 0 + 1) = ((2 ^ Q * A : ℕ) : ℝ) / (B : ℝ) := by rw [hw]; push_cast; ring
      _ ≤ _ := real_le_natceil _ _ hBpos
  obtain ⟨hqn, hacc⟩ := atHi_sound (A * A) (B * B) hB2pos w (2 ^ Q) hw2 hw0 hQs n 0 _ 0 hq0
    (by simp [atR])
  rw [zero_add] at hqn hacc
  set r := atHi (A * A) (B * B) n 0 ((2 ^ Q * A + B - 1) / B) 0 with hr
  -- tail
  have hden : 0 < B * B - A * A := by
    have : A * A < B * B := Nat.mul_self_lt_mul_self hAB
    omega
  have hdenR : ((B * B - A * A : ℕ) : ℝ) = (B : ℝ) ^ 2 - (A : ℝ) ^ 2 := by
    rw [Nat.cast_sub (Nat.mul_le_mul hAB.le hAB.le)]; push_cast; ring
  have hdenRpos : (0 : ℝ) < (B : ℝ) ^ 2 - (A : ℝ) ^ 2 := by
    rw [← hdenR]; exact_mod_cast hden
  have htail : 2 ^ Q * (w ^ (2 * n + 1) / (1 - w ^ 2)) ≤
      (((r.1 * (B * B) + (B * B - A * A) - 1) / (B * B - A * A) : ℕ) : ℝ) := by
    have hc := real_le_natceil (r.1 * (B * B)) (B * B - A * A) hden
    have e1 : 1 - w ^ 2 = ((B : ℝ) ^ 2 - (A : ℝ) ^ 2) / (B : ℝ) ^ 2 := by
      rw [hw]; field_simp
    calc 2 ^ Q * (w ^ (2 * n + 1) / (1 - w ^ 2))
        = 2 ^ Q * w ^ (2 * n + 1) * (B : ℝ) ^ 2 / ((B : ℝ) ^ 2 - (A : ℝ) ^ 2) := by
          rw [e1]; field_simp
      _ ≤ (r.1 : ℝ) * (B : ℝ) ^ 2 / ((B : ℝ) ^ 2 - (A : ℝ) ^ 2) := by
          apply div_le_div_of_nonneg_right _ hdenRpos.le
          exact mul_le_mul_of_nonneg_right hqn (by positivity)
      _ = ((r.1 * (B * B) : ℕ) : ℝ) / ((B * B - A * A : ℕ) : ℝ) := by
          rw [hdenR]; push_cast; ring
      _ ≤ _ := hc
  unfold lnY
  simp only
  rw [← hA, ← hB, ← hr]
  constructor
  · push_cast
    have := mul_le_mul_of_nonneg_left b1 hQs
    nlinarith [hlo]
  · push_cast
    have := mul_le_mul_of_nonneg_left b2 hQs
    nlinarith [hacc, htail]

/-- Fixed-point bounds of `2^Q log 2` from `w = 1/3` with `n` terms. -/
def ln2Q (Q n : ℕ) : ℕ × ℕ := lnY Q n 2 0

theorem ln2Q_sound (Q n : ℕ) :
    ((ln2Q Q n).1 : ℝ) ≤ 2 ^ Q * Real.log 2 ∧ 2 ^ Q * Real.log 2 ≤ ((ln2Q Q n).2 : ℝ) := by
  have h := lnY_sound (Q := Q) (n := n) (N := 2) (k := 0) (by norm_num)
  have e : ((2 : ℕ) : ℝ) / 2 ^ (0 : ℕ) = 2 := by norm_num
  rw [e] at h
  exact h

/-- Bounds (scaled by `2^Q`, as integers) of `log (N / 2^P)` for `N ≥ 1`, given fixed-point
bounds `l2 = (l2lo, l2hi)` of `2^Q log 2`.  `n` series terms; range reduction by `Nat.log2`. -/
def lnDy (P Q n : ℕ) (l2 : ℕ × ℕ) (N : ℕ) : ℤ × ℤ :=
  let k := Nat.log2 N
  let y := lnY Q n N k
  let e : ℤ := (k : ℤ) - (P : ℤ)
  let lo : ℤ := (y.1 : ℤ) + (if 0 ≤ e then e * (l2.1 : ℤ) else e * (l2.2 : ℤ))
  let hi : ℤ := (y.2 : ℤ) + (if 0 ≤ e then e * (l2.2 : ℤ) else e * (l2.1 : ℤ))
  (lo, hi)

theorem lnDy_sound {P Q n N : ℕ} {l2 : ℕ × ℕ}
    (hl2 : (l2.1 : ℝ) ≤ 2 ^ Q * Real.log 2 ∧ 2 ^ Q * Real.log 2 ≤ (l2.2 : ℝ)) (hN : 1 ≤ N) :
    ((lnDy P Q n l2 N).1 : ℝ) ≤ 2 ^ Q * Real.log ((N : ℝ) / 2 ^ P) ∧
      2 ^ Q * Real.log ((N : ℝ) / 2 ^ P) ≤ ((lnDy P Q n l2 N).2 : ℝ) := by
  set k := Nat.log2 N with hk
  have hkN : 2 ^ k ≤ N := Nat.log2_self_le (by omega)
  obtain ⟨y1, y2⟩ := lnY_sound (Q := Q) (n := n) hkN
  obtain ⟨l1, l2'⟩ := hl2
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsplit : Real.log ((N : ℝ) / 2 ^ P) =
      Real.log ((N : ℝ) / 2 ^ k) + ((k : ℝ) - (P : ℝ)) * Real.log 2 := by
    rw [Real.log_div hNpos.ne' (by positivity), Real.log_div hNpos.ne' (by positivity),
      Real.log_pow, Real.log_pow]
    ring
  unfold lnDy
  simp only
  rw [← hk]
  set e : ℤ := (k : ℤ) - (P : ℤ) with he
  have heR : ((e : ℤ) : ℝ) = (k : ℝ) - (P : ℝ) := by rw [he]; push_cast; ring
  rw [hsplit]
  constructor
  · split_ifs with hs
    · have hs' : (0 : ℝ) ≤ ((e : ℤ) : ℝ) := by exact_mod_cast hs
      have hm := mul_le_mul_of_nonneg_left l1 hs'
      push_cast
      rw [heR] at hm
      nlinarith [y1, hm]
    · have hs' : ((e : ℤ) : ℝ) ≤ 0 := by
        have : e < 0 := lt_of_not_ge hs
        exact_mod_cast this.le
      have hm := mul_le_mul_of_nonpos_left l2' hs'
      push_cast
      rw [heR] at hm
      nlinarith [y1, hm]
  · split_ifs with hs
    · have hs' : (0 : ℝ) ≤ ((e : ℤ) : ℝ) := by exact_mod_cast hs
      have hm := mul_le_mul_of_nonneg_left l2' hs'
      push_cast
      rw [heR] at hm
      nlinarith [y2, hm]
    · have hs' : ((e : ℤ) : ℝ) ≤ 0 := by
        have : e < 0 := lt_of_not_ge hs
        exact_mod_cast this.le
      have hm := mul_le_mul_of_nonpos_left l1 hs'
      push_cast
      rw [heR] at hm
      nlinarith [y2, hm]

/-- The standard constant pair `2^64 log 2` (34 series terms). -/
def l2c64 : ℕ × ℕ := ln2Q 64 34

theorem l2c64_sound : ((l2c64.1 : ℕ) : ℝ) ≤ 2 ^ 64 * Real.log 2 ∧
    2 ^ 64 * Real.log 2 ≤ ((l2c64.2 : ℕ) : ℝ) := ln2Q_sound 64 34

/-- Pilot: `log(3/2) ∈ [0.405465108108, 0.405465108109]` at `Q = 64`. -/
theorem lnDy_pilot :
    let r := lnDy 1 64 20 l2c64 3
    (405465108108 : ℤ) * 2 ^ 64 ≤ r.1 * 10 ^ 12 ∧ r.2 * 10 ^ 12 ≤ (405465108109 : ℤ) * 2 ^ 64 := by
  decide +kernel

/-- Pilot: `log(3/1024) = log 3 - 10 log 2` (negative exponent branch), window `10^-11`. -/
theorem lnDy_pilot2 :
    let r := lnDy 10 64 20 l2c64 3
    (-58328595170 : ℤ) * 2 ^ 64 ≤ r.1 * 10 ^ 10 ∧ r.2 * 10 ^ 10 ≤ (-58328595169 : ℤ) * 2 ^ 64 := by
  decide +kernel

end CKLaneP

end


