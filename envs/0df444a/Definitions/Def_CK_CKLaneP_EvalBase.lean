-- Prove2me | Definitions.Def_CK_CKLaneP_EvalBase
-- name    : CK_CKLaneP_EvalBase
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:09:42.035581+00:00
-- url     : https://prove2.me/theorems/c180763d-bd80-4db1-b6b1-f09a768fa9f4
-- title:
--   Courtade–Kumar proof module `CKLaneP.EvalBase` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.EvalBase` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.EvalBase` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.EvalBase (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/EvalBase.lean)

import Definitions.Def_CK_CKLaneP_LogCheck

-- ===== source module CKLaneP.EvalBase =====
section
/-
Lane P — evaluator base layer: rational intervals with outward dyadic rounding, and certified
enclosures of `Real.log` at positive rationals (computed, not checked), proved sound once.

* `QI` : closed rational interval, `QI.Mem x I : I.lo ≤ x ≤ I.hi` (real membership).
* `rdn P q ≤ q ≤ rup P q` : outward rounding to the dyadic grid `2^-P`.
* `logQ P n x` : for rational `x > 0`, an interval containing `Real.log x`
  (range reduction by powers of two with structural fuel, atanh series with `n` terms,
  inputs rounded to the grid before the series so sizes stay bounded).
Everything is plain `ℚ`/`ℤ`/`ℕ` arithmetic evaluated by the kernel (`decide +kernel`).
-/

set_option autoImplicit false

namespace CKLaneP

/-- A closed rational interval. -/
structure QI where
  lo : ℚ
  hi : ℚ
deriving Repr, DecidableEq

namespace QI

def Mem (x : ℝ) (I : QI) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def pt (q : ℚ) : QI := ⟨q, q⟩

theorem mem_pt (q : ℚ) : Mem (q : ℝ) (pt q) := ⟨le_rfl, le_rfl⟩

end QI

/-- Downward rounding to the dyadic grid `2^-P`. -/
def rdn (P : ℕ) (q : ℚ) : ℚ := ((Rat.floor (q * (2 : ℚ) ^ P) : ℤ) : ℚ) / (2 : ℚ) ^ P

/-- Upward rounding to the dyadic grid `2^-P`. -/
def rup (P : ℕ) (q : ℚ) : ℚ := -(rdn P (-q))

theorem rdn_le (P : ℕ) (q : ℚ) : rdn P q ≤ q := by
  unfold rdn
  have h2 : (0 : ℚ) < (2 : ℚ) ^ P := by positivity
  rw [div_le_iff₀ h2]
  exact Rat.floor_le _

theorem le_rup (P : ℕ) (q : ℚ) : q ≤ rup P q := by
  unfold rup
  have := rdn_le P (-q)
  linarith

theorem rdn_le_real (P : ℕ) (q : ℚ) : ((rdn P q : ℚ) : ℝ) ≤ (q : ℝ) := by
  exact_mod_cast rdn_le P q

theorem le_rup_real (P : ℕ) (q : ℚ) : (q : ℝ) ≤ ((rup P q : ℚ) : ℝ) := by
  exact_mod_cast le_rup P q

namespace QI

/-- Outward-rounded addition. -/
def add (P : ℕ) (I J : QI) : QI := ⟨rdn P (I.lo + J.lo), rup P (I.hi + J.hi)⟩
def neg (I : QI) : QI := ⟨-I.hi, -I.lo⟩
def sub (P : ℕ) (I J : QI) : QI := ⟨rdn P (I.lo - J.hi), rup P (I.hi - J.lo)⟩
def mul (P : ℕ) (I J : QI) : QI :=
  ⟨rdn P (min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))),
   rup P (max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi)))⟩
/-- Reciprocal of a positive interval. -/
def inv (P : ℕ) (I : QI) : QI := ⟨rdn P (1 / I.hi), rup P (1 / I.lo)⟩
def div (P : ℕ) (I J : QI) : QI := mul P I (inv P J)
/-- Scaling by a nonnegative rational. -/
def smul (P : ℕ) (c : ℚ) (I : QI) : QI := ⟨rdn P (c * I.lo), rup P (c * I.hi)⟩

theorem mem_add {P : ℕ} {x y : ℝ} {I J : QI} (hx : Mem x I) (hy : Mem y J) :
    Mem (x + y) (add P I J) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  have a1 := rdn_le_real P (I.lo + J.lo)
  have a2 := le_rup_real P (I.hi + J.hi)
  push_cast at a1 a2
  exact ⟨by simp only [add]; linarith, by simp only [add]; linarith⟩

theorem mem_neg {x : ℝ} {I : QI} (hx : Mem x I) : Mem (-x) (neg I) := by
  obtain ⟨h1, h2⟩ := hx
  constructor <;> simp only [neg, Rat.cast_neg] <;> linarith

theorem mem_sub {P : ℕ} {x y : ℝ} {I J : QI} (hx : Mem x I) (hy : Mem y J) :
    Mem (x - y) (sub P I J) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  have a1 := rdn_le_real P (I.lo - J.hi)
  have a2 := le_rup_real P (I.hi - J.lo)
  push_cast at a1 a2
  exact ⟨by simp only [sub]; linarith, by simp only [sub]; linarith⟩

/-- `x*y` lies between the extreme corner products. -/
theorem mul_between {a b c d x y : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) (hy1 : c ≤ y) (hy2 : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have key : ∀ u : ℝ, a ≤ u → u ≤ b →
      min (a * y) (b * y) ≤ u * y ∧ u * y ≤ max (a * y) (b * y) := by
    intro u hu1 hu2
    rcases le_total 0 y with hy | hy
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hu1 hy),
        (mul_le_mul_of_nonneg_right hu2 hy).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hu2 hy),
        (mul_le_mul_of_nonpos_right hu1 hy).trans (le_max_left _ _)⟩
  have key2 : ∀ u : ℝ, ∀ v : ℝ, c ≤ v → v ≤ d →
      min (u * c) (u * d) ≤ u * v ∧ u * v ≤ max (u * c) (u * d) := by
    intro u v hv1 hv2
    rcases le_total 0 u with hu | hu
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hv1 hu),
        (mul_le_mul_of_nonneg_left hv2 hu).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hv2 hu),
        (mul_le_mul_of_nonpos_left hv1 hu).trans (le_max_left _ _)⟩
  obtain ⟨k1, k2⟩ := key x hx1 hx2
  obtain ⟨la1, la2⟩ := key2 a y hy1 hy2
  obtain ⟨lb1, lb2⟩ := key2 b y hy1 hy2
  constructor
  · rcases min_choice (a * y) (b * y) with h | h <;> rw [h] at k1
    · exact le_trans (le_trans (min_le_left _ _) la1) k1
    · exact le_trans (le_trans (min_le_right _ _) lb1) k1
  · rcases max_choice (a * y) (b * y) with h | h <;> rw [h] at k2
    · exact le_trans k2 (le_trans la2 (le_max_left _ _))
    · exact le_trans k2 (le_trans lb2 (le_max_right _ _))

theorem mem_mul {P : ℕ} {x y : ℝ} {I J : QI} (hx : Mem x I) (hy : Mem y J) :
    Mem (x * y) (mul P I J) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  obtain ⟨m1, m2⟩ := mul_between h1 h2 h3 h4
  have a1 := rdn_le_real P (min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)))
  have a2 := le_rup_real P (max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi)))
  push_cast at a1 a2
  exact ⟨by simp only [mul]; linarith, by simp only [mul]; linarith⟩

theorem mem_inv {P : ℕ} {x : ℝ} {I : QI} (hx : Mem x I) (hpos : 0 < I.lo) :
    Mem (1 / x) (inv P I) := by
  obtain ⟨h1, h2⟩ := hx
  have hl : (0 : ℝ) < I.lo := by exact_mod_cast hpos
  have hx0 : 0 < x := lt_of_lt_of_le hl h1
  have hh : (0 : ℝ) < I.hi := lt_of_lt_of_le hx0 h2
  have a1 := rdn_le_real P (1 / I.hi)
  have a2 := le_rup_real P (1 / I.lo)
  push_cast at a1 a2
  have b1 : 1 / (I.hi : ℝ) ≤ 1 / x := one_div_le_one_div_of_le hx0 h2
  have b2 : 1 / x ≤ 1 / (I.lo : ℝ) := one_div_le_one_div_of_le hl h1
  exact ⟨by simp only [inv]; linarith, by simp only [inv]; linarith⟩

theorem mem_div {P : ℕ} {x y : ℝ} {I J : QI} (hx : Mem x I) (hy : Mem y J) (hpos : 0 < J.lo) :
    Mem (x / y) (div P I J) := by
  have h := mem_mul (P := P) hx (mem_inv (P := P) hy hpos)
  rw [div_eq_mul_one_div]
  exact h

theorem mem_smul {P : ℕ} {c : ℚ} {x : ℝ} {I : QI} (hc : 0 ≤ c) (hx : Mem x I) :
    Mem ((c : ℝ) * x) (smul P c I) := by
  obtain ⟨h1, h2⟩ := hx
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  have a1 := rdn_le_real P (c * I.lo)
  have a2 := le_rup_real P (c * I.hi)
  push_cast at a1 a2
  have b1 := mul_le_mul_of_nonneg_left h1 hc'
  have b2 := mul_le_mul_of_nonneg_left h2 hc'
  exact ⟨by simp only [smul]; linarith, by simp only [smul]; linarith⟩

theorem mem_widen {x : ℝ} {I J : QI} (hx : Mem x I) (h1 : J.lo ≤ I.lo) (h2 : I.hi ≤ J.hi) :
    Mem x J := by
  obtain ⟨a, b⟩ := hx
  have c1 : (J.lo : ℝ) ≤ I.lo := by exact_mod_cast h1
  have c2 : (I.hi : ℝ) ≤ J.hi := by exact_mod_cast h2
  exact ⟨le_trans c1 a, le_trans b c2⟩

end QI

/-! ### Logarithm enclosures -/

/-- Range reduction exponent: largest `k ≤ fuel` with `x / 2^k ≥ 1` found greedily. -/
def logK (x : ℚ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 => if 2 ≤ x then logK (x / 2) fuel + 1 else 0

/-- Enclosure of `log x` for `x ≥ 1` (exact input). -/
def logGe1 (P n : ℕ) (x : ℚ) : QI :=
  let k := logK x 4096
  let y := x / 2 ^ k
  let w := (y - 1) / (y + 1)
  ⟨rdn P ((k : ℚ) * L2lo + 2 * atSum w n),
   rup P ((k : ℚ) * L2hi + 2 * atSum w n + 2 * (w ^ (2 * n + 1) / (1 - w ^ 2)))⟩

/-- Lower endpoint of `log x` for rational `x > 0` (exact input). -/
def logLo (P n : ℕ) (x : ℚ) : ℚ :=
  if 1 ≤ x then (logGe1 P n x).lo else -(logGe1 P n (1 / x)).hi

/-- Upper endpoint of `log x` for rational `x > 0` (exact input). -/
def logHi (P n : ℕ) (x : ℚ) : ℚ :=
  if 1 ≤ x then (logGe1 P n x).hi else -(logGe1 P n (1 / x)).lo

/-- Enclosure of `log x` for rational `x > 0`: both endpoints are computed at dyadic
roundings of `x` (monotonicity of `log`), keeping the series inputs short. -/
def logQ (P n : ℕ) (x : ℚ) : QI := ⟨logLo P n (rdn P x), logHi P n (rup P x)⟩

theorem logK_spec (x : ℚ) (fuel : ℕ) (hx : 1 ≤ x) : 1 ≤ x / 2 ^ (logK x fuel) := by
  induction fuel generalizing x with
  | zero => simp only [logK, pow_zero, div_one]; exact hx
  | succ n ih =>
      unfold logK
      split_ifs with h
      · have h1 : 1 ≤ x / 2 := by linarith
        have := ih (x / 2) h1
        rw [pow_succ]
        calc (1 : ℚ) ≤ x / 2 / 2 ^ logK (x / 2) n := this
          _ = x / (2 ^ logK (x / 2) n * 2) := by field_simp
      · simpa using hx

theorem logGe1_sound {P n : ℕ} {x : ℚ} (hx : 1 ≤ x) :
    QI.Mem (Real.log (x : ℝ)) (logGe1 P n x) := by
  have hL := log2_bounds
  set k := logK x 4096 with hk
  have hy1 : 1 ≤ x / 2 ^ k := logK_spec x 4096 hx
  set y : ℚ := x / 2 ^ k with hy
  set w : ℚ := (y - 1) / (y + 1) with hw
  have hypos : (0 : ℚ) < y + 1 := by linarith
  have hw0 : 0 ≤ w := by rw [hw]; apply div_nonneg <;> linarith
  have hw1 : w < 1 := by rw [hw, div_lt_one hypos]; linarith
  obtain ⟨b1, b2⟩ := log_artanh_bounds hw0 hw1 n
  have hratio : (1 + (w : ℝ)) / (1 - (w : ℝ)) = (y : ℝ) := by
    have hyposR : (0 : ℝ) < (y : ℝ) + 1 := by exact_mod_cast hypos
    rw [hw]; push_cast
    field_simp
    ring
  rw [hratio] at b1 b2
  have hqeq : (x : ℝ) = (2 : ℝ) ^ k * (y : ℝ) := by
    rw [hy]; push_cast; field_simp
  have hyposR : (0 : ℝ) < (y : ℝ) := by
    have : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
    linarith
  have hlog : Real.log (x : ℝ) = (k : ℝ) * Real.log 2 + Real.log (y : ℝ) := by
    rw [hqeq, Real.log_mul (by positivity) hyposR.ne', Real.log_pow]
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hkL1 : (k : ℝ) * (L2lo : ℝ) ≤ (k : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left hL.1 hk0
  have hkL2 : (k : ℝ) * Real.log 2 ≤ (k : ℝ) * (L2hi : ℝ) := mul_le_mul_of_nonneg_left hL.2 hk0
  have r1 := rdn_le_real P ((k : ℚ) * L2lo + 2 * atSum w n)
  have r2 := le_rup_real P ((k : ℚ) * L2hi + 2 * atSum w n + 2 * (w ^ (2 * n + 1) / (1 - w ^ 2)))
  push_cast at r1 r2
  unfold logGe1
  simp only
  rw [← hk, ← hy, ← hw]
  constructor
  · rw [hlog]; linarith
  · rw [hlog]; linarith

theorem logLo_le {P n : ℕ} {x : ℚ} (hx : 0 < x) :
    ((logLo P n x : ℚ) : ℝ) ≤ Real.log (x : ℝ) := by
  unfold logLo
  by_cases h1 : 1 ≤ x
  · rw [if_pos h1]
    exact (logGe1_sound (P := P) (n := n) h1).1
  · rw [if_neg h1]
    have hlt : x < 1 := not_le.mp h1
    have hinv : 1 ≤ 1 / x := by rw [le_div_iff₀ hx]; linarith
    have hs := (logGe1_sound (P := P) (n := n) hinv).2
    have e : Real.log (((1 / x : ℚ)) : ℝ) = -Real.log (x : ℝ) := by
      push_cast; rw [one_div, Real.log_inv]
    rw [e] at hs
    push_cast
    linarith

theorem le_logHi {P n : ℕ} {x : ℚ} (hx : 0 < x) :
    Real.log (x : ℝ) ≤ ((logHi P n x : ℚ) : ℝ) := by
  unfold logHi
  by_cases h1 : 1 ≤ x
  · rw [if_pos h1]
    exact (logGe1_sound (P := P) (n := n) h1).2
  · rw [if_neg h1]
    have hlt : x < 1 := not_le.mp h1
    have hinv : 1 ≤ 1 / x := by rw [le_div_iff₀ hx]; linarith
    have hs := (logGe1_sound (P := P) (n := n) hinv).1
    have e : Real.log (((1 / x : ℚ)) : ℝ) = -Real.log (x : ℝ) := by
      push_cast; rw [one_div, Real.log_inv]
    rw [e] at hs
    push_cast
    linarith

theorem logQ_sound {P n : ℕ} {x : ℚ} (hx : 0 < x) (hxl : 0 < rdn P x) :
    QI.Mem (Real.log (x : ℝ)) (logQ P n x) := by
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hl := rdn_le P x
  have hh := le_rup P x
  have hxlR : (0 : ℝ) < ((rdn P x : ℚ) : ℝ) := by exact_mod_cast hxl
  have hxhpos : 0 < rup P x := lt_of_lt_of_le hx hh
  have mono1 : Real.log ((rdn P x : ℚ) : ℝ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log hxlR (by exact_mod_cast hl)
  have mono2 : Real.log (x : ℝ) ≤ Real.log ((rup P x : ℚ) : ℝ) :=
    Real.log_le_log hxR (by exact_mod_cast hh)
  exact ⟨le_trans (logLo_le (P := P) (n := n) hxl) mono1,
    le_trans mono2 (le_logHi (P := P) (n := n) hxhpos)⟩

/-- Kernel pilot: `log 3` enclosure. -/
def pilotLog3 : QI := logQ 64 20 3

/-- The computed enclosure is tight: `log 3 = 1.098612288668...` lies in a window of width
`10^-10` containing both endpoints. -/
theorem pilotLog3_ok : 10986122886 / 10000000000 ≤ pilotLog3.lo ∧
    pilotLog3.hi ≤ 10986122887 / 10000000000 := by
  decide +kernel

theorem pilotLog3_sound : QI.Mem (Real.log 3) pilotLog3 := by
  have h := logQ_sound (P := 64) (n := 20) (x := 3) (by norm_num) (by decide +kernel)
  have e : ((3 : ℚ) : ℝ) = 3 := by norm_num
  rw [e] at h
  exact h

end CKLaneP

end


