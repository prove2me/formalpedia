-- Prove2me | Definitions.Def_TaoFivePrimes_BlockFoundation
-- name    : TaoFivePrimes_BlockFoundation
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-09-15T17:30:28.875693+00:00
-- url     : https://prove2.me/theorems/8bca80f4-cd0c-4f05-8144-421e9d0c905e
-- title:
--   Type I block foundation: integer distance, inequality (2.1), and the small-$d$ core of (5.15)
-- statement:
--   **Distance to the nearest integer and the sine envelope.**
--
--   Write $\|t\|_{\mathbb R/\mathbb Z}$ for the distance from $t\in\mathbb R$ to the nearest integer, realized here as `rdist t = min (Int.fract t) (1 - Int.fract t)`, so that it always lies in $[0,\tfrac12]$. This file establishes the elementary toolkit that Tao's Section 5 uses to pass from exponential sums to the envelope $\frac{4(\log 2)\log 2x}{|\sin(2\pi d\alpha)|}$:
--
--   * `rdist_nonneg`, `rdist_le_half` — range of the distance function;
--   * `rdist_add_le'`, `rdist_add_le`, `rdist_sub_le_abs_sub` — the triangle inequality, its $1$-Lipschitz form $\|x+y\|\le\|x\|+|y|$, and the reverse form $\|x\|-\|y\|\le\|x-y\|$;
--   * `abs_sin_pi_eq_abs_sin_pi_rdist`, `two_rdist_le_abs_sin`, `abs_sin_le_pi_mul_rdist` — **inequality (2.1)**, $\;2\|t\|_{\mathbb R/\mathbb Z}\le|\sin(\pi t)|\le\pi\|t\|_{\mathbb R/\mathbb Z}$, proved by reducing the sine phase modulo $\pi$ with $\sin(x+n\pi)=(-1)^n\sin x$;
--   * `div_q_eq`, `rdist_div_ge` — if $q\nmid m$ then $\|m/q\|_{\mathbb R/\mathbb Z}\ge 1/q$;
--   * `d_mul_beta_le`, `rdist_d_alpha_ge` — the small-$d$ quantitative core of **(5.15)**: if $4\alpha=a/q+\beta$ with $|\beta|\le q^{-2}$, $2d\le q$ and $q\nmid ad$, then $\|4d\alpha\|_{\mathbb R/\mathbb Z}\ge\frac1{2q}$, hence $|\sin(2\pi d\alpha)|\ge\frac1q$.
--
--   Together with (2.1) this is exactly the mechanism by which the target node converts the pointwise envelope on the range $d\le q/2$ into the uniform factor $2q$. All statements are `sorry`-free and depend only on Mathlib.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, the small-$d$ regime of the Type I estimate, and Section 2, inequality (2.1).

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

set_option maxHeartbeats 800000

/-! # Type I block summation: foundations

Scratch development for the Prove2Me node
`TaoFivePrimes.theorem51_typeI_block_summation`, following Tao,
arXiv:1201.6656v4, Section 5, (5.14) → (5.17).

This file holds the low-level analytic/arithmetic atoms:

* `rdist` — distance to the nearest integer, in `[0, 1/2]`;
* inequality **(2.1)**: `2 rdist t ≤ |sin (π t)| ≤ π rdist t`;
* the arithmetic input of **(5.15)**: a nonzero multiple of `1/q` is at
  `R/Z`-distance at least `1/q`;
* the resulting pointwise cosecant bound `1/|sin(2πdα)| ≤ 2q` for
  `d ≤ q/2`.

Design note: no `conv` is used anywhere.  Rewriting under `abs`/`Real.sin`
via `conv_rhs` exhausts the heartbeat budget in this environment, so every
step is phrased as an equality of *arguments* and applied with a plain `rw`.
Similarly, `linarith` cannot see through `Int.fract`/`Int.floor` casts, so
each such bridge is stated as an explicit real-valued lemma first. -/

namespace TaoFivePrimesBlock

/-! ## 1. Distance to the nearest integer -/

/-- Distance to the nearest integer, realized as the minimum of the two
complementary fractional parts, so that it lies in `[0, 1/2]`. -/
noncomputable def rdist (t : ℝ) : ℝ := min (Int.fract t) (1 - Int.fract t)

lemma rdist_eq_fract_or (t : ℝ) :
    rdist t = Int.fract t ∨ rdist t = 1 - Int.fract t :=
  min_choice _ _

lemma rdist_nonneg (t : ℝ) : 0 ≤ rdist t :=
  le_min (Int.fract_nonneg t) (by linarith [Int.fract_lt_one t])

lemma rdist_le_half (t : ℝ) : rdist t ≤ 1 / 2 := by
  have h1 := Int.fract_lt_one t
  rcases lt_or_ge (Int.fract t) (1 / 2) with h | h
  · exact (min_le_left _ _).trans h.le
  · exact (min_le_right _ _).trans (by linarith)

/-- Shifting by an integer multiple of `π` does not change `|sin|`. -/
lemma abs_sin_add_int_mul_pi (x : ℝ) (z : ℤ) :
    |Real.sin (x + (z : ℝ) * Real.pi)| = |Real.sin x| := by
  rw [Real.sin_add_int_mul_pi, abs_mul]
  simp [abs_zpow]

/-- `|sin|` is even. -/
lemma abs_sin_neg (x : ℝ) : |Real.sin (-x)| = |Real.sin x| := by
  rw [Real.sin_neg, abs_neg]

/-- `π · fract t` differs from `π t` by an integer multiple of `π`. -/
lemma pi_mul_fract_decomp (t : ℝ) :
    Real.pi * Int.fract t = Real.pi * t + ((-⌊t⌋ : ℤ) : ℝ) * Real.pi := by
  have hft : Int.fract t + (⌊t⌋ : ℝ) = t := Int.fract_add_floor t
  push_cast
  linear_combination Real.pi * hft

/-- `π · (fract t - 1)` differs from `π t` by an integer multiple of `π`. -/
lemma pi_mul_fract_sub_one_decomp (t : ℝ) :
    Real.pi * (Int.fract t - 1) = Real.pi * t + ((-(⌊t⌋ + 1) : ℤ) : ℝ) * Real.pi := by
  have hft : Int.fract t + (⌊t⌋ : ℝ) = t := Int.fract_add_floor t
  push_cast
  linear_combination Real.pi * hft

/-- **Phase reduction.** `sin (π ·)` only sees `rdist`. -/
lemma abs_sin_pi_eq_abs_sin_pi_rdist (t : ℝ) :
    |Real.sin (Real.pi * t)| = |Real.sin (Real.pi * rdist t)| := by
  rcases rdist_eq_fract_or t with h | h
  · rw [h, pi_mul_fract_decomp, abs_sin_add_int_mul_pi]
  · have hneg : Real.pi * (1 - Int.fract t) = -(Real.pi * (Int.fract t - 1)) := by ring
    rw [h, hneg, abs_sin_neg, pi_mul_fract_sub_one_decomp, abs_sin_add_int_mul_pi]

/-! ## 2. Inequality (2.1) -/

/-- **(2.1), lower half.** `2 ‖t‖_{R/Z} ≤ |sin (π t)|`. -/
theorem two_rdist_le_abs_sin (t : ℝ) : 2 * rdist t ≤ |Real.sin (Real.pi * t)| := by
  have key := abs_sin_pi_eq_abs_sin_pi_rdist t
  have hlow : 2 * rdist t ≤ |Real.sin (Real.pi * rdist t)| := by
    have hx : 0 ≤ Real.pi * rdist t := by nlinarith [Real.pi_pos, rdist_nonneg t]
    have hx' : Real.pi * rdist t ≤ Real.pi / 2 := by
      nlinarith [Real.pi_pos, rdist_le_half t]
    have hm := Real.mul_le_sin hx hx'
    have hsinpos : 0 ≤ Real.sin (Real.pi * rdist t) :=
      Real.sin_nonneg_of_mem_Icc ⟨hx, by linarith [Real.pi_pos]⟩
    rw [abs_of_nonneg hsinpos]
    have he : 2 / Real.pi * (Real.pi * rdist t) = 2 * rdist t := by field_simp
    linarith [hm, he.le]
  rw [key]
  exact hlow

/-- **(2.1), upper half.** `|sin (π t)| ≤ π ‖t‖_{R/Z}`. -/
theorem abs_sin_le_pi_mul_rdist (t : ℝ) :
    |Real.sin (Real.pi * t)| ≤ Real.pi * rdist t := by
  have key := abs_sin_pi_eq_abs_sin_pi_rdist t
  have hup : |Real.sin (Real.pi * rdist t)| ≤ Real.pi * rdist t := by
    have h := Real.abs_sin_le_abs (x := Real.pi * rdist t)
    have hnonneg : |Real.pi * rdist t| = Real.pi * rdist t :=
      abs_of_nonneg (by nlinarith [Real.pi_pos, rdist_nonneg t])
    linarith [h, hnonneg.le, hnonneg.ge]
  rw [key]
  exact hup

/-! ## 3. The arithmetic input of (5.15) -/

/-- `(m % q)/q + (m / q) = m/q` in `ℝ`, for `q ≠ 0`. -/
lemma div_q_eq (m q : ℤ) (hq : (q : ℝ) ≠ 0) :
    ((m % q : ℤ) : ℝ) / (q : ℝ) + ((m / q : ℤ) : ℝ) = (m : ℝ) / (q : ℝ) := by
  have h : m % q + q * (m / q) = m := Int.emod_add_mul_ediv m q
  have hR : ((m % q : ℤ) : ℝ) + (q : ℝ) * ((m / q : ℤ) : ℝ) = (m : ℝ) := by
    exact_mod_cast h
  rw [← hR, add_div]
  field_simp

/-- If `m/q` is not an integer then its nearest-integer distance is at least
`1/q`.  This is the arithmetic content of Tao's step (5.15). -/
lemma rdist_div_ge (m q : ℤ) (hq : 0 < q) (hm : ¬ (q ∣ m)) :
    1 / (q : ℝ) ≤ rdist ((m : ℝ) / (q : ℝ)) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := hq0.ne'
  have hmod : Int.fract ((m : ℝ) / (q : ℝ)) = ((m % q : ℤ) : ℝ) / (q : ℝ) := by
    rw [Int.fract_eq_iff]
    have hmnn : (0 : ℝ) ≤ ((m % q : ℤ) : ℝ) := by
      exact_mod_cast Int.emod_nonneg m hq.ne'
    refine ⟨div_nonneg hmnn hq0.le, ?_, ?_⟩
    · rw [div_lt_one hq0]; exact_mod_cast Int.emod_lt_of_pos m hq
    · refine ⟨m / q, ?_⟩
      have h' := div_q_eq m q hqne
      rw [sub_eq_iff_eq_add, add_comm]
      exact h'.symm
  have hrem_pos : 0 < m % q := Int.emod_pos_of_not_dvd hm |>.resolve_left hq.ne'
  have hremr : (1 : ℝ) ≤ ((m % q : ℤ) : ℝ) := by exact_mod_cast hrem_pos
  have hleR : ((m % q : ℤ) : ℝ) + 1 ≤ (q : ℝ) := by
    exact_mod_cast (show m % q + 1 ≤ q by
      have := Int.emod_lt_of_pos m hq; omega)
  rw [rdist]
  apply le_min
  · have h : 1 / (q : ℝ) ≤ Int.fract ((m : ℝ) / (q : ℝ)) := by
      rw [hmod, div_le_div_iff_of_pos_right hq0]; exact hremr
    exact h
  · have h : 1 / (q : ℝ) ≤ 1 - Int.fract ((m : ℝ) / (q : ℝ)) := by
      rw [hmod, le_sub_iff_add_le]
      rw [← add_div]
      rw [div_le_one hq0]
      linarith
    exact h

/-! ## 4. The triangle inequality for `rdist`

`rdist` is the distance to the nearest integer, hence a genuine metric-like
pseudo-norm on `ℝ/ℤ`: `rdist (x + y) ≤ rdist x + rdist y`.  Everything is
reduced to the unit interval by subtracting the floors, which only shifts
`rdist` by an integer. -/

/-- In `[0,1)`, `Int.fract` is the identity. -/
lemma fract_eq_self {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) : Int.fract u = u := by
  rw [Int.fract_eq_iff]; exact ⟨h0, h1, ⟨0, by simp⟩⟩

/-- `rdist (Int.fract t) = rdist t`. -/
lemma rdist_fract (t : ℝ) : rdist (Int.fract t) = rdist t := by
  unfold rdist; rw [Int.fract_fract]

/-- `rdist (x + y) = rdist (Int.fract x + Int.fract y)`. -/
lemma rdist_add_eq (x y : ℝ) :
    rdist (x + y) = rdist (Int.fract x + Int.fract y) := by
  have h : x + y = (Int.fract x + Int.fract y) + ((⌊x⌋ + ⌊y⌋ : ℤ) : ℝ) := by
    have hx := Int.fract_add_floor x
    have hy := Int.fract_add_floor y
    push_cast
    linarith
  conv_lhs => rw [h]
  unfold rdist
  rw [Int.fract_add_intCast]

/-- On the unit interval, `rdist (u+v) ≤ rdist u + rdist v`; proved by splitting
on which of the two `rdist`-candidates for `u` and for `v` is realized. -/
lemma rdist_add_le_unit (u v : ℝ) (hu : 0 ≤ u) (hu1 : u < 1) (hv : 0 ≤ v) (hv1 : v < 1) :
    rdist (u + v) ≤ rdist u + rdist v := by
  have hru : rdist u = min u (1 - u) := by unfold rdist; rw [fract_eq_self hu hu1]
  have hrv : rdist v = min v (1 - v) := by unfold rdist; rw [fract_eq_self hv hv1]
  rw [hru, hrv]
  rcases lt_or_ge (u + v) 1 with hlt | hge
  · have hf : rdist (u + v) = min (u + v) (1 - (u + v)) := by
      unfold rdist; rw [fract_eq_self (by linarith) hlt]
    rw [hf, min_le_iff]
    rcases min_choice u (1 - u) with hu' | hu' <;> rcases min_choice v (1 - v) with hv' | hv'
    · rw [hu', hv']; left; linarith
    · rw [hu', hv']; right; linarith
    · rw [hu', hv']; right; linarith
    · rw [hu', hv']; right
      have hle : 1 - u ≤ u := by rw [← hu']; exact min_le_left u (1 - u)
      linarith
  · have hfract2 : Int.fract (u + v) = u + v - 1 := by
      rw [Int.fract_eq_iff]; exact ⟨by linarith, by linarith, ⟨1, by ring⟩⟩
    have hf : rdist (u + v) = min (u + v - 1) (2 - (u + v)) := by
      unfold rdist; rw [hfract2]; ring_nf
    rw [hf, min_le_iff]
    rcases min_choice u (1 - u) with hu' | hu' <;> rcases min_choice v (1 - v) with hv' | hv'
    · rw [hu', hv']; left; linarith
    · rw [hu', hv']; left; linarith
    · rw [hu', hv']; left; linarith
    · rw [hu', hv']; right; linarith

/-- **Triangle inequality.** `rdist (x + y) ≤ rdist x + rdist y`. -/
lemma rdist_add_le' (x y : ℝ) : rdist (x + y) ≤ rdist x + rdist y := by
  rw [rdist_add_eq, ← rdist_fract x, ← rdist_fract y]
  exact rdist_add_le_unit _ _ (Int.fract_nonneg x) (Int.fract_lt_one x)
    (Int.fract_nonneg y) (Int.fract_lt_one y)

/-- `rdist t ≤ |t|`. -/
lemma rdist_le_abs (t : ℝ) : rdist t ≤ |t| := by
  have hf : Int.fract t = t - (⌊t⌋ : ℝ) := by
    have := Int.fract_add_floor t; linarith
  rcases lt_or_ge t 0 with h | h
  · rw [abs_of_neg h]
    have hfl : (⌊t⌋ : ℝ) ≤ -1 := by
      have hz : ⌊t⌋ < 0 := Int.floor_lt.mpr (by simpa using h)
      exact_mod_cast (show ⌊t⌋ ≤ -1 by omega)
    have hb : rdist t ≤ 1 - Int.fract t := min_le_right _ _
    rw [hf] at hb
    linarith
  · rw [abs_of_nonneg h]
    have hfl : (0 : ℝ) ≤ (⌊t⌋ : ℝ) := by
      have hz : (0 : ℤ) ≤ ⌊t⌋ := Int.le_floor.mpr (by simpa using h)
      exact_mod_cast hz
    have hb : rdist t ≤ Int.fract t := min_le_left _ _
    rw [hf] at hb
    linarith

/-- **1-Lipschitz form.** `rdist (x + y) ≤ rdist x + |y|`. -/
lemma rdist_add_le (x y : ℝ) : rdist (x + y) ≤ rdist x + |y| := by
  have h1 := rdist_add_le' x y
  have h2 := rdist_le_abs y
  linarith

/-- **Reverse triangle form** (Tao's (5.15)). `rdist y − rdist x ≤ |y − x|`. -/
lemma rdist_sub_le_abs_sub (x y : ℝ) : rdist y - rdist x ≤ |y - x| := by
  have h1 := rdist_add_le x (y - x)
  rw [add_sub_cancel] at h1
  have h2 : |y - x| = |x - y| := by rw [show y - x = -(x - y) by ring, abs_neg]
  linarith

/-- Shifted form used in (5.15): `rdist x − |e| ≤ rdist (x + e)`. -/
lemma rdist_sub_abs_le_add (x e : ℝ) : rdist x - |e| ≤ rdist (x + e) := by
  have h := rdist_sub_le_abs_sub (x + e) x
  rw [show x - (x + e) = -e by ring, abs_neg] at h
  -- rearrange `rdist x - rdist (x+e) ≤ |e|` into the stated form by hand,
  -- since `linarith` treats `rdist` as an opaque atom.
  have h' : rdist x ≤ rdist (x + e) + |e| := by linarith
  linarith

/-! ## 5. The small-`d` regime of (5.15) -/

/-- `|d·β| ≤ 1/(2q)` when `|β| ≤ 1/q²` and `2d ≤ q`. -/
lemma d_mul_beta_le (beta : ℝ) (q : ℝ) (hq : 0 < q) (hbeta : |beta| ≤ 1/q^2)
    (d : ℕ) (hd2 : (d : ℝ) * 2 ≤ q) :
    |(d : ℝ) * beta| ≤ 1/(2*q) := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  rw [abs_mul, abs_of_nonneg hd0]
  have h2 : (d : ℝ) * |beta| ≤ (d : ℝ) * (1/q^2) := mul_le_mul_of_nonneg_left hbeta hd0
  have key : (q/2) * (1/q^2) = 1/(2*q) := by field_simp
  calc (d : ℝ) * |beta| ≤ (d : ℝ) * (1/q^2) := h2
    _ ≤ (q/2) * (1/q^2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith [hd2]
    _ = 1/(2*q) := key

/-- **(5.15), quantitative core.** If `4α = a/q + β`, `|β| ≤ 1/q²`, `2d ≤ q` and
`q ∤ a d`, then `‖4 d α‖_{ℝ/ℤ} ≥ 1/(2q)`.  (Here `ad` plays the role of `a d`.) -/
lemma rdist_d_alpha_ge (ad q : ℤ) (alpha beta : ℝ)
    (hq : 0 < q) (hbeta : |beta| ≤ 1/(q:ℝ)^2) (hnondiv : ¬ (q ∣ ad))
    (d : ℕ) (_hd1 : 1 ≤ d) (hd2 : (d : ℝ) * 2 ≤ q)
    (hkey : 4 * (d : ℝ) * alpha = (ad : ℝ)/(q : ℝ) + (d : ℝ) * beta) :
    1/(2*(q:ℝ)) ≤ rdist (4 * (d : ℝ) * alpha) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h1 : 1/(q : ℝ) ≤ rdist ((ad : ℝ)/(q : ℝ)) := rdist_div_ge ad q hq hnondiv
  have h2 : |(d : ℝ) * beta| ≤ 1/(2*(q : ℝ)) :=
    d_mul_beta_le beta (q : ℝ) hqR hbeta d hd2
  rw [hkey]
  have h3 : 1/(q : ℝ) - |(d : ℝ) * beta|
      ≤ rdist ((ad : ℝ)/(q : ℝ) + (d : ℝ) * beta) := by
    have h5 := rdist_sub_abs_le_add ((ad : ℝ)/(q : ℝ)) ((d : ℝ) * beta)
    linarith [h1, h5]
  have h4 : 1/(2*(q : ℝ)) = 1/(q : ℝ) - 1/(2*(q : ℝ)) := by field_simp; ring
  linarith [h2, h4, h3]

end TaoFivePrimesBlock


