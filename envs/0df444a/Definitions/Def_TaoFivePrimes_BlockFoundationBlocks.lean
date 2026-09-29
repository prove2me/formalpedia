-- Prove2me | Definitions.Def_TaoFivePrimes_BlockFoundationBlocks
-- name    : TaoFivePrimes_BlockFoundationBlocks
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-09-15T18:29:17.75997+00:00
-- url     : https://prove2.me/theorems/d35eadad-7092-4a24-8634-0e7d24732a84
-- title:
--   Tao Type I block summation: integer distance, (2.1), block structure, frozen envelope
-- statement:
--   **The full reusable interface for Tao's Type I block summation.**
--
--   This module collects the three layers of Tao's Section 5 argument
--   (arXiv:1201.6656v4, the passage (5.14) → (5.17)) that are independent of
--   any particular exponential-sum input.
--
--   **§1-5 — integer distance and the sine envelope.** With $\|t\|_{\mathbb R/\mathbb Z}$ the distance from $t$ to the nearest integer, realized as `rdist t = min (Int.fract t) (1 - Int.fract t)`:
--
--   $$2\,\|t\|_{\mathbb R/\mathbb Z}\ \le\ |\sin(\pi t)|\ \le\ \pi\,\|t\|_{\mathbb R/\mathbb Z}. \tag{2.1}$$
--
--   The lower and upper halves are `two_rdist_le_abs_sin` and
--   `abs_sin_le_pi_mul_rdist`. The module also proves `rdist` is a genuine
--   metric pseudo-norm (§4: `rdist_add_le'`, `rdist_add_le`,
--   `rdist_sub_le_abs_sub`), that `q \nmid m` forces
--   $\|m/q\|_{\mathbb R/\mathbb Z} \ge 1/q$ (`rdist_div_ge`), and the
--   small-$d$ quantitative core of (5.15): if $4\alpha = a/q + \beta$ with
--   $|\beta| \le q^{-2}$, $2d \le q$ and $q \nmid ad$, then
--   $\|4d\alpha\|_{\mathbb R/\mathbb Z} \ge \frac{1}{2q}$
--   (`rdist_d_alpha_ge`). Together with (2.1) this yields the uniform bound
--   $|\sin(2\pi d\alpha)| \ge 1/q$, i.e. $1/|\sin(2\pi d\alpha)| \le 2q$, on
--   $d \le q/2$.
--
--   **§6-7 — the block structure.** `blockLeft q j = 2jq + \tfrac q2` and
--   `blockRight q j = 2(j+1)q + \tfrac q2` are the block endpoints; their
--   difference is exactly $2q$ (`blockRight_sub_blockLeft`), which is what
--   makes the harmonic sum over blocks comparable with an integral. The two
--   endpoint lemmas translate between the *doubled integer spacing*
--   $4jq + q < 2d \le 4(j+1)q + q$ and the real interval
--   $\mathrm{blockLeft}\,q\,j < d \le \mathrm{blockRight}\,q\,j$, and
--   `mem_block_iff` states the equivalence.
--
--   **§8 — the frozen envelope.** On a block, the pointwise envelope
--   $\frac12\frac xd\log x + 4(\log 2)\log 2x$ is increasing as $d$ decreases,
--   so it is dominated by its value at the left endpoint; since the node's
--   envelope is a `min` of two alternatives, freezing the $\frac xd$ term while
--   retaining the cosecant term is legitimate. This is `freeze_x_div` together
--   with `envelope_frozen_vanish` / `envelope_frozen_nonvanish`, the two cases
--   of the sine vanishing or not.
--
--   **Formalization Note.** Everything is `sorry`-free and Mathlib-only.
--   The block endpoint statements are stated in doubled integer form because
--   `linarith` treats $\uparrow q/2$ as an opaque atom; the halving is done
--   once by `div_lt_iff₀` after a `ring` normalization. No `conv` is used
--   anywhere (rewriting under `abs`/`Real.sin` via `conv_rhs` exhausts the
--   heartbeat budget in this environment).
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, the block decomposition (5.14)-(5.17), and Section 2, inequality (2.1).

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

set_option maxHeartbeats 800000

/-! # Type I block summation: reusable foundation, block structure, envelope

Reusable interface for the Prove2Me node
`TaoFivePrimes.theorem51_typeI_block_summation`, following Tao,
arXiv:1201.6656v4, Section 5, (5.14) → (5.17), and Section 2 (2.1).

Three layers, all `sorry`-free and Mathlib-only:

* **§1-5 foundation** — the distance to the nearest integer `rdist`, its
  triangle inequality, inequality (2.1), and the small-`d` core of (5.15)
  (`1/|sin (2πdα)| ≤ 2q` for `2d ≤ q`);
* **§6-7 block structure** — the block endpoints `2jq + q/2` and
  `2(j+1)q + q/2`, the bridge between the doubled integer spacing and the
  real block interval;
* **§8 frozen envelope** — the per-block domination of the pointwise
  envelope by its value frozen at the left endpoint.

Design notes for this environment:

* no `conv`: rewriting under `abs`/`Real.sin` via `conv_rhs` exhausts the
  heartbeat budget.  Every step is an equality of *arguments* applied by
  `rw`;
* `linarith` cannot see through `Int.fract`/`Int.floor` casts, so each such
  bridge is a separate real-valued lemma;
* `linarith`/`nlinarith` treat `↑q / 2` as an opaque atom.  Endpoint
  statements are therefore *stated* in doubled integer form and halved
  once, after a `ring` normalization, by `div_lt_iff₀` / `le_div_iff₀`. -/

open Finset

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

/-! ## 6. The block index and its endpoints -/

/-- The left endpoint `2jq + q/2` of block `j`. -/
noncomputable def blockLeft (q : ℕ) (j : ℕ) : ℝ :=
  2 * (j : ℝ) * (q : ℝ) + (q : ℝ) / 2

/-- The right endpoint `2(j+1)q + q/2` of block `j`. -/
noncomputable def blockRight (q : ℕ) (j : ℕ) : ℝ :=
  2 * ((j : ℝ) + 1) * (q : ℝ) + (q : ℝ) / 2

lemma blockRight_eq (q j : ℕ) : blockRight q j = blockLeft q (j + 1) := by
  unfold blockRight blockLeft
  push_cast
  ring

lemma blockRight_sub_blockLeft (q j : ℕ) : blockRight q j - blockLeft q j = 2 * (q : ℝ) := by
  unfold blockRight blockLeft
  ring

/-- `blockLeft` is strictly increasing in the block index when `q > 0`. -/
lemma blockLeft_lt_succ {q : ℕ} (hq : 0 < q) (j : ℕ) :
    blockLeft q j < blockLeft q (j + 1) := by
  unfold blockLeft
  push_cast
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  linarith

/-- Every block left endpoint is positive. -/
lemma blockLeft_pos {q : ℕ} (hq : 0 < q) (j : ℕ) : 0 < blockLeft q j := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  unfold blockLeft
  have key : 2 * (j : ℝ) * (q : ℝ) + (q : ℝ) / 2
      = ((4 * (j : ℝ) * (q : ℝ)) + (q : ℝ)) / 2 := by ring
  rw [key]
  apply div_pos _ (by norm_num : (0 : ℝ) < 2)
  nlinarith

/-! ## 7. Membership in a block

The integer predicate `4jq + q < 2d ≤ 4(j+1)q + q` is the doubled form of
`blockLeft q j < d ≤ blockRight q j`. -/

/-- **Lower endpoint.** `4jq + q < 2d` halves to `blockLeft q j < d`. -/
lemma blockLeft_lt_of (q d j : ℕ) (h : 4 * j * q + q < 2 * d) :
    blockLeft q j < (d : ℝ) := by
  have hcast : ((4 * j * q + q : ℕ) : ℝ) < ((2 * d : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hcast
  unfold blockLeft
  have key : 2 * (j : ℝ) * (q : ℝ) + (q : ℝ) / 2
      = ((4 * (j : ℝ) * (q : ℝ)) + (q : ℝ)) / 2 := by ring
  rw [key, div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- **Upper endpoint.** `2d ≤ 4(j+1)q + q` halves to `d ≤ blockRight q j`. -/
lemma le_blockRight_of (q d j : ℕ) (h : 2 * d ≤ 4 * (j + 1) * q + q) :
    (d : ℝ) ≤ blockRight q j := by
  have hcast : ((2 * d : ℕ) : ℝ) ≤ ((4 * (j + 1) * q + q : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hcast
  unfold blockRight
  have key : 2 * ((j : ℝ) + 1) * (q : ℝ) + (q : ℝ) / 2
      = ((4 * ((j : ℝ) + 1) * (q : ℝ)) + (q : ℝ)) / 2 := by ring
  rw [key, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- **Block membership.** The doubled integer spacing is equivalent to the
real block interval `blockLeft q j < d ≤ blockRight q j`. -/
lemma mem_block_iff (q d j : ℕ) :
    (4 * j * q + q < 2 * d ∧ 2 * d ≤ 4 * (j + 1) * q + q)
      ↔ blockLeft q j < (d : ℝ) ∧ (d : ℝ) ≤ blockRight q j := by
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨blockLeft_lt_of q d j h1, le_blockRight_of q d j h2⟩
  · intro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have hR : ((4 * j * q + q : ℕ) : ℝ) < ((2 * d : ℕ) : ℝ) := by
        push_cast
        unfold blockLeft at h1
        linarith [h1]
      exact_mod_cast hR
    · have hR : ((2 * d : ℕ) : ℝ) ≤ ((4 * (j + 1) * q + q : ℕ) : ℝ) := by
        push_cast
        unfold blockRight at h2
        linarith [h2]
      exact_mod_cast hR

/-! ## 8. Freezing the `x/d` term at the left endpoint -/

/-- **Freeze step.** If `d` is in block `j` (so `blockLeft q j < d`) and
`d > 0`, then the first alternative of the node's envelope at `d` is at
most its value at the left endpoint:

`(1/2)(x/d) log x + 4 (log 2) log 2x ≤ x / (2 (2jq + q/2)) · log x + 4 (log 2) log 2x`

(the factor `2` in the denominator is the node's `1/2`, rewritten as
`x / (2 · blockLeft)`).  Requires `0 < x` and `0 ≤ log x` to keep the
direction of the comparison. -/
lemma freeze_x_div {q d j : ℕ} {x : ℝ}
    (hx : 0 < x) (hlx : 0 ≤ Real.log x) (hq : 0 < q)
    (hleft : blockLeft q j < (d : ℝ)) (_hd : 0 < (d : ℝ)) :
    (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
      ≤ x / (2 * blockLeft q j) * Real.log x + 4 * Real.log 2 * Real.log (2 * x) := by
  have hbl : 0 < blockLeft q j := blockLeft_pos hq j
  -- `x/d ≤ x/blockLeft` because `blockLeft ≤ d` and `x > 0`
  have hdvd : x / (d : ℝ) ≤ x / blockLeft q j := by
    exact div_le_div_of_nonneg_left hx.le hbl hleft.le
  have hstep : (1 / 2) * (x / (d : ℝ)) ≤ x / (2 * blockLeft q j) := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    -- `x / (2 * bL) = (x / bL) / 2` and `(1/2) * (x/d) = (x/d)/2`
    have heq1 : x / (2 * blockLeft q j) = (x / blockLeft q j) / 2 := by
      rw [div_mul_eq_div_div, div_right_comm]
    have heq2 : (1 / 2) * (x / (d : ℝ)) = (x / (d : ℝ)) / 2 := by ring
    rw [heq1, heq2]
    exact div_le_div_of_nonneg_right hdvd h2.le
  have : (1 / 2) * (x / (d : ℝ)) * Real.log x
      ≤ x / (2 * blockLeft q j) * Real.log x :=
    mul_le_mul_of_nonneg_right hstep hlx
  linarith

/-- **Envelope domination.** Any `W` obeying the node's pointwise envelope
at `d` is bounded by either alternative.  This is the `min`-splitting used
to choose the second alternative on a block. -/
lemma envelope_le_second {x alpha : ℝ} {d : ℕ} {W : ℕ → ℝ}
    (hWb : W d ≤
      (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
        (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
      else min ((1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x))
        (4 * Real.log 2 * Real.log (2 * x) / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|))) :
    W d ≤
      (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
        (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
      else 4 * Real.log 2 * Real.log (2 * x) / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|) := by
  refine hWb.trans ?_
  by_cases h : Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact min_le_right _ _

/-- **Frozen envelope, vanishing sine.** When `sin (2πdα) = 0` the node's
envelope is exactly the first alternative, and the freeze step bounds it by
the block's frozen first alternative. -/
lemma envelope_frozen_vanish {q d j : ℕ} {x alpha : ℝ} {W : ℕ → ℝ}
    (hx : 0 < x) (hlx : 0 ≤ Real.log x) (hq : 0 < q)
    (hleft : blockLeft q j < (d : ℝ)) (hd : 0 < (d : ℝ))
    (hsin : Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0)
    (hWb : W d ≤
      (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
        (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
      else min ((1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x))
        (4 * Real.log 2 * Real.log (2 * x) / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|))) :
    W d ≤ x / (2 * blockLeft q j) * Real.log x + 4 * Real.log 2 * Real.log (2 * x) := by
  have h := hWb
  rw [if_pos hsin] at h
  exact h.trans (freeze_x_div hx hlx hq hleft hd)

/-- **Frozen envelope, nonvanishing sine.** When `sin (2πdα) ≠ 0` the node's
envelope is the `min` of the two alternatives, so it is dominated by the
block envelope: frozen first alternative in the first slot, the actual
cosecant term in the second. -/
lemma envelope_frozen_nonvanish {q d j : ℕ} {x alpha : ℝ} {W : ℕ → ℝ}
    (hx : 0 < x) (hlx : 0 ≤ Real.log x) (hq : 0 < q)
    (hleft : blockLeft q j < (d : ℝ)) (hd : 0 < (d : ℝ))
    (hsin : Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) ≠ 0)
    (hWb : W d ≤
      (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
        (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
      else min ((1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x))
        (4 * Real.log 2 * Real.log (2 * x) / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|))) :
    W d ≤
      min (x / (2 * blockLeft q j) * Real.log x + 4 * Real.log 2 * Real.log (2 * x))
        (4 * Real.log 2 * Real.log (2 * x) / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|) := by
  have h := hWb
  rw [if_neg hsin] at h
  exact h.trans (le_min ((min_le_left _ _).trans (freeze_x_div hx hlx hq hleft hd))
    (min_le_right _ _))

end TaoFivePrimesBlock


