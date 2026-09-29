-- Prove2me | Definitions.Def_TaoFivePrimes_BlockFoundationCor35
-- name    : TaoFivePrimes_BlockFoundationCor35
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-09-15T19:39:04.978646+00:00
-- url     : https://prove2.me/theorems/384412a7-65a6-4f99-b834-2ca2c916e7ed
-- title:
--   Tao Type I block summation: (2.1), block structure, frozen envelope, and Corollary 3.5 from Lemma 3.4
-- statement:
--   **The reusable interface for Tao's Type I block summation, with the odd-restricted Vinogradov reduction.**
--
--   This module collects the layers of Tao's Section 5 argument
--   (arXiv:1201.6656v4, the passage (5.14) → (5.17)) that are independent of any
--   particular exponential-sum input, plus the reduction of Corollary 3.5 to
--   Lemma 3.4.
--
--   **§1-5 — integer distance and the sine envelope.** With $\|t\|_{\mathbb R/\mathbb Z}$ the distance from $t$ to the nearest integer, realized as `rdist t = min (Int.fract t) (1 - Int.fract t)`:
--
--   $$2\,\|t\|_{\mathbb R/\mathbb Z}\ \le\ |\sin(\pi t)|\ \le\ \pi\,\|t\|_{\mathbb R/\mathbb Z}. \tag{2.1}$$
--
--   Lower and upper halves are `two_rdist_le_abs_sin` and `abs_sin_le_pi_mul_rdist`. `rdist` is proved to be a genuine metric pseudo-norm (`rdist_add_le'`, `rdist_add_le`, `rdist_sub_le_abs_sub`); `q \nmid m` forces $\|m/q\|_{\mathbb R/\mathbb Z} \ge 1/q$ (`rdist_div_ge`); and the small-$d$ core of (5.15): if $4\alpha = a/q + \beta$, $|\beta| \le q^{-2}$, $2d \le q$, $q \nmid ad$, then $\|4d\alpha\|_{\mathbb R/\mathbb Z} \ge 1/(2q)$ (`rdist_d_alpha_ge`).
--
--   **§6-7 — the block structure.** `blockLeft q j = 2jq + q/2`, `blockRight q j = 2(j+1)q + q/2`, differing by exactly $2q$ (`blockRight_sub_blockLeft`), which is what makes the harmonic sum over blocks comparable with an integral. `blockLeft_lt_of` / `le_blockRight_of` translate between the doubled integer spacing $4jq + q < 2d \le 4(j+1)q + q$ and the real interval; `mem_block_iff` states the equivalence.
--
--   **§8 — the frozen envelope.** On a block the pointwise envelope $\frac12\frac xd\log x + 4(\log 2)\log 2x$ is dominated by its value at the left endpoint; since the node's envelope is a `min`, freezing the $\frac xd$ term while retaining the cosecant term is legitimate. This is `freeze_x_div` plus `envelope_frozen_vanish` / `envelope_frozen_nonvanish`.
--
--   **§9-12 — Corollary 3.5 from Lemma 3.4.** The published statements are recorded as the `Prop`-valued definitions `vinogradovMinSum` (Lemma 3.4) and `vinogradovMinSumOdd` (Corollary 3.5). The genuinely new content is the **reindexing**:
--
--   * `odd_mem_Ioc_iff`: for $1 \le x$, the odd integer $2m+1$ lies in $(x, y]$ exactly when $m$ lies in $((x-1)/2, (y-1)/2]$, i.e.
--     $2m+1 \in \mathrm{Ioc}\,\lfloor x\rfloor\,\lfloor y\rfloor \iff \lfloor (x-1)/2\rfloor < m \le \lfloor (y-1)/2\rfloor$.
--     The hypothesis $1 \le x$ is **not** removable: at $x=0, y=1$ the odd integer $1 = 2\cdot 0 + 1$ lies in $(0,1]$ but $\lfloor -1/2\rfloor < 0$ is false.
--   * `odd_min_sum_reindex`: `Finset.sum_bij` along $n \mapsto (n-1)/2$ identifies the odd min-sum with parameter $\alpha$ and phase $\theta$ with the full min-sum with parameter $2\alpha$ and phase $\pi\alpha + \theta$.
--   * `odd_vinogradov_min_sum`: Corollary 3.5 for $(\alpha, \theta)$ follows from Lemma 3.4 instantiated at $(2\alpha, \pi\alpha+\theta)$ on the shifted endpoints, since $(y-x)/(2q) = ((y-1)/2 - (x-1)/2)/q$.
--
--   Only this index arithmetic is proved; the analytic content of Lemma 3.4 (the Vinogradov bound) stays a hypothesis of the reduction.
--
--   **Formalization Note.** Everything is `sorry`-free and Mathlib-only, with the only axioms `propext`, `Classical.choice`, `Quot.sound`. Endpoint statements are stated in doubled integer form because `linarith` treats $\uparrow q/2$ as an opaque atom; the halving is done once by `div_lt_iff₀` after a `ring` normalization. No `conv` is used (rewriting under `abs`/`Real.sin` via `conv_rhs` exhausts the heartbeat budget in this environment). `Nat.floor_lt` requires an explicit `0 ≤ a` side condition, which is why the reindexing carries `1 ≤ x`.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, the block decomposition (5.14)-(5.17) and the odd-restricted Vinogradov estimate (5.15)-(5.16); Section 2, inequality (2.1); Lemma 3.4 and Corollary 3.5.

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
  envelope by its value frozen at the left endpoint;
* **§9-12 Corollary 3.5** — the floor helper lemmas, the index-set identity
  `2m+1 ∈ (x,y] ↔ m ∈ ((x-1)/2, (y-1)/2]`, the reindexing of the
  odd min-sum onto the full min-sum with parameter `2α` and phase
  `π α + θ`, and the resulting reduction of Corollary 3.5 to Lemma 3.4.

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

/-! ## 9. Floor helper lemmas for the reindexing -/

/-- If `1 ≤ ⌊y⌋₊` then `1 ≤ y`.  Used to make `Nat.floor_le` applicable to
`y` in the reindexing, where positivity of `y` is not a hypothesis but does
follow from the interval being nonempty. -/
lemma one_le_of_one_le_floor {y : ℝ} (h : 1 ≤ ⌊y⌋₊) : (1 : ℝ) ≤ y := by
  by_contra hc
  push_neg at hc
  have hz : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith : y < 1)
  omega

/-- `⌊y⌋₊ ≤ y` whenever `⌊y⌋₊ ≥ 1`; the positivity of `y` comes from the
previous lemma rather than being assumed. -/
lemma floor_le_of_one_le_floor {y : ℝ} (h : 1 ≤ ⌊y⌋₊) : (⌊y⌋₊ : ℝ) ≤ y :=
  Nat.floor_le (le_trans zero_le_one (one_le_of_one_le_floor h))

/-! ## 10. The reindexing `n = 2m + 1` -/

/-- **The index-set identity.**  For `1 ≤ x` and `m : ℕ`, the odd integer
`2m + 1` lies in `(x, y]` exactly when `m` lies in `((x-1)/2, (y-1)/2]`.

The hypothesis `1 ≤ x` is what makes `(x-1)/2 ≥ 0`, so that
`Nat.floor_lt` applies to `(x-1)/2`.  It is not removable: at `x = 0`,
`y = 1` the odd integer `1 = 2·0+1` lies in `(0, 1]` but the right-hand
side is `⌊-1/2⌋₊ < 0`, which is false. -/
lemma odd_mem_Ioc_iff (x y : ℝ) (hx : 1 ≤ x) (m : ℕ) :
    2 * m + 1 ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n.Coprime 2)
      ↔ ⌊(x - 1) / 2⌋₊ < m ∧ m ≤ ⌊(y - 1) / 2⌋₊ := by
  have hx0 : (0 : ℝ) ≤ (x - 1) / 2 := by linarith
  rw [Finset.mem_filter, Finset.mem_Ioc, Nat.coprime_two_right]
  constructor
  · rintro ⟨⟨h1, h2⟩, _hodd⟩
    have hfloor1 : 1 ≤ ⌊y⌋₊ := by omega
    have hy1 : (1 : ℝ) ≤ y := one_le_of_one_le_floor hfloor1
    have hy0 : (0 : ℝ) ≤ (y - 1) / 2 := by linarith
    constructor
    · rw [Nat.floor_lt hx0]
      have h1'' : ⌊x⌋₊ ≤ 2 * m := by omega
      have h1' : ((⌊x⌋₊ : ℕ) : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast h1''
      push_cast at h1'
      have hxlt := Nat.lt_floor_add_one x
      linarith
    · rw [Nat.le_floor_iff hy0]
      have h2' : ((2 * m + 1 : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast h2
      push_cast at h2'
      linarith [floor_le_of_one_le_floor hfloor1]
  · rintro ⟨h1, h2⟩
    have hm1 : 1 ≤ m := Nat.lt_of_le_of_lt (Nat.zero_le _) h1
    have hy0 : (0 : ℝ) ≤ (y - 1) / 2 := by
      -- `m ≥ 1` and `m ≤ ⌊(y-1)/2⌋₊`, so `(y-1)/2 ≥ 1`
      have hfloor1 : 1 ≤ ⌊(y - 1) / 2⌋₊ := le_trans hm1 h2
      have hstep : (1 : ℝ) ≤ (y - 1) / 2 := one_le_of_one_le_floor hfloor1
      linarith
    constructor
    · constructor
      · -- `⌊x⌋₊ < 2m + 1`
        have hm : ((x - 1) / 2 : ℝ) < (m : ℝ) := (Nat.floor_lt hx0).mp h1
        have hx' : x < ((2 * m + 1 : ℕ) : ℝ) := by push_cast; linarith
        -- `⌊x⌋₊ ≤ x < 2m+1` in `ℕ`, so `⌊x⌋₊ ≤ 2m`
        have hxle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
        have h2m : ((2 * m : ℕ) : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by push_cast; linarith
        have : (⌊x⌋₊ : ℕ) < 2 * m + 1 := by
          have hR : ((⌊x⌋₊ : ℕ) : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by linarith
          exact_mod_cast hR
        omega
      · -- `2m + 1 ≤ ⌊y⌋₊`
        have hm : (m : ℝ) ≤ (y - 1) / 2 := (Nat.le_floor_iff hy0).mp h2
        have hy : ((2 * m + 1 : ℕ) : ℝ) ≤ y := by push_cast; linarith
        exact Nat.le_floor hy
    · exact ⟨m, by ring⟩

/-! ## 11. The reindexing as a sum identity -/

/-- **The reindexing step.** `n = 2m + 1` turns the odd min-sum with
`α` and phase `θ` into the full min-sum with `2α` and phase `π α + θ`.
This is the entire content of the proof of Corollary 3.5.

The identity is stated with `1 ≤ x`, which the index-set identity requires;
in every application `x ≥ 1` (the summations start at `d = 1`). -/
lemma odd_min_sum_reindex (A B alpha theta : ℝ) (x y : ℝ) (hx : 1 ≤ x) :
    (∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n.Coprime 2),
        min A (B / |Real.sin (Real.pi * alpha * (n : ℝ) + theta)|))
      = ∑ m ∈ Finset.Ioc ⌊(x - 1) / 2⌋₊ ⌊(y - 1) / 2⌋₊,
          min A (B / |Real.sin (Real.pi * (2 * alpha) * (m : ℝ)
            + (Real.pi * alpha + theta))|) := by
  refine Finset.sum_bij (fun n _ => (n - 1) / 2) ?_ ?_ ?_ ?_
  · -- the image lands in the target index set
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨h1, h2⟩, hcop⟩ := hn
    have hodd : Odd n := Nat.coprime_two_right.mp hcop
    -- `n` is odd, so `n = 2k + 1`; then `(n-1)/2 = k`
    obtain ⟨k, hk⟩ := hodd
    rw [Finset.mem_Ioc]
    have hkx : (n - 1) / 2 = k := by omega
    rw [hkx]
    -- translate `⌊x⌋₊ < n = 2k+1 ≤ ⌊y⌋₊` into the `k`-range
    have hk1 : ((x - 1) / 2 : ℝ) < (k : ℝ) := by
      have hx0 : (0 : ℝ) ≤ (x - 1) / 2 := by linarith
      have hxl : ⌊x⌋₊ ≤ 2 * k := by omega
      have hcast : ((⌊x⌋₊ : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast hxl
      push_cast at hcast
      have hxlt := Nat.lt_floor_add_one x
      linarith
    have hk2 : (k : ℝ) ≤ (y - 1) / 2 := by
      have hy0 : (0 : ℝ) ≤ (y - 1) / 2 := by
        have hfloor1 : 1 ≤ ⌊y⌋₊ := by omega
        have := one_le_of_one_le_floor hfloor1
        linarith
      have h2' : ((2 * k + 1 : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by
        exact_mod_cast (show 2 * k + 1 ≤ ⌊y⌋₊ by omega)
      push_cast at h2'
      linarith [floor_le_of_one_le_floor (show 1 ≤ ⌊y⌋₊ by omega)]
    constructor
    · exact (Nat.floor_lt (by linarith : (0 : ℝ) ≤ (x - 1) / 2)).mpr hk1
    · exact Nat.le_floor hk2
  · -- injectivity
    intro n hn n' hn' heq
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn hn'
    obtain ⟨⟨_, _⟩, hcop⟩ := hn
    obtain ⟨⟨_, _⟩, hcop'⟩ := hn'
    obtain ⟨k, hk⟩ := Nat.coprime_two_right.mp hcop
    obtain ⟨k', hk'⟩ := Nat.coprime_two_right.mp hcop'
    have h1 : (n - 1) / 2 = k := by omega
    have h2 : (n' - 1) / 2 = k' := by omega
    omega
  · -- surjectivity
    intro m hm
    refine ⟨2 * m + 1, ?_, ?_⟩
    · have hmem : 2 * m + 1 ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n.Coprime 2) :=
        (odd_mem_Ioc_iff x y hx m).mpr (Finset.mem_Ioc.mp hm)
      exact hmem
    · show (2 * m + 1 - 1) / 2 = m
      omega
  · -- the summands agree
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨_, _⟩, hcop⟩ := hn
    obtain ⟨k, hk⟩ := Nat.coprime_two_right.mp hcop
    rw [hk, show (2 * k + 1 - 1) / 2 = k by omega]
    congr 1
    push_cast
    ring

/-! ## 12. The published statements as reusable `Prop`s

Both Lemma 3.4 and Corollary 3.5 are stated as `Prop`-valued definitions so
that they can be cited, instantiated, and reused across modules without
repeating the long Finset expression.  The **content** of Lemma 3.4 is the
classical Vinogradov bound and is carried as a hypothesis of the reduction
below; only the reindexing (the passage from Corollary 3.5 to Lemma 3.4) is
proved here. -/

/-- **Lemma 3.4 (Vinogradov-type lemma).**  The full-sum bound, with the
summation variable an integer `n` in the half-open interval `(x, y]`, phase
`π α n + θ`, and `⌊(y-x)/q⌋ + 1` blocks of length `q`.

This is the published input; it is *not* re-proved here. -/
def vinogradovMinSum (q : ℕ) (A B alpha theta x y : ℝ) : Prop :=
  (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, min A (B / |Real.sin (Real.pi * alpha * (n : ℝ) + theta)|))
    ≤ (((⌊(y - x) / (q : ℝ)⌋₊ + 1 : ℕ)) : ℝ)
        * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * (q : ℝ)))

/-- **Corollary 3.5 (restricting to odd integers).**  The odd-sum bound: the
summand is the same `min` expression, restricted to odd `n` in `(x, y]`, and
the block count is `⌊(y-x)/(2q)⌋ + 1` — the factor of two coming from the odd
restriction. -/
def vinogradovMinSumOdd (q : ℕ) (A B alpha theta x y : ℝ) : Prop :=
  (∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n.Coprime 2),
      min A (B / |Real.sin (Real.pi * alpha * (n : ℝ) + theta)|))
    ≤ (((⌊(y - x) / (2 * (q : ℝ))⌋₊ + 1 : ℕ)) : ℝ)
        * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * (q : ℝ)))

/-- **Corollary 3.5 from Lemma 3.4.**  The odd-restricted min-sum with
parameter `α` and phase `θ` is bounded by applying the Vinogradov bound to
the *full* interval with parameter `2α`, phase `π α + θ`, and the shifted
endpoints `(x-1)/2`, `(y-1)/2`.

The proof is the reindexing `n = 2m + 1` (`odd_min_sum_reindex`) together
with the arithmetic identity `(y - x)/(2q) = ((y-1)/2 - (x-1)/2)/q`, which
makes the two block counts agree.  Only the *index arithmetic* is proved
here; the analytic content of Lemma 3.4 stays a hypothesis. -/
theorem odd_vinogradov_min_sum (q : ℕ) (A B alpha theta x y : ℝ) (hx : 1 ≤ x)
    (hmain : vinogradovMinSum q A B (2 * alpha) (Real.pi * alpha + theta)
      ((x - 1) / 2) ((y - 1) / 2)) :
    vinogradovMinSumOdd q A B alpha theta x y := by
  unfold vinogradovMinSumOdd vinogradovMinSum at *
  rw [odd_min_sum_reindex A B alpha theta x y hx]
  -- The two block counts agree because `(y-x)/(2q) = ((y-1)/2-(x-1)/2)/q`.
  have hkey : (y - x) / (2 * (q : ℝ))
      = ((y - 1) / 2 - (x - 1) / 2) / (q : ℝ) := by ring
  rw [hkey]
  exact hmain

end TaoFivePrimesBlock


