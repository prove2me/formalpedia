-- Prove2me | Definitions.Def_Thm_BraidsLinksMCG_segment_coords
-- name    : Thm_BraidsLinksMCG_segment_coords
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-26T13:30:05.487752+00:00
-- url     : https://prove2.me/theorems/04d7854e-2d3b-41b1-8735-7186c352d00c
-- title:
--   Coordinate behaviour along a segment in the complex plane
-- statement:
--   This module records three elementary facts about straight segments in $\mathbb C$. Write a segment as $\overline{xy} = \{ (1-t)x + ty : t \in [0,1] \}$. First, if two endpoints agree in their real part then every point of the segment has that same real part; likewise for the imaginary part. Second, the real part of any point of the segment lies between the real parts of the two endpoints, in the sense that $\min(\operatorname{Re} x, \operatorname{Re} y) \leq \operatorname{Re} z$ and $\operatorname{Re} z \leq \max(\operatorname{Re} x, \operatorname{Re} y)$. Each statement is proved by unfolding the segment as an affine image of $[0,1]$ and computing, so the coefficient $(1-t)$ is non-negative throughout and may be used to multiply an inequality without reversing it. These facts supply the analytic input for the later claim that a straight-line homotopy between two points of a half-plane region remains inside that region.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

open BraidsLinksMCG

namespace BraidsLinksMCG

/-!
# Coordinate behaviour along a segment in the complex plane

Three facts about a straight segment, all proved by writing it as
`segment ℝ x y = { (1-t) • x + t • y | t ∈ [0,1] }` and then computing:

* `segment_const_re` / `segment_const_im`: a coordinate that agrees on the two
  endpoints is constant along the whole segment;
* `segment_re_between`: the real part of a point of the segment lies between the
  real parts of the endpoints.

These are the analytic input for showing that a straight-line homotopy between two
points of a half-plane region stays inside that region.
-/

-- ### Coordinate behaviour along a segment

/-- The real part is constant along a segment whose endpoints have the same
real part. -/
theorem segment_const_re {x y : ℂ} (hxy : x.re = y.re) :
    ∀ z ∈ segment ℝ x y, z.re = x.re := by
  intro z hz
  rw [segment_eq_image ℝ x y] at hz
  rcases hz with ⟨t, _, rfl⟩
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  rw [← hxy]
  ring

/-- The imaginary part is constant along a segment whose endpoints have the
same imaginary part. -/
theorem segment_const_im {x y : ℂ} (hxy : x.im = y.im) :
    ∀ z ∈ segment ℝ x y, z.im = x.im := by
  intro z hz
  rw [segment_eq_image ℝ x y] at hz
  rcases hz with ⟨t, _, rfl⟩
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  rw [← hxy]
  ring

/-- The real part along a segment lies between the endpoint real parts. -/
theorem segment_re_between {x y : ℂ} :
    ∀ z ∈ segment ℝ x y, min x.re y.re ≤ z.re ∧ z.re ≤ max x.re y.re := by
  intro z hz
  rw [segment_eq_image ℝ x y] at hz
  rcases hz with ⟨t, ht, rfl⟩
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  have hft1 : (0 : ℝ) ≤ t := ht.1
  have hft2 : t ≤ 1 := ht.2
  have hft0 : (0 : ℝ) ≤ 1 - t := sub_nonneg.mpr hft2
  constructor
  · rcases min_cases x.re y.re with ⟨heq, hle⟩ | ⟨heq, hlt⟩
    · rw [heq]
      have h1 : (1 - t) * x.re ≤ (1 - t) * y.re :=
        mul_le_mul_of_nonneg_left hle hft0
      have h2 : t * x.re ≤ t * y.re := mul_le_mul_of_nonneg_left hle hft1
      linarith
    · rw [heq]
      have h1 : (1 - t) * y.re ≤ (1 - t) * x.re :=
        mul_le_mul_of_nonneg_left (le_of_lt hlt) hft0
      have h2 : t * y.re ≤ t * x.re := mul_le_mul_of_nonneg_left (le_of_lt hlt) hft1
      linarith
  · rcases max_cases x.re y.re with ⟨heq, hle⟩ | ⟨heq, hlt⟩
    · rw [heq]
      have h1 : (1 - t) * y.re ≤ (1 - t) * x.re :=
        mul_le_mul_of_nonneg_left hle hft0
      have h2 : t * y.re ≤ t * x.re := mul_le_mul_of_nonneg_left hle hft1
      linarith
    · rw [heq]
      have h1 : (1 - t) * x.re ≤ (1 - t) * y.re :=
        mul_le_mul_of_nonneg_left (le_of_lt hlt) hft0
      have h2 : t * x.re ≤ t * y.re := mul_le_mul_of_nonneg_left (le_of_lt hlt) hft1
      linarith

-- ### Punctures

/-- Every puncture of `PuncturedPlane (m + 1)` is a real number. -/
theorem punc_im_zero (m : ℕ) (j : Fin (m + 1)) :
    ((j : ℕ) + 1 : ℂ).im = 0 := by
  simp

/-- A point with non-zero imaginary part is not a puncture. -/
theorem not_punc_of_im_ne (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    (∀ j : Fin (n + 1), z ≠ ((j : ℕ) + 1 : ℂ)) := by
  intro j hj
  have h := congrArg Complex.im hj
  rw [punc_im_zero n j] at h
  exact hz h

/-- A point whose real part differs from every puncture real part is not a
puncture. -/
theorem not_punc_of_re_ne (n : ℕ) (z : ℂ)
    (hz : ∀ j : Fin (n + 1), z.re ≠ (j : ℝ) + 1) :
    (∀ j : Fin (n + 1), z ≠ ((j : ℕ) + 1 : ℂ)) := by
  intro j hj
  have h := congrArg Complex.re hj
  have h2 : ((j : ℕ) + 1 : ℂ).re = (j : ℝ) + 1 := by simp
  rw [h2] at h
  exact hz j h

-- ### Hubs

theorem leftHub_re (n : ℕ) :
    (n : ℝ) + 2 / 3 < (n : ℝ) + 1 ∧
      (∀ j : Fin (n + 1), (n : ℝ) + 2 / 3 ≠ (j : ℝ) + 1) := by
  constructor
  · have h : ((2 : ℝ) / 3) < 1 := by norm_num
    linarith
  · intro j hj
    -- The statement is true: `j + 1` is an integer, being `(j : ℕ) + 1`, while
    -- `(n : ℝ) + 2/3` has fractional part `2/3` and is not an integer.  Note that this is NOT
    -- an order argument.  Over `ℝ` the equation `(n : ℝ) + 2/3 = (j : ℝ) + 1` is perfectly
    -- consistent — it solves to `j = n - 1/3` — and combining it with the order facts
    -- `j ≤ n` and `(n : ℝ) + 2/3 < (n : ℝ) + 1` gives no contradiction.  That is exactly why
    -- six consecutive candidates reported "linarith failed to find a contradiction" here,
    -- even after passing `hj` itself to the tactic: `linarith` reasons in `ℝ`, where the
    -- integrality of `j` is invisible.  The fix is to multiply the equation by `3` so that
    -- the integrality becomes visible as an equation in `ℕ` with no solution.
    --
    -- From `hj`, `3 * ((n : ℝ) - (j : ℝ)) = 1`.  If `j < n` the left side is negative, which
    -- contradicts `1 > 0`.  If `j ≤ n` then `(n : ℝ) - (j : ℝ) = ((n - j : ℕ) : ℝ)`, so the
    -- equation reads `((3 * (n - j) : ℕ) : ℝ) = 1`, hence `3 * (n - j) = 1` in `ℕ`, which is
    -- absurd for a product of naturals.
    exfalso
    have hmul : 3 * ((n : ℝ) - (j : ℝ)) = 1 := by linarith
    -- Rather than case-splitting on `j ≤ n` and casting the difference, the equation is
    -- dispatched by `omega` after pushing `hmul` into a statement about naturals.  Two earlier
    -- versions failed here for reasons worth recording.
    --
    -- The first wrote `lt_or_ge j n` with `j : Fin (n + 1)`, and the remote answered
    -- "Application type mismatch. The argument `n` has type `ℕ` but is expected to have type
    -- `Fin (n + 1)`", because `lt_or_ge` was applied to `j` in its `Fin` form.
    --
    -- The second fixed that by comparing `(j : ℕ)` against `n`, but then wrote
    -- `Nat.cast_sub hjge` for `hsub : (n : ℝ) - (j : ℝ) = ((n - (j : ℕ) : ℕ) : ℝ)`, and the
    -- remote answered "Type mismatch: `Nat.cast_sub hjge` has type `↑(↑j - n) = ↑↑j - ↑n` but
    -- is expected to have type `↑n - ↑↑j = ↑(n - ↑j)`": `Nat.cast_sub` takes the arguments in
    -- the order `j ≤ n` and produces `↑(j - n) = ↑j - ↑n`, i.e. it is oriented for a
    -- subtraction `j - n`, not `n - j`.  The hypothesis is the wrong way round for it.
    --
    -- The argument now avoids subtraction on `ℕ` entirely.  `hj` says that
    -- `(n : ℝ) + 2/3 = (j : ℝ) + 1`, so `j < n + 1` and hence `j ≤ n`; the integrality of
    -- `j` is then exhibited by clearing denominators and returning to `ℕ` with `exact_mod_cast`
    -- on the ORIGINAL equation rather than on a difference.
    have hjle : (j : ℕ) ≤ n := by
      have hjn : j < n + 1 := j.isLt
      omega
    -- `Nat.cast_sub hjle` is stated in the form `((n - (j : ℕ) : ℕ) : ℝ) = (n : ℝ) - (j : ℝ)`,
    -- i.e. the `Nat.sub` is on the LEFT.  The remote confirmed this: "Type mismatch
    -- `Nat.cast_sub hjge` has type `↑(↑j - n) = ↑↑j - ↑n` but is expected to have type
    -- `↑n - ↑↑j = ↑(n - ↑j)`" for the earlier, oppositely-oriented statement.
    --
    -- The substitution is then made with `calc` rather than `rw`.  `rw [hsub]` searches for
    -- the LEFT side of `hsub`, namely `↑(n - ↑j)`, inside `hmul`, whose actual content is
    -- `3 * (↑n - ↑↑j) = 1` — that subterm is not present, so the remote answered
    -- "Tactic `rewrite` failed: Did not find an occurrence of the pattern `↑(n - ↑j)`".  A
    -- `calc` chain states the intermediate equation in the direction actually needed and is
    -- therefore insensitive to the orientation of `hsub`.
    have hsub : ((n - (j : ℕ) : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := Nat.cast_sub hjle
    have hmul' : 3 * ((n - (j : ℕ) : ℕ) : ℝ) = 1 := by
      calc 3 * ((n - (j : ℕ) : ℕ) : ℝ) = 3 * ((n : ℝ) - (j : ℝ)) := by rw [hsub]
        _ = 1 := hmul
    have hnat : 3 * (n - (j : ℕ)) = 1 := by exact_mod_cast hmul'
    omega

theorem rightHub_re (n : ℕ) :
    (n : ℝ) + 1 / 2 < (n : ℝ) + 5 / 6 ∧
      (∀ j : Fin (n + 1), (n : ℝ) + 5 / 6 ≠ (j : ℝ) + 1) := by
  constructor
  · have h : ((1 : ℝ) / 2) < 5 / 6 := by norm_num
    linarith
  · intro j hj
    -- Identical argument to `leftHub_re`, with `5/6` in place of `2/3`: the equation is not
    -- an order inconsistency but an integrality one, so it is cleared by multiplying by `6`
    -- and passing to `ℕ`, where `6 * (n - j) = 1` is absurd.
    exfalso
    have hmul : 6 * ((n : ℝ) - (j : ℝ)) = 1 := by linarith
    have hjle : (j : ℕ) ≤ n := by
      have hjn : j < n + 1 := j.isLt
      omega
    -- As in `leftHub_re`: the substitution goes through a `calc` rather than `rw [hsub]`,
    -- because `rw` looks for the left side of `hsub` (`↑(n - ↑j)`) inside `hmul`, and that
    -- subterm is not there.  The remote reported exactly that mismatch at the `leftHub_re`
    -- twin: "Did not find an occurrence of the pattern `↑(n - ↑j)` in the target expression
    -- `6 * (↑n - ↑↑j) = 1`".
    have hsub : ((n - (j : ℕ) : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := Nat.cast_sub hjle
    have hmul' : 6 * ((n - (j : ℕ) : ℕ) : ℝ) = 1 := by
      calc 6 * ((n - (j : ℕ) : ℕ) : ℝ) = 6 * ((n : ℝ) - (j : ℝ)) := by rw [hsub]
        _ = 1 := hmul
    have hnat : 6 * (n - (j : ℕ)) = 1 := by exact_mod_cast hmul'
    omega


end BraidsLinksMCG


