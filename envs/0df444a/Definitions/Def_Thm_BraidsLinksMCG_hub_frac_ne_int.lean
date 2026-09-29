-- Prove2me | Definitions.Def_Thm_BraidsLinksMCG_hub_frac_ne_int
-- name    : Thm_BraidsLinksMCG_hub_frac_ne_int
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-26T13:16:21.334204+00:00
-- url     : https://prove2.me/theorems/7ec0c7e2-5d5e-4f0f-bb36-569c8fe570e4
-- title:
--   Fractional hub coordinates are distinct from the integer puncture coordinates
-- statement:
--   The two hub coordinates used to join the two half-plane regions of the punctured plane, n + 2/3 and n + 5/6, lie strictly inside the gap between the two regions and are distinct from every puncture j + 1 for j ranging over Fin (n + 1). The second component of each statement is an integrality fact, not an order fact: j + 1 is an integer while n + 2/3 and n + 5/6 have fractional part 2/3 and 5/6 respectively, so they can never coincide. This is proved by clearing the denominator, which turns the hypothetical equality into an equation 3 * (n - j) = 1 (respectively 6 * (n - j) = 1) in the naturals, which is impossible.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

open BraidsLinksMCG

namespace BraidsLinksMCG

/-!
# Fractional hub coordinates are not puncture coordinates

The first remote unit of `puncturedPlane_succ_cover_halfplanes_v1`. Both facts
below are the arithmetic core of the two-half-plane cover, and both are pure
statements about integers, so they are proved here independently of the
geometric regions, the membership characterisation, and the segment-safety
lemmas that consume them.

The content of each is an **integrality** argument, not an order argument. Over
`ℝ` the equation `(n : ℝ) + 2/3 = (j : ℝ) + 1` is perfectly consistent, solving to
`j = n - 1/3`, so `linarith` cannot close it and never did: the fractional part
of the left-hand side is simply not visible to a solver reasoning in `ℝ`. The
way to make it visible is to clear the denominator and return to `ℕ`.
-/

/-- `n + 2/3` is strictly below the rightmost puncture `n + 1`, and differs from
every puncture `j + 1` for `j : Fin (n + 1)`. -/
theorem leftHub_re (n : ℕ) :
    (n : ℝ) + 2 / 3 < (n : ℝ) + 1 ∧
      (∀ j : Fin (n + 1), (n : ℝ) + 2 / 3 ≠ (j : ℝ) + 1) := by
  constructor
  · have h : ((2 : ℝ) / 3) < 1 := by norm_num
    linarith
  · intro j hj
    exfalso
    -- Clear the denominator. `hj` is the only hypothesis relating the two sides,
    -- and `linarith` needs it passed in explicitly; earlier versions left `hj`
    -- unused in the context and the remote correctly reported "failed to find a
    -- contradiction".
    have hmul : 3 * ((n : ℝ) - (j : ℝ)) = 1 := by linarith
    -- `j : Fin (n + 1)` gives `j < n + 1` and hence `(j : ℕ) ≤ n` by `omega`.
    have hjle : (j : ℕ) ≤ n := by
      have hjn : j < n + 1 := j.isLt
      omega
    -- `Nat.cast_sub hjle` is stated as `↑(n - j) = ↑n - ↑j`, with the `Nat.sub`
    -- on the LEFT. The remote rejected the oppositely-oriented version with
    -- "Type mismatch: `Nat.cast_sub hjge` has type `↑(↑j - n) = ↑↑j - ↑n` but is
    -- expected to have type `↑n - ↑↑j = ↑(n - ↑j)`".
    --
    -- The substitution is made by `calc`, not `rw`: `rw` searches for the
    -- left-hand side `↑(n - ↑j)`, which does not occur in `hmul`'s actual
    -- content `3 * (↑n - ↑↑j) = 1`, so the remote answered "Did not find an
    -- occurrence of the pattern `↑(n - ↑j)`". A `calc` chain states the
    -- intermediate equation in the direction needed and is orientation-proof.
    have hsub : ((n - (j : ℕ) : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := Nat.cast_sub hjle
    have hmul' : 3 * ((n - (j : ℕ) : ℕ) : ℝ) = 1 := by
      calc 3 * ((n - (j : ℕ) : ℕ) : ℝ) = 3 * ((n : ℝ) - (j : ℝ)) := by rw [hsub]
        _ = 1 := hmul
    have hnat : 3 * (n - (j : ℕ)) = 1 := by exact_mod_cast hmul'
    omega

/-- `n + 5/6` is strictly above `n + 1/2` and differs from every puncture
`j + 1` for `j : Fin (n + 1)`. -/
theorem rightHub_re (n : ℕ) :
    (n : ℝ) + 1 / 2 < (n : ℝ) + 5 / 6 ∧
      (∀ j : Fin (n + 1), (n : ℝ) + 5 / 6 ≠ (j : ℝ) + 1) := by
  constructor
  · have h : ((1 : ℝ) / 2) < 5 / 6 := by norm_num
    linarith
  · intro j hj
    exfalso
    have hmul : 6 * ((n : ℝ) - (j : ℝ)) = 1 := by linarith
    have hjle : (j : ℕ) ≤ n := by
      have hjn : j < n + 1 := j.isLt
      omega
    have hsub : ((n - (j : ℕ) : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := Nat.cast_sub hjle
    have hmul' : 6 * ((n - (j : ℕ) : ℕ) : ℝ) = 1 := by
      calc 6 * ((n - (j : ℕ) : ℕ) : ℝ) = 6 * ((n : ℝ) - (j : ℝ)) := by rw [hsub]
        _ = 1 := hmul
    have hnat : 6 * (n - (j : ℕ)) = 1 := by exact_mod_cast hmul'
    omega

end BraidsLinksMCG


