-- Prove2me | Definitions.Def_Grunbaum2003_IsMSequence
-- name    : Grunbaum2003_IsMSequence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:21:24.097028+00:00
-- url     : https://prove2.me/theorems/2edd1d23-27b8-486b-9cf1-ea85520c3e14
-- title:
--   Finite M-sequence condition
-- statement:
--   A finite sequence beginning with one whose positive entries have increasing binomial expansions satisfying Macaulay’s upper-boundary inequality; zero entries use the empty expansion.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §10.6, printed pp. 198a–198b / PDF pp. 235–236; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
open scoped BigOperators
namespace Grunbaum2003

/-- The finite M-sequence condition in §10.6, pp.198a–198b (PDF235–236).
Only entries 0 through m are used. For a positive entry, the witnesses give
its unique k-binomial expansion and the printed upper boundary inequality.
The zero entry has the empty expansion, whose boundary is zero.
This relational definition avoids choice of an expansion algorithm. -/
def IsMSequence (m : ℕ) (g : ℕ → ℕ) : Prop :=
  g 0 = 1 ∧ ∀ k : ℕ, 0 < k → k ≤ m →
    g k = 0 ∨ ∃ (i : ℕ) (a : ℕ → ℕ),
      0 < i ∧ i ≤ k ∧ i ≤ a i ∧
      (∀ r s : ℕ, i ≤ r → r < s → s ≤ k → a r < a s) ∧
      g k = ∑ r ∈ Finset.Icc i k, Nat.choose (a r) r ∧
      (∑ r ∈ Finset.Icc i k, Nat.choose (a r - 1) (r - 1)) ≤ g (k - 1)

end Grunbaum2003


