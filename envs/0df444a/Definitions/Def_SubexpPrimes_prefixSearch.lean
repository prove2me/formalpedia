-- Prove2me | Definitions.Def_SubexpPrimes_prefixSearch
-- name    : SubexpPrimes_prefixSearch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:57:30.75552+00:00
-- url     : https://prove2.me/theorems/33936b0e-3aa8-41ce-aef9-f8e5b3a92512
-- title:
--   The search by prefixes
-- statement:
--   The procedure of Corollary 2.8(c) over a zero-test oracle: first test the empty prefix, and if its sum is zero report that no input qualifies. Otherwise, knowing a prefix $\pi$ of the least qualifying input, test the sum over the inputs beginning with $\pi0$: go to $\pi1$ if it is zero and to $\pi0$ otherwise. The procedure also returns its number of calls. This file also defines the restricted sum, and what it means for an output to be the answer of the search: the least word, as an integer, that qualifies, or "none".
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), proof of Corollary 2.8(c), p.17

import Mathlib
import Definitions.Def_SubexpPrimes_bitsToNat

set_option autoImplicit false

namespace SubexpPrimes

/-- The bit loop of the search (proof of Corollary 2.8(c), p.17): knowing a prefix `π`, test the
inputs beginning with `π0`; go to `π1` if that sum is zero and to `π0` otherwise. It returns the
final word and the number of tests. -/
def prefixLoop (z : List Bool → Bool) : ℕ → List Bool → List Bool × ℕ
  | 0, π => (π, 0)
  | k + 1, π =>
    let r := prefixLoop z k (π ++ [z (π ++ [false])])
    (r.1, r.2 + 1)

/-- **The search by prefixes** — Gajulapalli, *Deterministic Construction of Primes in
Subexponential Time* (manuscript, sha256 6ad4d3de…), proof of Corollary 2.8(c), p.17, over a
zero-test oracle `z`: `z π = true` means that the sum restricted to the inputs beginning with `π`
is zero. First test the empty prefix; if it is zero, report that none exists. It returns the
answer and the number of calls, derived from the recursion. -/
def prefixSearch (n : ℕ) (z : List Bool → Bool) : Option (List Bool) × ℕ :=
  if z [] then (none, 1)
  else
    let r := prefixLoop z n []
    (some r.1, r.2 + 1)

/-- **The answer of a search** over `n`-bit words: `some x` with `x` the least word (as an integer,
most significant bit first) satisfying `q`, or `none` if no word does. -/
def IsSearchAnswer (n : ℕ) (q : List Bool → Prop) : Option (List Bool) → Prop
  | none => ∀ x : List Bool, x.length = n → ¬ q x
  | some x => x.length = n ∧ q x ∧ ∀ y : List Bool, y.length = n → q y → bitsToNat x ≤ bitsToNat y

/-- The output word of a search: `[false]` for "none exists", `true :: x` for the word `x`. -/
def searchWord : Option (List Bool) → List Bool
  | none => [false]
  | some x => true :: x

open scoped Classical in
/-- The sum of Corollary 2.8(c), p.17, restricted to the `n`-bit inputs that begin with `π`:
`∑_x C(x) ω(x)`. -/
noncomputable def restrictedSum (n : ℕ) (C : List Bool → Prop) (ω : List Bool → ℝ)
    (π : List Bool) : ℝ :=
  ∑ x : Fin n → Bool,
    if π <+: List.ofFn x ∧ C (List.ofFn x) then ω (List.ofFn x) else 0

end SubexpPrimes


