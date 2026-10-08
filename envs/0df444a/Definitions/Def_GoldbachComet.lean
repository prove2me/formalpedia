-- Prove2me | Definitions.Def_GoldbachComet
-- name    : GoldbachComet
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-04T20:34:36.051797+00:00
-- url     : https://prove2.me/theorems/5f7aa5a3-c78c-423f-a835-01a319830a6b
-- title:
--   Ordered Goldbach representation counts
-- statement:
--   Defines `primeLeftSummand`, `orderedReprPairs`, and `orderedReprCount` for ordered prime pairs (p,q) with p+q=n, plus basic membership lemmas.
-- source:
--   Mission stream goldbach-comet; see docs/goldbach-comet/README.md

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic

/-!
Goldbach representation counts for the prime-race imprint program.

We count **ordered** pairs `(p, q)` of primes with `p + q = n`. This matches the
convolution / generating-function convention used in analytic number theory
(Hardy–Littlewood, Montgomery–Vaughan) and in the empirical scripts under
`docs/captain/goldbach/experiments/`.
-/

namespace GoldbachComet

/-- Primes `p` with `2 ≤ p ≤ n` for which `n - p` is also prime. -/
def primeLeftSummand (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun p =>
    2 ≤ p ∧
    let q := n - p
    2 ≤ q ∧ p.Prime ∧ q.Prime

/-- Left coordinate determines an ordered pair with sum `n`. -/
def pairEmbedding (n : ℕ) : ℕ ↪ ℕ × ℕ where
  toFun p := (p, n - p)
  inj' := by
    intro a b h
    exact Prod.ext_iff.mp h |>.1

/-- Ordered representation pairs `(p, q)` with `p`, `q` prime and `p + q = n`. -/
def orderedReprPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (primeLeftSummand n).map (pairEmbedding n)

/-- Number of ordered prime pairs summing to `n`. -/
def orderedReprCount (n : ℕ) : ℕ :=
  (orderedReprPairs n).card

theorem mem_primeLeftSummand {n p : ℕ} :
    p ∈ primeLeftSummand n ↔
      2 ≤ p ∧ p ≤ n ∧ let q := n - p; 2 ≤ q ∧ p.Prime ∧ q.Prime := by
  simp [primeLeftSummand, Finset.mem_filter, Finset.mem_range, and_assoc, and_left_comm]

theorem mem_orderedReprPairs {n p q : ℕ} :
    (p, q) ∈ orderedReprPairs n ↔
      p ∈ primeLeftSummand n ∧ q = n - p := by
  constructor
  · intro h
    rcases Finset.mem_map.mp h with ⟨a, ha, hab⟩
    dsimp [pairEmbedding] at hab
    rcases Prod.ext_iff.mp hab with ⟨rfl, hq⟩
    exact ⟨ha, hq.symm⟩
  · intro ⟨hp, hq⟩
    subst hq
    exact Finset.mem_map.mpr ⟨p, hp, rfl⟩

theorem orderedReprPairs_pair_primes {n p q : ℕ} (h : (p, q) ∈ orderedReprPairs n) :
    p.Prime ∧ q.Prime ∧ p + q = n := by
  rcases (mem_orderedReprPairs (n := n)).mp h with ⟨hp', hq⟩
  rcases (mem_primeLeftSummand (n := n)).mp hp' with ⟨_, hp_le, _, hpp, hqp⟩
  subst hq
  exact ⟨hpp, hqp, Nat.add_sub_of_le hp_le⟩

end GoldbachComet


