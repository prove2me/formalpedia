-- Prove2me | solution 1 for AlpoegeClaudeRH.EveryCharacter_below_record
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T18:45:40.172074+00:00
-- url     : https://prove2.me/submissions/5ec0043e-0ef3-4b8a-a405-222280e71761
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Theorems.Thm_GRH_dirichlet_zero_free_bound

/-!
Reduction of `AlpoegeClaudeRH.EveryCharacter_below_record` to the open platform node
`GRH.dirichlet_zero_free_bound` (nonvanishing of every Dirichlet `L`-function on `Re s > 1/2`
away from the pole of the principal character).

The target restricts that statement to `1/2 < Re s ≤ 0.8749570698`; the cap is not used.
The only conversion is the pole exclusion: the target states it as `χ ≠ 1 ∨ s ≠ 1`, the
imported node as `¬ (χ = 1 ∧ s = 1)`, and these are equivalent by `not_and_or`.
-/

theorem solution
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hs : 1 / 2 < s.re) (h : χ ≠ 1 ∨ s ≠ 1)
    (hcap : s.re ≤ 0.8749570698) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  GRH.dirichlet_zero_free_bound χ hs (not_and_or.mpr h)
