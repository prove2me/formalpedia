-- Prove2me | Definitions.Def_Supermodularity_Cooperative_InitialCoalition
-- name    : Supermodularity_Cooperative_InitialCoalition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:32:00.211795+00:00
-- url     : https://prove2.me/theorems/4b1acd70-c6fc-4bbc-8372-5a155aa7edc3
-- title:
--   Section 5.1 notation - the initial coalition S_pi(j) for a permutation
-- statement:
--   For a set of players $N = \{1,\dots,n\}$ (modeled as `Fin n`) and a permutation $\pi$ of $N$
--   (modeled as `Equiv.Perm (Fin n)`, thought of as the order $\pi(0), \pi(1), \dots, \pi(n-1)$ in
--   which the greedy algorithm of Section 5.1 adds players, using Lean's `0`-indexed positions
--   where the book uses $1,\dots,n$), `InitialCoalition σ j` is the coalition
--   $$S_\pi(j) = \{k \in N : \sigma^{-1}(k) < j\}$$
--   of the first $j$ players added, for $j = 0,\dots,n$. `InitialCoalition σ 0 = \emptyset` and
--   `InitialCoalition σ n = N`.
--
--   **Formalization note.** The book indexes permutation values $\pi(1),\dots,\pi(n)$ from $1$; this
--   development follows Lean's convention of `Equiv.Perm (Fin n)` acting on `0`-indexed positions
--   `0,\dots,n-1`, so `InitialCoalition σ j` for `0`-indexed `j` corresponds to the book's
--   $S_\pi(j)$ for the same integer `j` (the shift is absorbed into the definition, not into `j`).
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 210, Section 5.1

import Mathlib

namespace Supermodularity.Cooperative

/-- `InitialCoalition σ j` is `Sπ(j) = {π(1),…,π(j)}` (Topkis p. 210): given a
permutation `σ` of the players `Fin n`, thought of as the order `σ 0, σ 1, …,
σ (n - 1)` in which the greedy algorithm adds players, the coalition of the first
`j` players added, for `j = 0, …, n`. `InitialCoalition σ 0 = ∅` and
`InitialCoalition σ n = Finset.univ`. -/
def InitialCoalition {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun k : Fin n => (σ.symm k : ℕ) < j)

end Supermodularity.Cooperative


