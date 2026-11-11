-- Prove2me | Definitions.Def_DynMaxMatchEC_Main_HittingGame
-- name    : DynMaxMatchEC_Main_HittingGame
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:01:41.420406+00:00
-- url     : https://prove2.me/theorems/e52980f6-163e-4853-9d59-03d8212363e6
-- title:
--   The element-hitting game with the greedy resetting player AlgGreedy
-- statement:
--   The **element-hitting game** (§2.4) has elements $e_1,\dots,e_n$ (here $0,\dots,n-1$), integral parameters $h,r\ge1$ and counters $N_j$, initially $0$. In every iteration the **loading player** chooses a set $H_i$ of elements with hit amounts $\Delta_j\ge1$ for $e_j\in H_i$ and $\sum_{e_j\in H_i}\Delta_j\le h$, and a set $R'_i\subseteq Z\setminus H_i$; each counter of $H_i$ grows by its hit amount and each counter of $R'_i$ is set to $0$. Then the **resetting player** chooses a set $R_i$ of at most $r$ elements and sets their counters to $0$. The value of the game is the largest counter at the end of any iteration.
--
--   **AlgGreedy** resets $r$ elements with the largest counters among those with a positive counter (ties arbitrary), or all elements with a positive counter if there are fewer than $r$.
--
--   `Reachable h r N` holds for the counter vectors $N$ at the end of some iteration of some play in which the resetting player is AlgGreedy (and for the initial zero vector).
--
--   **Formalization Note.** A move of the loading player is a hit vector `hit` (so $H_i$ is its support) and a set `reset` disjoint from the support. `IsGreedyReset r N R` describes the possible choices of AlgGreedy. Quantifying over all reachable vectors covers every adaptive loading player and every tie-breaking.
-- source:
--   Chuzhoy, New Algorithms for Dynamic Maximal Matching and Edge Coloring (manuscript, Nov. 1, 2026; PDF sha256 2c277528…4ca5), p. 13, §2.4

import Mathlib

namespace DynMaxMatchEC.Main

/-!
# The element-hitting game with the resetting player AlgGreedy

Chuzhoy, *New Algorithms for Dynamic Maximal Matching and Edge Coloring* (manuscript, Nov. 1,
2026; PDF sha256 2c277528…4ca5), §2.4, p. 13.

* The elements are `Fin n` (the paper's `e₁, …, eₙ`, shifted to start at `0`); a counter vector is
  `N : Fin n → ℕ`, initially `0`.
* In every iteration the loading player chooses hit amounts `hit : Fin n → ℕ` (the set `Hᵢ` is the
  support of `hit`, so every element of `Hᵢ` is hit `Δⱼ = hit j ≥ 1` times) with total at most `h`,
  and a set `reset` of elements outside `Hᵢ` (the paper's `R′ᵢ ⊆ Z \ Hᵢ`). Every counter of `Hᵢ`
  grows by its hit amount and every counter of `R′ᵢ` becomes `0`.
* The resetting player AlgGreedy then resets a set `Rᵢ` of `r` elements with the largest counters
  among the elements with a positive counter (the heap `Λ`), ties broken arbitrarily; if fewer than
  `r` counters are positive, all of them are reset.
* `Reachable h r N`: `N` is the counter vector at the end of some iteration of some play, for some
  sequence of moves of the loading player and some tie-breaking of AlgGreedy (including the initial
  all-zero vector). Since every play of an adaptive loading player is one such sequence, and every
  sequence is played by some (oblivious) loading player, "for every reachable `N`" is "regardless of
  how the loading player plays".
-/

/-- One move of the loading player: the hit amounts and the set `R′ᵢ` of counters to reset. -/
structure LoadMove (n : ℕ) where
  hit : Fin n → ℕ
  reset : Finset (Fin n)

/-- A legal move: the hit amounts total at most `h`, and no reset element is hit. -/
def LoadMove.IsValid {n : ℕ} (h : ℕ) (m : LoadMove n) : Prop :=
  (∑ j, m.hit j) ≤ h ∧ ∀ j ∈ m.reset, m.hit j = 0

/-- The counters after the loading player's move. -/
def afterLoad {n : ℕ} (N : Fin n → ℕ) (m : LoadMove n) : Fin n → ℕ :=
  fun j => if j ∈ m.reset then 0 else N j + m.hit j

/-- `R` is a choice AlgGreedy may make on the counters `N`: `R` consists of elements with a positive
counter, has `min r (number of positive counters)` elements, and no element outside `R` has a larger
counter than an element of `R`. -/
def IsGreedyReset {n : ℕ} (r : ℕ) (N : Fin n → ℕ) (R : Finset (Fin n)) : Prop :=
  R ⊆ Finset.univ.filter (fun j => 0 < N j) ∧
    R.card = min r (Finset.univ.filter (fun j => 0 < N j)).card ∧
    ∀ j ∈ R, ∀ k ∉ R, N k ≤ N j

/-- The counters after resetting the set `R`. -/
def afterReset {n : ℕ} (N : Fin n → ℕ) (R : Finset (Fin n)) : Fin n → ℕ :=
  fun j => if j ∈ R then 0 else N j

/-- The counter vectors that occur at the end of an iteration of the element-hitting game with
parameters `h, r` when the resetting player is AlgGreedy (plus the initial all-zero vector). -/
inductive Reachable {n : ℕ} (h r : ℕ) : (Fin n → ℕ) → Prop
  | init : Reachable h r (fun _ => 0)
  | step (N : Fin n → ℕ) (m : LoadMove n) (R : Finset (Fin n)) :
      Reachable h r N → m.IsValid h → IsGreedyReset r (afterLoad N m) R →
        Reachable h r (afterReset (afterLoad N m) R)

end DynMaxMatchEC.Main


