-- Prove2me | Definitions.Def_HousingImprove_Prog
-- name    : HousingImprove_Prog
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:15.821365+00:00
-- url     : https://prove2.me/theorems/6e8831ca-8c69-43e3-8eb3-b9492270345e
-- title:
--   Charged programs: the cost model
-- statement:
--   Running time is measured in the **unit-cost RAM** model: a program is a computation that also counts the unit operations it performs. One unit is charged for each read or write of an array cell, each comparison or arithmetic operation, each push or pop on a stack, and each iteration of a loop; allocating an array of $k$ cells costs $k$. A program reads its input lists only by walking along them, one unit per cell, and loops are given a fuel bound computed from the input size, which only guarantees termination.
--
--   The running-time statements bound the total count by a constant multiple of the input length $|H|$.
--
--   **Formalization Note** `Prog α` is `StateM ℕ α`, the state being the count. The combinators `tick`, `opn`, `alloc`, `rd`, `wr`, `push`, `pop`, `pushAt`, `forL` and `whileF` each charge their own operations; a charged read or write may compute its index from at most two values already held.
-- source:
--   Schlotter, Biró, Fleiner, The core of housing markets from an agent's perspective: Is it worth sprucing up your home?, arXiv:2110.06875v3, Theorem 2, p.10 and Lemma 4, p.18 ("O(|H|) time"); the unit-cost RAM reading of time

import Mathlib

namespace HousingImprove

/-- **Charged programs** (the unit-cost RAM reading of "time" in Schlotter, Biró, Fleiner,
arXiv:2110.06875v3, Theorem 2, p.10, and Lemma 4, p.18): a state monad whose state is the number of
unit operations performed so far.

**Charging discipline.** Every primitive a program performs is charged at its own site by one of the
combinators of this file: a read or write of one array cell, a comparison, an arithmetic operation, a
push or pop on a stack, and one loop iteration, each cost at least one; allocating an array of `k`
cells costs `k`. A program reads its input lists only by iterating over them (one unit per cell).
Pure Lean code inside a charged block of `opn k` performs at most `k` primitive operations, and a
charged read, write or push may compute its index from at most two values already held (a RAM
address computation, absorbed in the unit). -/
abbrev Prog (α : Type) : Type := StateM ℕ α

/-- Charge `k` unit operations. -/
def tick (k : ℕ) : Prog Unit := modify (· + k)

/-- A straight-line block of at most `k` primitive operations with result `a`. -/
def opn {α : Type} (k : ℕ) (a : α) : Prog α := do
  tick k
  pure a

/-- Allocate an array of `k` cells, all equal to `v`: cost `k`. -/
def alloc {α : Type} (k : ℕ) (v : α) : Prog (Array α) := do
  tick k
  pure (Array.replicate k v)

/-- Read cell `i` of an array (cost 1; `d` outside the array). -/
def rd {α : Type} (A : Array α) (i : ℕ) (d : α) : Prog α := do
  tick 1
  pure (A.getD i d)

/-- Write `v` into cell `i` of an array (cost 1). -/
def wr {α : Type} (A : Array α) (i : ℕ) (v : α) : Prog (Array α) := do
  tick 1
  pure (A.setIfInBounds i v)

/-- Push `v` onto the stack stored in cell `i` of an array of stacks (cost 1). -/
def pushAt {α : Type} (A : Array (Array α)) (i : ℕ) (v : α) : Prog (Array (Array α)) := do
  tick 1
  pure (A.modify i (·.push v))

/-- Push onto a stack (cost 1). -/
def push {α : Type} (S : Array α) (v : α) : Prog (Array α) := do
  tick 1
  pure (S.push v)

/-- Pop the top of a stack, if any (cost 1). -/
def pop {α : Type} (S : Array α) : Prog (Option α × Array α) := do
  tick 1
  pure (S.back?, S.pop)

/-- A loop over a list: one charged iteration per cell, threading an accumulator. -/
def forL {α β : Type} : List α → β → (β → α → Prog β) → Prog β
  | [], b, _ => pure b
  | a :: l, b, f => do
    tick 1
    let b' ← f b a
    forL l b' f

/-- A `while` loop with at most `fuel` iterations, each charged one unit: the body returns `none` to
stop. Running out of fuel stops the loop; the programs of the mission are given fuel computed from
the input size, and their specifications state that it suffices. -/
def whileF {σ : Type} : ℕ → σ → (σ → Prog (Option σ)) → Prog σ
  | 0, s, _ => pure s
  | k + 1, s, body => do
    tick 1
    match ← body s with
    | none => pure s
    | some s' => whileF k s' body

end HousingImprove


