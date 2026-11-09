-- Prove2me | Definitions.Def_GirthFiltering_RandomFiltering_ChargedPrimitives
-- name    : GirthFiltering_RandomFiltering_ChargedPrimitives
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:16.246655+00:00
-- url     : https://prove2.me/theorems/2ca66fd5-9a7e-4d1c-b8e7-cb14b234aa19
-- title:
--   Charged ideal-real operations and deterministic selection
-- statement:
--   The computation model counts visited list cells, scalar instructions, and sparse random-access memory operations. A charged computation returns a value and its accumulated natural-number work count. Each tick charges a bounded straight-line block: tuple and list constructors or projections, integer arithmetic and tests, scalar real arithmetic and comparisons, or a bounded number of sparse RAM reads and writes. The ideal scalar interface also permits natural ceiling, logarithm, exponential, and an exact exponential draw. Allocation of an empty sparse memory is constant; it is not initialization of all vertex addresses.
--
--   The file defines charged traversal, reversal, indexing, partition, insertion sorting for groups of at most five, and median-of-medians selection. For a nonempty list $x$ and zero-based index $j<|x|$, the selection specification is
--
--   $$
--   v\in x,\qquad |\{i:x_i<v\}|\le j<|\{i:x_i\le v\}|.
--   $$
--
--   Selection is an actual recursively defined computation. Its correctness and linear charged cost are conclusions of the goal theorem. Fuel is a totality device, with a bottom return on exhaustion; proving that exhaustion never occurs on the specified calls is part of correctness. No primitive selects a median or an order statistic in one step.
--
--   This model gives ideal-real operation complexity, not bit complexity or a finite-precision error guarantee. Sparse writes are RAM operations represented extensionally by function updates, not association-list lookup. The implementation constant in the theorem absorbs the fixed length of straight-line instruction blocks; it is not a numeral claimed by the paper.
-- source:
--   Yablon, Approximating the Girth of an Undirected, Weighted Graph for Larger Approximation Factors, STOC 2027 submission #59 (2026), pinned PDF sha256 cf63df259cbd099089184755e2c32f0d51f00dea322509f35766f4a91a4e021f, p. 4, linear-time median selection and linear-work display; p. 7, Section 3.2 running-time paragraph and Remark 2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/59.pdf

import Mathlib

namespace GirthFiltering.RandomFiltering

/-! A charged ideal-real RAM. One tick charges a bounded straight-line block of
list/record operations, scalar arithmetic/comparison, or sparse RAM accesses.
RAM is represented extensionally by functions; Function.update is a single
random-access write, NOT a functional linked-list implementation. Empty RAM
with a fixed default is a new empty sparse memory, not a scan of its addresses.
Real exp, log, ceiling, and an exact exponential draw are scalar primitives.
Every traversal below ticks on each visited cell. No graph or selection oracle
is a primitive. The universal theorem constant absorbs bounded block lengths. -/

abbrev Charged (α : Type) := StateM ℕ α

def tick : Charged Unit := modify (fun n => n + 1)

def runCharged {α : Type} (p : Charged α) : α × ℕ := p.run 0

def cLength {α : Type} : List α → Charged ℕ
  | [] => do tick; return 0
  | _ :: xs => do tick; let n ← cLength xs; return n + 1

def cReverseAux {α : Type} : List α → List α → Charged (List α)
  | [], acc => do tick; return acc
  | x :: xs, acc => do tick; cReverseAux xs (x :: acc)

def cReverse {α : Type} (xs : List α) : Charged (List α) := cReverseAux xs []

def cMap {α β : Type} (f : α → Charged β) : List α → Charged (List β)
  | [] => do tick; return []
  | x :: xs => do
    tick
    let y ← f x
    let ys ← cMap f xs
    return y :: ys

/-- Generate finite indexed data without an uncharged range-list traversal. -/
def cFinAux {α : Type} (n : ℕ) (f : Fin n → Charged α) :
    ℕ → ℕ → Charged (List α)
  | 0, _ => do tick; return []
  | fuel + 1, i => do
    tick
    if h : i < n then
      let x ← f ⟨i, h⟩
      let xs ← cFinAux n f fuel (i + 1)
      return x :: xs
    else return []

def cOfFn {α : Type} {n : ℕ} (f : Fin n → Charged α) : Charged (List α) :=
  cFinAux n f n 0

def cGet {α : Type} (fallback : α) : List α → ℕ → Charged α
  | [], _ => do tick; return fallback
  | x :: _, 0 => do tick; return x
  | _ :: xs, k + 1 => do tick; cGet fallback xs k

noncomputable def cInsert (a : EReal) : List EReal → Charged (List EReal)
  | [] => do tick; return [a]
  | b :: bs => do
    tick
    if a ≤ b then return a :: b :: bs
    else return b :: (← cInsert a bs)

/-- Used only for groups of at most five, never to sort an input-size list. -/
noncomputable def cSmallSort : List EReal → Charged (List EReal)
  | [] => do tick; return []
  | x :: xs => do tick; cInsert x (← cSmallSort xs)

/-- Partition with cached cardinalities; equal keys are never recursed upon. -/
noncomputable def cPartition (p : EReal) :
    List EReal → Charged (List EReal × ℕ × List EReal × ℕ × List EReal)
  | [] => do tick; return ([], 0, [], 0, [])
  | x :: xs => do
    tick
    let (lo, nl, eq, ne, hi) ← cPartition p xs
    if x < p then return (x :: lo, nl + 1, eq, ne, hi)
    else if p < x then return (lo, nl, eq, ne, x :: hi)
    else return (lo, nl, x :: eq, ne + 1, hi)

/-- Consecutive groups of five; the last group may be shorter. -/
noncomputable def cGroupMedians : List EReal → Charged (List EReal)
  | [] => do tick; return []
  | a :: b :: c :: d :: e :: rest => do
    tick
    let sorted ← cSmallSort [a,b,c,d,e]
    let v ← cGet ⊥ sorted 2
    let vs ← cGroupMedians rest
    return v :: vs
  | rest => do
    tick
    let sorted ← cSmallSort rest
    let n ← cLength rest
    let v ← cGet ⊥ sorted (n / 2)
    return [v]

/-- Deterministic median-of-medians selection, zero-based ascending index.
Fuel is only a totality device. Exhaustion returns bottom and is excluded by
the correctness conclusion, rather than by an input hypothesis. -/
noncomputable def selectFuel : ℕ → List EReal → ℕ → Charged EReal
  | 0, _, _ => do tick; return ⊥
  | fuel + 1, xs, k => do
    tick
    let n ← cLength xs
    if n ≤ 5 then
      cGet ⊥ (← cSmallSort xs) k
    else
      let medians ← cGroupMedians xs
      let nm ← cLength medians
      let pivot ← selectFuel fuel medians (nm / 2)
      let (lo, nl, _, ne, hi) ← cPartition pivot xs
      if k < nl then selectFuel fuel lo k
      else if k < nl + ne then return pivot
      else selectFuel fuel hi (k - nl - ne)

noncomputable def select (xs : List EReal) (k : ℕ) : Charged EReal := do
  let n ← cLength xs
  selectFuel (2 * n + 10) xs k

/-- Semantic order-statistic specification; not called by any program. -/
def IsOrderStatistic (xs : List EReal) (k : ℕ) (v : EReal) : Prop :=
  v ∈ xs ∧ (xs.filter (fun x => x < v)).length ≤ k ∧
    k < (xs.filter (fun x => x ≤ v)).length

end GirthFiltering.RandomFiltering


