-- Prove2me | Definitions.Def_DynColorWC_Main_MaxMill
-- name    : DynColorWC_Main_MaxMill
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:46:20.665749+00:00
-- url     : https://prove2.me/theorems/aa98d6b8-cb27-488d-995f-e3a9ac47e213
-- title:
--   The MaxMill with period T: the abstract process (all tie-breaks) and its word-RAM protocol
-- statement:
--   A **MaxMill with period $T$** keeps an initially empty set $S$, a counter $c(x)\in\mathbb N$ for each $x\in S$, and a distinguished **head** when $S\ne\emptyset$. $\mathrm{add}(x)$, for $x\notin S$, adds $x$ with $c(x)=1$ (and makes it the head if $S$ was empty); $\mathrm{increment}(x)$, for $x\in S$, sets $c(x)\leftarrow c(x)+1$. After every $T$-th call to increment, the mill outputs and removes the head, then selects a remaining element of maximum counter as the new head, **breaking ties arbitrarily**.
--
--   The process is a relation $\mathrm{MillStep}_T(s,\mathrm{op},\mathrm{out},s')$: every tie-break is an allowed step, and $\mathrm{out}$ is the head output by the operation, if any. A state is **reachable with size bound $N$** if it arises from the empty mill by valid operations ($\mathrm{add}$ of a non-member, $\mathrm{increment}$ of a member) along which $|S|\le N$.
--
--   On the word RAM (`DynBrooks_Machine`), elements are naturals below $U$; preprocessing receives $T,N,U$; $\mathrm{add}(x)$ and $\mathrm{increment}(x)$ arrive as the words $0,x$ and $1,x$; the machine reports an output head $h$ by writing $h$. The word size is $a\lceil\log_2(U+NT+2)\rceil$.
--
--   **Formalization Note.** The state records the number $k$ of increments since the last output, so the head is output after the $T$-th, $2T$-th, … call to increment.
-- source:
--   Flin and Ghaffari (2026), Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time, STOC 2027 submission, supplied PDF sha256 93ebb2ffd4839b5e525b4550a6569cf5234550ee4a44351aedab3ea3154300e3, §3.3, pp. 14–15 (PDF 16–17)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol

namespace DynColorWC.Main

/-! # The MaxMill data structure with period `T`

Flin and Ghaffari (2026), *Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time*,
STOC 2027 submission, supplied PDF sha256 93ebb2ff…3154300e3, §3.3, pp. 14–15 (PDF 16–17):
"A MaxMill with period T maintains an initially empty set S, a counter c(x) ∈ ℕ for each x ∈ S,
and a distinguished head when S ≠ ∅. It provides two operations: add(x), for x ∉ S, which adds x to
S and sets c(x) = 1, and increment(x), for x ∈ S, which sets c(x) ← c(x) + 1. If the mill is empty
when x gets added to S, x becomes its head. Once every T calls to increment, the mill outputs and
removes the head, then selects a remaining element of maximum counter value as its new head,
breaking ties arbitrarily."

* The abstract process is a **relation** `MillStep T s op out s'`: every tie-break of the head
  selection is a separate allowed step. `out` is the head output by the operation, if any.
  `k` counts the `increment` calls since the last output (so the head is output after the `T`-th,
  `2T`-th, … call to `increment`).
* `MillReach T N s`: `s` is reached from the empty mill by valid operations (`add` only of a
  non-member, `increment` only of a member) along which `S` never has more than `N` elements.
* On the machine (the published `DynBrooks` word RAM), elements are natural numbers `x < U`; the
  preprocessing words are `T, N, U`; `add x` arrives as the words `0, x` and `increment x` as `1, x`;
  the machine reports the output head `h` by writing the word `h`. -/

/-- The state of a MaxMill: the set `S`, the counters, the head, and the number of `increment` calls
since the last output. -/
structure MillState (α : Type) where
  S : Finset α
  cnt : α → ℕ
  head : Option α
  k : ℕ

/-- The empty mill. -/
def MillState.empty (α : Type) : MillState α := ⟨∅, fun _ => 0, none, 0⟩

/-- The two operations. -/
inductive MillOp (α : Type) where
  | add (x : α)
  | increment (x : α)

/-- One operation of the MaxMill with period `T`, as a relation: from `s`, operation `op` outputs
`out` and leads to `s'`. Every tie-break of the new head is allowed. -/
def MillStep {α : Type} [DecidableEq α] (T : ℕ) (s : MillState α) (op : MillOp α)
    (out : Option α) (s' : MillState α) : Prop :=
  match op with
  | .add x =>
      x ∉ s.S ∧ out = none ∧
      s' = { S := insert x s.S, cnt := Function.update s.cnt x 1,
             head := if s.S = ∅ then some x else s.head, k := s.k }
  | .increment x =>
      x ∈ s.S ∧
      let c1 := Function.update s.cnt x (s.cnt x + 1)
      if s.k + 1 < T then
        out = none ∧ s' = { S := s.S, cnt := c1, head := s.head, k := s.k + 1 }
      else
        let S1 := match s.head with
          | some h => s.S.erase h
          | none => s.S
        out = s.head ∧ s'.S = S1 ∧ s'.cnt = c1 ∧ s'.k = 0 ∧
          ((S1 = ∅ ∧ s'.head = none) ∨
            ∃ y ∈ S1, s'.head = some y ∧ ∀ z ∈ S1, c1 z ≤ c1 y)

/-- An operation is valid for `s` with size bound `N`: `add x` only for `x ∉ S` and only if `S` then
still has at most `N` elements; `increment x` only for `x ∈ S`. -/
def MillValid {α : Type} [DecidableEq α] (N : ℕ) (s : MillState α) : MillOp α → Prop
  | .add x => x ∉ s.S ∧ s.S.card + 1 ≤ N
  | .increment x => x ∈ s.S

/-- States reachable from the empty mill by valid operations, `S` never exceeding `N` elements, under
any tie-breaking. -/
inductive MillReach {α : Type} [DecidableEq α] (T N : ℕ) : MillState α → Prop
  | empty : MillReach T N (MillState.empty α)
  | step {s s' : MillState α} {op : MillOp α} {out : Option α} :
      MillReach T N s → MillValid N s op → MillStep T s op out s' → MillReach T N s'

/-- The words of a MaxMill operation on the machine: `add x` is `0, x`, `increment x` is `1, x`. -/
def MillOp.words : MillOp ℕ → List ℕ
  | .add x => [0, x]
  | .increment x => [1, x]

/-- The element named by an operation. -/
def MillOp.elem {α : Type} : MillOp α → α
  | .add x => x
  | .increment x => x

/-- The word size `a · ⌈log₂ (U + N·T + 2)⌉` for a mill with period `T`, size bound `N` and elements
below `U`. -/
def millWordSize (a T N U : ℕ) : ℕ := a * Nat.clog 2 (U + N * T + 2)

/-- The starting configuration of a mill run: preprocessing words `T, N, U` pending. -/
def millInit (w T N U : ℕ) : DynBrooks.Config w :=
  ⟨0, fun _ => 0, [T, N, U], 0, [], ∅⟩

/-- The completed state after preprocessing and the first `i` operations (if reached). -/
noncomputable def millStateAt (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w) (T N U : ℕ)
    (ops : List (MillOp ℕ)) (i : ℕ) : Option (DynBrooks.Config w) :=
  DynBrooks.stateFrom P ω (DynBrooks.complete P ω (millInit w T N U)) ((ops.take i).map MillOp.words)

/-- The time of operation `i` (0-based): steps from delivering its words to the next completed state;
`⊤` if it or an earlier run never completes. -/
noncomputable def millOpTime (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w) (T N U : ℕ)
    (ops : List (MillOp ℕ)) (i : ℕ) : ℕ∞ :=
  match millStateAt P ω T N U ops i, ops[i]? with
  | some s, some op => DynBrooks.time P ω (DynBrooks.feed s op.words)
  | _, _ => ⊤

/-- The words written by the machine during operation `i` (empty if the states are not reached). -/
noncomputable def millOpOutput (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w) (T N U : ℕ)
    (ops : List (MillOp ℕ)) (i : ℕ) : List ℕ :=
  match millStateAt P ω T N U ops i, millStateAt P ω T N U ops (i + 1) with
  | some s, some s' => s'.output.drop s.output.length
  | _, _ => []

end DynColorWC.Main


