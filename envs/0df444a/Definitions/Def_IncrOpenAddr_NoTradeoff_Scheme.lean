-- Prove2me | Definitions.Def_IncrOpenAddr_NoTradeoff_Scheme
-- name    : IncrOpenAddr_NoTradeoff_Scheme
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:35:29.176203+00:00
-- url     : https://prove2.me/theorems/068f1e69-7139-4703-a79d-aee0c6345fee
-- title:
--   Open-addressed hash tables as word-RAM schemes: insertion and query runs, oblivious queries, expected time over a uniform hash function
-- statement:
--   An **incremental open-addressed hash table with reordering** is given by a **scheme** $S$: a probe function $\mathrm{probe}(n,w,f,y,k)$, the $k$-th slot ($k=0,1,\dots$) of key $y$'s probe sequence, which depends only on $n$, $w$, the hash function $f$ and $y$; and two programs $\mathrm{INSERT}$ and $\mathrm{QUERY}$ for the machine of `Machine`, the same programs for every $n$ and $w$.
--
--   Each operation on key $x$ starts on wiped scratch memory holding $n$, $w$, $x$ in cells $0,1,2$ and $0$ elsewhere; the only state that survives an operation is the slot array, and the counter $c$ is the number of insertions performed so far. Inserting $x_1,\dots,x_m$ in order into the empty array, the $(k+1)$-st insertion runs $\mathrm{INSERT}$ on key $x_{k+1}$ with counter $k$; it may read and write any slots in any order (so it may move stored keys). `tableAfter` is the resulting array (undefined if some insertion never halts). `insertTime` $(f, ys, x)$ is the number of steps of $\mathrm{INSERT}$ on key $x$ after the keys $ys$; `queryTime` $(f, xs, y)$ the steps of $\mathrm{QUERY}$ on key $y$ after $xs$. $\mathrm{QUERY}$ never writes, and `queryAnswer` is "present" iff cell $0$ is nonzero when it halts.
--
--   The query is **oblivious** (`IsOblivious`) if, on every array content, every counter value and at every moment of its run, its $k$-th slot read is slot $\mathrm{probe}(n,w,f,y,k)$: it may stop at any time, but never chooses where to probe next. `HoldsExactly A xs` says that every key of $xs$ occupies exactly one slot of $A$ and no other key occurs. Finally, for $T$ a function of the hash function,
--   $$\mathbb E_f[T]=\frac{1}{|\mathrm{Word}_w^{\mathrm{Word}_w\times\mathrm{Word}_w}|}\sum_{f}T(f),$$
--   the expectation over a **uniformly random hash function**.
--
--   **Formalization Note.** Times are in $\mathbb N\cup\{\infty\}$; a run that never halts has time $\infty$, so a finite expected time forces halting for every $f$.
-- source:
--   Farach-Colton, Krapivin, Kuszmaul, Incremental Open Addressing Has No Time-Space Tradeoff, arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 1 (PDF 2), §1 clauses 1–3 and footnote 1; p. 2 (PDF 3), worst-case expected time

import Mathlib
import Definitions.Def_IncrOpenAddr_NoTradeoff_Machine

set_option autoImplicit false

/-!
# Incremental open-addressed hash tables with reordering, as word-RAM schemes

Farach-Colton, Krapivin, Kuszmaul, arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 1 (PDF 2),
the three clauses of open addressing and footnote 1; p. 2 (PDF 3), worst-case expected time.

A scheme is a probe function `probe n w f y k` (the `k`-th slot, `k = 0, 1, …`, of key `y`'s fixed
probe sequence; it depends only on `n`, `w`, the hash function and `y`) and two programs `INSERT`
and `QUERY`, the same for every `n` and `w`.  Each operation starts on wiped scratch memory
holding `n` in cell 0, `w` in cell 1 and the key in cell 2 (all other cells `0`).  The only state
that survives an operation is the slot array; the element counter `c` is maintained by the model
(it is the number of insertions performed) and is read-only for the programs.  A query never
writes; it answers "present" iff cell 0 is nonzero when it halts.
-/

namespace IncrOpenAddr.NoTradeoff

open scoped ENNReal

/-- A scheme: a probe function and the two width-generic programs. -/
structure Scheme where
  probe : (n w : ℕ) → HashFn w → Word w → ℕ → ℕ
  insertProg : Program
  queryProg : Program

variable {n w : ℕ}

/-- The empty array. -/
def emptyArray : SlotArray n w := fun _ => none

/-- Wiped scratch memory holding `n`, `w` and the key in cells 0, 1, 2. -/
def initMem (n w : ℕ) (key : Word w) : Scratch w :=
  fun a => if a = 0 then BitVec.ofNat w n else if a = 1 then BitVec.ofNat w w
    else if a = 2 then key else 0

/-- The initial state of an operation on key `key` and array `A`. -/
def initState (n w : ℕ) (key : Word w) (A : SlotArray n w) : State n w :=
  { mem := initMem n w key, arr := A, pc := 0, halted := false, reads := [] }

/-- The array after `INSERT` of key `x` on array `A` with counter `c` (`none` if it never halts). -/
noncomputable def insertResult (S : Scheme) (f : HashFn w) (c : ℕ) (A : SlotArray n w)
    (x : Word w) : Option (SlotArray n w) :=
  (finalState true f c S.insertProg (initState n w x A)).map (·.arr)

/-- The array after inserting the keys `xs` in order into the empty array, the `(k+1)`-st
insertion running with counter `k` (`none` if some insertion never halts). -/
noncomputable def tableAfter (S : Scheme) (n w : ℕ) (f : HashFn w) (xs : List (Word w)) :
    Option (SlotArray n w) :=
  (xs.foldl (fun (acc : Option (SlotArray n w) × ℕ) x =>
      (acc.1.bind (fun A => insertResult S f acc.2 A x), acc.2 + 1))
    (some emptyArray, 0)).1

/-- Steps taken by inserting `x` after the keys `ys` (`⊤` if it or an earlier insertion never
halts). -/
noncomputable def insertTime (S : Scheme) (n w : ℕ) (f : HashFn w) (ys : List (Word w))
    (x : Word w) : ℕ∞ :=
  match tableAfter S n w f ys with
  | none => ⊤
  | some A => haltTime true f ys.length S.insertProg (initState n w x A)

/-- Steps taken by querying `y` after inserting the keys `xs` (`⊤` if it never halts). -/
noncomputable def queryTime (S : Scheme) (n w : ℕ) (f : HashFn w) (xs : List (Word w))
    (y : Word w) : ℕ∞ :=
  match tableAfter S n w f xs with
  | none => ⊤
  | some A => haltTime false f xs.length S.queryProg (initState n w y A)

/-- The answer of the query for `y` after inserting `xs`: `some true` ("present") if it halts
with cell 0 nonzero, `some false` ("absent") if it halts with cell 0 zero, `none` if it or an
insertion never halts. -/
noncomputable def queryAnswer (S : Scheme) (n w : ℕ) (f : HashFn w) (xs : List (Word w))
    (y : Word w) : Option Bool :=
  (tableAfter S n w f xs).bind fun A =>
    (finalState false f xs.length S.queryProg (initState n w y A)).map
      (fun s => decide (s.mem 0 ≠ 0))

/-- The query is oblivious (classical open addressing, footnote 1): on every array content and
every counter value, at every moment of its run, its `k`-th slot read is slot
`S.probe n w f y k`. -/
def IsOblivious (S : Scheme) (n w : ℕ) (f : HashFn w) (y : Word w) : Prop :=
  ∀ (A : SlotArray n w) (c t k : ℕ)
    (hk : k < (runN false f c S.queryProg t (initState n w y A)).reads.length),
    ((runN false f c S.queryProg t (initState n w y A)).reads.get ⟨k, hk⟩).val =
      S.probe n w f y k

/-- Expectation over a uniformly random hash function `f : Word w → Word w → Word w`. -/
noncomputable def expectHash (T : HashFn w → ℕ∞) : ℝ≥0∞ :=
  (∑ f : HashFn w, (T f : ℝ≥0∞)) / (Fintype.card (HashFn w) : ℝ≥0∞)

/-- The array holds exactly the keys of `xs`, each in exactly one slot, and nothing else. -/
def HoldsExactly (A : SlotArray n w) (xs : List (Word w)) : Prop :=
  ∀ v : Word w, (Finset.univ.filter (fun i => A i = some v)).card = if v ∈ xs then 1 else 0

end IncrOpenAddr.NoTradeoff


