-- Prove2me | Definitions.Def_CLRS_MergeSort
-- name    : CLRS_MergeSort
-- status  : Definition
-- author  : @lunjia
-- created : 2026-09-28T03:04:19.140739+00:00
-- url     : https://prove2.me/theorems/707821a0-f275-4e9a-93a4-78d4a2714a62
-- title:
--   CLRS array merge-sort executions and resource model
-- statement:
--   **The algorithm being formalized**
--
--   The input is a fixed-length array `A` of `N` keys with a linear order, together with endpoints `p` and `r` satisfying `0 ≤ p ≤ r ≤ N`. Indices start at zero. The notation `A[p:r)` means positions `p, p+1, ..., r-1`; the position `r` is excluded. The algorithm updates this slice of the existing array. It allocates temporary merge buffers but does not allocate a separate output array.
--
--   `MERGE_SORT` first checks the slice length. Empty and one-element slices need no changes. A larger slice is split into a left half containing the extra element when the length is odd, and a right half. The algorithm sorts the left half, sorts the right half in the resulting array, and then merges the two halves back into the same array.
--
--   ```text
--   MERGE_SORT(A, p, r)
--       requires 0 ≤ p ≤ r ≤ length(A)
--
--       n ← r - p
--       if n ≤ 1:
--           return
--
--       q ← p + floor((n + 1) / 2)
--       MERGE_SORT(A, p, q)
--       MERGE_SORT(A, q, r)
--       MERGE(A, p, q, r)
--       return
--   ```
--
--   For example, `[p,p+5)` splits into `[p,p+3)` and `[p+3,p+5)`. The recursive calls finish before this call's merge buffers are allocated. This split is the fourth edition's split translated from inclusive endpoints into half-open endpoints.
--
--   `MERGE` copies the two adjacent slices into separate temporary buffers before overwriting any destination cell. It compares the next unread key in each buffer and writes the smaller one into the array; a tie takes the left key. Once either buffer is exhausted, it runs the left remainder loop and then the right remainder loop. Both loops are reached, even when one has nothing left to copy. There are no extra sentinel keys.
--
--   ```text
--   MERGE(A, p, q, r)
--       requires 0 ≤ p ≤ q ≤ r ≤ length(A)
--
--       nL ← q - p
--       nR ← r - q
--       L ← allocate_empty(nL)
--       R ← allocate_empty(nR)
--
--       i ← 0
--       while i < nL:
--           L[i] ← A[p + i]
--           i ← i + 1
--
--       j ← 0
--       while j < nR:
--           R[j] ← A[q + j]
--           j ← j + 1
--
--       i ← 0
--       j ← 0
--       k ← p
--       while i < nL and j < nR:       # test left condition first; short-circuit
--           if L[i] ≤ R[j]:
--               A[k] ← L[i]            # read the selected key again
--               i ← i + 1
--           else:
--               A[k] ← R[j]
--               j ← j + 1
--           k ← k + 1
--
--       while i < nL:
--           A[k] ← L[i]
--           i ← i + 1
--           k ← k + 1
--
--       while j < nR:
--           A[k] ← R[j]
--           j ← j + 1
--           k ← k + 1
--
--       free(L)
--       free(R)
--       return
--   ```
--
--   Here `allocate_empty(k)` creates a fresh temporary buffer with exactly `k` cells, each initialized to an empty marker. This marker is not a key or a sentinel and is never compared with a key. Copying fills the cells before merging reads them. Both buffers stay live until both remainder loops finish; each is then reclaimed once. The Lean model represents these lifetimes by separate buffer scopes rather than general-purpose `allocate` and `free` instructions. It does not distinguish the order of the two final reclamations. The displayed order gives a concrete reading of the same end-of-scope behavior.
--
--   The `requires` lines state input conditions, not runtime checks. Bounds and initialized-cell conditions are proof obligations on executions. Sorted input halves are needed for the merge correctness theorem, but are not required just to execute `MERGE` or obtain its time bound. Empty halves are explicitly allowed. The recursive non-base calls of `MERGE_SORT` use nonempty halves.
--
--   **How the annotations measure this execution**
--
--   The following are the fixed charges used in this mission. They summarize the operations in the displayed pseudocode; they are counted once, rather than added on top of the same primitive charges.
--
--   | Executed work | Charged time |
--   | --- | --- |
--   | Successful iteration of either copy loop | 6: guard 2, address addition 1, read 1, write 1, increment 1 |
--   | Successful iteration of the main merge loop | 12: two guards 4, two comparison-operand reads 2, key comparison 1, branch 1, selected-key reread 1, write 1, two increments 2 |
--   | Successful iteration of either remainder loop | 6: guard 2, read 1, write 1, two increments 2 |
--   | Final failed test of a copy or remainder loop | 2, including for an empty loop |
--   | Final failed main-loop test | 2 if the left buffer is exhausted; otherwise 4 when the right buffer is exhausted |
--   | Other work in one `MERGE` call | `8 + nL + nR`: two length subtractions, two allocation overheads, two reclamations, call and return, plus initialization of every temporary cell |
--   | Empty/singleton `MERGE_SORT` call | 5: length subtraction, comparison, branch, call and return |
--   | Other work in a non-base `MERGE_SORT` call | 8, in addition to its three subcalls: the same five operations plus addition, division and addition for the midpoint |
--
--   The midpoint reuses `n`, so the length subtraction is charged once in that call. Each call and return is charged inside the called procedure. Scalar assignments, loop back-edges, proof obligations and analysis counters are free in this model. Arithmetic on indices and comparisons of keys have unit cost; this is an abstract cost convention, not a statement about native Lean evaluation or bit complexity.
--
--   Time adds across executed steps and subcalls. Heap usage records the greatest number of simultaneously live temporary key cells, excluding the original array and scalar registers. A merge reaches `nL + nR` such cells. Because the left sort, right sort and merge execute sequentially, and the parent owns no buffers during its recursive sorts, a non-base sort's peak auxiliary heap is the maximum of those three peaks. Stack usage counts one frame for the current sort plus the greatest frame count of its subcalls. A base sort and a merge each use one frame; loop iterations do not add procedure frames.
--
--   **What the formal statements say about it**
--
--   The Lean definitions describe finite executions of precisely these branches, loop updates and resource annotations. `CopyLoop` describes each copy loop, `MergeMain` describes the comparison loop, and `RemainderLoop` describes each tail loop. `MergeExec` combines the five loops and their temporary buffers; `MergeSortExec` combines the base case or the two recursive sorts followed by merge. Their resulting array represents updates of the same abstract array. `Usage` records charged time, peak auxiliary cells and peak procedure frames.
--
--   The open theorems must establish that an execution exists for every valid input, and that every such execution satisfies the claimed correctness and resource bounds. Correctness means the selected slice is nondecreasing, contains exactly its original keys with their multiplicities, and leaves every exterior position unchanged. Repeated keys are allowed; left-first ties are part of the algorithm, although a separate stability theorem is not among the current targets. The guarantees concern this declared abstract execution model. A connection to a RAM program or compiled implementation remains a separate possible result.
-- source:
--   Cormen, Leiserson, Rivest, Stein, Introduction to Algorithms, 4th ed., MIT Press (2022), §2.3; official publisher pseudocode https://mitp-content-server.mit.edu/books/content/sectbyfn/books_pres_0/11599/Pseudocode-and-Figures_PDF.zip, nested PDF Pseudocode .zip, Chapter 2/Merge.pdf lines 1–27 and Chapter 2/Merge-Sort.pdf lines 1–7. The half-open indexing, initialized allocation and unit charging rules are explicit formalization conventions. Resource inequalities are derived targets, not quotations or invented numbered textbook theorems. Errata: https://mitp-content-server.mit.edu/books/content/sectbyfn/books_pres_0/11599/e4-bugs.html.

import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Perm.Basic
import Mathlib.Order.Defs.LinearOrder

/-!
# CLRS fourth-edition merge sort: charged indexed-memory semantics

The source is CLRS (4th ed.), §2.3.1, MERGE and MERGE-SORT. We use zero-based,
half-open intervals. Thus `[p,r)` corresponds to the book's inclusive
`[p+1,r]`, and its midpoint becomes `p + (r-p+1)/2`: the left half has the
ceiling length. MERGE is sentinel-free, takes the left key on ties, and runs
both remainder loops after the main loop. Empty slices are also admitted.

`Memory α N` is an abstract array of N cells. A finite function represents its
contents; the model below charges an indexed read or write one unit, irrespective
of the cost of evaluating that function in Lean. This is an abstract unit-cost
indexed-memory model, not a claim about compiled Lean or machine-word arithmetic.
Keys may have any linear order; a key comparison has unit cost.

Every read and write carries its index-bound proof. Temporary cells contain
`Option α`: allocation initializes every cell to `none` at one unit per cell,
plus one unit of allocation overhead. The explicit copy loops fill these cells;
the merge loops can only read cells proved to contain `some x`. Each MERGE scope
owns exactly two distinct blocks (left and right), whose contents cannot escape
through the key-array interface. They are allocated before the copies and freed
once, after both remainder loops. The syntax has no other allocation, deallocation,
or access to these blocks. Recursive MERGE-SORT calls run before the enclosing
MERGE allocates anything. This lexical ownership discipline accounts for legal
lifetimes without an unrestricted heap language.

Time charges one unit per indexed read, indexed write, key/index comparison,
index arithmetic operation, conditional branch, procedure call, procedure return,
allocation overhead, deallocation, and initialized cell. Scalar variable bindings
and assignments are free, as are proof witnesses, function-representation work,
resource counters and resource maxima. Integer arithmetic is mathematical and
unit cost, including division by two and truncated subtraction. Loop back-edges
are free; each loop test charges comparison plus conditional branch, including
the final unsuccessful test. The main `and` guard short-circuits left to right.

The precise loop charges are:
* copying: 2 for its guard, 1 address addition, 1 read, 1 write, 1 increment = 6;
* main merge: 4 for both guards, 2 comparison-operand reads, 1 key comparison,
  1 branch, 1 reread of the selected key, 1 write, 2 increments = 12;
* remainder: 2 guard, 1 read, 1 write, 2 increments = 6.

Each procedure call and return is charged inside that procedure's execution.
MERGE's fixed overhead is 8 (2 length subtractions, 2 allocation overheads,
2 deallocations, call and return), plus one initialization per temporary cell.
MERGE-SORT's base cost is 5 (length subtraction, comparison, branch, call, return).
Its recursive case adds 3 for the translated midpoint's addition, division, and
addition, hence fixed cost 8. The body costs come from the actual loop/recursive
executions, rather than an independently postulated complexity recurrence.

Heap usage counts live auxiliary key cells, excluding the pre-existing input
array and scalar registers. Stack usage counts pseudocode procedure frames,
including the current frame, at one unit per frame. Operational loop derivations
are iteration, not additional pseudocode calls. Fixed scalar-register storage per
frame is represented by this frame unit. No output array is allocated by the
abstract execution: changed finite functions represent updates of the same array.
-/

namespace CLRS

universe u

/-- The contents of a fixed-size abstract indexed array. -/
abbrev Memory (α : Type u) (N : Nat) := Fin N → α

/-- The contents of one owned, fixed-size temporary block. -/
abbrev Buffer (α : Type u) (n : Nat) := Fin n → Option α

/-- Safe abstract indexed update; its semantic charge is supplied by its caller. -/
def write {α : Type u} {N : Nat} (A : Memory α N) (i : Nat) (_hi : i < N)
    (x : α) : Memory α N :=
  fun j => if j.val = i then x else A j

/-- The initialized contents of a newly allocated temporary block. -/
def emptyBuffer (α : Type u) (n : Nat) : Buffer α n := fun _ => none

/-- A valid zero-based half-open slice. -/
def ValidSlice (N p r : Nat) : Prop := p ≤ r ∧ r ≤ N

/-- The exact fourth-edition midpoint after conversion to half-open indexing. -/
def split (p r : Nat) : Nat := p + (r - p + 1) / 2

/-- Contents of a slice, in index order, also defined for invalid slice bounds. -/
def sliceList {α : Type u} {N : Nat} (A : Memory α N) (p r : Nat) : List α :=
  ((List.finRange N).filter fun i => decide (p ≤ i.val ∧ i.val < r)).map A

/-- Nondecreasing order throughout the target slice. -/
def SortedSlice {α : Type u} {N : Nat} [LE α] (A : Memory α N)
    (p r : Nat) : Prop :=
  ∀ i j : Fin N, p ≤ i.val → i.val ≤ j.val → j.val < r → A i ≤ A j

/-- Exactly the same keys, with their multiplicities, occur in the target slice. -/
def PermSlice {α : Type u} {N : Nat} (A B : Memory α N) (p r : Nat) : Prop :=
  (sliceList A p r).Perm (sliceList B p r)

/-- Every cell outside the target slice is unchanged. -/
def OutsideEq {α : Type u} {N : Nat} (A B : Memory α N) (p r : Nat) : Prop :=
  ∀ i : Fin N, i.val < p ∨ r ≤ i.val → A i = B i

/-- Actual charged time, peak auxiliary key cells, and peak procedure frames. -/
structure Usage where
  time : Nat
  heap : Nat
  stack : Nat
  deriving DecidableEq, Repr

/-- Copy `A[start+i]` into temporary cell `i`, then increment `i`.
The final guard is charged even for an empty block. -/
inductive CopyLoop {α : Type u} {N n : Nat} (A : Memory α N) (start : Nat) :
    Nat → Buffer α n → Buffer α n → Nat → Prop where
  | done (i : Nat) (B : Buffer α n) (hi : n ≤ i) :
      CopyLoop A start i B B 2
  | step {i t : Nat} {B B' : Buffer α n}
      (hi : i < n) (ha : start + i < N)
      (next : CopyLoop A start (i + 1)
        (write B i hi (some (A ⟨start + i, ha⟩))) B' t) :
      CopyLoop A start i B B' (6 + t)

/-- The sentinel-free main loop. The final three indices are explicit outputs,
so both remainder loops continue from the exact state reached here. -/
inductive MergeMain {α : Type u} {N nL nR : Nat} [LinearOrder α]
    (L : Buffer α nL) (R : Buffer α nR) :
    Memory α N → Nat → Nat → Nat →
    Memory α N → Nat → Nat → Nat → Nat → Prop where
  | stopLeft (A : Memory α N) (i j k : Nat) (hi : nL ≤ i) :
      MergeMain L R A i j k A i j k 2
  | stopRight (A : Memory α N) (i j k : Nat) (hi : i < nL) (hj : nR ≤ j) :
      MergeMain L R A i j k A i j k 4
  | left {A A' : Memory α N} {i j k i' j' k' t : Nat} {x y : α}
      (hi : i < nL) (hj : j < nR) (hk : k < N)
      (hx : L ⟨i, hi⟩ = some x) (hy : R ⟨j, hj⟩ = some y)
      (hxy : x ≤ y)
      (next : MergeMain L R (write A k hk x) (i + 1) j (k + 1)
        A' i' j' k' t) :
      MergeMain L R A i j k A' i' j' k' (12 + t)
  | right {A A' : Memory α N} {i j k i' j' k' t : Nat} {x y : α}
      (hi : i < nL) (hj : j < nR) (hk : k < N)
      (hx : L ⟨i, hi⟩ = some x) (hy : R ⟨j, hj⟩ = some y)
      (hxy : ¬ x ≤ y)
      (next : MergeMain L R (write A k hk y) i (j + 1) (k + 1)
        A' i' j' k' t) :
      MergeMain L R A i j k A' i' j' k' (12 + t)

/-- A single remainder loop, reading its still-live owned block. -/
inductive RemainderLoop {α : Type u} {N n : Nat} (B : Buffer α n) :
    Memory α N → Nat → Nat → Memory α N → Nat → Nat → Nat → Prop where
  | done (A : Memory α N) (i k : Nat) (hi : n ≤ i) :
      RemainderLoop B A i k A i k 2
  | step {A A' : Memory α N} {i k i' k' t : Nat} {x : α}
      (hi : i < n) (hk : k < N) (hx : B ⟨i, hi⟩ = some x)
      (next : RemainderLoop B (write A k hk x) (i + 1) (k + 1) A' i' k' t) :
      RemainderLoop B A i k A' i' k' (6 + t)

/-- Resource use of one scoped MERGE execution. Its two blocks remain live
through copying, main merging, and both remainder loops, then are freed. -/
def mergeUsage (nL nR tCopyL tCopyR tMain tTailL tTailR : Nat) : Usage :=
  ⟨8 + nL + nR + tCopyL + tCopyR + tMain + tTailL + tTailR,
    nL + nR, 1⟩

/-- Finite, safe execution of CLRS MERGE on adjacent slices `[p,q)` and `[q,r)`.
Sorted inputs are not needed to execute; they are hypotheses of correctness.
The left and right temporary blocks are fresh, distinct lexical allocations.
Only key values are written back to the pre-existing input array. -/
inductive MergeExec {α : Type u} {N : Nat} [LinearOrder α] :
    Memory α N → Nat → Nat → Nat → Memory α N → Usage → Prop where
  | run {A A₁ A₂ A₃ : Memory α N} {p q r : Nat}
      {L : Buffer α (q - p)} {R : Buffer α (r - q)}
      {i j k i₂ k₂ j₃ k₃ tCopyL tCopyR tMain tTailL tTailR : Nat}
      (hpq : p ≤ q) (hqr : q ≤ r) (hr : r ≤ N)
      (copyL : CopyLoop A p 0 (emptyBuffer α (q - p)) L tCopyL)
      (copyR : CopyLoop A q 0 (emptyBuffer α (r - q)) R tCopyR)
      (main : MergeMain L R A 0 0 p A₁ i j k tMain)
      (tailL : RemainderLoop L A₁ i k A₂ i₂ k₂ tTailL)
      (tailR : RemainderLoop R A₂ j k₂ A₃ j₃ k₃ tTailR) :
      MergeExec A p q r A₃
        (mergeUsage (q - p) (r - q) tCopyL tCopyR tMain tTailL tTailR)

/-- Resource use of the empty/singleton MERGE-SORT branch. -/
def baseUsage : Usage := ⟨5, 0, 1⟩

/-- Sequential left sort, right sort, and merge. No enclosing temporary blocks
are live during either recursive sort. The current sort frame encloses all three
calls; main/copy/remainder loop derivations do not allocate call frames. -/
def sortUsage (left right merge : Usage) : Usage :=
  ⟨8 + left.time + right.time + merge.time,
    max left.heap (max right.heap merge.heap),
    1 + max left.stack (max right.stack merge.stack)⟩

/-- Finite, safe execution of the fourth-edition MERGE-SORT algorithm.
Existence is a separate termination obligation; this inductive relation does not
assume that a successful result exists. All result and resource fields come from
its executed branch and recursive/loop premises. -/
inductive MergeSortExec {α : Type u} {N : Nat} [LinearOrder α] :
    Memory α N → Nat → Nat → Memory α N → Usage → Prop where
  | base (A : Memory α N) (p r : Nat) (valid : ValidSlice N p r)
      (small : r - p ≤ 1) :
      MergeSortExec A p r A baseUsage
  | step {A A₁ A₂ A₃ : Memory α N} {p r : Nat} {uL uR uM : Usage}
      (valid : ValidSlice N p r) (large : 1 < r - p)
      (left : MergeSortExec A p (split p r) A₁ uL)
      (right : MergeSortExec A₁ (split p r) r A₂ uR)
      (merge : MergeExec A₂ p (split p r) r A₃ uM) :
      MergeSortExec A p r A₃ (sortUsage uL uR uM)

end CLRS


