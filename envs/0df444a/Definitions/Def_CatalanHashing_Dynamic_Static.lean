-- Prove2me | Definitions.Def_CatalanHashing_Dynamic_Static
-- name    : CatalanHashing_Dynamic_Static
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:05:30.915049+00:00
-- url     : https://prove2.me/theorems/fe9b22a2-a02f-451d-8a26-f8c652a3d63a
-- title:
--   Static Catalan tables: placements, the Catalan nesting property, bottom-up priority placement, Catalan representation, query procedure, Catalan parser, simple Catalan hashing and H_Y, ARCH
-- statement:
--   A static table has $m$ cells indexed cyclically by $\{0,\dots,m-1\}$; $\mathrm{cdist}(a,c)=(c-a)\bmod m$ is the forward distance. The stored items form a finite set; item $x$ has length $|x|\ge1$ and canonical cell $c(x)$. An **occupancy** says which word $j\in\{0,\dots,|x|-1\}$ of which item each cell holds, if any. It is a **placement** if every word of every item is held by exactly one cell and the words of $x$ appear in logical order in the forward scan from the first word of $x$. Then $I_x=[a_x,b_x]$ is the cyclic interval from the cell $a_x$ of the first word of $x$ to the cell $b_x$ of its last word.
--
--   **Catalan nesting property** (Definition 3.1). Every $I_x$ lies inside a run (all its cells are occupied), and for distinct items $x,y$: (1) $I_x\cap I_y=\emptyset$, or $I_y\subsetneq I_x$, or $I_x\subsetneq I_y$; (2) if $I_y\subsetneq I_x$, no cell of $I_y$ stores a word of $x$. A **Catalan placement** for canonical cells $c$ also has every item at or after its canonical cell inside its run: $a_x$ comes no later than $b_x$ in the forward scan from $c(x)$ and every cell from $c(x)$ through $b_x$ is occupied.
--
--   **Bottom-up construction.** For a priority rule, listed as the items in decreasing priority, place the items in that order, each in the first $|x|$ empty cells at or after $c(x)$.
--
--   **Catalan representation.** Each cell carries a tag in $\{\mathrm{open},\mathrm{middle},\mathrm{close},\mathrm{open\text{-}close},\mathrm{empty}\}$ (open-close for an item of length 1; otherwise open, middle, close for its first, interior and last words), a home bit (the cell is the canonical cell of a stored item) and a stop bit (the cell is the last cell, in the forward order from $c(x)$, holding a word of an item with canonical cell $c(x)$).
--
--   **Query procedure.** A query with canonical cell $j$ reads $j$ and returns at once if $j$ is not a home cell (cost 1). Otherwise it scans forward from $j$ and stops at the first cell that is empty, or is the last cell of the item sought, or is the last cell of another item with canonical cell $j$ and has its stop bit set. Its scan cost is the number of cells from $j$ through that cell; `queryCost` gives it for a positive query (the item sought is stored) and for a negative one (it is not).
--
--   **Catalan parser** (Appendix A). State: a stack of frames, one per item whose open tag was read, each buffering the words of its item read so far (its counter $\mathrm{cnt}$ is the buffer length), and an unmatched-suffix counter $f$. On open: push a frame with the word. On open-close: complete a one-word item. On middle (close) with a nonempty stack: append the word to the top frame (and pop it, completing its item). On middle with an empty stack: $f\leftarrow f+1$. On close with an empty stack: $f\leftarrow0$. On empty: stop.
--
--   **Hashing.** A hash value $u\in[0,1]$ has canonical cell $\lfloor mu\rfloor$. **Simple Catalan hashing** prioritises $y$ over $z$ iff $|y|<|z|$, or $|y|=|z|$ and $h(y)<h(z)$. For an item $x$, $H_Y$ is the simple Catalan table on $Y=\{y:|y|\le|x|\}$, and $W_x$ is the length of the run of $H_Y$ containing $c(x)$. **ARCH** (anti-Robin-Hood Catalan hashing) is the bottom-up table in which $x$ has priority over $y$ iff $h(x)>h(y)$, the hashes being compared cyclically: within each run, positions $mh(\cdot)$ are measured forward from the first cell of the run. The runs do not depend on the priority order: a cell $d$ is empty iff for every $j<m$ the items with canonical cell in $[d-j,d]$ have total length at most $j$.
--
--   **Formalization Note.** Items are indexed by a finite type `ι`; `len`, `c` and the hash `h : ι → unitInterval` are functions on it. The canonical cell is capped at $m-1$, which only matters on the null event $u=1$. The bottom-up construction for an ordering with total length above $m$ is junk and is never used.
-- source:
--   Conway, Komlós, Kuszmaul, Catalan Hashing: Efficient Linear Probing for Variable-Length Items, arXiv:2611.05235 (copy sha256 e2048176…), pp. 9-12 (Section 3, Definitions 3.1 and 3.4; Section 4), p. 17 (occupied cells), p. 26 (Section 7.2, ARCH), pp. 39-40 (Appendix A)

import Mathlib

/-!
# Static Catalan hash tables: placements, nesting, representation, query procedure, parser,
# simple Catalan hashing and ARCH

Conway, Komlós, Kuszmaul, *Catalan Hashing: Efficient Linear Probing for Variable-Length Items*,
arXiv:2611.05235 (copy sha256 e2048176…), pp. 7-12 (Sections 2-4), p. 26 (Section 7.2) and
pp. 39-40 (Appendix A).

A table has `m` cells indexed cyclically by `Fin m`. The stored items are indexed by a finite
type `ι`; item `x` has length `len x` (in words) and canonical cell `c x`.

* `cdist a c` is the forward cyclic distance from cell `a` to cell `c`; `shift t d` is the cell
  `d` steps after `t`.
* An `Occupancy` says which word of which item each cell holds. `IsPlacement` says it is a
  placement: every word of every item is in exactly one cell and the words of an item appear in
  logical order along the forward scan from its first word.
* `InInterval len occ x c` is `c ∈ I_x = [a_x, b_x]`, the cyclic interval from the first word of
  `x` to its last word. `CatalanNesting` is Definition 3.1, with "within every run" read as
  "every interval `I_x` lies inside a run (all of its cells are occupied)".
* `IsCatalanPlacement` adds that every item lies at or after its canonical cell, in the run
  containing it: the placements of a static Catalan table ("an arbitrary placement rule").
* `bottomUp len c order` is the bottom-up construction for the priority rule whose decreasing
  order is the list `order`: each item in turn takes the first `|x|` empty cells at or after
  `c(x)`.
* The Catalan representation: a 5-valued tag per cell, a home bit (the cell is the canonical
  cell of a stored item) and a stop bit (the cell is the last cell containing a word of an item
  whose canonical cell is some home cell `j`, last in the forward order from `j`).
* `queryCost` is the scan cost of the query procedure of Section 3: a query for the item
  `target` (or, if `target = none`, for a key that is not stored) with canonical cell `j`
  reads `j` and stops at once if `j` is not a home cell; otherwise it scans forward from `j`
  and stops at the first cell that is empty, that is the last cell of the target item, or that
  is the last cell of another item with canonical cell `j` and carries the stop bit. The cost is
  the number of cells from `j` through that cell.
* `parserStep` and `parseRun` are the Catalan parser of Appendix A; a frame buffers the words of
  its item read so far (its counter `cnt` is the buffer's length; the key comparison and the
  canonical cell are functions of the buffer).
* Hash values lie in `[0, 1]` (`unitInterval`); the canonical cell of hash `u` in an `m`-cell
  table is `⌊m u⌋` (capped at `m - 1`, which matters only on the null event `u = 1`).
* `simpleOrder` is the priority order of simple Catalan hashing (shorter first, then smaller
  hash); `runLengthHY` is `W_x`, the length of the run of `H_Y` containing `c(x)`, where `H_Y`
  is the simple Catalan table on `Y = {y : |y| ≤ |x|}` (Lemma 4.2).
* `arch` is the ARCH placement: priority to the larger hash, hashes compared cyclically after
  unwrapping each run at the empty cell before it. The occupied cells (and hence the runs) do
  not depend on the priority order: a cell `c` is empty iff for every `j < m` the items hashing
  into `[c - j, c]` have total length at most `j` (p. 17).
-/

namespace CatalanHashing.Dynamic

/-- The five delimiter tags of the Catalan representation. -/
inductive Tag where
  | open_
  | middle
  | close
  | openClose
  | empty
  deriving DecidableEq

instance : Fintype Tag :=
  ⟨{.open_, .middle, .close, .openClose, .empty}, by intro x; cases x <;> simp⟩

end CatalanHashing.Dynamic

open scoped Classical

namespace CatalanHashing.Dynamic

section Cyclic

variable {m : ℕ}

/-- Forward cyclic distance from `a` to `c` in `Fin m`. -/
def cdist (a c : Fin m) : ℕ :=
  ((c : ℕ) + m - (a : ℕ)) % m

/-- The cell `d` steps after `t`. -/
def shift (t : Fin m) (d : ℕ) : Fin m :=
  ⟨((t : ℕ) + d) % m, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) t.isLt)⟩

/-- The cell `d` steps before `t`. -/
def shiftBack (t : Fin m) (d : ℕ) : Fin m :=
  ⟨((t : ℕ) + m - d % m) % m, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) t.isLt)⟩

end Cyclic

/-- Which word of which item each cell holds: `some (x, j)` is word `j` (0-based) of `x`. -/
abbrev Occupancy (m : ℕ) (ι : Type*) : Type _ := Fin m → Option (ι × ℕ)

section Placement

variable {m : ℕ} {ι : Type*}

/-- `occ` is a placement of items of lengths `len`: only words `j < len x` are stored, each
exactly once, and the words of `x` follow each other in logical order in the forward scan from
the first word of `x`. -/
def IsPlacement (len : ι → ℕ) (occ : Occupancy m ι) : Prop :=
  (∀ c x j, occ c = some (x, j) → j < len x) ∧
  (∀ x j, j < len x → ∃! c, occ c = some (x, j)) ∧
  (∀ x j j' a c c', occ a = some (x, 0) → occ c = some (x, j) → occ c' = some (x, j') →
    j < j' → cdist a c < cdist a c')

/-- `c ∈ I_x`: cell `c` lies in the cyclic interval from the first to the last word of `x`. -/
def InInterval (len : ι → ℕ) (occ : Occupancy m ι) (x : ι) (c : Fin m) : Prop :=
  ∃ a e, occ a = some (x, 0) ∧ occ e = some (x, len x - 1) ∧ cdist a c ≤ cdist a e

/-- `I_y ⊊ I_x`. -/
def StrictSubInterval (len : ι → ℕ) (occ : Occupancy m ι) (y x : ι) : Prop :=
  (∀ c, InInterval len occ y c → InInterval len occ x c) ∧
  ∃ c, InInterval len occ x c ∧ ¬ InInterval len occ y c

/-- Definition 3.1 (Catalan nesting property). Every interval `I_x` lies in a run, and for
distinct `x, y`: (1) `I_x`, `I_y` are disjoint or one strictly contains the other; (2) if
`I_y ⊊ I_x`, no cell of `I_y` stores a word of `x`. -/
def CatalanNesting (len : ι → ℕ) (occ : Occupancy m ι) : Prop :=
  (∀ x c, InInterval len occ x c → occ c ≠ none) ∧
  (∀ x y, x ≠ y →
    (∀ c, ¬ (InInterval len occ x c ∧ InInterval len occ y c)) ∨
      StrictSubInterval len occ y x ∨ StrictSubInterval len occ x y) ∧
  (∀ x y, x ≠ y → StrictSubInterval len occ y x →
    ∀ c, InInterval len occ y c → ∀ j, occ c ≠ some (x, j))

/-- A placement of a static Catalan table with canonical cells `c`: a placement with the Catalan
nesting property in which every item lies at or after its canonical cell, inside the run that
contains it (every cell from `c(x)` through the last word of `x` is occupied). -/
def IsCatalanPlacement (len : ι → ℕ) (c : ι → Fin m) (occ : Occupancy m ι) : Prop :=
  IsPlacement len occ ∧ CatalanNesting len occ ∧
  ∀ x a e, occ a = some (x, 0) → occ e = some (x, len x - 1) →
    cdist (c x) a ≤ cdist (c x) e ∧ ∀ d ≤ cdist (c x) e, occ (shift (c x) d) ≠ none

/-- The cells `t, t + 1, …, t + m - 1` in forward order. -/
def scanFrom (t : Fin m) : List (Fin m) :=
  (List.range m).map (shift t)

/-- Place item `x` in the first `|x|` empty cells at or after `c(x)` (word `j` in the `j`-th of
them). -/
noncomputable def placeItem (len : ι → ℕ) (c : ι → Fin m) (occ : Occupancy m ι) (x : ι) :
    Occupancy m ι :=
  let cells := ((scanFrom (c x)).filter (fun d => decide (occ d = none))).take (len x)
  fun d => if d ∈ cells then some (x, cells.idxOf d) else occ d

/-- The bottom-up construction for the priority rule whose decreasing priority order is
`order`. -/
noncomputable def bottomUp (len : ι → ℕ) (c : ι → Fin m) (order : List ι) : Occupancy m ι :=
  order.foldl (placeItem len c) (fun _ => none)

end Placement

/-- The per-cell metadata of the Catalan representation: tag, home bit, stop bit. -/
abbrev CellMeta : Type := Tag × Bool × Bool

section Representation

variable {m : ℕ} {ι : Type*}

/-- The delimiter tag of cell `d`. -/
def tagOf (len : ι → ℕ) (occ : Occupancy m ι) (d : Fin m) : Tag :=
  match occ d with
  | none => .empty
  | some (x, j) =>
      if len x = 1 then .openClose
      else if j = 0 then .open_
      else if j + 1 = len x then .close
      else .middle

/-- Home bit: `d` is the canonical cell of some stored item. -/
def homeBit (c : ι → Fin m) (d : Fin m) : Prop :=
  ∃ x, c x = d

/-- Stop bit: `d` holds a word of an item `x`, and no item with canonical cell `c x` has a word
in a cell farther from `c x` than `d` (so `d` is the stop cell of the home cell `c x`). -/
def stopBit (c : ι → Fin m) (occ : Occupancy m ι) (d : Fin m) : Prop :=
  ∃ x j, occ d = some (x, j) ∧
    ∀ y, c y = c x → ∀ e j', occ e = some (y, j') → cdist (c x) e ≤ cdist (c x) d

/-- The Catalan representation of cell `d`. -/
noncomputable def catalanMeta (len : ι → ℕ) (c : ι → Fin m) (occ : Occupancy m ι)
    (d : Fin m) : CellMeta :=
  (tagOf len occ d, decide (homeBit c d), decide (stopBit c occ d))

/-- The query procedure stops at cell `s`: `s` is empty, or `s` is the last cell of the target
item, or `s` is the last cell of another item with canonical cell `j` and its stop bit is set. -/
def queryStopsAt (len : ι → ℕ) (c : ι → Fin m) (occ : Occupancy m ι) (target : Option ι)
    (j s : Fin m) : Prop :=
  occ s = none ∨
  (∃ x, target = some x ∧ occ s = some (x, len x - 1)) ∨
  (∃ y, target ≠ some y ∧ c y = j ∧ occ s = some (y, len y - 1) ∧ stopBit c occ s)

/-- Scan cost of a query with canonical cell `j` for the stored item `target = some x` (then
`j = c x`) or, for `target = none`, for a key not in the table. -/
noncomputable def queryCost (len : ι → ℕ) (c : ι → Fin m) (occ : Occupancy m ι)
    (target : Option ι) (j : Fin m) : ℕ :=
  if ¬ homeBit c j then 1 else
    match (List.range m).find? (fun d => decide (queryStopsAt len c occ target j (shift j d)))
    with
    | some d => d + 1
    | none => m

end Representation

section Parser

variable {W : Type*}

/-- State of the Catalan parser: a stack of frames (head = top; a frame buffers the words of
its item read so far, so its counter `cnt` is the buffer's length), the unmatched-suffix
counter `f`, and whether the scan has terminated. -/
structure ParserState (W : Type*) where
  /-- The stack `S` of active frames. -/
  stack : List (List W)
  /-- The unmatched-suffix counter `f`. -/
  f : ℕ
  /-- Set once an empty cell has been read (transition (vii)). -/
  halted : Bool

/-- The initial parser state: empty stack, `f = 0`. -/
def ParserState.init : ParserState W :=
  ⟨[], 0, false⟩

/-- One transition of the Catalan parser on a cell with tag `t` and word `wd`; the second
component is the item completed at this cell, if any (transitions (i)-(vii) of Appendix A). -/
def parserStep (s : ParserState W) (t : Tag) (wd : W) : ParserState W × Option (List W) :=
  if s.halted then (s, none) else
  match t, s.stack with
  | .open_, st => (⟨[wd] :: st, s.f, false⟩, none)
  | .openClose, _ => (s, some [wd])
  | .middle, top :: rest => (⟨(top ++ [wd]) :: rest, s.f, false⟩, none)
  | .close, top :: rest => (⟨rest, s.f, false⟩, some (top ++ [wd]))
  | .middle, [] => (⟨[], s.f + 1, false⟩, none)
  | .close, [] => (⟨[], 0, false⟩, none)
  | .empty, st => (⟨st, s.f, true⟩, none)

/-- Run the parser over the `n` cells `t, t + 1, …, t + n - 1`: the final state, and the list
of `(d, item)` for every item completed at the cell `t + d`. -/
def parseRun {m : ℕ} (tag : Fin m → Tag) (word : Fin m → W) (t : Fin m) (n : ℕ) :
    ParserState W × List (ℕ × List W) :=
  (List.range n).foldl
    (fun acc d =>
      let r := parserStep acc.1 (tag (shift t d)) (word (shift t d))
      (r.1, match r.2 with
        | some ws => acc.2 ++ [(d, ws)]
        | none => acc.2))
    (ParserState.init, [])

/-- The words of item `x` held in the first `n` cells `t, …, t + n - 1` of the scan, in scan
order. -/
noncomputable def seenWords {m : ℕ} {ι : Type*} (occ : Occupancy m ι) (itemWord : ι → ℕ → W) (t : Fin m)
    (x : ι) (n : ℕ) : List W :=
  (List.range n).filterMap (fun d =>
    match occ (shift t d) with
    | some (y, j) => if y = x then some (itemWord x j) else none
    | none => none)

end Parser

section Hashing

/-- The canonical cell `⌊m u⌋` of the hash value `u ∈ [0, 1]` in an `m`-cell table (capped at
`m - 1`). -/
noncomputable def canonical (m : ℕ) [NeZero m] (u : unitInterval) : Fin m :=
  ⟨min (⌊(m : ℝ) * (u : ℝ)⌋₊) (m - 1),
    lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne m)) one_pos)⟩

variable {ι : Type*} [Fintype ι]

/-- The priority order of simple Catalan hashing (decreasing priority): `y` before `z` iff
`|y| < |z|`, or `|y| = |z|` and `h(y) ≤ h(z)`. -/
noncomputable def simpleOrder (len : ι → ℕ) (h : ι → unitInterval) : List ι :=
  (Finset.univ : Finset ι).toList.mergeSort
    (fun y z => decide (len y < len z ∨ (len y = len z ∧ (h y : ℝ) ≤ (h z : ℝ))))

/-- The occupied cells of a table: `d` is occupied iff `occ d ≠ none`. -/
def Occupied {m : ℕ} {κ : Type*} (occ : Occupancy m κ) (d : Fin m) : Prop :=
  occ d ≠ none

/-- Length of the run (maximal cyclic interval of cells satisfying `O`) containing `d`;
`0` if `d` is not in `O`, `m` if every cell is in `O`. -/
noncomputable def runLength {m : ℕ} (O : Fin m → Prop) (d : Fin m) : ℕ :=
  if ¬ O d then 0 else
    match (List.range m).find? (fun e => decide (¬ O (shift d e))),
        (List.range m).find? (fun e => decide (¬ O (shiftBack d e))) with
    | some f, some g => f + g - 1
    | _, _ => m

/-- `H_Y` for the item `x`: the simple Catalan table (bottom-up placement in the simple
priority order) on `Y = {y : |y| ≤ |x|}`, with canonical cells `⌊m h(y)⌋`. -/
noncomputable def simpleTableHY (m : ℕ) [NeZero m] (len : ι → ℕ) (h : ι → unitInterval)
    (x : ι) : Occupancy m {y : ι // len y ≤ len x} :=
  bottomUp (fun y => len y.1) (fun y => canonical m (h y.1))
    (simpleOrder (fun y : {y : ι // len y ≤ len x} => len y.1) (fun y => h y.1))

/-- `W_x`: the length of the run of `H_Y` containing `c(x)`. -/
noncomputable def runLengthHY (m : ℕ) [NeZero m] (len : ι → ℕ) (h : ι → unitInterval)
    (x : ι) : ℕ :=
  runLength (Occupied (simpleTableHY m len h x)) (canonical m (h x))

/-- The occupied cells of every priority placement: `d` is empty iff for every `j < m` the
items whose canonical cell lies in `[d - j, d]` have total length at most `j`. -/
def loadOccupied {m : ℕ} (len : ι → ℕ) (c : ι → Fin m) (d : Fin m) : Prop :=
  ∃ j < m, j < ∑ x ∈ Finset.univ.filter (fun x => cdist (c x) d ≤ j), len x

/-- The first cell of the run containing `d` (cells occupied in `loadOccupied`). -/
noncomputable def runStart {m : ℕ} (len : ι → ℕ) (c : ι → Fin m) (d : Fin m) : Fin m :=
  match (List.range m).find? (fun e => decide (¬ loadOccupied len c (shiftBack d (e + 1)))) with
  | some e => shiftBack d e
  | none => d

/-- The ARCH priority value of `x`: its hash position `m h(x)` measured forward from the first
cell of the run containing `c(x)` (hashes compared cyclically within the run). -/
noncomputable def archKey (m : ℕ) [NeZero m] (len : ι → ℕ) (h : ι → unitInterval) (x : ι) : ℝ :=
  let c := fun y => canonical m (h y)
  let r := (m : ℝ) * (h x : ℝ) - ((runStart len c (c x) : ℕ) : ℝ)
  if r < 0 then r + m else r

/-- The ARCH decreasing priority order: larger (cyclically compared) hash first. -/
noncomputable def archOrder (m : ℕ) [NeZero m] (len : ι → ℕ) (h : ι → unitInterval) : List ι :=
  (Finset.univ : Finset ι).toList.mergeSort
    (fun y z => decide (archKey m len h z ≤ archKey m len h y))

/-- The ARCH table: the bottom-up placement in the ARCH priority order. -/
noncomputable def arch (m : ℕ) [NeZero m] (len : ι → ℕ) (h : ι → unitInterval) :
    Occupancy m ι :=
  bottomUp len (fun y => canonical m (h y)) (archOrder m len h)

end Hashing

end CatalanHashing.Dynamic


