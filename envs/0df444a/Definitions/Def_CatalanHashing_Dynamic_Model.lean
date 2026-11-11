-- Prove2me | Definitions.Def_CatalanHashing_Dynamic_Model
-- name    : CatalanHashing_Dynamic_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:05:29.187188+00:00
-- url     : https://prove2.me/theorems/b8bb7743-bd41-4ac4-a46c-4994450ecd82
-- title:
--   Cell-array dictionaries: N cells of one word and b metadata bits, bounded global state, decision-tree operation programs, scan cost, fully random hashing, valid oblivious sequences
-- statement:
--   A **word** is a string of $w$ bits. A **key** $k$ is a nonempty finite sequence of words and a **value** $v$ a finite, possibly empty, sequence of words; the **length** of the item $x=(k,v)$ is $|x|=|k|+|v|$.
--
--   A **dynamic dictionary on $N$ cells with $b$ metadata bits** works on a physical array of $N$ cells indexed cyclically by $\{0,\dots,N-1\}$; each cell holds one $w$-bit data word and $b$ metadata bits, and all cells are initially zero. Besides the array it keeps a **persistent global state**, a list of words, initially empty. Each operation $\mathrm{Insert}(k,v)$, $\mathrm{Delete}(k)$, $\mathrm{Query}(k)$ is executed by a **program**, chosen as a function of the operation and the current global state: a finite adaptive decision tree whose nodes read a cell and branch on its content, write a cell, or evaluate the $j$-th random function at a key and branch on the real value; a leaf halts with an answer ($\mathrm{Found}$ with a value, or $\mathrm{Not\ Found}$) and the new global state. Within one operation the program may remember everything it has seen; only the array and the global state persist. The dictionary **keeps at most $B$ words of global state** if every program started from at most $B$ words halts with at most $B$ words.
--
--   **Randomness.** The sample space is $\Omega=(\mathbb N\times\mathrm{Key}\to[0,1])$ with the product of uniform measures: $\omega(j,k)$ is the value of the $j$-th fully random hash function at $k$, independent over all $(j,k)$.
--
--   **Scan cost.** The scan cost of one operation is the size of the smallest cyclic interval of $\{0,\dots,N-1\}$ containing every cell it read or wrote ($0$ if none). For an operation sequence $\sigma$, run from the zero array and the empty global state, $\mathrm{cost}_\sigma(\omega)$ is the sum of the scan costs of its operations.
--
--   **Valid sequences.** The live set before operation $i$ is obtained from the empty dictionary by applying the first $i$ operations ($\mathrm{Insert}$ adds an item, $\mathrm{Delete}$ removes the item with that key). A finite sequence $\sigma$, fixed in advance, is **valid for $(N,\varepsilon)$** if every insertion is of an absent key, every deletion of a present key, and after every operation the live volume $\sum_{x\ \mathrm{live}}|x|$ is at most $(1-\varepsilon)N$. A run is **correct** if every $\mathrm{Query}(k)$ returns $\mathrm{Found}$ with the live value of $k$ when $k$ is live, and $\mathrm{Not\ Found}$ otherwise.
--
--   **Budgets.** With $\log s=\max\{1,\log_2 s\}$, the budget of one operation, given the live set before it, is
--   $$b(\mathrm{op})=\begin{cases}|x|/\varepsilon & \text{positive query for the live item }x,\\ 1/\varepsilon & \text{negative query (any key length)},\\ |x|\,(\log|x|)^{1+\delta}/\varepsilon & \text{insertion or deletion of }x.\end{cases}$$
--
--   **Formalization Note.** Words and metadata are `BitVec w` and `BitVec b`; cells are indexed by `Fin N`. Hash values are uniform on $[0,1]$ (`unitInterval`) rather than on $[0,N)$; a program rescales. The global-state allowance used by the goal is `globalAllowance N cg` $=c_g(\lceil\log_2 N\rceil+1)^2$ words.
-- source:
--   Conway, Komlós, Kuszmaul, Catalan Hashing: Efficient Linear Probing for Variable-Length Items, arXiv:2611.05235 (copy sha256 e2048176…), pp. 7-8, Section 2 (Preliminaries); p. 31, Section 8.1 (physical array)

import Mathlib

/-!
# Cell-array dictionaries with scan cost (the machine model of Theorem 1.4)

Conway, Komlós, Kuszmaul, *Catalan Hashing: Efficient Linear Probing for Variable-Length Items*,
arXiv:2611.05235 (copy sha256 e2048176…), pp. 7-8, Section 2 (Preliminaries), and p. 31.

* A word is a `w`-bit string (`BitVec w`). A key is a nonempty list of words, a value a list of
  words (possibly empty), and the length of the item `x = (k, v)` is `|x| = |k| + |v|`.
* Physical memory is `N` cells indexed cyclically by `Fin N`; each cell holds one data word and
  `b` metadata bits (`BitVec b`). Initially every cell is all-zero.
* A persistent global state is a list of words; its length bound is part of the theorem.
* One operation is executed by a program: a finite, adaptive decision tree that reads a cell and
  branches on its content, writes a cell, evaluates random function `j` at a key and branches on
  the real value, or halts with an answer and a new global state. Inside one operation the
  program may remember everything it has seen (unbounded transient memory); only the cells and
  the global state persist.
* Randomness: `Ω = (ℕ × Key → [0, 1])`, with the product of uniform measures; coordinate
  `(j, k)` is the value of the `j`-th fully random hash function at the key `k`.
* The scan cost of an operation is the size of the smallest cyclic interval of `Fin N` that
  contains every cell it read or wrote (`0` if it accessed none).
* Operation sequences are fixed lists (oblivious adversary). `LiveSet` is the dictionary that
  the sequence itself determines; `Valid N ε σ` says that every insertion is of an absent key,
  every deletion of a present key, and the live volume is at most `(1 - ε) N` after every
  operation. `Correct` says that every query of the run returned the live value of its key.
* `budget ε δ` is the cost bound of Theorem 1.4 for one operation: `|x|/ε` for a positive
  query, `1/ε` for a negative one, `|x| · (log |x|)^{1+δ} / ε` for an insertion or deletion of
  `x`, with `log s = max {1, log₂ s}`.
-/

open MeasureTheory

namespace CatalanHashing.Dynamic

/-- A machine word of `w` bits. -/
abbrev Word (w : ℕ) : Type := BitVec w

/-- A key: a nonempty finite sequence of words. -/
abbrev Key (w : ℕ) : Type := {l : List (Word w) // l ≠ []}

/-- A value: a finite, possibly empty, sequence of words. -/
abbrev Value (w : ℕ) : Type := List (Word w)

/-- The length `|x| = |k| + |v|` (in words) of the item `x = (k, v)`. -/
def itemLength {w : ℕ} (k : Key w) (v : Value w) : ℕ :=
  k.1.length + v.length

/-- A cell: one data word and `b` metadata bits. -/
abbrev Cell (w b : ℕ) : Type := Word w × BitVec b

/-- The physical array: `N` cells indexed cyclically by `Fin N`. -/
abbrev Memory (N w b : ℕ) : Type := Fin N → Cell w b

/-- The all-zero initial memory. -/
def initialMemory (N w b : ℕ) : Memory N w b :=
  fun _ => (0, 0)

/-- The persistent global state: a list of words. -/
abbrev GlobalState (w : ℕ) : Type := List (Word w)

/-- The three dictionary operations. -/
inductive Op (w : ℕ) where
  /-- `Insert(k, v)`. -/
  | insert (k : Key w) (v : Value w)
  /-- `Delete(k)`. -/
  | delete (k : Key w)
  /-- `Query(k)`. -/
  | query (k : Key w)

/-- The answer of an operation: `some v` is `Found` with value `v`, `none` is `Not Found`. -/
abbrev Answer (w : ℕ) : Type := Option (Value w)

/-- The sample space: the value of the `j`-th fully random function at the key `k` is
`ω (j, k) ∈ [0, 1]`. -/
abbrev Omega (w : ℕ) : Type := ℕ × Key w → unitInterval

/-- The law of the randomness: independent uniform values at every coordinate. -/
noncomputable def omegaMeasure (w : ℕ) : Measure (Omega w) :=
  Measure.infinitePi (fun _ : ℕ × Key w => (volume : Measure unitInterval))

/-- An operation program: a finite adaptive decision tree. -/
inductive Prog (N w b : ℕ) : Type where
  /-- Read cell `i` and continue according to its content. -/
  | read (i : Fin N) (next : Cell w b → Prog N w b)
  /-- Write `c` into cell `i`. -/
  | write (i : Fin N) (c : Cell w b) (next : Prog N w b)
  /-- Evaluate random function `j` at key `k` and continue according to its value. -/
  | hash (j : ℕ) (k : Key w) (next : unitInterval → Prog N w b)
  /-- Halt with an answer and the new persistent global state. -/
  | halt (ans : Answer w) (g : GlobalState w)

/-- What one execution of a program leaves behind. -/
structure Outcome (N w b : ℕ) where
  /-- The answer returned. -/
  ans : Answer w
  /-- The memory afterwards. -/
  mem : Memory N w b
  /-- The global state afterwards. -/
  glob : GlobalState w
  /-- Every cell that was read or written. -/
  touched : Finset (Fin N)

/-- Execute a program on memory `M` with the random functions `ω`. -/
def Prog.exec {N w b : ℕ} (ω : Omega w) : Prog N w b → Memory N w b → Outcome N w b
  | .read i next, M =>
      let o := (next (M i)).exec ω M
      { o with touched := insert i o.touched }
  | .write i c next, M =>
      let o := next.exec ω (Function.update M i c)
      { o with touched := insert i o.touched }
  | .hash j k next, M => (next (ω (j, k))).exec ω M
  | .halt a g, M => ⟨a, M, g, ∅⟩

/-- Every global state with which the program can halt has at most `B` words. -/
def Prog.GlobalBounded {N w b : ℕ} (B : ℕ) : Prog N w b → Prop
  | .read _ next => ∀ c, (next c).GlobalBounded B
  | .write _ _ next => next.GlobalBounded B
  | .hash _ _ next => ∀ u, (next u).GlobalBounded B
  | .halt _ g => g.length ≤ B

/-- The size of the smallest cyclic interval of `Fin N` containing `A` (`0` if `A = ∅`). -/
noncomputable def cyclicSpan (N : ℕ) (A : Finset (Fin N)) : ℕ :=
  if A = ∅ then 0 else
    sInf {L : ℕ | ∃ s : Fin N, ∀ a ∈ A, ((a : ℕ) + N - (s : ℕ)) % N < L}

/-- A dynamic dictionary on `N` cells of one `w`-bit word and `b` metadata bits: one program
per operation, which sees the operation and the current global state. -/
structure Dictionary (N w b : ℕ) where
  /-- The program run for operation `op` when the global state is `g`. -/
  prog : Op w → GlobalState w → Prog N w b

/-- Global state allowance `c_g · (⌈log₂ N⌉ + 1)²` words. -/
def globalAllowance (N cg : ℕ) : ℕ :=
  cg * (Nat.clog 2 N + 1) ^ 2

/-- The dictionary never stores more than `B` words of global state: started from at most `B`
words, every program halts with at most `B` words. -/
def Dictionary.GlobalBounded {N w b : ℕ} (D : Dictionary N w b) (B : ℕ) : Prop :=
  ∀ op g, g.length ≤ B → (D.prog op g).GlobalBounded B

/-- Run a list of operations from memory `M` and global state `g`: the answer and the scan
cost of each operation, in order. -/
noncomputable def Dictionary.runFrom {N w b : ℕ} (D : Dictionary N w b) (ω : Omega w) :
    Memory N w b → GlobalState w → List (Op w) → List (Answer w × ℕ)
  | _, _, [] => []
  | M, g, op :: ops =>
      let o := (D.prog op g).exec ω M
      (o.ans, cyclicSpan N o.touched) :: D.runFrom ω o.mem o.glob ops

/-- Run `σ` from the all-zero memory and the empty global state. -/
noncomputable def Dictionary.run {N w b : ℕ} (D : Dictionary N w b) (ω : Omega w)
    (σ : List (Op w)) : List (Answer w × ℕ) :=
  D.runFrom ω (initialMemory N w b) [] σ

/-- The total scan cost of `σ`. -/
noncomputable def Dictionary.totalCost {N w b : ℕ} (D : Dictionary N w b) (σ : List (Op w))
    (ω : Omega w) : ℕ :=
  ((D.run ω σ).map Prod.snd).sum

/-- The live items, in insertion order. -/
abbrev LiveSet (w : ℕ) : Type := List (Key w × Value w)

/-- The value stored under `k`, if any. -/
def LiveSet.lookup {w : ℕ} (S : LiveSet w) (k : Key w) : Option (Value w) :=
  (S.find? (fun p => decide (p.1 = k))).map Prod.snd

/-- The live volume `Σ_x |x|`. -/
def LiveSet.volume {w : ℕ} (S : LiveSet w) : ℕ :=
  (S.map (fun p => itemLength p.1 p.2)).sum

/-- The effect of one operation on the live set. -/
def LiveSet.step {w : ℕ} : LiveSet w → Op w → LiveSet w
  | S, .insert k v => S ++ [(k, v)]
  | S, .delete k => S.filter (fun p => decide (p.1 ≠ k))
  | S, .query _ => S

/-- The live set before operation `i` of `σ` (after its first `i` operations). -/
def liveBefore {w : ℕ} (σ : List (Op w)) (i : ℕ) : LiveSet w :=
  (σ.take i).foldl LiveSet.step []

/-- Insertions are of absent keys, deletions of present keys, queries of any key. -/
def OpAdmissible {w : ℕ} (S : LiveSet w) : Op w → Prop
  | .insert k _ => S.lookup k = none
  | .delete k => (S.lookup k).isSome
  | .query _ => True

/-- `σ` is valid for `N` cells and slack `ε`: every operation is admissible and the live volume
after every operation is at most `(1 - ε) N`. -/
def Valid {w : ℕ} (N : ℕ) (ε : ℝ) (σ : List (Op w)) : Prop :=
  ∀ i (h : i < σ.length), OpAdmissible (liveBefore σ i) σ[i] ∧
    ((liveBefore σ (i + 1)).volume : ℝ) ≤ (1 - ε) * N

/-- Every query of the run answered correctly: `Found v` for the live value `v` of its key,
`Not Found` if the key is not live. -/
def Dictionary.Correct {N w b : ℕ} (D : Dictionary N w b) (σ : List (Op w)) (ω : Omega w) :
    Prop :=
  ∀ i (h : i < σ.length) (k : Key w), σ[i] = .query k →
    ((D.run ω σ)[i]?).map Prod.fst = some ((liveBefore σ i).lookup k)

/-- `log s = max {1, log₂ s}`. -/
noncomputable def logC (s : ℕ) : ℝ :=
  max 1 (Real.logb 2 s)

/-- The cost bound of Theorem 1.4 for one operation, given the live set before it. -/
noncomputable def budget {w : ℕ} (ε δ : ℝ) (S : LiveSet w) : Op w → ℝ
  | .query k =>
      match S.lookup k with
      | some v => (itemLength k v : ℝ) / ε
      | none => 1 / ε
  | .insert k v => (itemLength k v : ℝ) * logC (itemLength k v) ^ (1 + δ) / ε
  | .delete k =>
      match S.lookup k with
      | some v => (itemLength k v : ℝ) * logC (itemLength k v) ^ (1 + δ) / ε
      | none => 0

/-- `Σ_{op ∈ σ} b(op)`. -/
noncomputable def totalBudget {w : ℕ} (ε δ : ℝ) (σ : List (Op w)) : ℝ :=
  ∑ i : Fin σ.length, budget ε δ (liveBefore σ i) σ[i]

end CatalanHashing.Dynamic


