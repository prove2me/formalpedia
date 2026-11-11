-- Prove2me | Definitions.Def_IncApproxVC_Oblivious_Online
-- name    : IncApproxVC_Oblivious_Online
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:42:35.391781+00:00
-- url     : https://prove2.me/theorems/5bfa32cd-56b7-406c-8158-b0bfa7e8c55d
-- title:
--   Incremental graph instances fed online to the randomized real RAM: input layout, outputs, maintained sets
-- statement:
--   The paper's algorithms are programs of a single machine, the published randomized exact real RAM `PNormReg` (rational literals, $+,-,\times,\div$, comparisons, integer pointers and integer memory, a pointer-to-real cast, $\sqrt{\cdot}$, $|r|^s$, fair coins, `halt`; one unit of work per executed instruction; one finite program for every input size). A **deterministic** algorithm is a program without a `coin` instruction.
--
--   An **incremental instance** on $\{0,\dots,n-1\}$ is an initial graph $G_0$ and a list of insertions $e_1,\dots,e_\ell$; $G_i$ is the graph after the first $i$ insertions. The instance is **valid** if $G_0$ has no loop and each $e_i=(u,v)$ has $u\ne v$ and is not an edge of $G_{i-1}$, so every $G_i$ is simple. The number of edges after all insertions is $m=|E(G_0)|+\ell$.
--
--   **Input.** The initial graph is written as adjacency lists: a header of parameters (tag $0$, $n$, and the theorem's parameters), then for each vertex the index of its block, then the blocks, the block of $v$ being $\deg^+(v)$, the out-neighbours of $v$ in increasing order, $\deg^-(v)$, the in-neighbours of $v$ in increasing order. An insertion of $(u,v)$ is the three words $1,u,v$; a set-output query is the word $2$. Integer word $i$ goes to integer cell $-1-i$ and real word $i$ to real cell $-2-i$.
--
--   **Online feeding.** The operations are given one at a time. Each is written into the memory of the state left by the previous operation (program counter, registers and pointers reset, memories, coin-tape cursor and work counter kept), and the program runs until it halts. A run never sees a later operation: an adversary that fixes the sequence in advance is oblivious, and a deterministic program against every sequence covers a randomness-adaptive adversary. Writing the input is free; the work counter totals the executed instructions over all operations.
--
--   **Outputs.** The answer to an operation is real cell $-1$ of the state after its run (a number, or $1$ for YES and $0$ for NO). A query that outputs $k$ sets writes their sizes $c_0,\dots,c_{k-1}$ to real cells $-2,\dots,-1-k$ and then their members, one vertex index per cell, consecutively downward from cell $-2-k$ (`SetsWritten`). A set that an algorithm maintains is read from integer cells $0,\dots,n-1$: $v$ belongs to it iff integer cell $v$ holds $1$ (`maintainedSet`).
--
--   **Formalization Note.** Each operation runs for a fixed fuel; a halted state stutters at no cost, so fuel beyond the halting time gives the same state. Theorems take the fuel equal to their time bound and assert that every run halted. The pattern follows the published `IncrementalER_runOps`, which is typed to its own operations and is not imported.
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 1 (Theorem 1.1, 'randomized incremental algorithm'), p. 5 (oblivious adversary), pp. 9, 19, 22 (Theorems 3.12, 6.1, 6.8: deterministic algorithms, adjacency-list input, optional set output)

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_IncApproxVC_Oblivious_Digraph

/-!
# Incremental graph instances fed online to one program of the randomized real RAM

Adena, Henzinger, Rutschmann, *Incremental Approximate Vertex Connectivity via Almost-Linear Time
Local Cut Algorithms*, STOC 2027 submission (manuscript sha256 d6baac6b…). The paper says "there is
a randomized incremental algorithm" (Theorem 1.1, p. 1) and "there is a deterministic incremental
algorithm" (Theorems 3.12, 6.1, 6.8) and names no machine. The machine is the published randomized
exact real RAM `PNormReg` (rational literals, `+ − × ÷`, `√`, `|r|^s`, integer pointers and integer
memory, a pointer-to-real cast, fair coins, `halt`, one unit of work per executed instruction; one
finite program for every input size). A deterministic algorithm is a program with no `coin`
instruction (`CoinFree`).

**Instances.** An incremental instance on the vertex set `Fin n` is an initial graph `G₀` and a list
of edge insertions. `graphAfter I i` is `G_i`, the graph after the first `i` insertions.
The instance is valid when `G₀` has no loops and every insertion `(u, v)` has `u ≠ v` and is not an
edge of the current graph, so every `G_i` is simple. `finalEdgeCount I = |E(G₀)| + ℓ` is the number
of edges after all insertions.

**Input layout.** An operation consists of integer words and real words. Integer word `i` is written
to integer cell `−1 − i` and real word `i` to real cell `−2 − i`; no other cell changes.
* The initial graph is given as adjacency lists (`adjacencyWords G h`, for a header of `h` words):
  first, for each vertex `v = 0, …, n − 1`, the index of the first word of `v`'s block; then the
  blocks, the block of `v` being `deg⁺(v)`, the out-neighbours of `v` in increasing order,
  `deg⁻(v)`, the in-neighbours of `v` in increasing order. The in-lists are the adjacency lists of
  the reversed graph.
* An initialization operation is `header ++ adjacencyWords G₀ header.length`, with the header
  fixed by each theorem (its first word is the tag `0`); an insertion of `(u, v)` is `[1, u, v]`;
  a set-output query is `[2]`.

**Online feeding (`runOps`).** Each operation is written into the memory of the state left by the
previous one; the program counter, the real registers and the pointers are reset to `0` and the
halted flag is cleared; both memories, the coin-tape cursor and the work counter are kept. The
program is then run for `fuel` steps. A run never sees a later operation. Writing the input costs
nothing, so `work` counts executed instructions only, summed over all operations.

**Outputs.** The answer to an operation is read from real cell `−1` of the state after its run
(a number, or `1` for YES and `0` for NO). A query that outputs `k` sets writes their sizes
`c₀, …, c_{k−1}` to real cells `−2, …, −1 − k` and then the members of set `0`, set `1`, …, one
vertex index per cell, at the consecutive cells `−2 − k, −3 − k, …` (`SetsWritten`). A set that an
algorithm maintains is read from integer cells `0, …, n − 1` (`v` belongs to it iff integer cell
`v` holds `1`: `maintainedSet`).

**Fuel.** A halted state stutters at no cost, so any fuel beyond the halting time gives the same
state; the theorems take the fuel equal to their time bound and assert that every run halted.
-/

namespace IncApproxVC.Oblivious


/-- An incremental instance on `Fin n`: an initial graph and a list of edge insertions. -/
structure IncInstance (n : ℕ) where
  /-- The initial graph `G₀`. -/
  G₀ : Digraph (Fin n)
  /-- The insertions `e₁, …, e_ℓ`, in order. -/
  ins : List (Fin n × Fin n)

namespace IncInstance

variable {n : ℕ}

/-- `G_i`: the initial graph plus the first `i` insertions. -/
def graphAfter (I : IncInstance n) (i : ℕ) : Digraph (Fin n) :=
  ⟨I.G₀.edges ∪ (I.ins.take i).toFinset⟩

/-- The instance keeps the graph simple: `G₀` has no loops, and each inserted edge is not a loop
and not already present. -/
def Valid (I : IncInstance n) : Prop :=
  I.G₀.Loopless ∧ ∀ i : ℕ, ∀ h : i < I.ins.length,
    (I.ins[i]'h).1 ≠ (I.ins[i]'h).2 ∧ I.ins[i]'h ∉ (I.graphAfter i).edges

/-- `m = |E(G₀)| + ℓ`, the number of edges after all insertions. -/
def finalEdgeCount (I : IncInstance n) : ℕ :=
  I.G₀.edges.card + I.ins.length

end IncInstance

/-- The vertex `v` as an integer word. -/
def vword {n : ℕ} (v : Fin n) : ℤ := ((v : ℕ) : ℤ)

/-- The out-neighbours of `v` in increasing order, as integer words. -/
def outList {n : ℕ} (G : Digraph (Fin n)) (v : Fin n) : List ℤ :=
  (((G.edges.filter (fun e => e.1 = v)).image Prod.snd).sort (· ≤ ·)).map vword

/-- The in-neighbours of `v` in increasing order, as integer words. -/
def inList {n : ℕ} (G : Digraph (Fin n)) (v : Fin n) : List ℤ :=
  (((G.edges.filter (fun e => e.2 = v)).image Prod.fst).sort (· ≤ ·)).map vword

/-- The block of `v`: `deg⁺(v)`, the out-neighbours, `deg⁻(v)`, the in-neighbours. -/
def vertexBlock {n : ℕ} (G : Digraph (Fin n)) (v : Fin n) : List ℤ :=
  (((outList G v).length : ℤ) :: outList G v) ++ (((inList G v).length : ℤ) :: inList G v)

/-- The adjacency-list words of `G` placed after a header of `h` words: the start index of each
vertex block, then the blocks of `0, 1, …, n − 1`. -/
def adjacencyWords {n : ℕ} (G : Digraph (Fin n)) (h : ℕ) : List ℤ :=
  let blocks := (List.finRange n).map (vertexBlock G)
  ((List.finRange n).map fun v =>
      (((h + n + ((blocks.take (v : ℕ)).map List.length).sum : ℕ)) : ℤ)) ++ blocks.flatten

/-- The initialization words: `header ++ adjacencyWords G₀ header.length`. -/
def initWords {n : ℕ} (header : List ℤ) (G₀ : Digraph (Fin n)) : List ℤ :=
  header ++ adjacencyWords G₀ header.length

/-- The words of an insertion `(u, v)`: `[1, u, v]`. -/
def insertWords {n : ℕ} (e : Fin n × Fin n) : List ℤ :=
  [1, vword e.1, vword e.2]

/-- The operations of a pure insertion run: the initialization (with the given header and real
words) followed by one operation per insertion. -/
def insertionOps {n : ℕ} (header : List ℤ) (reals : List ℝ) (I : IncInstance n) :
    List (List ℤ × List ℝ) :=
  (initWords header I.G₀, reals) :: I.ins.map fun e => (insertWords e, [])

/-- An operation of an incremental algorithm that answers set-output queries. -/
inductive LocalOp (n : ℕ) where
  /-- Insert the edge `(u, v)`. -/
  | insert (u v : Fin n)
  /-- Ask for the set(s) behind the current YES answer. -/
  | query

namespace LocalOp

variable {n : ℕ}

/-- The words of an operation: `[1, u, v]` for an insertion, `[2]` for a query. -/
def words : LocalOp n → List ℤ
  | .insert u v => insertWords (u, v)
  | .query => [2]

/-- The inserted edge of an operation, if any. -/
def edge? : LocalOp n → Option (Fin n × Fin n)
  | .insert u v => some (u, v)
  | .query => none

/-- The incremental instance made of `G₀` and the insertions among `ops`. -/
def toInstance (G₀ : Digraph (Fin n)) (ops : List (LocalOp n)) : IncInstance n :=
  ⟨G₀, ops.filterMap edge?⟩

/-- The graph after the first `j` operations of `ops`. -/
def graphAfterOps (G₀ : Digraph (Fin n)) (ops : List (LocalOp n)) (j : ℕ) : Digraph (Fin n) :=
  ⟨G₀.edges ∪ ((ops.take j).filterMap edge?).toFinset⟩

/-- The number of insertions among `ops`. -/
def numInsertions (ops : List (LocalOp n)) : ℕ :=
  (ops.filterMap edge?).length

end LocalOp

/-- The operations of a run with queries: the initialization (header, no real words) followed by
one operation per element of `ops`. -/
def localOps {n : ℕ} (header : List ℤ) (G₀ : Digraph (Fin n)) (ops : List (LocalOp n)) :
    List (List ℤ × List ℝ) :=
  (initWords header G₀, []) :: ops.map fun o => (o.words, [])

/-- Write an operation (integer words `ints`, real words `reals`) into the state `s` left by the
previous one: integer word `i` at integer cell `−1 − i`, real word `i` at real cell `−2 − i`, other
cells unchanged; program counter, registers and pointers reset to `0`, halted flag cleared; cursor
and work kept. -/
noncomputable def load (s : PNormReg.State) (ints : List ℤ) (reals : List ℝ) : PNormReg.State :=
  { core :=
      { pc := 0
        regs := fun _ => 0
        ptrs := fun _ => 0
        mem := fun z =>
          if -((reals.length : ℤ) + 1) ≤ z ∧ z ≤ -2 then reals.getD (-2 - z).toNat 0
          else s.core.mem z }
    integerMemory := fun z =>
      if -(ints.length : ℤ) ≤ z ∧ z ≤ -1 then ints.getD (-1 - z).toNat 0
      else s.integerMemory z
    cursor := s.cursor
    halted := false
    work := s.work }

/-- The state after the first `k` operations of `ops`, each run for `fuel` steps on the coin tape
`ω`, starting from the all-zero state. -/
noncomputable def runOps (P : PNormReg.Program) (ω : ℕ → Bool) (fuel : ℕ)
    (ops : List (List ℤ × List ℝ)) (k : ℕ) : PNormReg.State :=
  (ops.take k).foldl (fun s op => PNormReg.run P (load s op.1 op.2) ω fuel)
    (PNormReg.initState [] [])

/-- The answer to operation `j` (`0`-indexed, the initialization is operation `0`): real cell
`−1` after its run. -/
noncomputable def answer (P : PNormReg.Program) (ω : ℕ → Bool) (fuel : ℕ)
    (ops : List (List ℤ × List ℝ)) (j : ℕ) : ℝ :=
  (runOps P ω fuel ops (j + 1)).core.mem (-1)

/-- The work spent on operation `j` alone. -/
noncomputable def opWork (P : PNormReg.Program) (ω : ℕ → Bool) (fuel : ℕ)
    (ops : List (List ℤ × List ℝ)) (j : ℕ) : ℕ :=
  (runOps P ω fuel ops (j + 1)).work - (runOps P ω fuel ops j).work

/-- A deterministic program: no `coin` instruction. -/
def CoinFree (P : PNormReg.Program) : Prop :=
  ∀ d : ℕ, PNormReg.Instr.coin d ∉ P

/-- The coin tape on which deterministic programs are run (they never read it). -/
def noCoins : ℕ → Bool := fun _ => false

/-- The state `s` holds `k` output sets `sets 0, …, sets (k − 1)`: their sizes `c i` at real cells
`−2 − i`, and the members of set `i`, one vertex index per cell, at the `c i` consecutive cells
starting at `−2 − k − (c 0 + ⋯ + c (i − 1))` and going down. -/
def SetsWritten {n : ℕ} (s : PNormReg.State) (k : ℕ) (sets : Fin k → Finset (Fin n)) : Prop :=
  ∃ c : Fin k → ℕ, (∀ i : Fin k, s.core.mem (-2 - (i : ℤ)) = (c i : ℝ)) ∧
    ∀ i : Fin k,
      (∀ j : ℕ, j < c i → ∃ v : Fin n,
        s.core.mem (-2 - (k : ℤ) - ((∑ i' ∈ Finset.univ.filter (· < i), c i' : ℕ) : ℤ) - j) =
          ((v : ℕ) : ℝ)) ∧
      ∀ v : Fin n, v ∈ sets i ↔ ∃ j : ℕ, j < c i ∧
        s.core.mem (-2 - (k : ℤ) - ((∑ i' ∈ Finset.univ.filter (· < i), c i' : ℕ) : ℤ) - j) =
          ((v : ℕ) : ℝ)

/-- The set maintained in the state `s`: the vertices `v` whose integer cell `v` holds `1`. -/
def maintainedSet {n : ℕ} (s : PNormReg.State) : Finset (Fin n) :=
  Finset.univ.filter fun v : Fin n => s.integerMemory ((v : ℕ) : ℤ) = 1

end IncApproxVC.Oblivious


