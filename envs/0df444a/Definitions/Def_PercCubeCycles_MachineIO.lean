-- Prove2me | Definitions.Def_PercCubeCycles_MachineIO
-- name    : PercCubeCycles_MachineIO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:32:55.072485+00:00
-- url     : https://prove2.me/theorems/5375c83a-fa22-4be4-b05a-7f7cb6f96141
-- title:
--   Word-RAM input and output for the algorithmic clauses
-- statement:
--   The time clauses of the paper name no machine. They are read on the published randomized word RAM, where every instruction costs one step.
--
--   A program must work for every word width $w$ with $w\ge b(\lfloor\log_2 x\rfloor+1)$, where $b$ is chosen with the program and $x$ is the input length plus the largest input number. Outputs are read unsigned from cells $0,1,2,\dots$. A cycle is output as its length followed by its vertices in cyclic order.
--
--   The percolated hypercube is given by $d$ followed by one bit per position $i2^d+c$, the bit of edge $(s,i)$ with $s$ numbered $c$. A graph on $\{0,\dots,n-1\}$ is given by its number of edges followed by the increasing list of its edges.
--
--   These conventions fix what the running-time bounds mean.
--
--   **Formalization Note** An edge list spends no word on an isolated vertex, so an instance with many isolated vertices can still be read in $O(|E|^2)$ steps.
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), Theorem 1, p.3; Theorem 3, p.4; Proposition 3.1, p.9 (the paper names no machine)

import Mathlib
import Definitions.Def_RandomGames_BRD_Percolation
import Definitions.Def_MatroidSensOracle_WordRAM

set_option autoImplicit false

namespace PercCubeCycles

open RandomGames.BRD

/-!
# Input and output of the algorithms on the word RAM

Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…) names no machine for its time clauses (Theorems 1, 3, Proposition 3.1). They are read on the
published randomized word RAM `MatroidSensOracle` (`Instr`, `exec`, `loadWords`, `coinLaw`): every
instruction is charged one step.

**Formalization Note.**
* **Word width.** A program must work for every width `w` above `b · (⌊log₂ x⌋ + 1)`, where `b` is a
  constant chosen with the program and `x` is the input length plus the largest input number
  (the convention of the published word RAM).
* **Output.** Cells `0, 1, 2, …` of the final memory, read unsigned.
* **Cycle.** A cycle is the list `v₀, …, v_{L-1}` of its distinct vertices, `L ≥ 3`, with `vᵢ ~ vᵢ₊₁`
  and `v_{L-1} ~ v₀`.
* **Graphs on `Fin n`** are given by the edge list in increasing order, each edge `u < v` as two
  words, preceded by the number of edges. An edge list costs no word for an isolated vertex.
-/

/-- The largest absolute value of a word of `ws`. -/
def maxWord (ws : List ℤ) : ℕ := (ws.map Int.natAbs).foldr max 0

/-- The admissible word widths on input `ws` for the constant `b`. -/
def WidthOK (b : ℕ) (ws : List ℤ) (w : ℕ) : Prop :=
  b * (Nat.log 2 (ws.length + maxWord ws) + 1) ≤ w

/-- The final memory holds the words `out` in cells `0, 1, 2, …`, read unsigned. -/
def OutputsWords {w : ℕ} (mem : ℤ → BitVec w) (out : List ℕ) : Prop :=
  ∀ (i : ℕ) (hi : i < out.length), (mem i).toNat = out[i]

/-- `c` lists the vertices of a cycle of `G`, in cyclic order. -/
def IsCycleList {V : Type*} (G : SimpleGraph V) (c : List V) : Prop :=
  3 ≤ c.length ∧ c.Nodup ∧ (c ++ c.take 1).IsChain G.Adj

/-- The number of the vertex `s` of `Q^d`: `∑ i, sᵢ 2^i`. -/
def profileCode {d : ℕ} (s : Profile d) : ℕ := ∑ i, if s i then 2 ^ (i : ℕ) else 0

open scoped Classical in
/-- The input for Theorem 1: cell `0` holds `d`; the cell at position `1 + i·2^d + c` holds `1` if
the edge `(s, i)` with `profileCode s = c` and `s i = false` is open, and `0` otherwise. -/
noncomputable def cubeInput {d : ℕ} (ω : Edge d → Bool) : List ℤ :=
  (d : ℤ) :: (List.finRange d).flatMap fun i => (List.range (2 ^ d)).map fun c =>
    if ∃ e : Edge d, e.1.2 = i ∧ profileCode e.1.1 = c ∧ ω e = true then 1 else 0

open scoped Classical in
/-- The edge list of `G`: the number of edges, then the edges `u < v` in increasing order. -/
noncomputable def edgeWords {n : ℕ} (G : SimpleGraph (Fin n)) : List ℤ :=
  (G.edgeSet.ncard : ℤ) :: (List.finRange n).flatMap fun u =>
    ((List.finRange n).filter fun v => u < v ∧ G.Adj u v).flatMap fun v => [((u : ℕ) : ℤ), ((v : ℕ) : ℤ)]

open scoped Classical in
/-- The vertices of a set: their number, then the vertices in increasing order. -/
noncomputable def setWords {n : ℕ} (A : Set (Fin n)) : List ℤ :=
  let l := (List.finRange n).filter fun v => v ∈ A
  (l.length : ℤ) :: l.map fun v => ((v : ℕ) : ℤ)

end PercCubeCycles


