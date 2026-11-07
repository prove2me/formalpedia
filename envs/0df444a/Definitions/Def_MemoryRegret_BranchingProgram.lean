-- Prove2me | Definitions.Def_MemoryRegret_BranchingProgram
-- name    : MemoryRegret_BranchingProgram
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:13.747752+00:00
-- url     : https://prove2.me/theorems/15346293-2dda-423e-a644-c9b0a896c5c7
-- title:
--   Layered branching programs, and randomized ones
-- statement:
--   A **branching program of length $\tau$** over an alphabet $A$ has vertices $(i,v)$ in layers $i=0,\dots,\tau$; a start vertex in layer 0; for each non-leaf $(i,v)$ one outgoing edge per letter of $A$ into layer $i+1$; and an output at each leaf. All vertices of the last layer are leaves and there may be additional leaves. A stream $a_1,\dots,a_\tau$ defines the **computation path**, which starts at the start vertex and at step $t$ follows the edge labeled $a_t$ until it reaches a leaf; the program outputs according to that leaf.
--
--   A **randomized** branching program is a distribution on seeds together with one deterministic program, of the same width, per seed. Its **advantage** between stream laws $D_0$ and $D_1$ is $|\Pr_{D_0}[\text{YES}]-\Pr_{D_1}[\text{YES}]|$, with seed and stream independent.
--
--   Branching programs are the model of memory-bounded streaming computation: a program of width $d$ has $\log_2 d$ bits of memory.
--
--   **Formalization Note** One finite state type $S$ labels the vertices of every layer, so the width is $|S|$ and a width-$d$ program is one with $S=\mathrm{Fin}\,d$. Layer 0's only relevant vertex is `start`.
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), §2, p.8; randomized programs, §3.2, p.12

import Mathlib
import Definitions.Def_MemoryRegret_IsProbVec

namespace MemoryRegret

/-- **Layered branching programs (p.8).**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
§2, p.8: "A branching program of length τ and width d is a directed (multi) graph with vertices
arranged in τ + 1 layers containing at most d vertices each. In the first layer, that we think
of as layer 0, there is only one vertex, called the start vertex. A vertex of outdegree 0 is
called a leaf. All vertices in the last layer are leaves (but there may be additional leaves).
If each element of the stream is from the set A, then every non-leaf vertex in the program has
|A| outgoing edges, labeled by elements a ∈ A, with exactly one edge labeled by each such a, and
all these edges going into vertices in the next layer. … The program outputs based on the leaf v
reached by the computation-path."

A `BranchingProgram S A len` has the vertices `(i, v)` for layers `i = 0, …, len` and `v : S`:
the start vertex `(0, start)`; the edge labeled `a` out of a non-leaf `(i, v)`, `i < len`, goes
to `(i+1, step i v a)`; `(i, v)` is a leaf when `i = len` or `isLeaf i v`; the output at a leaf
`(i, v)` is `out i v` (`true` = YES).

**Formalization Note.** One finite state type `S` labels the vertices of every layer, so the
width is `Fintype.card S` (a width-`d` program is one with `S = Fin d`; vertices that are never
reached are harmless). Layer 0's only relevant vertex is `start`. Layer indices are natural
numbers; only `i ≤ len` matters. The output is `Bool`. -/
structure BranchingProgram (S A : Type) (len : ℕ) where
  /-- the start vertex in layer 0 -/
  start : S
  /-- `step i v a`: the end in layer `i + 1` of the edge labeled `a` out of `(i, v)` -/
  step : ℕ → S → A → S
  /-- `isLeaf i v`: the vertex `(i, v)` has outdegree 0 (layer `len` is always a leaf layer) -/
  isLeaf : ℕ → S → Bool
  /-- the output at a leaf -/
  out : ℕ → S → Bool

namespace BranchingProgram

variable {S A : Type} {len : ℕ}

/-- The vertex in layer `i` on the path that follows the edges labeled `a_0, a_1, …` (ignoring
leaves; see `Reaches`). -/
def stateAt (B : BranchingProgram S A len) (a : Fin len → A) : ℕ → S
  | 0 => B.start
  | i + 1 => if h : i < len then B.step i (B.stateAt a i) (a ⟨i, h⟩) else B.stateAt a i

/-- `(i, v)` is a leaf: the last layer, or a vertex of outdegree 0. -/
def IsLeafVertex (B : BranchingProgram S A len) (i : ℕ) (v : S) : Prop :=
  len ≤ i ∨ B.isLeaf i v = true

/-- The computation path of the stream `a` reaches the vertex `(i, v)`: it is at `v` in layer
`i` and has met no leaf before layer `i`. -/
def Reaches (B : BranchingProgram S A len) (a : Fin len → A) (i : ℕ) (v : S) : Prop :=
  i ≤ len ∧ B.stateAt a i = v ∧ ∀ j < i, ¬ B.IsLeafVertex j (B.stateAt a j)

open Classical in
/-- The layer of the leaf reached by the computation path. -/
noncomputable def exitLayer (B : BranchingProgram S A len) (a : Fin len → A) : ℕ :=
  Nat.find (⟨len, Or.inl le_rfl⟩ : ∃ i, B.IsLeafVertex i (B.stateAt a i))

/-- The output of the program on the stream `a`: the label of the leaf it reaches. -/
noncomputable def output (B : BranchingProgram S A len) (a : Fin len → A) : Bool :=
  B.out (B.exitLayer a) (B.stateAt a (B.exitLayer a))

/-- `Pr_{a ∼ D}[B(a) = b]` for a law `D` on streams. -/
noncomputable def outProb [Fintype A] (D : (Fin len → A) → ℝ) (B : BranchingProgram S A len)
    (b : Bool) : ℝ :=
  ∑ a, D a * if B.output a = b then 1 else 0

end BranchingProgram

/-- A randomized branching program: a probability vector `law` on a finite seed type `Ω` and a
deterministic program `prog ω` of the same state type (hence width) for every seed. -/
structure RandBP (S A : Type) (len : ℕ) (Ω : Type) [Fintype Ω] where
  law : Ω → ℝ
  law_prob : IsProbVec law
  prog : Ω → BranchingProgram S A len

namespace RandBP

variable {S A Ω : Type} [Fintype Ω] {len : ℕ}

/-- `Pr[P(a) = b]` when `a ∼ D` and the seed `ω ∼ law` are independent. -/
noncomputable def outProb [Fintype A] (D : (Fin len → A) → ℝ) (P : RandBP S A len Ω)
    (b : Bool) : ℝ :=
  ∑ ω, P.law ω * (P.prog ω).outProb D b

/-- The distinguishing advantage `|Pr_{D_0}[YES] − Pr_{D_1}[YES]|`. -/
noncomputable def advantage [Fintype A] (D₀ D₁ : (Fin len → A) → ℝ) (P : RandBP S A len Ω) : ℝ :=
  |P.outProb D₀ true - P.outProb D₁ true|

end RandBP

end MemoryRegret


