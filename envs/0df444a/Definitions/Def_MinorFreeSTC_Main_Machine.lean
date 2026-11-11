-- Prove2me | Definitions.Def_MinorFreeSTC_Main_Machine
-- name    : MinorFreeSTC_Main_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:18:53.71487+00:00
-- url     : https://prove2.me/theorems/9f51b83a-1a79-4c5d-99f3-99c53cabc1b1
-- title:
--   The randomized real RAM with power-of-γ rounding and oracle calls; coin-tape measure; input and output layouts
-- statement:
--   The paper's algorithmic claims ("computable in polynomial time", "with high probability") are read on the following machine.
--
--   **Instructions.** The published unit-cost real RAM `SmaleNinth.RAMInstr` (real registers and a real memory indexed by integer pointers; exact $+,-,\times,\div$ with $x/0=0$; literals; pointer set, copy, increment, decrement and comparison; conditional jumps on $r\le 0$; `accept`/`reject` halt), extended by exactly: `coin d`, which writes the next bit of a fair coin tape ($1$ or $0$) to $r_d$; `roundUpPow d i j`, which writes $r_j^{\lceil\log_{r_j}r_i\rceil}$ if $r_i>0$ and $r_j>1$ and $0$ otherwise (the paper's "rounding positive values up to powers of $\gamma$", §9.2); and, only for the black-box statements (Theorem 9, Lemma 24), `oracle d q`, which writes the oracle's answer list for the query $r_d$ into memory from address $p_q$ on and its length into $r_d$. There is no floor, exp, log, square root, real-to-pointer cast or real-valued random draw. Each executed instruction is one step. A program is **admissible** if its literals are rational.
--
--   **Runs.** The input list occupies memory cells $0,1,\dots$; all registers and pointers start at $0$. The output of a halted run is the memory block of length $p_1$ starting at $p_2$. The coin tape $\omega\in\{0,1\}^{\mathbb N}$ carries the product of fair Bernoulli laws. A program **computes $\mathrm{Good}$ in $T$ steps with failure at most $\delta$** if every run halts within $T$ steps and the set of tapes on which it does not halt with an output satisfying $\mathrm{Good}$ has measure at most $\delta$; it does so **surely** if that set is empty.
--
--   **Input layout.** An *encoding* of $G$ is a numbering $V\cong\{0,\dots,n-1\}$ and a list of the $m$ edges, each once, in any order and orientation. The graph occupies the cells $[n,m,a_1,b_1,w_1,\dots,a_m,b_m,w_m]$; parameters follow; a partition given as input is a vertex labelling (one cell per vertex, in vertex order); a hierarchy is $[\lambda,\kappa]$ followed by $\kappa+1$ blocks giving, for each vertex, the number of the center of its cluster.
--
--   **Output layouts.** A partition: a vertex labelling. A family of partial partitions (also every oracle answer): $[k]$ then $k$ labellings, a negative label meaning "in no cluster". A family of spanning trees: $[k]$ then, per tree, the positions in the edge list of its $n-1$ edges. Centered partitions: per vertex, the number of its cluster's center. Hierarchy families: $[m]$ then $m$ hierarchy layouts. A cop decomposition: per vertex three cells (its supernode's root; the parent supernode's root if it is a root, $-1$ otherwise or at the top; its skeleton parent, $-1$ at the root, $-2$ outside the skeleton).
--
--   **Formalization Note.** Probability statements bound the (outer) measure of the failure set; no measurability is assumed.
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), p. 13 (with high probability), §9.2 p. 53 (assumed operations)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_RamseyLST_Main_RamseySpanningTree
import Definitions.Def_MinorFreeSTC_Main_Graphs
import Definitions.Def_MinorFreeSTC_Main_Covers
import Definitions.Def_MinorFreeSTC_Main_Structures

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace MinorFreeSTC.Main

open ARTreeCover

/-!
# The machine: a randomized real RAM with power-of-`γ` rounding, and the input/output layouts

Filtser, Fletcher, Hershkowitz, Milenković, *(1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free
Graphs with Size O(log log n)*, STOC 2027 submission (manuscript sha256 f475e254…), p. 13 (PDF 15,
"with high probability"), §9.2, p. 53 (PDF 55: "basic arithmetic operations, comparisons, and
rounding positive values up to powers of γ take polynomial time"). The paper names no machine;
this model is a reading of those sentences.

* The core is the published `SmaleNinth.RAMInstr` real pointer machine (exact `+ − × ÷` with
  `x/0 = 0`, real literals, indirect real memory `ℤ → ℝ` through integer pointers, pointer
  set/copy/increment/decrement, jumps on `r ≤ 0` and `p ≤ p'`, `accept`/`reject` = halt).
* Added instructions: `coin d` writes the next bit (`0` or `1`) of a fair coin tape to `r[d]`;
  `roundUpPow d i j` writes `r[j]^⌈log_{r[j]} r[i]⌉` to `r[d]` if `r[i] > 0` and `r[j] > 1`, else
  `0`; `oracle d q` (only in the black-box statements, Theorem 9 and Lemma 24) writes the oracle's
  answer to the query `r[d]` into memory from address `p[q]` on and its length into `r[d]`.
  No floor, `exp`, `log`, square root, real-to-pointer cast or real-valued draws.
* Each executed instruction is one step. Real literals are rational (`Admissible`).
* Input: memory cells `0, 1, …` hold the input list. Output: on halting, the memory block of
  length `p[1]` starting at address `p[2]`.
* The coin tape `ℕ → Bool` carries the product of fair Bernoulli laws (`coinMeasure`).
* A graph is given by an `Encoding`: an enumeration `V ≃ Fin n` and a duplicate-free list of its
  edges in any order and orientation; it is laid out as `[n, m, a₁, b₁, w₁, …, aₘ, bₘ, wₘ]`.
-/

/-- An instruction. -/
inductive Instr where
  /-- A `SmaleNinth` real-RAM instruction. -/
  | core (instruction : SmaleNinth.RAMInstr)
  /-- `r[d] :=` the next coin (`1` for heads, `0` for tails). -/
  | coin (d : ℕ)
  /-- `r[d] := r[j]^⌈log_{r[j]} r[i]⌉` if `r[i] > 0` and `r[j] > 1`, else `0`. -/
  | roundUpPow (d i j : ℕ)
  /-- Oracle call: query `r[d]`; the answer list is written to `M[p[q]], M[p[q] + 1], …` and its
  length to `r[d]`. -/
  | oracle (d q : ℕ)

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- The program's real literals are rational. -/
def Admissible (P : Program) : Prop :=
  ∀ ins ∈ P, ∀ (d : ℕ) (c : ℝ), ins = .core (.const d c) → ∃ q : ℚ, c = (q : ℝ)

/-- The program makes no oracle call. -/
def NoOracle (P : Program) : Prop := ∀ ins ∈ P, ∀ d q : ℕ, ins ≠ .oracle d q

/-- The core table of `P` (non-core instructions are placeholders, dispatched by `step`). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun ins => match ins with
    | .core i => i
    | _ => .const 0 0

/-- A machine state: the core configuration and the number of coins read. -/
structure State where
  /-- Program counter, registers, pointers and memory. -/
  cfg : SmaleNinth.RAMConfig
  /-- The position of the next unread coin. -/
  cursor : ℕ

/-- The coin tape. -/
abbrev Tape := ℕ → Bool

/-- An oracle: an answer list for every real query. -/
abbrev Oracle := ℝ → List ℝ

/-- The power-of-`γ` rounding `γ^⌈log_γ x⌉` for `x > 0`, `γ > 1`; `0` otherwise. -/
noncomputable def roundUpPowVal (x γ : ℝ) : ℝ :=
  if 0 < x ∧ 1 < γ then γ ^ ⌈Real.logb γ x⌉ else 0

/-- One step of `P` with coin tape `ω` and oracle `O`. A state at `accept`/`reject` is halted and
stutters (the core step leaves it unchanged); a program counter outside `P` is stuck. -/
noncomputable def step (P : Program) (ω : Tape) (O : Oracle) (s : State) : State :=
  match P[s.cfg.pc]? with
  | none => s
  | some (.core _) => ⟨SmaleNinth.RAMStep (coreProgram P) s.cfg, s.cursor⟩
  | some (.coin d) =>
      ⟨⟨s.cfg.pc + 1, Function.update s.cfg.regs d (if ω s.cursor then 1 else 0), s.cfg.ptrs,
        s.cfg.mem⟩, s.cursor + 1⟩
  | some (.roundUpPow d i j) =>
      ⟨⟨s.cfg.pc + 1, Function.update s.cfg.regs d (roundUpPowVal (s.cfg.regs i) (s.cfg.regs j)),
        s.cfg.ptrs, s.cfg.mem⟩, s.cursor⟩
  | some (.oracle d q) =>
      ⟨⟨s.cfg.pc + 1, Function.update s.cfg.regs d ((O (s.cfg.regs d)).length : ℝ), s.cfg.ptrs,
        fun z => if s.cfg.ptrs q ≤ z ∧ z < s.cfg.ptrs q + (O (s.cfg.regs d)).length then
          (O (s.cfg.regs d)).getD (z - s.cfg.ptrs q).toNat 0 else s.cfg.mem z⟩, s.cursor⟩

/-- The input memory: the list `l` in cells `0, 1, …`, `0` elsewhere. -/
noncomputable def inputMem (l : List ℝ) : ℤ → ℝ := fun z => if 0 ≤ z then l.getD z.toNat 0 else 0

/-- The state after `t` steps on input `l` (program counter, registers and pointers `0`). -/
noncomputable def run (P : Program) (ω : Tape) (O : Oracle) (l : List ℝ) (t : ℕ) : State :=
  (step P ω O)^[t] ⟨⟨0, fun _ => 0, fun _ => 0, inputMem l⟩, 0⟩

/-- The state is halted: the program counter is at `accept` or `reject`. -/
def Halted (P : Program) (s : State) : Prop :=
  P[s.cfg.pc]? = some (.core .accept) ∨ P[s.cfg.pc]? = some (.core .reject)

/-- The output of a state: the memory block of length `p[1]` from address `p[2]`. -/
noncomputable def output (s : State) : List ℝ :=
  (List.range (s.cfg.ptrs 1).toNat).map fun j => s.cfg.mem (s.cfg.ptrs 2 + (j : ℤ))

/-- The fair-coin tape law: the product of uniform laws on `Bool`. -/
noncomputable def coinMeasure : Measure Tape :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure

/-- Every run of `P` on input `l` with oracle `O` (every coin tape) halts within `T` steps. -/
def HaltsWithin (P : Program) (O : Oracle) (l : List ℝ) (T : ℝ) : Prop :=
  ∀ ω : Tape, ∃ t : ℕ, (t : ℝ) ≤ T ∧ Halted P (run P ω O l t)

/-- The run on tape `ω` halts with an output satisfying `Good`. -/
def Succeeds (P : Program) (O : Oracle) (l : List ℝ) (Good : List ℝ → Prop) (ω : Tape) : Prop :=
  ∃ t : ℕ, Halted P (run P ω O l t) ∧ Good (output (run P ω O l t))

/-- Randomized computation with failure probability at most `δ` in at most `T` steps: every run
halts within `T` steps, and the coin tapes on which the output is not `Good` have measure at most
`δ`. -/
def ComputesWHP (P : Program) (O : Oracle) (l : List ℝ) (Good : List ℝ → Prop) (T δ : ℝ) :
    Prop :=
  HaltsWithin P O l T ∧ coinMeasure {ω | ¬ Succeeds P O l Good ω} ≤ ENNReal.ofReal δ

/-- Computation in at most `T` steps with no failure: every run halts within `T` steps with a
`Good` output. -/
def ComputesSurely (P : Program) (O : Oracle) (l : List ℝ) (Good : List ℝ → Prop) (T : ℝ) :
    Prop :=
  HaltsWithin P O l T ∧ ∀ ω : Tape, Succeeds P O l Good ω

/-- The empty oracle (for programs without oracle calls). -/
def noOracle : Oracle := fun _ => []

/-! ### Input layout -/

variable {V : Type}

/-- An encoding of `G`: an enumeration `idx : V ≃ Fin n` of the vertices and a list of the edges,
each exactly once, in any order and either orientation. -/
structure Encoding [Fintype V] (G : WGraph V) where
  /-- The vertex numbering. -/
  idx : V ≃ Fin (Fintype.card V)
  /-- The edge list. -/
  edges : List (V × V)
  /-- No edge is listed twice. -/
  nodup : (edges.map fun p => s(p.1, p.2)).Nodup
  /-- The listed pairs are exactly the edges of `G`. -/
  complete : ∀ e : Sym2 V, e ∈ edges.map (fun p => s(p.1, p.2)) ↔ e ∈ G.graph.edgeSet

variable [Fintype V] {G : WGraph V}

/-- The number of a vertex, as a real. -/
def Encoding.vtx (E : Encoding G) (v : V) : ℝ := ((E.idx v : ℕ) : ℝ)

/-- The cells of the graph: `[n, m]` and, per listed edge, its two endpoint numbers and weight. -/
noncomputable def Encoding.cells (E : Encoding G) : List ℝ :=
  [(Fintype.card V : ℝ), (E.edges.length : ℝ)] ++
    E.edges.flatMap fun p => [E.vtx p.1, E.vtx p.2, G.w s(p.1, p.2)]

/-- A vertex labelling laid out in vertex order. -/
def Encoding.labelCells (E : Encoding G) (L : V → ℝ) : List ℝ :=
  List.ofFn fun j : Fin (Fintype.card V) => L (E.idx.symm j)

/-- The block of `n` cells of a centered partition `(P, cent)`: cell `j` holds the number of the
center of the cluster of the `j`-th vertex. -/
noncomputable def Encoding.centerCells (E : Encoding G) (P : Finset (Finset V))
    (cent : Finset V → V) : List ℝ :=
  List.ofFn fun j : Fin (Fintype.card V) => E.vtx (cent (clusterOf P (E.idx.symm j)))

/-- The layout of a hierarchy: `[λ, κ]` followed by the center blocks of levels `0, …, κ`. -/
noncomputable def Encoding.hierCells (E : Encoding G) (H : Hierarchy V) : List ℝ :=
  [H.offset, (H.κ : ℝ)] ++
    ((List.range (H.κ + 1)).map fun i => E.centerCells (H.C i) (H.cent i)).flatten

/-! ### Output layouts and their validity predicates -/

/-- `o` is a vertex labelling (`n` cells in vertex order) whose fibres form a partition `P` with
`Valid P`. -/
def PartitionOut (E : Encoding G) (Valid : Finset (Finset V) → Prop) (o : List ℝ) : Prop :=
  ∃ L : V → ℝ, o = E.labelCells L ∧ Valid (labelPartition L)

/-- `o = [k]` followed by `k` labellings; labelling `i` gives the partial partition `𝒞_i` as the
fibres of its nonnegative labels; `(k, 𝒞)` satisfies `Valid`. This is also the layout of every
oracle answer in Theorem 9 and Lemma 24. -/
def CoverOut (E : Encoding G) (Valid : (k : ℕ) → (Fin k → Finset (Finset V)) → Prop)
    (o : List ℝ) : Prop :=
  ∃ (k : ℕ) (L : Fin k → V → ℝ),
    o = [(k : ℝ)] ++ (List.ofFn fun i => E.labelCells (L i)).flatten ∧
      Valid k fun i => labelPartial (L i)

/-- `o = [k]` followed, for each of `k` spanning trees, by the positions in `E.edges` of its
`n − 1` edges; the family satisfies `Valid`. -/
def TreesOut (E : Encoding G) (Valid : (k : ℕ) → (Fin k → RamseyLST.Main.SpanningTree G) → Prop)
    (o : List ℝ) : Prop :=
  ∃ (k : ℕ) (T : Fin k → RamseyLST.Main.SpanningTree G) (L : Fin k → List ℕ),
    Valid k T ∧
    (∀ i, (L i).length = Fintype.card V - 1 ∧ ∀ x y : V, (T i).tree.Adj x y ↔
      ∃ j ∈ L i, (E.edges[j]?).map (fun p => s(p.1, p.2)) = some s(x, y)) ∧
    o = [(k : ℝ)] ++ (List.ofFn fun i => (L i).map fun j => (j : ℝ)).flatten

/-- `o = [m]` followed by `m` centered partitions `(C_i, cent_i)` as center blocks; the family
satisfies `Valid`. -/
def CenteredFamilyOut (E : Encoding G)
    (Valid : (m : ℕ) → (Fin m → Finset (Finset V)) → (Fin m → Finset V → V) → Prop)
    (o : List ℝ) : Prop :=
  ∃ (m : ℕ) (C : Fin m → Finset (Finset V)) (cent : Fin m → Finset V → V),
    Valid m C cent ∧
      o = [(m : ℝ)] ++ (List.ofFn fun i => E.centerCells (C i) (cent i)).flatten

/-- `o = [m]` followed by the layouts of `m` hierarchies; the family satisfies `Valid`. -/
def HierarchiesOut (E : Encoding G) (Valid : (m : ℕ) → (Fin m → Hierarchy V) → Prop)
    (o : List ℝ) : Prop :=
  ∃ (m : ℕ) (F : Fin m → Hierarchy V),
    Valid m F ∧ o = [(m : ℝ)] ++ (List.ofFn fun j => E.hierCells (F j)).flatten

open Classical in
/-- `o` holds, for each vertex `v` (in vertex order), three cells: the number of the root
`c_η` of its supernode `η`; if `v = c_η`, the number of the root of the parent supernode (`−1` at
the root of `T`), else `−1`; and `−2` if `v ∉ T_η`, `−1` if `v = c_η`, else the number of its
parent in `T_η` (its neighbour in `T_η` closer to `c_η`). `D` satisfies `Valid`. -/
def CopOut (E : Encoding G) (Valid : CopData G → Prop) (o : List ℝ) : Prop :=
  ∃ D : CopData G, Valid D ∧ o.length = 3 * Fintype.card V ∧
    ∀ v : V, ∀ η ∈ D.S, v ∈ η →
      let i := 3 * (E.idx v : ℕ)
      o.getD i 0 = E.vtx (D.root η) ∧
      o.getD (i + 1) 0 =
        (if v = D.root η then (match D.parent η with
          | none => -1
          | some X => E.vtx (D.root X)) else -1) ∧
      (v ∉ D.skelV η → o.getD (i + 2) 0 = -2) ∧ (v = D.root η → o.getD (i + 2) 0 = -1) ∧
      (v ∈ D.skelV η → v ≠ D.root η → ∃ p : V, o.getD (i + 2) 0 = E.vtx p ∧
        (D.skel η).Adj v p ∧
        (D.skelGraph η).dist (D.root η) p < (D.skelGraph η).dist (D.root η) v)

end MinorFreeSTC.Main


