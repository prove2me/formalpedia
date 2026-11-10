-- Prove2me | Definitions.Def_FullyDynamicCorrelation_VertexUpdates_RAM
-- name    : FullyDynamicCorrelation_VertexUpdates_RAM
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:53:47.477629+00:00
-- url     : https://prove2.me/theorems/17a0ef56-2e6f-4043-97a9-d227bd9aa345
-- title:
--   The randomized adjacency-list random access machine
-- statement:
--   The cost model of Definition 1 (p. 12), Definition 2 and Proposition 3.2 (pp. 13–14), fixed as a unit-cost RAM. A **program** (`Program`) is a finite list of instructions on a memory $m:\mathbb N\to\mathbb N$: constants, addition, truncated subtraction, indirect load and store, jumps, the three adjacency-list queries of Definition 1 — degree `deg`, $i$-th neighbour `nbr` (in the list's order; $0$ if $i$ is out of range) and edge `edge` — and `rand`, a fresh uniform element of $\{0,\dots,m-1\}$. Every executed instruction costs one unit; there is no multiplication, division or problem-specific instruction. `Presents H adj`: the adjacency lists `adj` list each open neighbourhood without repetition, in arbitrary order (they are maintained outside the machine at no cost). `exec` is one instruction (a probability distribution, `PMF`), `runFuel` a run with an instruction allowance (`none` if it does not halt within it; halting = program counter past the end), `runCall` a single call on a static graph returning the final memory and the number of instructions executed.
--
--   **Layout.** Cells $0$–$7$ are scalars: cell $0$ the update kind ($1$ insert, $2$ delete) or a call's answer, cell $1$ the vertex, cell $2$ the bound $n$, cells $3$/$4$ the lengths of the input/output lists; above them address $8k+8+r$ is entry $k$ of region $r$: input list (`inAddr`), output list (`outAddr`, read by `outputList`), cluster label of vertex $u$ (`labAddr`), stored cluster size (`sizeAddr`). `inputMem` is the memory at the start of a call.
--
--   **Dynamic runs.** `execStream P n us adj F` processes the stream from the all-zero memory: before update $t$, cells $0,1,2$ receive its kind, vertex and $n$ (`updateMem`; the neighbours are read through the lists), the machine runs to halting on `graphAt us (t+1)` presented by `adj t`, and its memory is kept; the result is the list of memories at the returned times, or `none` if the total allowance $F$ runs out. `labelRel m` is the clustering a memory represents: same label cell value.
-- source:
--   Braverman, Dharangutte, Fan, Wang, Xie and Zhou (2026), Fully Dynamic Correlation Clustering with Vertex Updates in Polylogarithmic Update Time, supplied manuscript sha256 07ee1c8f4214025e0b6a81ffc141dbcc4d3bc385abe36d5b298e3ec6037aaab2, Definition 1 (p. 12), Definition 2 (p. 13), Proposition 3.2 (pp. 13–14)

import Mathlib
import Definitions.Def_FullyDynamicCorrelation_VertexUpdates_Stream

namespace FullyDynamicCorrelation.VertexUpdates

open Classical

/-!
# The randomized adjacency-list RAM

Braverman et al. (2026), supplied manuscript sha256 07ee1c8f…aab2, Definition 1 (p. 12),
Definition 2 (p. 13), Proposition 3.2 (pp. 13–14).

The paper counts time in operations: a positive degree query, a positive neighbour query, a
positive edge query and a uniform random choice cost `O(1)` each, and the algorithm's own data
structures are built from such operations. This module fixes that count as a unit-cost random
access machine: a program is a finite list of instructions acting on a memory `ℕ → ℕ`; every
executed instruction costs one unit. Besides constants, addition, truncated subtraction,
indirect load and store and jumps, the only instructions are the three adjacency-list queries of
Definition 1 and a uniform random choice in `{0, …, m − 1}`. Sampling a uniform positive
neighbour is a degree query, a random choice and a neighbour query. There is no multiplication,
no division and no instruction referring to correlation clustering, so the machine is no
stronger than the paper's model. The adjacency lists themselves are maintained outside the
machine and are free (Definition 2, p. 2): the machine only queries them.

A halted machine has its program counter past the end of the program.
-/

/-- Instructions. Operands `d a b s` are memory addresses, `l` is a program location. -/
inductive Instr where
  /-- `m[d] := k` -/
  | const (d k : ℕ)
  /-- `m[d] := m[a] + m[b]` -/
  | add (d a b : ℕ)
  /-- `m[d] := m[a] - m[b]` (truncated at `0`) -/
  | sub (d a b : ℕ)
  /-- `m[d] := m[m[a]]` -/
  | load (d a : ℕ)
  /-- `m[m[a]] := m[s]` -/
  | store (a s : ℕ)
  /-- go to location `l` -/
  | jump (l : ℕ)
  /-- go to location `l` if `m[a] = 0` -/
  | jumpZ (a l : ℕ)
  /-- positive degree query: `m[d] := deg⁺(m[a])` -/
  | deg (d a : ℕ)
  /-- positive neighbour query: `m[d] :=` the `m[b]`-th entry (`1 ≤ m[b] ≤ deg⁺`) of the
  adjacency list of `m[a]`; `0` when `m[b]` is out of range -/
  | nbr (d a b : ℕ)
  /-- positive edge query: `m[d] := 1` if `(m[a], m[b]) ∈ E⁺`, else `0` -/
  | edge (d a b : ℕ)
  /-- uniform random choice: `m[d] :=` a fresh uniform element of `{0, …, m[a] − 1}`
  (`0` when `m[a] = 0`) -/
  | rand (d a : ℕ)

/-- A program: a finite instruction list, fixed before any input is seen. -/
abbrev Program := List Instr

/-- `adj` is an adjacency-list presentation of the graph `H`: the list of every vertex lists its
open positive neighbourhood without repetition, in an arbitrary order (empty for an absent
vertex). -/
def Presents (H : SGraph) (adj : ℕ → List ℕ) : Prop :=
  ∀ v, (adj v).Nodup ∧ ∀ u, u ∈ adj v ↔ u ∈ H.nbr v

/-- A machine configuration: program counter and memory. -/
structure Config where
  pc : ℕ
  mem : ℕ → ℕ

/-- Write `x` to cell `d` and move to the next instruction. -/
def Config.write (c : Config) (d x : ℕ) : Config :=
  ⟨c.pc + 1, Function.update c.mem d x⟩

/-- One instruction, executed against the graph `H` with adjacency lists `adj`; the result is a
probability distribution on configurations (only `rand` is random). -/
noncomputable def exec (H : SGraph) (adj : ℕ → List ℕ) (i : Instr) (c : Config) : PMF Config :=
  match i with
  | .const d k => PMF.pure (c.write d k)
  | .add d a b => PMF.pure (c.write d (c.mem a + c.mem b))
  | .sub d a b => PMF.pure (c.write d (c.mem a - c.mem b))
  | .load d a => PMF.pure (c.write d (c.mem (c.mem a)))
  | .store a s => PMF.pure ⟨c.pc + 1, Function.update c.mem (c.mem a) (c.mem s)⟩
  | .jump l => PMF.pure ⟨l, c.mem⟩
  | .jumpZ a l => PMF.pure ⟨if c.mem a = 0 then l else c.pc + 1, c.mem⟩
  | .deg d a => PMF.pure (c.write d (adj (c.mem a)).length)
  | .nbr d a b =>
      PMF.pure (c.write d
        (if 1 ≤ c.mem b ∧ c.mem b ≤ (adj (c.mem a)).length then
          (adj (c.mem a)).getD (c.mem b - 1) 0 else 0))
  | .edge d a b => PMF.pure (c.write d (if H.Adj (c.mem a) (c.mem b) then 1 else 0))
  | .rand d a =>
      if h : 0 < c.mem a then
        (PMF.uniformOfFinset (Finset.range (c.mem a)) ⟨0, Finset.mem_range.mpr h⟩).map
          (fun x => c.write d x)
      else PMF.pure (c.write d 0)

/-- The machine has halted: the program counter is past the end of the program. -/
def Halted (P : Program) (c : Config) : Prop := P.length ≤ c.pc

/-- Run from `c` with at most `f` further instructions: `some (c', r)` if the machine halts in
`c'` with `r` units of the allowance left, `none` if the allowance runs out first. -/
noncomputable def runFuel (P : Program) (H : SGraph) (adj : ℕ → List ℕ) :
    ℕ → Config → PMF (Option (Config × ℕ))
  | 0, c => if Halted P c then PMF.pure (some (c, 0)) else PMF.pure none
  | f + 1, c =>
      if Halted P c then PMF.pure (some (c, f + 1))
      else
        match P[c.pc]? with
        | some i => (exec H adj i c).bind (fun c' => runFuel P H adj f c')
        | none => PMF.pure (some (c, f + 1))

/-- One call of a program on a static graph, from memory `m₀` with allowance `F`: the final
memory and the number of executed instructions, or `none` if it does not halt within `F`. -/
noncomputable def runCall (P : Program) (H : SGraph) (adj : ℕ → List ℕ) (m₀ : ℕ → ℕ)
    (F : ℕ) : PMF (Option ((ℕ → ℕ) × ℕ)) :=
  (runFuel P H adj F ⟨0, m₀⟩).map (Option.map (fun p => (p.1.mem, F - p.2)))

/-! ## Memory layout

Cells `0, …, 7` hold scalars. Cell `1` holds the vertex an update or call concerns, cell `2`
holds `n`, cell `0` holds the kind of update (`1` insertion, `2` deletion) or a call's answer.
Above them, address `8k + 8 + r` is entry `k` of region `r`. -/

/-- Entry `k` of an input list (region 0); its length is in cell `3`. -/
def inAddr (k : ℕ) : ℕ := 8 * k + 8

/-- Entry `k` of an output list (region 1); its length is in cell `4`. -/
def outAddr (k : ℕ) : ℕ := 8 * k + 9

/-- The cluster label of vertex `u` (region 2). -/
def labAddr (u : ℕ) : ℕ := 8 * u + 10

/-- The stored size of the cluster with label `l` (region 3). -/
def sizeAddr (l : ℕ) : ℕ := 8 * l + 11

/-- The list stored in an output region: cell `4` gives its length. -/
def outputList (m : ℕ → ℕ) : List ℕ := (List.range (m 4)).map (fun k => m (outAddr k))

/-- The memory at the start of a single call: cell `1` holds the vertex `v`, cell `2` the bound
`n`, cell `3` the length of the input list `xs`, whose entries are in region 0; region 2 holds
the cluster label `lab u` of every vertex `u` (`0`: no cluster) and region 3 the stored size
`sz l` of every label `l`; every other cell is `0`. -/
def inputMem (n v : ℕ) (xs : List ℕ) (lab sz : ℕ → ℕ) (a : ℕ) : ℕ :=
  if a < 8 then
    (if a = 1 then v else if a = 2 then n else if a = 3 then xs.length else 0)
  else if (a - 8) % 8 = 0 then xs.getD ((a - 8) / 8) 0
  else if (a - 8) % 8 = 2 then lab ((a - 8) / 8)
  else if (a - 8) % 8 = 3 then sz ((a - 8) / 8)
  else 0

/-! ## The fully dynamic setting -/

/-- Before update `u` is processed, cell `0` receives its kind, cell `1` its vertex and cell `2`
the bound `n`; the rest of memory is what the previous update left. The positive neighbours of
an inserted vertex are not written: the program reads them through the adjacency lists. -/
def updateMem (n : ℕ) (u : Update) (m : ℕ → ℕ) : ℕ → ℕ :=
  match u with
  | .ins v _ => Function.update (Function.update (Function.update m 0 1) 1 v) 2 n
  | .del v => Function.update (Function.update (Function.update m 0 2) 1 v) 2 n

/-- Process the updates of `us` from index `t` on, starting from memory `m` with a total
allowance of `F` instructions for all of them. Update `t` is processed on the graph
`graphAt us (t + 1)` presented by the adjacency lists `adj t`, and runs until the machine halts;
then the next update is delivered. The result is the list of memories at the end of each update
(the returned states), or `none` if the allowance is exhausted. -/
noncomputable def execFrom (P : Program) (n : ℕ) (us : List Update) (adj : ℕ → ℕ → List ℕ) :
    ℕ → (t : ℕ) → (ℕ → ℕ) → PMF (Option (List (ℕ → ℕ)))
  | F, t, m =>
    if ht : t < us.length then
      (runFuel P (graphAt us (t + 1)) (adj t) F ⟨0, updateMem n (us[t]'ht) m⟩).bind
        (fun o => match o with
          | none => PMF.pure none
          | some (c, r) =>
              (execFrom P n us adj r (t + 1) c.mem).map (Option.map (fun ms => c.mem :: ms)))
    else PMF.pure (some [])
  termination_by _ t _ => us.length - t

/-- The whole run on a stream, from the all-zero memory with total allowance `F`. -/
noncomputable def execStream (P : Program) (n : ℕ) (us : List Update) (adj : ℕ → ℕ → List ℕ)
    (F : ℕ) : PMF (Option (List (ℕ → ℕ))) :=
  execFrom P n us adj F 0 (fun _ => 0)

/-- The clustering a memory represents: two active vertices are in the same cluster iff their
label cells hold the same value. -/
def labelRel (m : ℕ → ℕ) (u v : ℕ) : Prop := m (labAddr u) = m (labAddr v)

end FullyDynamicCorrelation.VertexUpdates


