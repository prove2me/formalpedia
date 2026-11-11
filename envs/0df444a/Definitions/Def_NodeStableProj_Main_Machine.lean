-- Prove2me | Definitions.Def_NodeStableProj_Main_Machine
-- name    : NodeStableProj_Main_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:58:17.965316+00:00
-- url     : https://prove2.me/theorems/7ae64532-5eac-46d3-9c56-668b12192846
-- title:
--   The machine: a unit-cost randomized real RAM with integer memory, floor, exp, log and uniform draws; graph input encodings, output decoding, output law and running time
-- statement:
--   The paper says "can be implemented in time" without naming a machine; this is the model used for that phrase. It is the published real-RAM core (`SmaleNinth.RAMInstr`: exact $+,-,\times,\div$ on reals with $x/0=0$, rational literals, indirect real memory through integer pointers, pointer set/copy/increment/decrement, the jumps $r\le0$ and $p\le p'$) extended with an **integer memory** $\mathbb Z\to\mathbb Z$ with constant-time indirect access, pointer $+,-,\times$, the cast $\mathbb Z\to\mathbb R$, $\lfloor\cdot\rfloor:\mathbb R\to\mathbb Z$, $\exp$, $\log$, a **draw** instruction reading the next value of a tape of independent uniform $[0,1]$ reals, and **halt**. Every executed instruction costs one step; only `halt` halts.
--
--   **Input.** A graph is given by an **encoding**: a duplicate-free list of its vertex labels in any order and a list of its edges, each exactly once, as ordered pairs in either orientation, in any order. Integer memory holds from cell $0$ the parameters followed by $[n,m,v_1,\dots,v_n,a_1,b_1,\dots,a_m,b_m]$; real memory holds the real parameters from cell $0$. A projection program receives integers $D,\hat D$ and the real $\tilde\varepsilon$; a release program receives the integer $D$ and the reals $\varepsilon,\delta$.
--
--   **Output.** On halting, pointer register $1$ holds an address $a$. A projection program outputs the edge list stored at $a$ (a count $k$ then $k$ pairs); a release program outputs $\hat D=I[a]$ and the edge list stored at $a+1$. A run that never halts outputs `none`. The **output law** is the pushforward of the tape law under the run. A program **halts within $T$ steps** if on every tape the run halts after at most $T$ steps.
--
--   **Formalization Note.** Every executed instruction, including reading the input and writing the output, costs one step. `Admissible` requires rational literals and excludes the core's `accept`/`reject`. Output spaces are `Option` types with the discrete σ-algebra. `log` is `Real.log` ($\log0=0$).
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), p. 11 Lemma 3.3 item 2; p. 12 Theorem 3.5 item 4; p. 32 Lemma B.1 and its proof

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_NodeStableProj_Main_Graph
import Definitions.Def_NodeStableProj_Main_Concurrent

open MeasureTheory

namespace NodeStableProj.Main

/-!
# The machine: a unit-cost randomized real RAM with integer memory, floor, exp, log and uniform draws

Aden-Ali, Sealfon, Smith, Steinke, Ullman, *Node Differential Privacy via Node-Stable Graph
Projections*, STOC 2027 submission (manuscript sha256 42f18565…), p. 11 Lemma 3.3 item 2, p. 12
Theorem 3.5 item 4, p. 32 Lemma B.1 and its proof. The paper says "can be implemented in time"
and names no machine; this model is a reading of those sentences.

**Formalization Note.**
* The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ` (exact
  `+ − × ÷` with `x/0 = 0`, literals, indirect real memory through integer pointers, pointer set,
  copy, increment, decrement, the jumps `r ≤ 0` and `p ≤ p'`). It is extended (following the
  published pattern of `NNPartTree.Instr`, not imported) with: an integer memory `ℤ → ℤ` with
  constant-time indirect access, pointer `+ − ×`, the cast `ℤ → ℝ`, `⌊·⌋ : ℝ → ℤ`, `exp`,
  `log` (`Real.log`, so `log 0 = 0`), a `draw` reading the next value of a tape of independent
  uniform `[0, 1]` reals, and `halt`.
* Every executed instruction costs one step. A program counter outside the program is stuck
  forever, and the core's `accept`/`reject` are excluded, so only `halt` halts. Real literals are
  rational (`Admissible`).
* Input: integer memory holds the list `ints` from cell `0` and real memory the list `reals` from
  cell `0`; every other cell, register and pointer is `0`. A graph is given by an *encoding*: a
  duplicate-free list of its vertex labels, in any order, and a list of its edges, each exactly
  once, as ordered pairs in either orientation, in any order (`IsEncoding`); it is laid out as
  `[n, m, v₁, …, vₙ, a₁, b₁, …, aₘ, bₘ]` (`graphCells`).
* Output: on halting, pointer register `1` holds an address `a`; the output is read from integer
  memory at `a` (`decodeEdges`, `decodeRelease`). A run that never halts has output `none`.
* The output law is the pushforward of the tape law (`tapeLaw`) under the run.
-/

/-- An instruction. -/
inductive Instr where
  /-- A `SmaleNinth` real-RAM instruction. -/
  | core (instruction : SmaleNinth.RAMInstr)
  /-- `p[dst] := I[p[addr]]`. -/
  | iload (dst addr : ℕ)
  /-- `I[p[addr]] := p[src]`. -/
  | istore (addr src : ℕ)
  /-- `p[dst] := p[a] + p[b]`. -/
  | padd (dst a b : ℕ)
  /-- `p[dst] := p[a] − p[b]`. -/
  | psub (dst a b : ℕ)
  /-- `p[dst] := p[a] * p[b]`. -/
  | pmul (dst a b : ℕ)
  /-- `r[dst] := (p[q] : ℝ)`. -/
  | toReal (dst q : ℕ)
  /-- `p[q] := ⌊r[src]⌋`. -/
  | floor (q src : ℕ)
  /-- `r[dst] := exp r[src]`. -/
  | exp (dst src : ℕ)
  /-- `r[dst] := log r[src]` (`Real.log`). -/
  | log (dst src : ℕ)
  /-- `r[dst] :=` the next unread tape value, uniform on `[0, 1]`. -/
  | draw (dst : ℕ)
  /-- Stop. -/
  | halt

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- Real literals are rational, and the core's `accept`/`reject` do not occur. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The static core table of `P` (extension instructions are placeholders, dispatched by `step`). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state: the core configuration, the integer memory, the tape cursor, the halted
flag. -/
structure State where
  core : SmaleNinth.RAMConfig
  imem : ℤ → ℤ
  cursor : ℕ
  halted : Bool

/-- One step of `P` on tape `tape`. Halted states stutter. -/
noncomputable def step (P : Program) (tape : ℕ → unitInterval) (st : State) : State :=
  if st.halted then st else
    let next : SmaleNinth.RAMConfig := { st.core with pc := st.core.pc + 1 }
    let setReg (d : ℕ) (v : ℝ) : State :=
      { st with core := { next with regs := Function.update st.core.regs d v } }
    let setPtr (d : ℕ) (v : ℤ) : State :=
      { st with core := { next with ptrs := Function.update st.core.ptrs d v } }
    match P[st.core.pc]? with
    | none => st
    | some (.core _) => { st with core := SmaleNinth.RAMStep (coreProgram P) st.core }
    | some (.iload d a) => setPtr d (st.imem (st.core.ptrs a))
    | some (.istore a b) =>
        { st with core := next,
                  imem := Function.update st.imem (st.core.ptrs a) (st.core.ptrs b) }
    | some (.padd d a b) => setPtr d (st.core.ptrs a + st.core.ptrs b)
    | some (.psub d a b) => setPtr d (st.core.ptrs a - st.core.ptrs b)
    | some (.pmul d a b) => setPtr d (st.core.ptrs a * st.core.ptrs b)
    | some (.toReal d q) => setReg d (st.core.ptrs q : ℝ)
    | some (.floor q a) => setPtr q ⌊st.core.regs a⌋
    | some (.exp d a) => setReg d (Real.exp (st.core.regs a))
    | some (.log d a) => setReg d (Real.log (st.core.regs a))
    | some (.draw d) =>
        { st with core := { next with regs := Function.update st.core.regs d (tape st.cursor) },
                  cursor := st.cursor + 1 }
    | some .halt => { st with core := next, halted := true }

/-- The state after `t` steps of `P` from `s₀` on tape `tape`. -/
noncomputable def run (P : Program) (tape : ℕ → unitInterval) (s₀ : State) (t : ℕ) : State :=
  (step P tape)^[t] s₀

/-- The initial state: integer memory holds `ints` from cell `0`, real memory holds `reals` from
cell `0`; everything else is `0`. -/
noncomputable def initState (ints : List ℤ) (reals : List ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun z => if 0 ≤ z then reals.getD z.toNat 0 else 0⟩,
    fun z => if 0 ≤ z then ints.getD z.toNat 0 else 0, 0, false⟩

/-- Every run of `P` from `s₀` (on every tape) halts within `T` steps. -/
def HaltsWithin (P : Program) (s₀ : State) (T : ℝ) : Prop :=
  ∀ tape : ℕ → unitInterval, ∃ t : ℕ, (t : ℝ) ≤ T ∧ (run P tape s₀ t).halted = true

open Classical in
/-- The halted state of the run of `P` from `s₀` on `tape`, if the run halts. -/
noncomputable def finalState (P : Program) (s₀ : State) (tape : ℕ → unitInterval) :
    Option State :=
  if h : ∃ t, (run P tape s₀ t).halted = true then some (run P tape s₀ (Nat.find h)) else none

/-- `(vs, es)` encodes `G`: `vs` lists every vertex label exactly once (any order), and `es` lists
every edge exactly once as an ordered pair in either orientation (any order). -/
def IsEncoding (G : Graph) (vs : List ℕ) (es : List (ℕ × ℕ)) : Prop :=
  vs.Nodup ∧ vs.toFinset = G.V ∧
    (es.map fun p => s(p.1, p.2)).Nodup ∧ (es.map fun p => s(p.1, p.2)).toFinset = G.E

/-- The integer cells of an encoded graph: `[n, m, v₁, …, vₙ, a₁, b₁, …, aₘ, bₘ]`. -/
def graphCells (vs : List ℕ) (es : List (ℕ × ℕ)) : List ℤ :=
  [(vs.length : ℤ), (es.length : ℤ)] ++ vs.map (fun v => (v : ℤ)) ++
    es.flatMap fun p => [(p.1 : ℤ), (p.2 : ℤ)]

/-- The edge list stored at `base`: a count `k = I[base]` followed by the pairs
`(I[base + 1 + 2i], I[base + 2 + 2i])`, `i < k`, read as unordered pairs of naturals. -/
def decodeEdges (mem : ℤ → ℤ) (base : ℤ) : Finset (Sym2 ℕ) :=
  ((List.range (mem base).toNat).map fun i =>
    s((mem (base + 1 + 2 * i)).toNat, (mem (base + 2 + 2 * i)).toNat)).toFinset

/-- Output of a projection program: the edge list at the address in pointer register `1`. -/
def decodeProjection (st : State) : Finset (Sym2 ℕ) :=
  decodeEdges st.imem (st.core.ptrs 1)

/-- Output of a release program: `D̂ = I[a]` and the edge list at `a + 1`, `a = p[1]`. -/
def decodeRelease (st : State) : Finset (Sym2 ℕ) × ℕ :=
  (decodeEdges st.imem (st.core.ptrs 1 + 1), (st.imem (st.core.ptrs 1)).toNat)

/-- The output space of a projection program (`none`: the run does not halt), discrete. -/
def EdgeOutput : Type := Option (Finset (Sym2 ℕ))

instance : MeasurableSpace EdgeOutput := ⊤

/-- The output space of a release program (`none`: the run does not halt), discrete. -/
def ReleaseOutput : Type := Option (Finset (Sym2 ℕ) × ℕ)

instance : MeasurableSpace ReleaseOutput := ⊤

/-- The initial state of a projection program on parameters `D, D̂` (integers), `ε̃` (real) and
the encoded graph `(vs, es)`: input cells `[D, D̂] ++ graphCells vs es`, real cells `[ε̃]`. -/
noncomputable def projectionInit (D Dhat : ℕ) (εt : ℝ) (vs : List ℕ) (es : List (ℕ × ℕ)) :
    State :=
  initState ([(D : ℤ), (Dhat : ℤ)] ++ graphCells vs es) [εt]

/-- A graph's edge set as the output of a halting projection program. -/
def edgeOutput (H : Graph) : EdgeOutput := some H.E

/-- `(H, D̂) ↦ (H_{−v}, D̂)` on release outputs (edges at `v` deleted; `none` stays `none`). -/
def releaseDeleteVertex (v : ℕ) (o : ReleaseOutput) : ReleaseOutput :=
  Option.map (fun p : Finset (Sym2 ℕ) × ℕ => (deleteVertexEdges p.1 v, p.2)) o

/-- The output law (edge set of the returned graph) of a projection program `P` on `D, D̂, ε̃`
and the encoded graph `(vs, es)`. -/
noncomputable def projectionProgramLaw (P : Program) (D Dhat : ℕ) (εt : ℝ) (vs : List ℕ)
    (es : List (ℕ × ℕ)) : Measure EdgeOutput :=
  tapeLaw.map fun tape =>
    ((finalState P (projectionInit D Dhat εt vs es) tape).map decodeProjection :
      Option (Finset (Sym2 ℕ)))

/-- The initial state of a release program on `D`, `ε`, `δ` and the encoded graph:
input cells `[D] ++ graphCells vs es`, real cells `[ε, δ]`. -/
noncomputable def releaseInit (D : ℕ) (ε δ : ℝ) (vs : List ℕ) (es : List (ℕ × ℕ)) : State :=
  initState ([(D : ℤ)] ++ graphCells vs es) [ε, δ]

/-- The output law `(P(G), D̂(G))` of a release program on `D`, `ε`, `δ` and the encoded graph. -/
noncomputable def releaseProgramLaw (P : Program) (D : ℕ) (ε δ : ℝ) (vs : List ℕ)
    (es : List (ℕ × ℕ)) : Measure ReleaseOutput :=
  tapeLaw.map fun tape =>
    ((finalState P (releaseInit D ε δ vs es) tape).map decodeRelease :
      Option (Finset (Sym2 ℕ) × ℕ))

end NodeStableProj.Main


