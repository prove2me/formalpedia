-- Prove2me | Definitions.Def_OptimalLCA_Matching_Machine
-- name    : OptimalLCA_Matching_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:46:10.909613+00:00
-- url     : https://prove2.me/theorems/e0e317f5-0775-4b0e-a9c4-612de7a6bb26
-- title:
--   §2.1 — the randomized real RAM with degree/neighbour oracles, its cost counters, LCA and estimator semantics
-- statement:
--   The machine of §2.1 extends the published real pointer machine `SmaleNinth.RAMInstr` (real registers, integer pointer registers, memory indexed by $\mathbb Z$, arbitrary real constants, $+,-,\times,\div$, indirect load/store, pointer operations, comparison jumps) by the unit-cost operations of the paper: $\exp$, $\log$ (natural), a fixed real power $r^a$ ($a$ a program constant), integer rounding $\lfloor\cdot\rfloor$, pointer $\to$ real, a **uniform draw** reading the tape cell $\omega(p)$ at a pointer $p$, the **degree query** and the **neighbour query** (the $i$-th neighbour, $1$-based, $-1$ out of range), and halt. Two oracle instructions serve Lemma 6.1 (flip of an input coin) and Proposition 9.3 (a mark bit; the sorted list of copies at a vertex). Oracles are supplied by an environment and reached only through these instructions.
--
--   Every executed instruction costs one unit of **work**; degree and neighbour instructions also count as one **graph query**. The work, query, flip and list-call totals are $\mathbb N\cup\{\infty\}$-valued ($\infty$ if the run never halts); `HaltsWithin P env m B` means the run halts having used at most $B$ work and at most $B$ graph queries. The output is register $0$ at halting.
--
--   The random tape is $\omega:\mathbb Z\to[0,1]$ with i.i.d. uniform cells (`Measure.infinitePi`); it is random-access, so a program can derive independent seeds for each proposal and each mark. Probabilities of failure events are values of this measure on arbitrary sets (outer measure); an outer expectation $\inf\{\int g : g\ge f \text{ measurable}\}$ is used for expected costs.
--
--   **LCA semantics.** A graph on $\mathrm{Fin}\,n$ (vertex $v$ is the integer $v$) is reached through its adjacency lists. Every query is a fresh run of the same program on the same tape $\omega$ with only the query in memory: a mate query at $v$ has memory $(0,v)$, an edge query at $uv$ has memory $(1,u,v)$. Answers are therefore functions of $(G,\omega,\text{query})$, consistent in every (adaptive) query order. A mate answer is a vertex or $-1$ for $\perp$; $f_\omega(uv)$ is the edge answer. **Estimator semantics:** one run on the tape with empty memory; $\hat\nu(\omega)$ is register $0$.
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), pp. 2, 11–12, §1, §2.1

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_OptimalLCA_Matching_Graph

/-!
# The randomized real RAM with graph oracles, LCAs and estimators (Cohen–Roghani, §2.1)

The machine extends the published real pointer machine `SmaleNinth.RAMInstr` (arbitrary real
constants, `+ − × ÷`, indirect memory, pointer registers, comparison jumps) by the unit-cost
operations of §2.1: `exp`, `log`, a fixed real power, integer rounding, pointer → real, a
uniform draw from a random-access tape of i.i.d. uniform `[0, 1]` values, the degree and
neighbour queries, and `halt`. Two further oracle instructions serve the factory model of
Lemma 6.1 (`flip`: the next flip of an input coin) and the degree-halving procedure of
Proposition 9.3 (`mark`: a mark bit; `list`: the sorted list of copies at a vertex).

Every executed instruction costs one unit of work; the degree and neighbour instructions
also cost one graph query each. No instruction carries a Lean function: the oracles are
supplied by the environment `Env` and are reached only through the oracle instructions.

* `run P env m t` is the configuration after `t` steps on input memory `m`;
* `Halts`, `output` (register `0` at the halting step), and the costs `workOf`,
  `queriesOf`, `flipsOf`, `listCallsOf : ℕ∞` (`⊤` if the program never halts);
* `HaltsWithin P env m B`: the program halts having used at most `B` units of work and at
  most `B` graph queries;
* `tapeMeasure`: the law of the tape, i.i.d. uniform on `[0, 1]` indexed by `ℤ`
  (`Measure.infinitePi`); `outerLIntegral` is the outer expectation of an `ℝ≥0∞`-valued
  function (the infimum of `∫⁻ g` over measurable `g ≥ f`);
* `graphEnv A ω`: the environment of a graph given by adjacency lists `A` on `Fin n`
  (vertex `v` is the integer `v.val`; the `i`-th neighbour query is `1`-based and returns
  `-1` out of range) with tape `ω`;
* LCA semantics: an invocation is a fresh run of the same program on the shared tape `ω`
  with only the query in memory (`mem 0 = 0, mem 1 = v` for a mate query at `v`;
  `mem 0 = 1, mem 1 = u, mem 2 = v` for an edge query at `uv`), so answers are functions of
  `(G, ω, query)` and are consistent in every query order. A mate answer is a vertex
  `u.val` or `-1` for `⊥`.
* Estimator semantics: one run on the tape with empty memory; the estimate is register `0`.
-/

namespace OptimalLCA.Matching

open MeasureTheory

/-- An instruction of the machine of §2.1. -/
inductive Instr : Type
  /-- An instruction of the published real pointer machine (its `accept`/`reject` halt). -/
  | core (i : SmaleNinth.RAMInstr)
  /-- `r[dst] := exp r[i]`. -/
  | exp (dst i : ℕ)
  /-- `r[dst] := log r[i]` (natural logarithm). -/
  | log (dst i : ℕ)
  /-- `r[dst] := r[i] ^ a` for a fixed real exponent `a` (a program constant). -/
  | rpow (dst i : ℕ) (a : ℝ)
  /-- Integer rounding `p[q] := ⌊r[i]⌋`. -/
  | round (q i : ℕ)
  /-- `r[dst] := p[q]` (pointer to real). -/
  | ofPtr (dst q : ℕ)
  /-- Uniform draw: `r[dst] := ω(p[q])`, the tape cell indexed by pointer `q`. -/
  | unif (dst q : ℕ)
  /-- Degree query: `p[dst] := deg(p[q])`. -/
  | deg (dst q : ℕ)
  /-- Neighbour query: `p[dst] :=` the `p[i]`-th neighbour of `p[q]` (`1`-based). -/
  | nbr (dst q i : ℕ)
  /-- Input-coin flip (Lemma 6.1): `r[dst] :=` the next flip (`0`/`1`) of input coin `k`. -/
  | flip (dst k : ℕ)
  /-- Mark query (Proposition 9.3): `r[dst] := mark(p[q], p[q+1], p[q+2])` (`0`/`1`). -/
  | mark (dst q : ℕ)
  /-- List query (Proposition 9.3): writes the list at vertex `(p[q], p[q+1])` to memory
  from address `p[a]`: its length, then five integers per entry. -/
  | list (q a : ℕ)
  /-- Halt. -/
  | halt

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- The oracles a run may consult. -/
structure Env where
  /-- Degree oracle. -/
  deg : ℤ → ℤ
  /-- Neighbour oracle (vertex, `1`-based index). -/
  nbr : ℤ → ℤ → ℤ
  /-- The random-access tape of uniform draws. -/
  tape : ℤ → ℝ
  /-- `coin k m`: the `m`-th flip (from `0`) of input coin `k`. -/
  coin : ℕ → ℕ → Bool
  /-- Mark oracle. -/
  mark : ℤ → ℤ → ℤ → Bool
  /-- List oracle: the entries (five integers each) at a vertex `(v, side)`. -/
  list : ℤ → ℤ → List (ℤ × ℤ × ℤ × ℤ × ℤ)

/-- A configuration: program counter, real registers, pointer registers, memory, and the
counters of work, graph queries, input flips (per coin and in total), and list calls. -/
structure Config where
  pc : ℕ
  regs : ℕ → ℝ
  ptrs : ℕ → ℤ
  mem : ℤ → ℝ
  work : ℕ
  queries : ℕ
  flips : ℕ → ℕ
  flipCount : ℕ
  listCalls : ℕ

/-- The core instruction at a position (non-core instructions are viewed as `accept`;
they are never executed through this view). -/
def coreView : Instr → SmaleNinth.RAMInstr
  | .core i => i
  | _ => .accept

/-- Halting instructions. -/
def isHaltInstr : Instr → Bool
  | .core .accept => true
  | .core .reject => true
  | .halt => true
  | _ => false

/-- A configuration is halted when its instruction halts or `pc` is outside the program. -/
def Halted (P : Program) (c : Config) : Prop :=
  match P[c.pc]? with
  | none => True
  | some i => isHaltInstr i = true

/-- The component `k` (`0 … 4`) of a list entry. -/
def entryComp (e : ℤ × ℤ × ℤ × ℤ × ℤ) (k : ℕ) : ℤ :=
  match k with
  | 0 => e.1
  | 1 => e.2.1
  | 2 => e.2.2.1
  | 3 => e.2.2.2.1
  | _ => e.2.2.2.2

/-- Memory after writing a list from address `a`: `mem a` = its length, then entry `k`
at addresses `a + 1 + 5k, …, a + 5 + 5k`. -/
noncomputable def writeList (mem : ℤ → ℝ) (a : ℤ) (L : List (ℤ × ℤ × ℤ × ℤ × ℤ)) :
    ℤ → ℝ := fun addr =>
  if addr = a then (L.length : ℝ)
  else if a + 1 ≤ addr ∧ addr < a + 1 + 5 * L.length then
    (entryComp (L.getD ((addr - a - 1) / 5).toNat (0, 0, 0, 0, 0))
      ((addr - a - 1) % 5).toNat : ℝ)
  else mem addr

/-- Execute one non-halting instruction (work is charged by `step`). -/
noncomputable def exec (P : Program) (env : Env) (c : Config) : Instr → Config
  | .core _ =>
      let s := SmaleNinth.RAMStep (P.map coreView) ⟨c.pc, c.regs, c.ptrs, c.mem⟩
      { c with pc := s.pc, regs := s.regs, ptrs := s.ptrs, mem := s.mem }
  | .exp dst i =>
      { c with pc := c.pc + 1, regs := Function.update c.regs dst (Real.exp (c.regs i)) }
  | .log dst i =>
      { c with pc := c.pc + 1, regs := Function.update c.regs dst (Real.log (c.regs i)) }
  | .rpow dst i a =>
      { c with pc := c.pc + 1, regs := Function.update c.regs dst (c.regs i ^ a) }
  | .round q i =>
      { c with pc := c.pc + 1, ptrs := Function.update c.ptrs q ⌊c.regs i⌋ }
  | .ofPtr dst q =>
      { c with pc := c.pc + 1, regs := Function.update c.regs dst (c.ptrs q : ℝ) }
  | .unif dst q =>
      { c with pc := c.pc + 1, regs := Function.update c.regs dst (env.tape (c.ptrs q)) }
  | .deg dst q =>
      { c with
        pc := c.pc + 1
        ptrs := Function.update c.ptrs dst (env.deg (c.ptrs q))
        queries := c.queries + 1 }
  | .nbr dst q i =>
      { c with
        pc := c.pc + 1
        ptrs := Function.update c.ptrs dst (env.nbr (c.ptrs q) (c.ptrs i))
        queries := c.queries + 1 }
  | .flip dst k =>
      { c with
        pc := c.pc + 1
        regs := Function.update c.regs dst (if env.coin k (c.flips k) then 1 else 0)
        flips := Function.update c.flips k (c.flips k + 1)
        flipCount := c.flipCount + 1 }
  | .mark dst q =>
      { c with
        pc := c.pc + 1
        regs := Function.update c.regs dst
          (if env.mark (c.ptrs q) (c.ptrs (q + 1)) (c.ptrs (q + 2)) then 1 else 0) }
  | .list q a =>
      { c with
        pc := c.pc + 1
        mem := writeList c.mem (c.ptrs a) (env.list (c.ptrs q) (c.ptrs (q + 1)))
        listCalls := c.listCalls + 1 }
  | .halt => c

/-- One step: a halted configuration is fixed; otherwise the instruction at `pc` is
executed and one unit of work is charged. -/
noncomputable def step (P : Program) (env : Env) (c : Config) : Config :=
  match P[c.pc]? with
  | none => c
  | some i => if isHaltInstr i then c else { exec P env c i with work := c.work + 1 }

/-- The initial configuration on input memory `m`: `pc = 0`, all registers and counters `0`. -/
def initConfig (m : ℤ → ℝ) : Config :=
  ⟨0, fun _ => 0, fun _ => 0, m, 0, 0, fun _ => 0, 0, 0⟩

/-- The configuration after `t` steps. -/
noncomputable def run (P : Program) (env : Env) (m : ℤ → ℝ) (t : ℕ) : Config :=
  (step P env)^[t] (initConfig m)

/-- The run halts. -/
def Halts (P : Program) (env : Env) (m : ℤ → ℝ) : Prop :=
  ∃ t, Halted P (run P env m t)

open Classical in
/-- The output: register `0` at the first halted step, or `none` if the run never halts. -/
noncomputable def output (P : Program) (env : Env) (m : ℤ → ℝ) : Option ℝ :=
  if h : Halts P env m then some ((run P env m (Nat.find h)).regs 0) else none

/-- The final value of a counter (`⊤` when it grows without bound, e.g. the work of a run
that never halts). -/
noncomputable def totalCost (P : Program) (env : Env) (m : ℤ → ℝ) (f : Config → ℕ) : ℕ∞ :=
  ⨆ t, (f (run P env m t) : ℕ∞)

/-- Total work (`⊤` if the run never halts). -/
noncomputable def workOf (P : Program) (env : Env) (m : ℤ → ℝ) : ℕ∞ :=
  totalCost P env m Config.work

/-- Total number of graph queries. -/
noncomputable def queriesOf (P : Program) (env : Env) (m : ℤ → ℝ) : ℕ∞ :=
  totalCost P env m Config.queries

/-- Total number of input-coin flips. -/
noncomputable def flipsOf (P : Program) (env : Env) (m : ℤ → ℝ) : ℕ∞ :=
  totalCost P env m Config.flipCount

/-- Total work other than input-coin flips (the "additional work" of Lemma 6.1). -/
noncomputable def addlWorkOf (P : Program) (env : Env) (m : ℤ → ℝ) : ℕ∞ :=
  totalCost P env m (fun c => c.work - c.flipCount)

/-- The run halts having used at most `B` units of work and at most `B` graph queries. -/
def HaltsWithin (P : Program) (env : Env) (m : ℤ → ℝ) (B : ℝ) : Prop :=
  ∃ t, Halted P (run P env m t) ∧ ((run P env m t).work : ℝ) ≤ B ∧
    ((run P env m t).queries : ℝ) ≤ B

/-- The law of the random tape: i.i.d. uniform `[0, 1]` cells indexed by `ℤ`. -/
noncomputable def tapeMeasure : Measure (ℤ → unitInterval) :=
  Measure.infinitePi (fun _ : ℤ => (volume : Measure unitInterval))

/-- The real values of a tape. -/
def tapeReal (ω : ℤ → unitInterval) : ℤ → ℝ := fun z => (ω z : ℝ)

/-- Outer expectation of an `ℝ≥0∞`-valued function: the infimum of `∫⁻ g` over measurable
`g ≥ f` (equal to `∫⁻ f` when `f` is measurable). -/
noncomputable def outerLIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ENNReal) : ENNReal :=
  ⨅ (g : Ω → ENNReal) (_ : Measurable g) (_ : ∀ ω, f ω ≤ g ω), ∫⁻ ω, g ω ∂μ

/-- The environment of a graph on `Fin n` given by adjacency lists, with tape `ω`. Vertex
`v` is the integer `v.val`; the neighbour query `(w, i)` returns the `i`-th entry
(`1 ≤ i ≤ deg w`) of the list of `w`, and `-1` otherwise; an invalid vertex has degree `0`. -/
noncomputable def graphEnv {n : ℕ} (A : AdjLists (Fin n)) (ω : ℤ → ℝ) : Env where
  deg w := if h : 0 ≤ w ∧ w < n then ((A.nbrs ⟨w.toNat, by omega⟩).length : ℤ) else 0
  nbr w i :=
    if h : 0 ≤ w ∧ w < n then
      (if 1 ≤ i ∧ i ≤ (A.nbrs ⟨w.toNat, by omega⟩).length then
        ((A.nbrs ⟨w.toNat, by omega⟩).map (fun x : Fin n => (x.val : ℤ))).getD (i - 1).toNat (-1)
      else -1)
    else -1
  tape := ω
  coin _ _ := false
  mark _ _ _ := false
  list _ _ := []

/-- Memory of a mate query at `v`. -/
def mateInput {n : ℕ} (v : Fin n) : ℤ → ℝ := fun a =>
  if a = 1 then (v.val : ℝ) else 0

/-- Memory of an edge query at `uv`. -/
def edgeInput {n : ℕ} (u v : Fin n) : ℤ → ℝ := fun a =>
  if a = 0 then 1 else if a = 1 then (u.val : ℝ) else if a = 2 then (v.val : ℝ) else 0

/-- The LCA's answer to the mate query at `v` on tape `ω` (`-1` encodes `⊥`). -/
noncomputable def mateAnswer {n : ℕ} (P : Program) (A : AdjLists (Fin n))
    (ω : ℤ → unitInterval) (v : Fin n) : ℝ :=
  (output P (graphEnv A (tapeReal ω)) (mateInput v)).getD 0

/-- The LCA's answer to the edge query at `uv` on tape `ω`. -/
noncomputable def edgeAnswer {n : ℕ} (P : Program) (A : AdjLists (Fin n))
    (ω : ℤ → unitInterval) (u v : Fin n) : ℝ :=
  (output P (graphEnv A (tapeReal ω)) (edgeInput u v)).getD 0

/-- The edge answers as a function on unordered pairs (`f_ω`); on an edge `uv` it is the
answer to the query `(u, v)` or `(v, u)` (these agree whenever answers are symmetric). -/
noncomputable def lcaEdgeFn {n : ℕ} (P : Program) (A : AdjLists (Fin n))
    (ω : ℤ → unitInterval) : Sym2 (Fin n) → ℝ :=
  fun e => edgeAnswer P A ω (Quot.out e).1 (Quot.out e).2

/-- The estimator's output on tape `ω` (one run with empty memory). -/
noncomputable def estimate {n : ℕ} (P : Program) (A : AdjLists (Fin n))
    (ω : ℤ → unitInterval) : ℝ :=
  (output P (graphEnv A (tapeReal ω)) (fun _ => 0)).getD 0

end OptimalLCA.Matching


