-- Prove2me | Definitions.Def_TZLevelsADO_IsADO
-- name    : TZLevelsADO_IsADO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:34.154609+00:00
-- url     : https://prove2.me/theorems/98871088-5883-4254-92f2-fe0cd5555264
-- title:
--   Approximate distance oracles with stretch $\alpha$ on the comparison–addition machine
-- statement:
--   An **approximate distance oracle** (ADO) is a data structure that, given a pair of vertices $u, v$, returns an estimate $\hat d(u, v)$; it has **stretch** $\alpha$ if $d(u, v) \le \hat d(u, v) \le \alpha\, d(u, v)$ for every pair. Here an ADO for a graph $G$ and a parameter $k$ is a pair of programs for the comparison–addition machine (a word RAM with real registers supporting addition, negation and comparison, unit cost, and preloaded fair coins):
--
--   1. The **preprocessing** program runs on the input: integer cells $n, m, k$ followed by the edge endpoints, and real cells holding the edge weights. The **data structure** is the memory of its halted state.
--   2. A **query** $\langle u, v\rangle$ runs the query program from that memory, with all coin cells cleared, $u$ and $v$ written into two fixed integer cells, and registers reset. It is deterministic, and its answer $\hat d(u,v)$ is a fixed real output cell.
--   3. The **space** is the number of distinct cells the preprocessing stores to, plus the $3 + 3m$ input cells.
--
--   The predicate says: there is a measurable set $E$ of coin tapes of probability at least $1 - \mathrm{fail}$ such that on **every** coin tape the preprocessing halts and every query halts with an answer satisfying
--   $$d(u, v) \le \hat d(u, v) \le \alpha\, d(u, v),$$
--   and on every tape in $E$ the preprocessing halts within $T_{\mathrm{pre}}$ steps with space at most $S$, and every query halts within $T_q$ steps.
--
--   This is the notion of an ADO in Theorem 1: stretch for every outcome of the sampling, time and space with high probability.
--
--   **Formalization Note** The machine is the published `RealAPSP.Machine`; the paper names no model. The word bound is $\mathrm{width}^{c}$ with $\mathrm{width} = n + m + k + 2$ and $c$ fixed with the program, so every input integer fits in a word. Clearing the coin cells and counting the input cells in the space keep a query from using free randomness or reading the whole graph for free.
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), §1, p.1 (PDF p.2) (definition of an ADO and of stretch); §7, p.26 (PDF p.27); §2, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_RealAPSP_Machine
import Definitions.Def_TZLevelsADO_Graph

open MeasureTheory

namespace TZLevelsADO

/-!
# Approximate distance oracles on the comparison–addition machine

S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), §1, p.1 (PDF p.2): "An ADO is a data structure that, given a pair of
vertices u, v ∈ V, returns an estimate d̂(u, v) of the distance d(u, v) between them. An ADO has
stretch α if d(u, v) ≤ d̂(u, v) ≤ αd(u, v) for every pair of vertices u, v ∈ V"; §7, p.26 (PDF p.27):
"we perform the preprocessing once and evaluate each query using the query procedure of Algorithm 2";
§2, p.7 (PDF p.8): "our running-time and space bounds hold with high probability, and our stretch
bounds hold for every outcome of the sampling."

**Formalization Note.**
* **Machine.** The paper names no model. Both programs run on the published comparison–addition RAM
  `RealAPSP.Machine` (word RAM plus real addition, negation and comparison, unit cost, fair coins
  preloaded in the odd negative integer cells, law `RealAPSP.coinTape`).
* **Word size.** `width G k = n + m + k + 2`, so words have `O(log(n + m + k))` bits and every input
  integer (including `k`) fits in a word.
* **Preprocessing input.** Integer cells `0, 1, 2` hold `n, m, k`; cells `3 + e` and `3 + m + e` hold
  the endpoints `src e`, `dst e`; real cell `e` holds `ℓ(e)`.
* **The data structure** is the memory of the halted preprocessing state. A query `⟨u, v⟩` starts
  from that memory with every coin cell (odd negative integer cell) set to `0`, with `u` in integer cell
  `outCell 0 = −2` and `v` in `outCell 1 = −4`, with registers and program counter reset. It is a
  deterministic run: it cannot use fresh coins or re-read the preprocessing coins. Its answer `d̂(u, v)`
  is real cell `routCell 0 = −1` when it halts.
* **Space** is the number of distinct cells (integer or real) the preprocessing stores to before it
  halts, plus the `3 + 3m` input cells.
* **Randomness.** `IsADO … fail` asks for one measurable set `E` of coin tapes with probability at least
  `1 − fail`. On **every** tape, preprocessing halts and every query halts with a stretch-`α` answer.
  On every tape in `E`, preprocessing halts within `Tpre` steps having used space at most `S`, and every
  query halts within `Tq` steps.
-/

/-- The word-size parameter: words have `O(log (n + m + k + 2))` bits. -/
def width (G : Graph) (k : ℕ) : ℕ := G.n + G.m + k + 2

/-- The integer input cells `n, m, k, src₀, …, src_{m−1}, dst₀, …, dst_{m−1}`. -/
def prepInts (G : Graph) (k : ℕ) : List ℤ :=
  [(G.n : ℤ), (G.m : ℤ), (k : ℤ)] ++ List.ofFn (fun e : Fin G.m => ((G.src e : ℕ) : ℤ)) ++
    List.ofFn (fun e : Fin G.m => ((G.dst e : ℕ) : ℤ))

/-- The real input cells `ℓ₀, …, ℓ_{m−1}`. -/
noncomputable def prepReals (G : Graph) : List ℝ := List.ofFn G.wt

/-- The state of the preprocessing program `Pre` after `t` steps on the coin tape `tape`. -/
noncomputable def prepState (Pre : RealAPSP.Program) (G : Graph) (k : ℕ) (tape : ℕ → Bool) (t : ℕ) :
    RealAPSP.State :=
  RealAPSP.stateAt Pre (width G k) tape (prepInts G k) (prepReals G) t

/-- The cell that the instruction about to be executed in state `σ` stores to, if it is a store
(`false` = integer bank, `true` = real bank). Halted and stuck states store nothing. -/
def writtenCell (P : RealAPSP.Program) (σ : RealAPSP.State) : Option (Bool × ℤ) :=
  if σ.halted || σ.stuck then none else
    match P.code[σ.pc]? with
    | some (.core (.istore a _)) => some (false, σ.ireg a)
    | some (.core (.rstore a _)) => some (true, σ.ireg a)
    | _ => none

/-- The distinct cells stored to during the first `t` steps of preprocessing. -/
noncomputable def cellsWritten (Pre : RealAPSP.Program) (G : Graph) (k : ℕ) (tape : ℕ → Bool)
    (t : ℕ) : Finset (Bool × ℤ) :=
  (Finset.range t).biUnion fun s => (writtenCell Pre (prepState Pre G k tape s)).toFinset

/-- The start state of the query `⟨u, v⟩` on the stored memory of `σ`: coin cells cleared, `u` and `v`
in integer cells `outCell 0` and `outCell 1`, registers and program counter reset. -/
def queryStart (σ : RealAPSP.State) (u v : ℕ) : RealAPSP.State where
  pc := 0
  ireg := fun _ => 0
  imem := fun z =>
    if z = RealAPSP.outCell 0 then (u : ℤ)
    else if z = RealAPSP.outCell 1 then (v : ℤ)
    else if z < 0 ∧ z % 2 = 1 then 0
    else σ.imem z
  rreg := fun _ => 0
  rmem := σ.rmem
  halted := false
  stuck := false

/-- The state of the query program `Qry` after `t` steps on the query `⟨u, v⟩` from the stored
memory of `σ`. -/
noncomputable def queryRun (Qry : RealAPSP.Program) (G : Graph) (k : ℕ) (σ : RealAPSP.State)
    (u v : Fin G.n) (t : ℕ) : RealAPSP.State :=
  (RealAPSP.step Qry (RealAPSP.wordBound Qry (width G k)))^[t] (queryStart σ u v)

/-- The answer `d̂(u, v)` of a halted query: real output cell `routCell 0`. -/
def answer (σ : RealAPSP.State) : ℝ := σ.rmem (RealAPSP.routCell 0)

/-- `Pre` and `Qry` form an approximate distance oracle for `G` with parameter `k` and stretch `α`,
with preprocessing time `Tpre`, space `S` and query time `Tq`, all three with probability at least
`1 − fail`; the stretch holds on every coin tape. -/
def IsADO (Pre Qry : RealAPSP.Program) (G : Graph) (k : ℕ) (α Tpre S Tq fail : ℝ) : Prop :=
  ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ ENNReal.ofReal (1 - fail) ≤ RealAPSP.coinTape E ∧
    ∀ tape : ℕ → Bool, ∃ t : ℕ, (prepState Pre G k tape t).halted = true ∧
      (tape ∈ E → (t : ℝ) ≤ Tpre ∧
        (((cellsWritten Pre G k tape t).card + (3 + 3 * G.m) : ℕ) : ℝ) ≤ S) ∧
      ∀ u v : Fin G.n, ∃ t' : ℕ, (queryRun Qry G k (prepState Pre G k tape t) u v t').halted = true ∧
        dist G u v ≤ answer (queryRun Qry G k (prepState Pre G k tape t) u v t') ∧
        answer (queryRun Qry G k (prepState Pre G k tape t) u v t') ≤ α * dist G u v ∧
        (tape ∈ E → (t' : ℝ) ≤ Tq)

end TZLevelsADO


