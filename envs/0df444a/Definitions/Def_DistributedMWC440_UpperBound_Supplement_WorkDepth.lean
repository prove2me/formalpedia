-- Prove2me | Definitions.Def_DistributedMWC440_UpperBound_Supplement_WorkDepth
-- name    : DistributedMWC440_UpperBound_Supplement_WorkDepth
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:49:50.713233+00:00
-- url     : https://prove2.me/theorems/b2ae0514-fd10-43b7-bbb7-4b22d7cfe13d
-- title:
--   A randomized fork-join work-depth machine, and Theorem 3's claim
-- statement:
--   The **work-depth model** [Ble96] measures the total number of operations (work) and the length of the longest chain of dependencies (depth). The machine here is a shared-memory fork-join machine:
--
--   1. Programs are finite syntax trees: integer words of absolute value at most $(\max(2,n))^B$, thread-private registers, shared-memory reads and writes, arithmetic and comparisons, sequencing, branching, procedure calls (recursion allowed) and a parallel loop running its body for every index of a range concurrently. An expression `coin a` reads bit number $a$ of a read-only tape of independent fair random bits.
--   2. Costs: every basic statement, test, fork and call costs one unit; sequencing adds work and depth; a parallel loop charges one plus the sum of the threads' work and one plus the maximum of the threads' depths. Concurrent reads are allowed; threads that write a cell another thread reads or writes make the run fail.
--   3. Input: shared memory holds $n$, $m$ and the edge list $(u_i,v_i,w_i)$, $i<m$, of an undirected simple graph on $\{0,\dots,n-1\}$ (connectivity not required) with positive integer weights at most $n^q$, every edge listed once in an arbitrary order and orientation.
--   4. Output (Definition 1.1, centralized): a flag for "cycle found", the actual weight $w(C)$ of a simple cycle $C$ with $w(C)\le\alpha\cdot\mathrm{OPT}$, and one membership bit per input edge; on an acyclic input, flag $0$ and all membership bits $0$.
--
--   The proposition `WDTradeoff q` is Theorem 3's claim: for every confidence exponent there are a word exponent and constants $C>0$, $p$, uniform in real $k\ge1$, and for each $k$ a program, such that on every input with $n\ge\max(2,n_0)$ vertices and $m$ edges, with probability at least $1-n^{-\text{confidence}}$ the program halts with work at most $C(\log n)^p(m+1)n^{1/k}$, depth at most $C(\log n)^p$, and a correct $(k+1)$-approximate output.
--
--   **Formalization Note** The design adapts the published fork-join machine `MSTCuts2027_Parallel_Machine` (no oracle, no real cells, plus the random tape). The factor $m+1$ only matters for edgeless inputs. Since programs are syntax trees, no computation can be hidden in a Lean function, and no SSSP oracle is available.
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf (SHA-256 cdee21a6e698b7d3caf34f1990ab2132af424195b394467946a89faadca70ac1), §1.2, printed pp. 4–5 / PDF pp. 6–7 (Theorem 3 and the model); §6.2–6.3, printed pp. 29–30 / PDF pp. 31–32.

import Definitions.Def_DistributedMWC440_UpperBound_Graph

open scoped ENNReal
open MeasureTheory Classical

noncomputable section

namespace DistributedMWC440.UpperBound.Supplement

/-!
The standard randomized work-depth model of parallel computation [Ble96] used by Theorem 3 of
Chang et al., STOC 2027 submission #440 (§1.2, printed pp. 4–5 / PDF pp. 6–7; §6.2–6.3, printed
pp. 29–30 / PDF pp. 31–32): "the work of an algorithm is the total number of operations performed,
while the depth is the length of the longest chain of dependencies".

The design follows the published fork-join machine `MSTCuts2027_Parallel_Machine`
(theorem id `dec3f48a-e8d6-470d-b2c9-4c15b6362a01`), adapted: no real cells, no external oracle,
and a read-only tape of independent fair random bits. Programs are finite syntax trees, so no
computation can be hidden in a Lean function; all words are integers of absolute value at most
`(max 2 n)^B` (`O(log n)`-bit words).
-/

/-- Expressions over integer words. `var i` is a thread-private register, `read a` a shared memory
cell, `coin a` the random bit number `a` of the tape (`1` or `0`). Division is `Int` division. -/
inductive Expr where
  | const (c : ℤ)
  | var (i : ℕ)
  | read (a : Expr)
  | coin (a : Expr)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | div (a b : Expr)
  | lt (a b : Expr)
  | le (a b : Expr)
  | eq (a b : Expr)

/-- Statements. `parFor i lo hi body` runs `body` for every `i ∈ [lo, hi)` concurrently.
`call f args` calls procedure number `f` with a fresh register frame. -/
inductive Stmt where
  | skip
  | setVar (i : ℕ) (e : Expr)
  | write (a e : Expr)
  | seq (s t : Stmt)
  | ite (c : Expr) (s t : Stmt)
  | parFor (i : ℕ) (lo hi : Expr) (body : Stmt)
  | call (f : ℕ) (args : List Expr)

/-- A program: a finite list of procedures (which may call each other recursively); procedure `0`
is the entry point. It is one finite term and does not depend on the input size. -/
abbrev Program := List Stmt

/-- The result of running a statement: final shared memory and registers, the shared cells read
and written, and the charged work and depth. -/
structure Outcome where
  mem : ℕ → ℤ
  vars : ℕ → ℤ
  reads : Finset ℕ
  writes : Finset ℕ
  work : ℕ
  depth : ℕ

/-- Two concurrent threads do not interfere: neither writes a cell that the other reads or
writes (concurrent reads are allowed). -/
def Compatible (o o' : Outcome) : Prop :=
  Disjoint o.writes o'.writes ∧ Disjoint o.writes o'.reads ∧ Disjoint o.reads o'.writes

/-- Memory `σ` with the cells in `w` replaced by their contents in `τ`. -/
def overlay (σ τ : ℕ → ℤ) (w : Finset ℕ) : ℕ → ℤ :=
  fun a => if a ∈ w then τ a else σ a

/-- A word, or failure if its absolute value exceeds `wordMax`. -/
def word (wordMax : ℕ) (z : ℤ) : Option ℤ :=
  if z.natAbs ≤ wordMax then some z else none

/-- An address, or failure if it is negative or exceeds `wordMax`. -/
def addr (wordMax : ℕ) (z : ℤ) : Option ℕ :=
  if 0 ≤ z ∧ z.toNat ≤ wordMax then some z.toNat else none

/-- Expression evaluation with random tape `ω`: the value and the shared cells read. -/
def eval (wordMax : ℕ) (ω : ℕ → Bool) (σ : ℕ → ℤ) (vars : ℕ → ℤ) :
    Expr → Option (ℤ × Finset ℕ)
  | .const c => do
      let z ← word wordMax c
      some (z, ∅)
  | .var i => do
      let z ← word wordMax (vars i)
      some (z, ∅)
  | .read a => do
      let (x, r) ← eval wordMax ω σ vars a
      let k ← addr wordMax x
      let z ← word wordMax (σ k)
      some (z, insert k r)
  | .coin a => do
      let (x, r) ← eval wordMax ω σ vars a
      let k ← addr wordMax x
      some (if ω k then 1 else 0, r)
  | .add a b => do
      let (x, r) ← eval wordMax ω σ vars a
      let (y, r') ← eval wordMax ω σ vars b
      let z ← word wordMax (x + y)
      some (z, r ∪ r')
  | .sub a b => do
      let (x, r) ← eval wordMax ω σ vars a
      let (y, r') ← eval wordMax ω σ vars b
      let z ← word wordMax (x - y)
      some (z, r ∪ r')
  | .mul a b => do
      let (x, r) ← eval wordMax ω σ vars a
      let (y, r') ← eval wordMax ω σ vars b
      let z ← word wordMax (x * y)
      some (z, r ∪ r')
  | .div a b => do
      let (x, r) ← eval wordMax ω σ vars a
      let (y, r') ← eval wordMax ω σ vars b
      let z ← word wordMax (x / y)
      some (z, r ∪ r')
  | .lt a b => do
      let (x, r) ← eval wordMax ω σ vars a
      let (y, r') ← eval wordMax ω σ vars b
      some (if x < y then 1 else 0, r ∪ r')
  | .le a b => do
      let (x, r) ← eval wordMax ω σ vars a
      let (y, r') ← eval wordMax ω σ vars b
      some (if x ≤ y then 1 else 0, r ∪ r')
  | .eq a b => do
      let (x, r) ← eval wordMax ω σ vars a
      let (y, r') ← eval wordMax ω σ vars b
      some (if x = y then 1 else 0, r ∪ r')

/-- Evaluate a list of expressions. -/
def evalList (wordMax : ℕ) (ω : ℕ → Bool) (σ : ℕ → ℤ) (vars : ℕ → ℤ) :
    List Expr → Option (List ℤ × Finset ℕ)
  | [] => some ([], ∅)
  | e :: es => do
      let (x, r) ← eval wordMax ω σ vars e
      let (xs, r') ← evalList wordMax ω σ vars es
      some (x :: xs, r ∪ r')

/-- The register frame of a call: argument `i` in register `i`, all others `0`. -/
def frame (args : List ℤ) : ℕ → ℤ := fun i => args.getD i 0

/-- Operational semantics with random tape `ω`; `fuel` bounds the nesting of statement executions
(recursion included), and `none` means that the fuel ran out or the program is stuck (an oversized
word, a bad address, an unknown procedure, or interfering parallel threads).

Costs (unit cost per basic operation): every basic statement, test, fork and call costs one step.
Sequencing adds work and depth. `parFor` charges one step plus the sum of the threads' work, and
one step plus the largest depth of a thread. -/
def run (wordMax : ℕ) (ω : ℕ → Bool) (P : Program) :
    ℕ → Stmt → (ℕ → ℤ) → (ℕ → ℤ) → Option Outcome
  | 0, _, _, _ => none
  | _ + 1, .skip, σ, vars => some ⟨σ, vars, ∅, ∅, 1, 1⟩
  | _ + 1, .setVar i e, σ, vars => do
      let (x, r) ← eval wordMax ω σ vars e
      some ⟨σ, Function.update vars i x, r, ∅, 1, 1⟩
  | _ + 1, .write a e, σ, vars => do
      let (x, r) ← eval wordMax ω σ vars a
      let (y, r') ← eval wordMax ω σ vars e
      let k ← addr wordMax x
      some ⟨Function.update σ k y, vars, r ∪ r', {k}, 1, 1⟩
  | fuel + 1, .seq s t, σ, vars => do
      let o ← run wordMax ω P fuel s σ vars
      let o' ← run wordMax ω P fuel t o.mem o.vars
      some ⟨o'.mem, o'.vars, o.reads ∪ o'.reads, o.writes ∪ o'.writes,
        o.work + o'.work, o.depth + o'.depth⟩
  | fuel + 1, .ite c s t, σ, vars => do
      let (x, r) ← eval wordMax ω σ vars c
      let o ← run wordMax ω P fuel (if x ≠ 0 then s else t) σ vars
      some ⟨o.mem, o.vars, r ∪ o.reads, o.writes, o.work + 1, o.depth + 1⟩
  | fuel + 1, .parFor i lo hi body, σ, vars => do
      let (a, r) ← eval wordMax ω σ vars lo
      let (b, r') ← eval wordMax ω σ vars hi
      let outs ← (List.range (b - a).toNat).mapM fun k =>
        run wordMax ω P fuel body σ (Function.update vars i (a + k))
      if outs.Pairwise Compatible then
        some ⟨outs.foldl (fun τ o => overlay τ o.mem o.writes) σ, vars,
          outs.foldl (fun w o => w ∪ o.reads) (r ∪ r'),
          outs.foldl (fun w o => w ∪ o.writes) ∅,
          (outs.map Outcome.work).sum + 1,
          (outs.map Outcome.depth).foldr max 0 + 1⟩
      else none
  | fuel + 1, .call f args, σ, vars => do
      let (xs, r) ← evalList wordMax ω σ vars args
      let body ← P[f]?
      let o ← run wordMax ω P fuel body σ (frame xs)
      some ⟨o.mem, vars, r ∪ o.reads, o.writes, o.work + 1, o.depth + 1⟩

/-- The entry procedure `0` of `P`, started on memory `σ` with all registers `0`, halts with
outcome `o` (for some sufficient fuel; fuel plays no role in costs or results). -/
def Halts (wordMax : ℕ) (ω : ℕ → Bool) (P : Program) (σ : ℕ → ℤ) (o : Outcome) : Prop :=
  ∃ fuel : ℕ, ∃ body : Stmt, P[0]? = some body ∧ run wordMax ω P fuel body σ (frame []) = some o

/-- The random tape: independent fair bits. -/
def coinLaw : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

/-- An input of the parallel problem: an undirected simple graph on `Fin n` (connectivity not
required) with positive integer weights at most `n^q`, presented as an edge list
`(u_i, v_i, w_i)`, `i < m`, listing every edge exactly once in an arbitrary order and orientation. -/
structure WDInstance (n q : ℕ) where
  W : WGraph (Fin n)
  weight : Fin n → Fin n → ℕ
  weight_eq : ∀ u v, W.graph.Adj u v → W.length u v = (weight u v : ℝ)
  weight_pos : ∀ u v, W.graph.Adj u v → 0 < weight u v
  weight_bound : ∀ u v, W.graph.Adj u v → weight u v ≤ n ^ q
  m : ℕ
  ends : Fin m → Fin n × Fin n
  ends_adj : ∀ i, W.graph.Adj (ends i).1 (ends i).2
  ends_injective : ∀ i j, s((ends i).1, (ends i).2) = s((ends j).1, (ends j).2) → i = j
  ends_surjective : ∀ u v, W.graph.Adj u v → ∃ i, s((ends i).1, (ends i).2) = s(u, v)

/-- The unordered edge number `i`. -/
def WDInstance.edge {n q : ℕ} (I : WDInstance n q) (i : Fin I.m) : Sym2 (Fin n) :=
  s((I.ends i).1, (I.ends i).2)

/-- Initial shared memory: cell `0` holds `n`, cell `1` holds `m`, and cells `2 + 3i`, `3 + 3i`,
`4 + 3i` hold `u_i`, `v_i`, `w(u_i, v_i)` for `i < m`; all other cells are `0`. -/
def WDInstance.initMem {n q : ℕ} (I : WDInstance n q) : ℕ → ℤ := fun a =>
  if a = 0 then (n : ℤ) else if a = 1 then (I.m : ℤ) else
  if h : 2 ≤ a ∧ a < 2 + 3 * I.m then
    let i : Fin I.m := ⟨(a - 2) / 3, by omega⟩
    if (a - 2) % 3 = 0 then ((I.ends i).1.val : ℤ)
    else if (a - 2) % 3 = 1 then ((I.ends i).2.val : ℤ)
    else (I.weight (I.ends i).1 (I.ends i).2 : ℤ)
  else 0

/-- Output convention of Definition 1.1 in shared memory (the computation is centralized, PDF
p. 31): cell `2 + 3m` is `1`, cell `3 + 3m` is the actual weight `w(C)` of a simple cycle `C` with
`w(C) ≤ ratio · OPT`, and cell `4 + 3m + i` is `1` if edge `i` belongs to `C` and `0` otherwise;
on an acyclic input, cell `2 + 3m` is `0` and every membership cell is `0`. -/
def WDCorrect {n q : ℕ} (I : WDInstance n q) (σ : ℕ → ℤ) (ratio : ℝ) : Prop :=
  (∃ C : Cycle I.W, ENNReal.ofReal C.weight ≤ ENNReal.ofReal ratio * optimum I.W ∧
    σ (2 + 3 * I.m) = 1 ∧ (σ (3 + 3 * I.m) : ℝ) = C.weight ∧
    ∀ i : Fin I.m, σ (4 + 3 * I.m + i.val) = if I.edge i ∈ C.walk.edges then 1 else 0) ∨
  (IsEmpty (Cycle I.W) ∧ σ (2 + 3 * I.m) = 0 ∧ ∀ i : Fin I.m, σ (4 + 3 * I.m + i.val) = 0)

/-- Success: with words bounded by `(max 2 n)^B`, the program halts with work at most `workBudget`,
depth at most `depthBudget`, and a correct `ratio`-approximate output. -/
def WDEvent {n q : ℕ} (I : WDInstance n q) (P : Program) (B : ℕ) (ratio workBudget depthBudget : ℝ) :
    Set (ℕ → Bool) :=
  {ω | ∃ o : Outcome, Halts ((max 2 n) ^ B) ω P I.initMem o ∧
    (o.work : ℝ) ≤ workBudget ∧ (o.depth : ℝ) ≤ depthBudget ∧ WDCorrect I o.mem ratio}

/-- Theorem 3's claim for weight exponent `q`, quantified as the base `Tradeoff`: for every
confidence exponent there are one word exponent and one soft-O constant pair, uniform in real
`k ≥ 1`, and for each `k` one program such that on every input with `n ≥ max 2 n₀` vertices and
`m` edges, with probability at least `1 - n^(-confidence)` the program halts with work at most
`C (log n)^p (m + 1) n^(1/k)`, depth at most `C (log n)^p`, and a correct `(k+1)`-approximate
output. -/
def WDTradeoff (q : ℕ) : Prop :=
  ∀ confidence : ℝ, 0 < confidence →
  ∃ (B p n₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ k : ℝ, 1 ≤ k →
    ∃ P : Program, ∀ n ≥ max 2 n₀, ∀ I : WDInstance n q,
      (let work := C * (Real.log n) ^ p * ((I.m : ℝ) + 1) * (n : ℝ) ^ (1 / k)
       let depth := C * (Real.log n) ^ p
       MeasurableSet (WDEvent I P B (k + 1) work depth) ∧
       ENNReal.ofReal (1 - (n : ℝ) ^ (-confidence)) ≤ coinLaw (WDEvent I P B (k + 1) work depth))

end DistributedMWC440.UpperBound.Supplement


