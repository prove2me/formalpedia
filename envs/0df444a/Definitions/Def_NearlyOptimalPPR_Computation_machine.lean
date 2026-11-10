-- Prove2me | Definitions.Def_NearlyOptimalPPR_Computation_machine
-- name    : NearlyOptimalPPR_Computation_machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T06:35:24.136294+00:00
-- url     : https://prove2.me/theorems/6258a43c-d667-4b82-8b52-7e8229ad2375
-- title:
--   Charged scalar/query machine with an exact SDDM primitive
-- statement:
--   Fix primitive constants $C_s>0$ and $p_s\in\mathbb N$. An SDDM matrix is symmetric positive definite and diagonally dominant, with nonpositive off-diagonal entries. Symmetry and diagonal dominance reuse the published predicate without adding a graph assumption.
--
--   Programs are finite lists extending the published randomized scalar/pointer/adjacency-query machine with two operations. An exact solve reads a supplied sparse matrix and right-hand side from memory and writes its exact solution. For dimension $k>0$ and supplied sparse length $q\ge0$, its charge is
--
--   $$1+C_s(k+q)(1+\log(2+k+q))^{p_s}.$$
--
--   It reads no graph data. Preparing the matrix, fetching graph rows, and propagating boundary flow require ordinary instructions. Invalid solve requests are stuck and charged. An emit instruction appends one labeled scalar to the explicit output, for one unit of work. All scalar instructions, including degree/neighbor queries, cost one unit. Every real program literal must be rational. No instruction carries an arbitrary function, logarithm, floor, square root, or PPR computation. The constant-size input contains only $s,\alpha,\varepsilon$; it contains no adjacency lists or graph size.
--
--   Work is a nonnegative extended real, with nontermination assigned $+\infty$. Its expectation is the nonnegative integral over independent fair coin tapes. Success is a conclusion requiring almost-sure halting, ACL accuracy, nonnegative output, and exact $e_s$ output for an isolated seed.
--
--   The explicit-output lower-bound predicate fixes $0<\alpha<1$, writes $\beta=(1-\alpha)/(2-\alpha)$, and, for $0<\varepsilon\le\beta/4$, takes $L=\lfloor\beta/(2\varepsilon)\rfloor$. It asserts the exact star PPR formula, $L\ge\beta/(4\varepsilon)\ge1$, and that every accurate sparse output has leaf estimates at least $\varepsilon$ and at least $\beta/(4\varepsilon)$ entries. Thus this predicate has no assumed formula for an unrelated vector.
--
--   This is an idealized exact-solve model, not a theorem about finite-precision SDDM solvers.
--
--   Differences from the source:
--   - reading: arithmetic and adjacency-list work with exact solves charged nearly linearly in volume → a finite rational-constant scalar/query program with a sparse-memory exact-solve extension and charged emits; reason: the source does not name an instruction set; matrix assembly and output cannot compute for free
--   - encoding: fixed O-tilde(vol T) exact principal-system charge → a fixed deterministic polynomial-logarithmic charge in supplied sparse length plus dimension; reason: principal graph systems have this size O(vol T); the deterministic charge is the idealized primitive work and introduces no alpha or graph-size factor
--   - encoding: expected work → ENNReal work and nonnegative expectation, with infinite work for nontermination; reason: unbounded or nonintegrable work cannot default to zero
-- source:
--   Rong-Hua Li, Quanqing Xu, Yichun Yang, Junjie Zhou, STOC 2027 submission #884 (October 2026), §2 p.4 and explicit-output paragraph p.2

import Mathlib
import Definitions.Def_LocalPush_Machine
import Definitions.Def_LocalPush_SDD
import Definitions.Def_NearlyOptimalPPR_Computation_model

set_option autoImplicit false

open Finset Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace NearlyOptimalPPR.Computation

/-! The exact-SDDM computational convention of §2 p.4, made explicit.
Only scalar/query instructions access the input graph. The additional solver
reads a sparse matrix and right-hand side already prepared in machine memory.
It does not read the graph, build a principal matrix, or propagate boundary flow.
Those operations must be programmed and paid for. -/

/-- Fixed primitive constants, chosen before graph size, alpha and epsilon. -/
structure SolveModel where
  constant : ℝ
  positive : 0 < constant
  logPower : ℕ

/-- A deterministic charge for the idealized exact primitive. The size is the
supplied sparse representation length plus its dimension, not a declared graph
volume which could be underreported. This is O-tilde(vol T) for principal graph
systems; scalar system assembly and boundary propagation are separate work. -/
def solveCharge (m : SolveModel) (k q : ℕ) : ℝ≥0∞ :=
  1 + ENNReal.ofReal (m.constant * (k + q : ℝ) *
    (1 + Real.log (2 + (k + q : ℝ))) ^ m.logPower)

/-- The source's definition of SDDM, without an accuracy or conditioning input. -/
def SDDM {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  A.PosDef ∧ LocalPush.IsSDD A ∧ ∀ i j, i ≠ j → A i j ≤ 0

/-- Registers naming the dimension, sparse length, row/column/value arrays,
right-hand side and answer arrays. All addresses are integer pointers. -/
structure SolveRegisters where
  dimension : ℕ
  length : ℕ
  rows : ℕ
  columns : ℕ
  values : ℕ
  rhs : ℕ
  answer : ℕ

inductive Instruction where
  | scalar (i : LocalPush.Instr)
  | solve (r : SolveRegisters)
  | emit (nodePointer valueRegister : ℕ)

abbrev Program := List Instruction

def scalarProgram (p : Program) : LocalPush.Program :=
  p.map fun i => match i with
    | .scalar s => s
    | _ => .core (.const 0 0)

def admissible (p : Program) : Prop := LocalPush.Admissible (scalarProgram p)

structure MachineState where
  scalar : LocalPush.State
  output : SparseOutput
  work : ℝ≥0∞

/-- Decode exactly the supplied sparse entries. Repeated coordinates add, and
invalid row/column labels contribute nothing. No graph-dependent data is read. -/
def suppliedMatrix (st : LocalPush.State) (r : SolveRegisters) (k q : ℕ) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun u v => ∑ a ∈ Finset.range q,
    if st.integerMemory (st.core.ptrs r.rows + a) = (u.val : ℤ) ∧
        st.integerMemory (st.core.ptrs r.columns + a) = (v.val : ℤ)
    then st.core.mem (st.core.ptrs r.values + a) else 0

/-- Write k exact answers. The charge includes k; no free dense output readout
is available, since final output consists only of executed emit instructions. -/
def writeAnswer (st : LocalPush.State) (r : SolveRegisters) (k : ℕ)
    (x : Fin k → ℝ) : LocalPush.State :=
  { st with core := { st.core with
      pc := st.core.pc + 1
      mem := fun a =>
        if h : 0 ≤ a - st.core.ptrs r.answer ∧
            (a - st.core.ptrs r.answer).toNat < k then
          x ⟨(a - st.core.ptrs r.answer).toNat, h.2⟩
        else st.core.mem a } }

/-- One executed instruction. An invalid program counter or invalid solve is
stuck and charged. A halt stutters; no instruction computes a logarithm, floor,
square root, graph-dependent function, or PPR vector. -/
def machineStep (m : SolveModel) (p : Program) {n : ℕ}
    (g : InputGraph n) (ω : ℕ → Bool) (st : MachineState) : MachineState := by
  classical
  exact if st.scalar.halted then st else
    match p[st.scalar.core.pc]? with
    | none => { st with work := st.work + 1 }
    | some (.scalar _) =>
        { st with scalar := LocalPush.step (scalarProgram p) g.neighbors ω st.scalar
                  work := st.work + 1 }
    | some (.emit a b) =>
        { st with scalar := { st.scalar with core := { st.scalar.core with pc := st.scalar.core.pc + 1 } }
                  output := st.output ++ [(st.scalar.core.ptrs a, st.scalar.core.regs b)]
                  work := st.work + 1 }
    | some (.solve r) =>
        let k := (st.scalar.core.ptrs r.dimension).toNat
        let q := (st.scalar.core.ptrs r.length).toNat
        let A := suppliedMatrix st.scalar r k q
        if 0 < st.scalar.core.ptrs r.dimension ∧ 0 ≤ st.scalar.core.ptrs r.length ∧ SDDM A then
          let b : Fin k → ℝ := fun i => st.scalar.core.mem (st.scalar.core.ptrs r.rhs + i.val)
          { st with scalar := writeAnswer st.scalar r k (A⁻¹ *ᵥ b)
                    work := st.work + solveCharge m k q }
        else { st with work := st.work + 1 }

/-- Constant-size input layout: s in integer memory cell 0;
alpha and epsilon in real memory cells 0 and 1. Graph access is by queries. -/
def machineInit {n : ℕ} (s : Fin n) (α ε : ℝ) : MachineState :=
  ⟨LocalPush.initState [(s.val : ℤ)] [α, ε], [], 0⟩

def machineRun (m : SolveModel) (p : Program) {n : ℕ}
    (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ω : ℕ → Bool) (t : ℕ) : MachineState :=
  (machineStep m p g ω)^[t] (machineInit s α ε)

/-- Nontermination has infinite work. The supremum is taken in ENNReal, so
neither unbounded runs nor empty real suprema can silently become zero. -/
def executionWork (m : SolveModel) (p : Program) {n : ℕ}
    (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ω : ℕ → Bool) : ℝ≥0∞ := by
  classical
  exact if ∃ t, (machineRun m p g s α ε ω t).scalar.halted = true then
    ⨆ t, (machineRun m p g s α ε ω t).work
  else ⊤

def expectedWork (m : SolveModel) (p : Program) {n : ℕ}
    (g : InputGraph n) (s : Fin n) (α ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, executionWork m p g s α ε ω ∂LocalPush.coinTape

/-- This is a desired conclusion, never an admissibility condition on programs. -/
def successful (m : SolveModel) (p : Program) {n : ℕ}
    (g : InputGraph n) (s : Fin n) (α ε : ℝ) : Prop :=
  ∀ᵐ ω ∂LocalPush.coinTape, ∃ t,
    (machineRun m p g s α ε ω t).scalar.halted = true ∧
    ACL g.graph α ε s (outputVector (machineRun m p g s α ε ω t).output) ∧
    (∀ v : Fin n, 0 ≤ outputVector (machineRun m p g s α ε ω t).output v) ∧
    (g.graph.degree s = 0 →
      outputVector (machineRun m p g s α ε ω t).output = LocalPush.e s)

/-- Explicit-output part of Theorem 1.2, §1 p.2, with the star family made
quantitative. This statement concerns arbitrary estimates, including negative
ones, with no residual-representation assumption. -/
def explicitOutputLowerBound : Prop := by
  classical
  exact ∀ α : ℝ, 0 < α → α < 1 →
    let β := (1 - α) / (2 - α)
    ∀ ε : ℝ, 0 < ε → ε ≤ β / 4 →
      let L := ⌊β / (2 * ε)⌋₊
      1 ≤ L ∧ β / (4 * ε) ≤ (L : ℝ) ∧
      (∀ v : Fin (L + 1), ppr (star L) α ⟨0, Nat.zero_lt_succ L⟩ v =
        if v.val = 0 then 1 / (2 - α) else β / (L : ℝ)) ∧
      ∀ o : SparseOutput,
        ACL (star L) α ε ⟨0, Nat.zero_lt_succ L⟩ (outputVector o) →
        (∀ v : Fin (L + 1), v.val ≠ 0 → ε ≤ outputVector o v) ∧
        β / (4 * ε) ≤ (o.length : ℝ)

end NearlyOptimalPPR.Computation


