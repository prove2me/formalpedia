-- Prove2me | Definitions.Def_SivanLPTensor_Recovery_algebraicMachine
-- name    : SivanLPTensor_Recovery_algebraicMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T05:31:00.081328+00:00
-- url     : https://prove2.me/theorems/bcbe25fb-1a8d-4f4c-ab10-99fe83fd66c9
-- title:
--   Finite randomized real-algebraic programs and executed cost
-- statement:
--   A program is a finite list of scalar instructions. Real instructions load rational constants or input entries, copy registers, perform field operations, find all distinct real roots of a univariate polynomial, draw the next real sample, test zero, and branch or halt. Natural registers provide addresses, dimensions and loop counters; they cannot read a real as an integer. There is no factorization, inverse, eigenspace, tensor-rank, or arbitrary-function instruction.
--   Execution starts with zero registers and is defined transition by transition. Arithmetic and zero tests increment an operation counter. Each root instruction records its requested coefficient degree. Given a fixed root-cost function $q$, its executed cost is
--   $$\text{arithmetic count}+\sum_{\text{executed root calls}}q(\text{degree}).$$
--   The model admits $q$ bounded by one polynomial in degree. Copies, constant writes and address operations do not count as real arithmetic. Division by zero halts; zero-polynomial root finding returns an empty list. A seed law must be a probability measure and have absolutely continuous finite-coordinate marginals. Measurability of the success set and its measure one are required in the recovery predicate.
--   One finite program and its polynomial bound precede every tensor dimension, hidden factor family and sampling law. Output equivalence uses the general CP definition. The input contains only dimensions and dense tensor entries; no correctness or runtime field is assumed.
-- source:
--   Shiri Sivan, STOC 2027 submission #1294 (October 2026), Computational model, printed p. 2 / PDF p. 4; Algorithm 1 and complexity proof, printed pp. 7–9 / PDF pp. 9–11

import Definitions.Def_SivanLPTensor_Recovery_tensorModel

noncomputable section

namespace SivanLPTensor.Recovery
open scoped BigOperators
open MeasureTheory Classical

/-- Natural registers are for addressing and dimensions only. -/
inductive Address where
  | literal : ℕ → Address
  | register : ℕ → Address
  | add : Address → Address → Address
  | sub : Address → Address → Address
  | mul : Address → Address → Address
  | div : Address → Address → Address
  | mod : Address → Address → Address
  | dimension : Address → Address
  | modes : Address

inductive FieldOp where
  | add | sub | mul | div

def FieldOp.eval : FieldOp → ℝ → ℝ → ℝ
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)
  | .div => (· / ·)

/-- Every real operation is an explicit scalar instruction. Roots read a coefficient array;
there is no tensor decomposition, inverse, eigenspace, or arbitrary-function instruction. -/
inductive Instruction where
  | natural : ℕ → Address → Instruction
  | constant : Address → ℚ → Instruction
  | copy : Address → Address → Instruction
  | input : Address → Address → Instruction
  | field : FieldOp → Address → Address → Address → Instruction
  | roots : Address → Address → Address → ℕ → Instruction
  | random : Address → Instruction
  | branchZero : Address → ℕ → ℕ → Instruction
  | branchLess : Address → Address → ℕ → ℕ → Instruction
  | jump : ℕ → Instruction
  | halt : Instruction

abbrev Program := List Instruction

structure MachineState where
  pc : ℕ := 0
  natural : ℕ → ℕ := fun _ => 0
  real : ℕ → ℝ := fun _ => 0
  randomCursor : ℕ := 0
  arithmetic : ℕ := 0
  rootDegrees : List ℕ := []
  stopped : Bool := false

structure MachineInput where
  modes : ℕ
  dimensions : ℕ → ℕ
  entries : ℕ → ℝ

def Address.eval (a : Address) (x : MachineInput) (s : MachineState) : ℕ :=
  match a with
  | .literal k => k
  | .register k => s.natural k
  | .add b c => b.eval x s + c.eval x s
  | .sub b c => b.eval x s - c.eval x s
  | .mul b c => b.eval x s * c.eval x s
  | .div b c => b.eval x s / c.eval x s
  | .mod b c => b.eval x s % c.eval x s
  | .dimension b => x.dimensions (b.eval x s)
  | .modes => x.modes

/-- The allowed exact-root primitive returns all distinct real roots, in increasing order.
The zero polynomial returns an empty list, rather than requesting infinitely many roots. -/
def realRoots (coeff : List ℝ) : List ℝ :=
  let p : Polynomial ℝ := (coeff.zipIdx).foldl
    (fun q ci => q + Polynomial.C ci.1 * Polynomial.X ^ ci.2) 0
  p.roots.toFinset.sort (· ≤ ·)

def machineStep (p : Program) (x : MachineInput) (seed : ℕ → ℝ)
    (s : MachineState) : MachineState := Id.run do
  if s.stopped then return s
  let a := fun e : Address => e.eval x s
  let r := fun e : Address => s.real (a e)
  let next := { s with pc := s.pc + 1 }
  match p[s.pc]?.getD .halt with
  | .natural k e => return { next with natural := Function.update s.natural k (a e) }
  | .constant dst c => return { next with real := Function.update s.real (a dst) c }
  | .copy dst src => return { next with real := Function.update s.real (a dst) (r src) }
  | .input dst src => return { next with real := Function.update s.real (a dst) (x.entries (a src)) }
  | .field op dst u v =>
      if (match op with | .div => r v = 0 | _ => False) then
        return { next with stopped := true, arithmetic := s.arithmetic + 1 }
      return { next with
        real := Function.update s.real (a dst) (op.eval (r u) (r v))
        arithmetic := s.arithmetic + 1 }
  | .roots start degree dst count =>
      let cs := (List.range (a degree + 1)).map (fun i => s.real (a start + i))
      let rs := realRoots cs
      return { next with
        real := fun k => if a dst ≤ k ∧ k < a dst + rs.length then rs[k - a dst]! else s.real k
        natural := Function.update s.natural count rs.length
        rootDegrees := (a degree) :: s.rootDegrees }
  | .random dst => return { next with
      real := Function.update s.real (a dst) (seed s.randomCursor)
      randomCursor := s.randomCursor + 1 }
  | .branchZero u yes no => return { s with
      pc := if r u = 0 then yes else no
      arithmetic := s.arithmetic + 1 }
  | .branchLess u v yes no => return { s with pc := if a u < a v then yes else no }
  | .jump target => return { s with pc := target }
  | .halt => return { s with stopped := true }

def machineRun (p : Program) (x : MachineInput) (seed : ℕ → ℝ) : ℕ → MachineState
  | 0 => {}
  | t + 1 => machineStep p x seed (machineRun p x seed t)

/-- A root implementation is charged by one fixed polynomial in the requested degree. -/
def executionCost (rootCost : ℕ → ℕ) (s : MachineState) : ℕ :=
  s.arithmetic + (s.rootDegrees.map rootCost).sum

def PolynomialRootCost (q : ℕ → ℕ) : Prop :=
  ∃ C k : ℕ, 0 < C ∧ ∀ degree, 1 ≤ q degree ∧ q degree ≤ C * (degree + 1) ^ k

def encodeInput {m : ℕ} {n : Fin m → ℕ} (T : Tensor n) : MachineInput :=
  { modes := m
    dimensions := fun j => if h : j < m then n ⟨j,h⟩ else 0
    entries := fun t => if h : ∀ j, 0 < n j then
      if t < inputSize n then
        T (fun j => ⟨(t / (∏ k ∈ Finset.univ.filter (fun k : Fin m => k < j), n k)) % n j,
          Nat.mod_lt _ (h j)⟩) else 0
      else 0 }


/-- Output length is natural register zero. Factors occupy real memory from address zero,
in mode, component, coordinate order. Positive-r success uses natural register one = 1. -/
def outputFactors {m : ℕ} {n : Fin m → ℕ} (s : MachineState) : Factors n (s.natural 0) :=
  fun j i x => s.real ((∑ k ∈ Finset.univ.filter (fun k : Fin m => k < j), n k) * s.natural 0 +
    i.val * n j + x.val)

def successful {m r : ℕ} {n : Fin m → ℕ} (a : Factors n r) (s : MachineState) : Prop :=
  s.stopped = true ∧ s.natural 1 = 1 ∧ Equivalent a (outputFactors (n := n) s)

/-- A normalized seed law with absolutely continuous finite-dimensional marginals.
This includes conditional continuous draws; it never assigns volume to an infinite space. -/
def AdmissibleSeedLaw (μ : Measure (ℕ → ℝ)) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ k : ℕ,
    Measure.map (fun seed : ℕ → ℝ => fun t : Fin k => seed t.val) μ ≪ volume

/-- Uniform polynomial cost, on every branch, and measurable probability-one exact recovery.
The program and polynomial are outside all dimensions, hidden factors and sampling laws. -/
def RecoversUniformly (p : Program) (q : ℕ → ℕ) (C k : ℕ) : Prop :=
  0 < C ∧ ∀ (m : ℕ) (n : Fin m → ℕ), 3 ≤ m → (∀ j, 0 < n j) →
    ∀ (r : ℕ) (a : Factors n r), 0 < r → NonzeroFactors a → LP a →
      (∀ seed, ∃ t, (machineRun p (encodeInput (synthesis a)) seed t).stopped = true ∧
        executionCost q (machineRun p (encodeInput (synthesis a)) seed t) ≤
          C * (inputSize n + 1) ^ k) ∧
      ∀ μ : Measure (ℕ → ℝ), AdmissibleSeedLaw μ →
        MeasurableSet { seed | ∃ t, successful a (machineRun p (encodeInput (synthesis a)) seed t) } ∧
        μ { seed | ∃ t, successful a (machineRun p (encodeInput (synthesis a)) seed t) } = 1

end SivanLPTensor.Recovery


