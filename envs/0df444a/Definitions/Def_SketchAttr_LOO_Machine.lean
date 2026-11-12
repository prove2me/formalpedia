-- Prove2me | Definitions.Def_SketchAttr_LOO_Machine
-- name    : SketchAttr_LOO_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:25:38.940241+00:00
-- url     : https://prove2.me/theorems/5f1af7d8-5c50-4c9d-b489-ff02c7000adf
-- title:
--   Section 3.2 — complex arithmetic RAM with counted call implementation
-- statement:
--   A finite **program** operates on natural registers, complex registers, and random-access memory, with a program counter and exact scalar cells. Natural instructions are constants, addition, truncated subtraction, indirect load/store and comparison branches. Complex instructions are literal constants, arithmetic, conjugation, real and imaginary parts, real square root, comparison branches and root-of-unity twiddle factors. The main program may sample the next Gaussian tape cell or invoke the call program; the call program may do neither.
--
--   One transition executes one instruction. Calls enter the second finite program and count every instruction until it returns. Main and call programs have private work memory and separate read-only inputs, plus a query/answer buffer. The call program can write only the prescribed complex answer segment. The main program never receives the circuit encoding. Neither program has a gradient or function-evaluation primitive, a logarithm instruction, a floor instruction, or natural multiplication.
--
--   Auxiliary space is
--   $$\#\{\text{distinct register and mutable-memory cells written}\}+8,$$
--   where the fixed eight cells cover counters and control state. Writes by both programs remain in the same cumulative set, so repeated calls cannot hide their memory costs. Invalid instructions, writes to input, nested calls and call-side sampling fault and cannot satisfy the goal.
--
--   This operational reading of the paper's exact complex arithmetic model makes work and space claims mathematical statements about executions. Default division and square root values are Lean's total scalar operations; correctness of the programs must account for them.
-- source:
--   Liaw, Mehta, Velegkas, Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2), p. 9, Section 3.2 computation convention; pp. 16, 18–19, Algorithm 1, complexity and oracle access; canonical PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/9.pdf

import Mathlib

namespace SketchAttr.LOO

/-- Input is read-only and private to each program. Work is private; shared
memory is the explicit query/answer buffer. All memory accesses use registers. -/
inductive Bank where
  | input | work | shared
  deriving DecidableEq

inductive NatOp where | add | sub
inductive ComplexOp where | add | sub | mul | div
inductive ComplexUnary where | conj | re | im | sqrt

/-- Literal values belong to the finite program; they cannot depend on its input. -/
inductive Instruction where
  | natConst (dst value : ℕ)
  | natBin (op : NatOp) (dst x y : ℕ)
  | natLoad (bank : Bank) (dst address : ℕ)
  | natStore (bank : Bank) (address src : ℕ)
  | natBranch (x y yes no : ℕ)
  | complexConst (dst : ℕ) (literal : ℂ)
  | complexBin (op : ComplexOp) (dst x y : ℕ)
  | complexUnary (op : ComplexUnary) (dst src : ℕ)
  | twiddle (dst denominator : ℕ)
  | complexLoad (bank : Bank) (dst address : ℕ)
  | complexStore (bank : Bank) (address src : ℕ)
  | realBranch (x y yes no : ℕ)
  | sample (dst : ℕ)
  | call
  | halt

abbrev Program := List Instruction
abbrev Cell := ℕ × ℕ × ℕ

structure MachineInput where
  naturals : Bool → ℕ → ℕ
  complexes : Bool → ℕ → ℂ

/-- False is the main program, true the implementation of a call.
The set of written cells counts registers as well as all mutable memory.
Program counters, flags and tape position contribute a fixed number of cells. -/
structure MachineState where
  inCall : Bool := false
  pc : Bool → ℕ := fun _ => 0
  nr : Bool → ℕ → ℕ := fun _ _ => 0
  cr : Bool → ℕ → ℂ := fun _ _ => 0
  nm : ℕ → ℕ → ℕ := fun _ _ => 0
  cm : ℕ → ℕ → ℂ := fun _ _ => 0
  cursor : ℕ := 0
  calls : ℕ := 0
  halted : Bool := false
  fault : Bool := false
  written : Finset Cell := ∅

namespace MachineState

def role (s : MachineState) : ℕ := if s.inCall then 1 else 0

def bankIndex (s : MachineState) (b : Bank) : ℕ :=
  if b = .shared then 2 else s.role

noncomputable def putNat (s : MachineState) (d v : ℕ) : MachineState :=
  {s with
    nr := Function.update s.nr s.inCall (Function.update (s.nr s.inCall) d v)
    written := insert (0, s.role, d) s.written}

noncomputable def putComplex (s : MachineState) (d : ℕ) (v : ℂ) : MachineState :=
  {s with
    cr := Function.update s.cr s.inCall (Function.update (s.cr s.inCall) d v)
    written := insert (1, s.role, d) s.written}

def space (s : MachineState) : ℕ := s.written.card + 8

end MachineState

/-- S may read the shared query but can only write the response segment:
complex cells [2n, 2n+1+n*(degree+1)), where n is its input header.
S cannot write shared natural cells. This prevents circuit leakage through
side-channel cells in addition to the specified oracle answer.
One transition is one instruction. Calls enter the second program, whose
instructions are subsequently charged one by one; no oracle is executed here. -/
noncomputable def machineStep (M S : Program) (input : MachineInput) (tape : ℕ → ℂ)
    (s : MachineState) : MachineState := by
  classical
  let b := s.inCall
  let nr := s.nr b
  let cr := s.cr b
  let next := {s with pc := Function.update s.pc b (s.pc b + 1)}
  let fail := {s with halted := true, fault := true}
  let p := if b then S else M
  exact if s.halted then s else
    match p[s.pc b]? with
    | none => fail
    | some (.natConst d v) => next.putNat d v
    | some (.natBin op d x y) => next.putNat d (match op with
        | .add => nr x + nr y | .sub => nr x - nr y)
    | some (.natLoad bank d a) => next.putNat d
        (if bank = .input then input.naturals b (nr a) else s.nm (s.bankIndex bank) (nr a))
    | some (.natStore bank a x) => if bank = .input ∨ (b = true ∧ bank = .shared) then fail else
        {next with
          nm := Function.update s.nm (s.bankIndex bank)
            (Function.update (s.nm (s.bankIndex bank)) (nr a) (nr x))
          written := insert (2, s.bankIndex bank, nr a) s.written}
    | some (.natBranch x y yes no) =>
        {s with pc := Function.update s.pc b (if nr x ≤ nr y then yes else no)}
    | some (.complexConst d z) => next.putComplex d z
    | some (.complexBin op d x y) => next.putComplex d (match op with
        | .add => cr x + cr y | .sub => cr x - cr y
        | .mul => cr x * cr y | .div => cr x / cr y)
    | some (.complexUnary op d x) => next.putComplex d (match op with
        | .conj => starRingEnd ℂ (cr x) | .re => (cr x).re
        | .im => (cr x).im | .sqrt => Real.sqrt (cr x).re)
    | some (.twiddle d t) => next.putComplex d
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (nr t : ℂ)))
    | some (.complexLoad bank d a) => next.putComplex d
        (if bank = .input then input.complexes b (nr a) else s.cm (s.bankIndex bank) (nr a))
    | some (.complexStore bank a x) => if bank = .input ∨
        (b = true ∧ bank = .shared ∧ ¬ (2 * input.naturals true 0 ≤ nr a ∧
          nr a < 2 * input.naturals true 0 + 1 + input.naturals true 0 * (s.nm 2 0 + 1)))
        then fail else
        {next with
          cm := Function.update s.cm (s.bankIndex bank)
            (Function.update (s.cm (s.bankIndex bank)) (nr a) (cr x))
          written := insert (3, s.bankIndex bank, nr a) s.written}
    | some (.realBranch x y yes no) =>
        {s with pc := Function.update s.pc b (if (cr x).re ≤ (cr y).re then yes else no)}
    | some (.sample d) => if b then fail else
        {(next.putComplex d (tape s.cursor)) with cursor := s.cursor + 1}
    | some .call => if b then fail else
        {next with inCall := true, pc := Function.update next.pc true 0, calls := s.calls + 1}
    | some .halt => if b then {s with inCall := false} else {s with halted := true}

noncomputable def machineRun (M S : Program) (input : MachineInput) (tape : ℕ → ℂ)
    (t : ℕ) : MachineState := (machineStep M S input tape)^[t] {}

end SketchAttr.LOO


