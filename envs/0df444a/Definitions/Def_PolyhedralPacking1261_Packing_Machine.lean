-- Prove2me | Definitions.Def_PolyhedralPacking1261_Packing_Machine
-- name    : PolyhedralPacking1261_Packing_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:35:50.569273+00:00
-- url     : https://prove2.me/theorems/14cda0d9-b3af-4055-8914-13fd13d75099
-- title:
--   Finite exact-real scalar programs and counted, fault-checked execution
-- statement:
--   The computational model is one fixed deterministic random-access machine over exact reals. A program is a finite list of scalar instructions with rational literal constants: copy, addition, subtraction, multiplication, guarded division, guarded square root, floor, scalar input access, indirect load and store, conditional comparison/branch, jump, and halt. There are no geometry, optimization, sorting, or packing primitives. Every instruction costs one step, including halt, loops and subroutines through their instructions. All registers and working memory start at zero. The program is fixed before the input and before epsilon.
--   Indirect addresses must be exact nonnegative integers. Division by zero, square roots of negative numbers, invalid input addresses and invalid program counters fault. A fault is absorbing and cannot yield a successful execution. Real floor is the usual integer floor, including for negative numbers. Execution records the actual first halt, with no fault. The use of noncomputable in Lean implements the semantics of exact real operations; code itself is finite syntax and contains no choice operator. Input is a scalar random-access array, represented by a list; an instruction accesses only a fixed number of scalar cells. This is the geometric exact-real reading of the source's unspecified machine model, not a bit-complexity claim.
-- source:
--   Simon Bartlmae, Anders Aamand, Mikkel Abrahamsen, Polylogarithmic Approximation for Packing Convex Polyhedra, STOC 2027 submission #1261 (October 2026), canonical PDF SHA-256 b915da2d5fece730ea9946885b05ad09e10e575374e6a1df96e8a6149cb0e67e, Theorem 1 and its following clarification, PDF p.2 = printed p.1; computational-model reading of polynomial time

import Mathlib

set_option autoImplicit false

namespace PolyhedralPacking1261.Packing

/-- A fixed, finite instruction set. Each instruction has unit cost. All operands
are scalar register addresses. The only constants in a program are rational. -/
inductive ScalarInstruction where
  | literal (destination : ℕ) (value : ℚ)
  | copy (destination source : ℕ)
  | add (destination left right : ℕ)
  | subtract (destination left right : ℕ)
  | multiply (destination left right : ℕ)
  | divide (destination numerator denominator : ℕ)
  | squareRoot (destination source : ℕ)
  | floor (destination source : ℕ)
  | input (destination addressRegister : ℕ)
  | load (destination addressRegister : ℕ)
  | store (addressRegister source : ℕ)
  | branchLE (left right yes no : ℕ)
  | jump (target : ℕ)
  | halt

/-- Code is finite syntax, not an arbitrary function or an oracle. -/
abbrev ScalarProgram := List ScalarInstruction

structure ScalarState where
  pc : ℕ
  memory : ℕ → ℝ
  halted : Bool
  faulted : Bool

def scalarInitial : ScalarState :=
  ⟨0, fun _ => 0, false, false⟩

noncomputable def writeScalar (state : ScalarState) (destination : ℕ)
    (value : ℝ) : ScalarState :=
  { state with
    pc := state.pc + 1
    memory := Function.update state.memory destination value }

/-- An indirect address must be an exact nonnegative integer. Invalid addresses
fault rather than being silently truncated to address zero. -/
noncomputable def scalarAddress (value : ℝ) : Option ℕ :=
  if 0 ≤ value ∧ value = (⌊value⌋ : ℤ) then some ⌊value⌋.toNat else none

/-- One scalar step, including branches and each memory or input access.
Division by zero, negative square roots, invalid input accesses, and an invalid
program counter fault. Faulted states cannot later produce a successful run. -/
noncomputable def scalarStep (program : ScalarProgram) (input : List ℝ)
    (state : ScalarState) : ScalarState :=
  if state.halted || state.faulted then state else
  match program[state.pc]? with
  | none => { state with faulted := true }
  | some instruction =>
    match instruction with
    | .literal d q => writeScalar state d (q : ℝ)
    | .copy d a => writeScalar state d (state.memory a)
    | .add d a b => writeScalar state d (state.memory a + state.memory b)
    | .subtract d a b => writeScalar state d (state.memory a - state.memory b)
    | .multiply d a b => writeScalar state d (state.memory a * state.memory b)
    | .divide d a b =>
        if state.memory b = 0 then { state with faulted := true }
        else writeScalar state d (state.memory a / state.memory b)
    | .squareRoot d a =>
        if state.memory a < 0 then { state with faulted := true }
        else writeScalar state d (Real.sqrt (state.memory a))
    | .floor d a => writeScalar state d (⌊state.memory a⌋ : ℤ)
    | .input d a =>
        match scalarAddress (state.memory a) with
        | none => { state with faulted := true }
        | some address =>
            match input[address]? with
            | none => { state with faulted := true }
            | some value => writeScalar state d value
    | .load d a =>
        match scalarAddress (state.memory a) with
        | none => { state with faulted := true }
        | some address => writeScalar state d (state.memory address)
    | .store a b =>
        match scalarAddress (state.memory a) with
        | none => { state with faulted := true }
        | some address => writeScalar state address (state.memory b)
    | .branchLE a b yes no =>
        { state with pc := if state.memory a ≤ state.memory b then yes else no }
    | .jump target => { state with pc := target }
    | .halt => { state with halted := true }

noncomputable def scalarRun (program : ScalarProgram) (input : List ℝ) :
    ℕ → ScalarState
  | 0 => scalarInitial
  | t + 1 => scalarStep program input (scalarRun program input t)

/-- The clock counts the first halting instruction. It cannot be padded by
repeatedly stepping an already halted state. There are no uncharged subroutines. -/
def ScalarExecution (program : ScalarProgram) (input : List ℝ)
    (time : ℕ) (finalState : ScalarState) : Prop :=
  scalarRun program input time = finalState ∧ finalState.halted = true ∧
    finalState.faulted = false ∧
    ∀ t < time, (scalarRun program input t).halted = false

end PolyhedralPacking1261.Packing


