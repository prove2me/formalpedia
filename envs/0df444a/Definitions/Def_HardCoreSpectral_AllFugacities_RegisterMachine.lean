-- Prove2me | Definitions.Def_HardCoreSpectral_AllFugacities_RegisterMachine
-- name    : HardCoreSpectral_AllFugacities_RegisterMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:35:06.205086+00:00
-- url     : https://prove2.me/theorems/cfbcf651-fc46-4a11-95aa-946a862d0510
-- title:
--   Finite real-register instruction syntax and charged execution
-- statement:
--   This file fixes the computational model used to state the paper's algorithmic conclusions. A program is a finite list of instructions whose real literals are rational numbers. Input consists of a finite Boolean adjacency matrix and a finite list of real parameters. Real registers, natural pointer registers, and working memory begin at zero.
--
--   Each executed instruction costs one unit. The instructions include scalar arithmetic, comparisons, guarded square root, exponential and guarded logarithm, indirect scalar memory access, scalar parameter access, adjacency-entry queries, and a draw from a random tape with values in $[0,1]$ (the $k$-th draw reads tape entry $k$). Division by zero and operations outside their mathematical domains fault. Powers and rounding have no primitive instructions and must be programmed with charged loops. Halt and fault are absorbing states. Both the output storage and the charged work come from the same fuel-bounded execution.
--
--   For a program $P$, input $x$, and bound $B$, the termination predicate asserts
--
--   $$
--   \forall u\in[0,1]^{\mathbb N},\quad \operatorname{Run}(P,x,u,B)\text{ has halted without fault and has work at most }B.
--   $$
--
--   The probability law of the tape (i.i.d. uniform draws), the output decoders and the approximation predicates are defined in the companion definition `HardCoreSpectral.AllFugacities.Approximation`. The paper itself does not fix a machine language; this real-register reading of its pseudocode is the one prescribed by the mission brief (unit-cost arithmetic, $\sqrt{\cdot}$, $\exp$, $\log$ and uniform draws on their mathematical domains; no oracle for $Z_G$, $\mu_{G,\lambda}$ or any localized law).
-- source:
--   Ijay Narang, Will Perkins, STOC 2027 submission #294 (October 2026), p. 2 (algorithmic conventions), pp. 15–21 (Algorithms 1–3, real-parameter pseudocode); computational reading fixed in the mission brief.

import Mathlib

set_option autoImplicit false

namespace HardCoreSpectral.AllFugacities

/-- Finite instruction syntax for the computational reading fixed in the brief.
There is no instruction for powers, rounding, integration, or sampling a Gibbs law. -/
inductive RegisterInstruction where
  | literal (dst : ℕ) (value : ℚ)
  | copy (dst src : ℕ)
  | add (dst lhs rhs : ℕ)
  | sub (dst lhs rhs : ℕ)
  | mul (dst lhs rhs : ℕ)
  | div (dst lhs rhs : ℕ)
  | sqrt (dst src : ℕ)
  | exp (dst src : ℕ)
  | log (dst src : ℕ)
  | pointerLiteral (dst value : ℕ)
  | pointerCopy (dst src : ℕ)
  | pointerIncrement (dst : ℕ)
  | pointerDecrement (dst : ℕ)
  | load (dst pointer : ℕ)
  | store (pointer src : ℕ)
  | parameter (dst index : ℕ)
  | inputSize (dst : ℕ)
  | adjacency (dst rowPointer columnPointer : ℕ)
  | branchReal (lhs rhs yes no : ℕ)
  | branchPointer (lhs rhs yes no : ℕ)
  | jump (target : ℕ)
  | uniform (dst : ℕ)
  | halt
  deriving DecidableEq

/-- A finite program, with only finitely encoded rational literals. -/
abbrev RegisterProgram := List RegisterInstruction

/-- The finite graph and scalar input are read only. Every access is an instruction. -/
structure RegisterInput where
  vertexCount : ℕ
  adjacency : Fin vertexCount → Fin vertexCount → Bool
  parameters : List ℝ

/-- Every reached configuration differs from initially zero storage in finitely many cells.
This structure stores no claimed runtime and no proposed probability law. -/
structure RegisterConfiguration where
  pc : ℕ := 0
  registers : ℕ → ℝ := fun _ => 0
  pointers : ℕ → ℕ := fun _ => 0
  memory : ℕ → ℝ := fun _ => 0
  draws : ℕ := 0
  work : ℕ := 0
  halted : Bool := false
  faulted : Bool := false

/-- One scalar write; its cost is included by the surrounding transition. -/
noncomputable def registerWrite (s : RegisterConfiguration) (dst : ℕ) (value : ℝ) :
    RegisterConfiguration :=
  { s with registers := Function.update s.registers dst value }

/-- A single charged transition. Invalid domains fault rather than exploiting totalized
real division/logarithms or truncated pointer subtraction. Halt and fault are absorbing.
A tape entry is read only by the uniform instruction. Tapes contain values in [0,1]. -/
noncomputable def registerStep (program : RegisterProgram) (input : RegisterInput)
    (tape : ℕ → Set.Icc (0 : ℝ) 1) (s : RegisterConfiguration) : RegisterConfiguration := by
  classical
  exact if s.halted || s.faulted then s else
    let next : RegisterConfiguration := { s with pc := s.pc + 1, work := s.work + 1 }
    let fail : RegisterConfiguration := { next with faulted := true }
    match program[s.pc]? with
    | none => fail
    | some instruction => match instruction with
      | .literal dst value => registerWrite next dst value
      | .copy dst src => registerWrite next dst (s.registers src)
      | .add dst lhs rhs => registerWrite next dst (s.registers lhs + s.registers rhs)
      | .sub dst lhs rhs => registerWrite next dst (s.registers lhs - s.registers rhs)
      | .mul dst lhs rhs => registerWrite next dst (s.registers lhs * s.registers rhs)
      | .div dst lhs rhs =>
          if s.registers rhs = 0 then fail
          else registerWrite next dst (s.registers lhs / s.registers rhs)
      | .sqrt dst src =>
          if 0 ≤ s.registers src then registerWrite next dst (Real.sqrt (s.registers src))
          else fail
      | .exp dst src => registerWrite next dst (Real.exp (s.registers src))
      | .log dst src =>
          if 0 < s.registers src then registerWrite next dst (Real.log (s.registers src))
          else fail
      | .pointerLiteral dst value => { next with pointers := Function.update s.pointers dst value }
      | .pointerCopy dst src =>
          { next with pointers := Function.update s.pointers dst (s.pointers src) }
      | .pointerIncrement dst =>
          { next with pointers := Function.update s.pointers dst (s.pointers dst + 1) }
      | .pointerDecrement dst =>
          if s.pointers dst = 0 then fail else
            { next with pointers := Function.update s.pointers dst (s.pointers dst - 1) }
      | .load dst pointer => registerWrite next dst (s.memory (s.pointers pointer))
      | .store pointer src =>
          { next with memory := Function.update s.memory (s.pointers pointer) (s.registers src) }
      | .parameter dst index =>
          match input.parameters[index]? with
          | none => fail
          | some value => registerWrite next dst value
      | .inputSize dst => registerWrite next dst input.vertexCount
      | .adjacency dst rowPointer columnPointer =>
          if hr : s.pointers rowPointer < input.vertexCount then
            if hc : s.pointers columnPointer < input.vertexCount then
              registerWrite next dst
                (if input.adjacency ⟨s.pointers rowPointer, hr⟩ ⟨s.pointers columnPointer, hc⟩
                  then 1 else 0)
            else fail
          else fail
      | .branchReal lhs rhs yes no =>
          { next with pc := if s.registers lhs ≤ s.registers rhs then yes else no }
      | .branchPointer lhs rhs yes no =>
          { next with pc := if s.pointers lhs ≤ s.pointers rhs then yes else no }
      | .jump target => { next with pc := target }
      | .uniform dst =>
          { registerWrite next dst (tape s.draws).val with draws := s.draws + 1 }
      | .halt => { next with halted := true }

/-- Fuel-bounded execution. The work and outputs belong to the same run. -/
noncomputable def registerRun (program : RegisterProgram) (input : RegisterInput)
    (tape : ℕ → Set.Icc (0 : ℝ) 1) : ℕ → RegisterConfiguration
  | 0 => {}
  | fuel + 1 => registerStep program input tape (registerRun program input tape fuel)

/-- Worst-case termination within a charged bound; neither faults nor divergent
executions count as algorithms that terminate. -/
def RegisterTerminatesWithin (program : RegisterProgram) (input : RegisterInput)
    (bound : ℕ) : Prop :=
  ∀ tape : ℕ → Set.Icc (0 : ℝ) 1,
    (registerRun program input tape bound).halted = true ∧
    (registerRun program input tape bound).faulted = false ∧
    (registerRun program input tape bound).work ≤ bound

end HardCoreSpectral.AllFugacities


