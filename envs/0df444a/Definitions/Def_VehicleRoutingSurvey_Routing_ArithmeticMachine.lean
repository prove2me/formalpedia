-- Prove2me | Definitions.Def_VehicleRoutingSurvey_Routing_ArithmeticMachine
-- name    : VehicleRoutingSurvey_Routing_ArithmeticMachine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T00:08:52.572964+00:00
-- url     : https://prove2.me/theorems/76565b35-78ff-4c14-8d10-15364cda31ab
-- title:
--   Uniform arithmetic random-access programs
-- statement:
--   A program is a finite list of arithmetic, memory, branch and halt instructions. Its state contains a program counter, natural and real registers, and natural and real random-access memory. Each instruction costs one step. Real constants in the finite program are rational; real input weights are loaded from memory. The step semantics provide no matching, shortest-path or routing oracle. A halted output is a length-delimited list of natural memory cells. This is the explicit unit-cost arithmetic model used for the report runtime convention.
-- source:
--   Lenstra and Rinnooy Kan, Complexity of vehicle routing and scheduling problems, Econometric Institute Report 7919/O (1979), Table 3, p. 5, arithmetic-operation interpretation

import Mathlib

namespace VehicleRoutingSurvey.Routing

/-- Finite random-access programs; all addresses are held in natural registers.
Arithmetic, memory access and branching each cost one step. No optimization oracle. -/
inductive ArithmeticInstruction where
  | natConst (dst value : ℕ)
  | natAdd (dst x y : ℕ)
  | natSub (dst x y : ℕ)
  | natLoad (dst address : ℕ)
  | natStore (address src : ℕ)
  | realConst (dst : ℕ) (value : ℚ)
  | realAdd (dst x y : ℕ)
  | realSub (dst x y : ℕ)
  | realMul (dst x y : ℕ)
  | realDiv (dst x y : ℕ)
  | realLoad (dst address : ℕ)
  | realStore (address src : ℕ)
  | natBranch (x y yes no : ℕ)
  | realBranch (x y yes no : ℕ)
  | jump (target : ℕ)
  | halt

structure ArithmeticState where
  pc : ℕ := 0
  nr : ℕ → ℕ := fun _ => 0
  rr : ℕ → ℝ := fun _ => 0
  nm : ℕ → ℕ := fun _ => 0
  rm : ℕ → ℝ := fun _ => 0
  halted : Bool := false

noncomputable def arithmeticStep (p : List ArithmeticInstruction)
    (s : ArithmeticState) : ArithmeticState := by
  classical
  exact if s.halted then s else
    let next := {s with pc := s.pc + 1}
    match p[s.pc]? with
    | none => {s with halted := true}
    | some (.natConst d v) => {next with nr := Function.update s.nr d v}
    | some (.natAdd d x y) => {next with nr := Function.update s.nr d (s.nr x + s.nr y)}
    | some (.natSub d x y) => {next with nr := Function.update s.nr d (s.nr x - s.nr y)}
    | some (.natLoad d a) => {next with nr := Function.update s.nr d (s.nm (s.nr a))}
    | some (.natStore a x) => {next with nm := Function.update s.nm (s.nr a) (s.nr x)}
    | some (.realConst d v) => {next with rr := Function.update s.rr d (v : ℝ)}
    | some (.realAdd d x y) => {next with rr := Function.update s.rr d (s.rr x + s.rr y)}
    | some (.realSub d x y) => {next with rr := Function.update s.rr d (s.rr x - s.rr y)}
    | some (.realMul d x y) => {next with rr := Function.update s.rr d (s.rr x * s.rr y)}
    | some (.realDiv d x y) => {next with rr := Function.update s.rr d (s.rr x / s.rr y)}
    | some (.realLoad d a) => {next with rr := Function.update s.rr d (s.rm (s.nr a))}
    | some (.realStore a x) => {next with rm := Function.update s.rm (s.nr a) (s.rr x)}
    | some (.natBranch x y yes no) => {s with pc := if s.nr x ≤ s.nr y then yes else no}
    | some (.realBranch x y yes no) => {s with pc := if s.rr x ≤ s.rr y then yes else no}
    | some (.jump t) => {s with pc := t}
    | some .halt => {s with halted := true}

def arithmeticInput (ns : List ℕ) (rs : List ℝ) : ArithmeticState :=
  {nm := fun i => ns[i]?.getD 0, rm := fun i => rs[i]?.getD 0}

noncomputable def arithmeticRun (p : List ArithmeticInstruction) (t : ℕ)
    (ns : List ℕ) (rs : List ℝ) : ArithmeticState :=
  (arithmeticStep p)^[t] (arithmeticInput ns rs)

/-- Output memory starts with a length, followed by that many natural cells. -/
def arithmeticOutput (s : ArithmeticState) : List ℕ :=
  (List.range (s.nm 0)).map (fun i => s.nm (i + 1))

end VehicleRoutingSurvey.Routing


