-- Prove2me | Definitions.Def_L1ResistanceCount_Counting_ArithmeticRAM
-- name    : L1ResistanceCount_Counting_ArithmeticRAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:07:23.438816+00:00
-- url     : https://prove2.me/theorems/3d0e2543-cb20-4e8b-a2fb-894ede215771
-- title:
--   Finite arithmetic programs, random tapes, and executed cost
-- statement:
--   A program is a finite list of arithmetic, comparison, indexed-memory and sampling instructions. Natural cells store indices; real cells store exact real numbers. Fixed program constants are natural or rational. Each executed instruction, including each uniform or Gaussian draw, costs one operation. Each instruction has a bounded number of operand accesses; changing to a convention charging each access separately changes time by an absolute factor.
--
--   Two independent infinite tapes carry uniform samples on $[0,1]$ and standard Gaussian samples. The tape law is a probability measure, with a sorry-free instance checking its total mass. The transition relation determines the entire execution and its output. The executed cost is the first halting time, and is $+\infty$ if the program never halts. Expected cost is a nonnegative extended integral over the tape law.
--
--   There is no determinant, pseudoinverse, optimizer, tree sampler, categorical distribution, arbitrary transition function, or freely assigned cost in the instruction set. Those operations require finite programs and their executed work is charged. This gives an operational arithmetic model for the runtime assertions, without a bit-complexity claim.
-- source:
--   Rong-Hua Li, Yichun Yang, STOC 2027 submission #881 (October 2026), p.1 (arithmetic operations and Õ convention), Theorem 1.1 p.2, Algorithms 1–5 pp.7–11,22; arithmetic-model reading in the captain brief; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/881.pdf

import Mathlib

namespace L1ResistanceCount.Counting

/-- A fixed finite arithmetic RAM instruction set. All indices name registers;
indirect loads/stores permit sparse input arrays. No graph, solve, determinant,
pseudoinverse, minimizer, summation, or categorical-sampling instruction exists.
Every executed instruction is charged one operation, including each random draw. -/
inductive Instruction where
  | natConst (dst value next : ℕ)
  | ratConst (dst : ℕ) (value : ℚ) (next : ℕ)
  | natAdd (dst a b next : ℕ)
  | natSub (dst a b next : ℕ)
  | natMul (dst a b next : ℕ)
  | natDiv (dst a b next : ℕ)
  | add (dst a b next : ℕ)
  | sub (dst a b next : ℕ)
  | mul (dst a b next : ℕ)
  | div (dst a b next : ℕ)
  | sqrt (dst a next : ℕ)
  | log (dst a next : ℕ)
  | exp (dst a next : ℕ)
  | toReal (dst a next : ℕ)
  | loadNat (dst addr next : ℕ)
  | loadReal (dst addr next : ℕ)
  | storeNat (addr src next : ℕ)
  | storeReal (addr src next : ℕ)
  | branchNatLE (a b yes no : ℕ)
  | branchRealLE (a b yes no : ℕ)
  | uniform (dst next : ℕ)
  | gaussian (dst next : ℕ)
  | halt

abbrev Program := List Instruction

structure MachineState where
  pc : ℕ := 0
  naturals : ℕ → ℕ
  reals : ℕ → ℝ
  uniformCursor : ℕ := 0
  gaussianCursor : ℕ := 0
  halted : Bool := false

abbrev RandomTape := (ℕ → ℝ) × (ℕ → ℝ)

open MeasureTheory ProbabilityTheory

/-- Two independent infinite streams, respectively uniform on [0,1] and Gaussian N(0,1). -/
noncomputable def tapeLaw : Measure RandomTape :=
  (Measure.infinitePi (fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1))).prod
    (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))

/-- The tape law has total mass one, so a missing typeclass can never silently
turn infinitePi into the zero measure in probability specifications. -/
instance tapeLaw_isProbabilityMeasure : IsProbabilityMeasure tapeLaw := by
  have hunif : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    constructor
    simp
  let := hunif
  unfold tapeLaw
  infer_instance

/-- Small-step semantics, with no user-supplied transition function or cost. An invalid
program counter does not halt and therefore has infinite runtime. -/
noncomputable def machineStep (P : Program) (ω : RandomTape) (s : MachineState) : MachineState :=
  if s.halted then s else
  match P[s.pc]? with
  | none => s
  | some i =>
    let nr := fun dst val next => { s with pc := next, naturals := Function.update s.naturals dst val }
    let rr := fun dst val next => { s with pc := next, reals := Function.update s.reals dst val }
    match i with
    | .natConst dst val next => nr dst val next
    | .ratConst dst val next => rr dst (val : ℝ) next
    | .natAdd dst a b next => nr dst (s.naturals a + s.naturals b) next
    | .natSub dst a b next => nr dst (s.naturals a - s.naturals b) next
    | .natMul dst a b next => nr dst (s.naturals a * s.naturals b) next
    | .natDiv dst a b next => nr dst (s.naturals a / s.naturals b) next
    | .add dst a b next => rr dst (s.reals a + s.reals b) next
    | .sub dst a b next => rr dst (s.reals a - s.reals b) next
    | .mul dst a b next => rr dst (s.reals a * s.reals b) next
    | .div dst a b next => rr dst (s.reals a / s.reals b) next
    | .sqrt dst a next => rr dst (Real.sqrt (s.reals a)) next
    | .log dst a next => rr dst (Real.log (s.reals a)) next
    | .exp dst a next => rr dst (Real.exp (s.reals a)) next
    | .toReal dst a next => rr dst (s.naturals a : ℝ) next
    | .loadNat dst addr next => nr dst (s.naturals (s.naturals addr)) next
    | .loadReal dst addr next => rr dst (s.reals (s.naturals addr)) next
    | .storeNat addr src next => nr (s.naturals addr) (s.naturals src) next
    | .storeReal addr src next => rr (s.naturals addr) (s.reals src) next
    | .branchNatLE a b yes no => { s with pc := if s.naturals a ≤ s.naturals b then yes else no }
    | .branchRealLE a b yes no => { s with pc := if s.reals a ≤ s.reals b then yes else no }
    | .uniform dst next => { rr dst (ω.1 s.uniformCursor) next with uniformCursor := s.uniformCursor + 1 }
    | .gaussian dst next => { rr dst (ω.2 s.gaussianCursor) next with gaussianCursor := s.gaussianCursor + 1 }
    | .halt => { s with halted := true }

noncomputable def execution (P : Program) (input : MachineState) (ω : RandomTape) : ℕ → MachineState
  | 0 => input
  | t + 1 => machineStep P ω (execution P input ω t)

/-- A finite trace ending at the halt instruction; the halt instruction is charged. -/
def HaltsAt (P : Program) (input : MachineState) (ω : RandomTape) (t : ℕ) : Prop :=
  (execution P input ω t).halted = true ∧
    ∀ j < t, (execution P input ω j).halted = false

/-- Infinite on nontermination, with no freely assigned runtime. -/
noncomputable def executedCost (P : Program) (input : MachineState) (ω : RandomTape) : ENNReal :=
  ⨅ t : ℕ, if (execution P input ω t).halted = true then (t : ENNReal) else ⊤

noncomputable def expectedCost (P : Program) (input : MachineState) : ENNReal :=
  ∫⁻ ω, executedCost P input ω ∂tapeLaw

/-- A postcondition on the actual output array of a halting computation. -/
def Returns (P : Program) (input : MachineState) (ω : RandomTape)
    (post : MachineState → Prop) : Prop :=
  ∃ t, HaltsAt P input ω t ∧ post (execution P input ω t)

/-- Outer probability; the goal also requires measurability of its success event. -/
noncomputable def successProbability (P : Program) (input : MachineState)
    (post : MachineState → Prop) : ENNReal := tapeLaw {ω | Returns P input ω post}

end L1ResistanceCount.Counting


