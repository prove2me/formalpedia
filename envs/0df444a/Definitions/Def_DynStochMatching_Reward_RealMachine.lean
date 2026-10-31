-- Prove2me | Definitions.Def_DynStochMatching_Reward_RealMachine
-- name    : DynStochMatching_Reward_RealMachine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T20:37:52.13436+00:00
-- url     : https://prove2.me/theorems/eac79760-caa7-4d91-81e8-647858b4769a
-- title:
--   Exact arithmetic register-machine semantics
-- statement:
--   Finite programs operate on real registers and natural address registers using constants, arithmetic, comparisons, indirect loads/stores, branches and an exact LP primitive. There is no arbitrary-function instruction. A fuel-bounded interpreter records LP call counts and total LP dimensions as well as actual memory output. Computation certificates compare that output against the specified algorithm functions. This is an arithmetic/comparison model relative to a polynomial LP solver and exact samples, not a claim of strongly polynomial bit complexity for arbitrary real input.
-- source:
--   Aouad and Sarıtaç (2022), Dynamic Stochastic Matching Under Limited Time, https://doi.org/10.1287/opre.2022.2293, held published-basis manuscript, Theorem 2 and Algorithm 2, printed 21, 45 / PDF 22, 46

import Definitions.Def_DynStochMatching_Reward_LinearPrograms

open scoped Classical

namespace DynStochMatching.Reward

/-- A uniform register-machine language for exact arithmetic/comparison computation.
Natural registers provide addresses and loop counters. There is no arbitrary-function instruction. -/
inductive Instruction where
  | natConst (dst value : ℕ)
  | realConst (dst : ℕ) (value : ℚ)
  | natCopy (dst src : ℕ)
  | realCopy (dst src : ℕ)
  | natAdd (dst lhs rhs : ℕ)
  | natSub (dst lhs rhs : ℕ)
  | natMul (dst lhs rhs : ℕ)
  | realAdd (dst lhs rhs : ℕ)
  | realSub (dst lhs rhs : ℕ)
  | realMul (dst lhs rhs : ℕ)
  | realDiv (dst lhs rhs : ℕ)
  | realLoad (dst addressRegister : ℕ)
  | realStore (addressRegister src : ℕ)
  | natToReal (dst src : ℕ)
  | branchNatLE (lhs rhs yes no : ℕ)
  | branchRealLE (lhs rhs yes no : ℕ)
  | jump (target : ℕ)
  | lp (rows cols matrixStart rhsStart objectiveStart outputStart : ℕ)
  | halt

structure MachineState where
  pc : ℕ
  naturals : ℕ → ℕ
  reals : ℕ → ℝ

noncomputable def memoryLP (s : MachineState) (nr nc pa pb pr : ℕ) : LinearProgram where
  rows := s.naturals nr
  cols := s.naturals nc
  matrix i j := s.reals (s.naturals pa + i.val * s.naturals nc + j.val)
  rhs i := s.reals (s.naturals pb + i.val)
  objective j := s.reals (s.naturals pr + j.val)

/-- A step charges scalar operations explicitly; an LP call records its dimensions separately. -/
noncomputable def machineStep (O : LinearOracle) (instr : Instruction)
    (s : MachineState) : MachineState :=
  let next := { s with pc := s.pc + 1 }
  match instr with
  | .natConst d v => { next with naturals := Function.update s.naturals d v }
  | .realConst d v => { next with reals := Function.update s.reals d (v : ℝ) }
  | .natCopy d a => { next with naturals := Function.update s.naturals d (s.naturals a) }
  | .realCopy d a => { next with reals := Function.update s.reals d (s.reals a) }
  | .natAdd d a b => { next with naturals := Function.update s.naturals d (s.naturals a + s.naturals b) }
  | .natSub d a b => { next with naturals := Function.update s.naturals d (s.naturals a - s.naturals b) }
  | .natMul d a b => { next with naturals := Function.update s.naturals d (s.naturals a * s.naturals b) }
  | .realAdd d a b => { next with reals := Function.update s.reals d (s.reals a + s.reals b) }
  | .realSub d a b => { next with reals := Function.update s.reals d (s.reals a - s.reals b) }
  | .realMul d a b => { next with reals := Function.update s.reals d (s.reals a * s.reals b) }
  | .realDiv d a b => { next with reals := Function.update s.reals d (s.reals a / s.reals b) }
  | .realLoad d a => { next with reals := Function.update s.reals d (s.reals (s.naturals a)) }
  | .realStore a r => { next with reals := Function.update s.reals (s.naturals a) (s.reals r) }
  | .natToReal d a => { next with reals := Function.update s.reals d (s.naturals a : ℝ) }
  | .branchNatLE a b y n => { s with pc := if s.naturals a ≤ s.naturals b then y else n }
  | .branchRealLE a b y n => { s with pc := if s.reals a ≤ s.reals b then y else n }
  | .jump t => { s with pc := t }
  | .lp nr nc pa pb pr po =>
    let P := memoryLP s nr nc pa pb pr
    { next with reals := fun k =>
        if h : s.naturals po ≤ k ∧ k - s.naturals po < P.cols then
          O.solve P ⟨k - s.naturals po, h.2⟩ else s.reals k }
  | .halt => s

/-- Count LP calls and their total matrix dimensions along the actual execution. -/
noncomputable def machineRun (O : LinearOracle) (code : List Instruction) :
    ℕ → MachineState → Option (MachineState × ℕ × ℕ)
  | 0, _ => none
  | fuel + 1, s =>
    match code[s.pc]? with
    | none => none
    | some .halt => some (s, 0, 0)
    | some instr =>
      (machineRun O code fuel (machineStep O instr s)).map fun (out, calls, size) =>
        match instr with
        | .lp nr nc _ _ _ _ => (out, calls + 1,
            size + (s.naturals nr + 1) * (s.naturals nc + 1))
        | _ => (out, calls, size)

noncomputable def machineInput (naturalInput : List ℕ) (realInput : List ℝ) : MachineState where
  pc := 0
  naturals k := naturalInput[k]?.getD 0
  reals k := realInput[k]?.getD 0

noncomputable def machineOutput (s : MachineState) (output : List ℝ) : Prop :=
  ∀ k : Fin output.length, s.reals k.val = output[k.val]

/-- A concrete execution witness, not a free predicate named 'polynomial time'.
One polynomial-size LP call plus the bounded scalar instructions is the offline convention. -/
noncomputable def computesWithin (O : LinearOracle) (code : List Instruction)
    (naturalInput : List ℕ) (realInput output : List ℝ) (budget maxCalls maxLPSize : ℕ) : Prop :=
  ∃ s calls size, machineRun O code budget (machineInput naturalInput realInput) = some (s, calls, size) ∧
    calls ≤ maxCalls ∧ size ≤ maxLPSize ∧ machineOutput s output

end DynStochMatching.Reward


