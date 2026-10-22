-- Prove2me | Definitions.Def_LeeSviridenkoVondrak_LocalSearch_OracleMachine
-- name    : LeeSviridenkoVondrak_LocalSearch_OracleMachine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:49:32.39496+00:00
-- url     : https://prove2.me/theorems/e12e034c-65fc-4ddf-9ed2-a541a9c8adab
-- title:
--   Finite oracle real-RAM programs and full execution cost
-- statement:
--   An oracle program is a finite list of instructions operating on natural, real, and subset registers. Natural operations are constants, copies, addition, truncated subtraction and comparison branches; real operations also include multiplication and division. Set instructions create, copy, insert, delete and test membership. Value queries return $f(S)$; independence queries return the answer of one of the $k$ matroids. Jumps and explicit halt instructions complete the language. Initially natural register zero contains $n$, other numeric registers are zero, and all sets are empty. The output is the set selected by a halt instruction.
--
--   Each executed instruction is conservatively charged $n+1$ elementary operations, including the halt. This accounts for set scans and query preparation as well as unit-cost real arithmetic and oracle calls. Out-of-range program counters are stuck, invalid element operations leave the set unchanged, and invalid membership or independence queries answer false. Real division is total, including division by zero. A bounded execution observes a finite prefix; it does not declare an unfinished run successful.
--
--   **Formalization Note** This operational language explicates the oracle model of p. 795. It is not a claim about bit complexity of arbitrary real numbers and it does not encode the desired approximation guarantee in the program definition. The goal existentially quantifies a finite program, requires an executed halt, and bounds its entire cost.
-- source:
--   Lee, Sviridenko and Vondrák (2010), Submodular Maximization over Multiple Matroids via Generalized Exchange Properties, Mathematics of Operations Research 35(4), 795–806, https://doi.org/10.1287/moor.1100.0463; introduction p. 795 / PDF 1 and §3 pp. 801–803 / PDF 7–9

import Definitions.Def_LeeSviridenkoVondrak_LocalSearch_Model

namespace LeeSviridenkoVondrak.LocalSearch

/-- A finite real-RAM instruction set for the oracle model on p. 795.
The value arguments of natConst and realConst are literals; all other numeric
arguments are register addresses or branch labels.
No instruction accepts an arbitrary function or the input objective/table as data. -/
inductive Instruction where
  | natConst (dst value : ℕ)
  | natCopy (dst src : ℕ)
  | natAdd (dst a b : ℕ)
  | natSub (dst a b : ℕ)
  | natBranch (a b yes no : ℕ)
  | realConst (dst : ℕ) (value : ℝ)
  | realCopy (dst src : ℕ)
  | realAdd (dst a b : ℕ)
  | realSub (dst a b : ℕ)
  | realMul (dst a b : ℕ)
  | realDiv (dst a b : ℕ)
  | realBranch (a b yes no : ℕ)
  | setEmpty (dst : ℕ)
  | setCopy (dst src : ℕ)
  | setInsert (dst src elementRegister : ℕ)
  | setErase (dst src elementRegister : ℕ)
  | setMember (setRegister elementRegister yes no : ℕ)
  | valueQuery (realDst setRegister : ℕ)
  | indepQuery (natDst matroidRegister setRegister : ℕ)
  | jump (label : ℕ)
  | halt (setRegister : ℕ)

structure MachineState (n : ℕ) where
  pc : ℕ
  natReg : ℕ → ℕ
  realReg : ℕ → ℝ
  setReg : ℕ → Finset (Fin n)
  halted : Bool
  output : Finset (Fin n)
  cost : ℕ

def initialState (n : ℕ) : MachineState n :=
  ⟨0, (fun r => if r = 0 then n else 0), (fun _ => 0), (fun _ => ∅), false, ∅, 0⟩

/-- Each executed instruction is charged n+1 operations, a conservative padding
covering a bit-vector copy/scan and oracle query preparation. Scalar real operations
and oracle calls are unit-cost. This is an oracle real-RAM model, not bit complexity.
An out-of-range program counter remains stuck (never becomes halted); a halt
instruction itself is charged. Invalid element/index accesses have explicit defaults. -/
noncomputable def machineStep {n k : ℕ} (code : List Instruction)
    (f : Finset (Fin n) → ℝ) (M : Fin k → Matroid (Fin n))
    (s : MachineState n) : MachineState n := by
  classical
  exact if s.halted then s else
    match code[s.pc]? with
    | none => { s with cost := s.cost + n + 1 }
    | some op =>
      let t := { s with pc := s.pc + 1, cost := s.cost + n + 1 }
      match op with
      | .natConst d v => { t with natReg := Function.update s.natReg d v }
      | .natCopy d a => { t with natReg := Function.update s.natReg d (s.natReg a) }
      | .natAdd d a b => { t with natReg := Function.update s.natReg d (s.natReg a + s.natReg b) }
      | .natSub d a b => { t with natReg := Function.update s.natReg d (s.natReg a - s.natReg b) }
      | .natBranch a b y z => { t with pc := if s.natReg a ≤ s.natReg b then y else z }
      | .realConst d v => { t with realReg := Function.update s.realReg d v }
      | .realCopy d a => { t with realReg := Function.update s.realReg d (s.realReg a) }
      | .realAdd d a b => { t with realReg := Function.update s.realReg d (s.realReg a + s.realReg b) }
      | .realSub d a b => { t with realReg := Function.update s.realReg d (s.realReg a - s.realReg b) }
      | .realMul d a b => { t with realReg := Function.update s.realReg d (s.realReg a * s.realReg b) }
      | .realDiv d a b => { t with realReg := Function.update s.realReg d (s.realReg a / s.realReg b) }
      | .realBranch a b y z => { t with pc := if s.realReg a ≤ s.realReg b then y else z }
      | .setEmpty d => { t with setReg := Function.update s.setReg d ∅ }
      | .setCopy d a => { t with setReg := Function.update s.setReg d (s.setReg a) }
      | .setInsert d a e =>
        { t with setReg := (Function.update s.setReg d (if h : s.natReg e < n then insert ⟨s.natReg e, h⟩ (s.setReg a) else s.setReg a)) }
      | .setErase d a e =>
        { t with setReg := (Function.update s.setReg d (if h : s.natReg e < n then (s.setReg a).erase ⟨s.natReg e, h⟩ else s.setReg a)) }
      | .setMember a e y z =>
        { t with pc := if h : s.natReg e < n then
            (if (⟨s.natReg e, h⟩ : Fin n) ∈ s.setReg a then y else z) else z }
      | .valueQuery d a => { t with realReg := Function.update s.realReg d (f (s.setReg a)) }
      | .indepQuery d j a =>
        { t with natReg := (Function.update s.natReg d (if h : s.natReg j < k then
            (if (M ⟨s.natReg j, h⟩).Indep (↑(s.setReg a) : Set (Fin n)) then 1 else 0)
           else 0)) }
      | .jump j => { t with pc := j }
      | .halt a => { t with halted := true, output := s.setReg a }

/-- Bounded observation of the machine, not a cutoff algorithm: the goal requires
an actually executed halt and bounds its full cost. After halt the state is fixed. -/
noncomputable def runMachine {n k : ℕ} (code : List Instruction)
    (f : Finset (Fin n) → ℝ) (M : Fin k → Matroid (Fin n)) (steps : ℕ) : MachineState n :=
  (machineStep code f M)^[steps] (initialState n)

end LeeSviridenkoVondrak.LocalSearch


