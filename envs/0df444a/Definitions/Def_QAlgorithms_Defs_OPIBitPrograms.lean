-- Prove2me | Definitions.Def_QAlgorithms_Defs_OPIBitPrograms
-- name    : QAlgorithms_Defs_OPIBitPrograms
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:15:39.236915+00:00
-- url     : https://prove2.me/theorems/6f06f1d9-482e-4279-ae80-1bcd852b36c1
-- title:
--   OPIBitPrograms
-- statement:
--   OPIBitPrograms
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\OPIBitPrograms.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.OPI

open Complexity

/-- Bit/tape machine instructions; 2607.14650 pp.14–19,
2607.16541 p.7, 2610.02145 p.16. There is no unit-cost field operation. -/
inductive BitInstruction where
  | write (tape : ℕ) (bit : Bool)
  | move (tape : ℕ) (right : Bool)
  | readBranch (tape zero one : ℕ)
  | jump (pc : ℕ)
  | coin (tape : ℕ)
  | query (tape length answerTape : ℕ)
  | emit (tape : ℕ)
  | halt (success : Bool)

/-- Public finite bit program; 2607.16541 p.7, 2610.02145 p.16.
Its description is fixed before membership tables or random coins. -/
structure BitOracleProgram where
  code : List BitInstruction

/-- Self-delimiting bit-program serialization; 2607.16541 p.7, 2610.02145 p.16.
Every instruction, address, length and branch target is encoded. -/
def bitProgramSerialization (P : BitOracleProgram) : Str :=
  encNat P.code.length ++ (P.code.map fun op =>
    (match op with
      | .write tape bit => [0,tape,if bit then 1 else 0]
      | .move tape right => [1,tape,if right then 1 else 0]
      | .readBranch tape zero one => [2,tape,zero,one]
      | .jump pc => [3,pc]
      | .coin tape => [4,tape]
      | .query tape length answer => [5,tape,length,answer]
      | .emit tape => [6,tape]
      | .halt success => [7,if success then 1 else 0]).flatMap encNat).flatten

/-- Operational bit state, including visited cells and actual call history;
2607.16541 p.7. Heads move one cell per instruction. -/
structure BitState where
  tape : ℕ → ℤ → Bool
  heads : ℕ → ℤ
  pc : ℕ
  coins : ℕ
  calls : List Str
  output : Str
  status : Option Bool
  time : ℕ
  visited : Finset (ℕ × ℤ)

/-- A charged bit transition; query-buffer access charges its full bit length;
2607.14650 pp.14–19, 2607.16541 p.7. -/
def bitTransition (P : BitOracleProgram) (oracle : Str → Bool) (random : ℕ → Bool)
    (s : BitState) : BitState :=
  if s.status.isSome then s else
  let t := {s with pc := s.pc+1, time := s.time+1}
  let write := fun tape bit =>
    { t with
      tape := Function.update s.tape tape (Function.update (s.tape tape) (s.heads tape) bit)
      visited := insert (tape,s.heads tape) s.visited }
  match P.code[s.pc]? with
  | none => {t with status := some false}
  | some (.write tape bit) => write tape bit
  | some (.move tape right) =>
      let h := s.heads tape + if right then 1 else -1
      {t with heads := Function.update s.heads tape h, visited := insert (tape,h) s.visited}
  | some (.readBranch tape zero one) =>
      { t with
        pc := if s.tape tape (s.heads tape) then one else zero
        visited := insert (tape,s.heads tape) s.visited}
  | some (.jump pc) => {t with pc := pc}
  | some (.coin tape) => { (write tape (random s.coins)) with coins := s.coins+1}
  | some (.query tape length answerTape) =>
      let address := List.ofFn fun i : Fin length => s.tape tape (s.heads tape+i.val)
      let result := write answerTape (oracle address)
      { result with
        time := s.time+length+1
        calls := s.calls ++ [address]
        visited := result.visited ∪ (Finset.range length).image
          (fun i => (tape,s.heads tape+(i : ℤ)))}
  | some (.emit tape) =>
      { t with
        output := s.output ++ [s.tape tape (s.heads tape)]
        visited := insert (tape,s.heads tape) s.visited}
  | some (.halt success) => {t with status := some success}

/-- Actual transition trajectory on public input and an independent coin tape;
2607.16541 p.7, 2610.02145 p.16. Nonhalting trajectories are explicit divergence. -/
def bitProgramExecution (P : BitOracleProgram) (input : Str) (oracle : Str → Bool)
    (random : ℕ → Bool) : ℕ → BitState
  | 0 => ⟨fun tape i => if tape = 0 ∧ 0 ≤ i then input.getD i.toNat false else false,
      fun _ => 0,0,0,[],[],none,0,
      (Finset.range input.length).image fun i => (0,(i : ℤ))⟩
  | t+1 => bitTransition P oracle random (bitProgramExecution P input oracle random t)

/-- No-query/no-coin public-preprocessing specialization; 2607.16541 p.7. -/
def IsPublicPreprocessor (P : BitOracleProgram) : Prop :=
  ∀ op ∈ P.code, (match op with | .query _ _ _ => False | .coin _ => False | _ => True)

/-- Finite fair-tape execution law at a charged transition cap;
2607.16541 p.7, 2610.02145 p.16. -/
def bitExecutionLaw (P : BitOracleProgram) (input : Str) (oracle : Str → Bool) (fuel : ℕ) :
    PMF BitState :=
  (PMF.uniformOfFintype (Fin fuel → Bool)).map fun r =>
    bitProgramExecution P input oracle (fun i => if h : i < fuel then r ⟨i,h⟩ else false) fuel

example (input : Str) (oracle : Str → Bool) (r : ℕ → Bool) :
    (bitProgramExecution ⟨[.halt true]⟩ input oracle r 1).status = some true := by
  simp [bitProgramExecution, bitTransition]

end QAlgorithms.OPI


