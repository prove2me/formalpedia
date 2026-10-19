-- Prove2me | Definitions.Def_QAlgorithms_Defs_NoisyEigenvaluePrograms
-- name    : QAlgorithms_Defs_NoisyEigenvaluePrograms
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:24:17.679977+00:00
-- url     : https://prove2.me/theorems/bf555bb1-812b-48ad-83be-6b0fc2000be1
-- title:
--   NoisyEigenvaluePrograms
-- statement:
--   NoisyEigenvaluePrograms
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\NoisyEigenvaluePrograms.lean

import Definitions.Def_QAlgorithms_Defs_PauliNoiseFourier
noncomputable section

namespace QAlgorithms.SparsePauliNoise

attribute [local instance] Classical.propDecidable

/-- Elementary arithmetic, addressed memory and noisy-eigenvalue reads
(2007.07901 pp.11-15, Algorithms 2-4). Reads access one fixed supplied observation vector. -/
inductive OracleInstruction (n : ℕ) where
  | constant (dst : ℕ) (value : ℝ)
  | add (dst a b : ℕ)
  | sub (dst a b : ℕ)
  | mul (dst a b : ℕ)
  | div (dst a b : ℕ)
  | load (dst base index : ℕ)
  | store (base index src : ℕ)
  | query (dst : ℕ) (address : Label n)
  | compare (a b : ℕ)

/-- Execution records sparse outputs, every query occurrence, and arithmetic work
(2007.07901 pp.12,14-15). Division by zero is explicit failure. -/
structure OracleState (n : ℕ) where
  memory : ℕ → ℝ
  trace : List (Label n)
  output : List (Label n × ℝ)
  work : ℕ
  failed : Bool

/-- Finite adaptive RAM syntax. Random choices are finite, with supplied PMFs;
branches and finite loops do not give hidden rates to the algorithm
(2007.07901 pp.12,14-15). -/
inductive OracleProgram (n : ℕ) where
  | halt
  | fail
  | step (op : OracleInstruction n) (next : Bool → OracleProgram n)
  | draw (size : ℕ) (weights : PMF (Fin size)) (next : Fin size → OracleProgram n)
  | emit (label : Label n) (src : ℕ) (next : OracleProgram n)
  | loop (count : ℕ) (body rest : OracleProgram n)

/-- One executed RAM instruction, with queried addresses recorded with multiplicity
(2007.07901 pp.11-15). Indexed load/store use nonnegative integer addresses. -/
def OracleInstruction.execute {n : ℕ} (observations : Label n → ℝ) (s : OracleState n) :
    OracleInstruction n → Bool × OracleState n :=
  let st := {s with work := s.work+1}
  let set := fun dst value => (false,{st with memory := Function.update s.memory dst value})
  if s.failed then fun _ => (false,s) else
  fun op => match op with
    | .constant dst v => set dst v
    | .add dst a b => set dst (s.memory a+s.memory b)
    | .sub dst a b => set dst (s.memory a-s.memory b)
    | .mul dst a b => set dst (s.memory a*s.memory b)
    | .div dst a b => if s.memory b = 0 then (false,{st with failed := true})
        else set dst (s.memory a/s.memory b)
    | .load dst base index => set dst (s.memory (base+⌊s.memory index⌋₊))
    | .store base index src => set (base+⌊s.memory index⌋₊) (s.memory src)
    | .query dst address => (false,{st with
        memory := Function.update s.memory dst (observations address)
        trace := s.trace ++ [address]})
    | .compare a b => (decide (s.memory a ≤ s.memory b),st)

/-- Computed finite execution law (2007.07901 pp.12,14-15).
No observations are resampled; repeated reads reuse a coordinate and each is charged. -/
def execution {n : ℕ} (observations : Label n → ℝ) :
    OracleProgram n → OracleState n → PMF (OracleState n)
  | .halt, s => PMF.pure s
  | .fail, s => PMF.pure {s with failed := true}
  | .step op next, s =>
      let result := op.execute observations s
      execution observations (next result.1) result.2
  | .draw _ weights next, s =>
      weights.bind fun i => execution observations (next i) {s with work := s.work+1}
  | .emit label src next, s =>
      execution observations next {s with output := s.output ++ [(label,s.memory src)],work := s.work+1}
  | .loop count body rest, s =>
      ((List.range count).foldl (fun law _ => law.bind (execution observations body))
        (PMF.pure s)).bind (execution observations rest)

/-- Straight-line compiler for elementary instructions (2007.07901 pp.12,15). -/
def oracleSteps {n : ℕ} (ops : List (OracleInstruction n)) : OracleProgram n :=
  ops.foldr (fun op next => .step op fun _ => next) .halt

/-- Sequential composition preserves the actual RAM state (2007.07901 Algorithms 2-4). -/
def OracleProgram.then {n : ℕ} : OracleProgram n → OracleProgram n → OracleProgram n
  | .halt, Q => Q
  | .fail, _ => .fail
  | .step op next, Q => .step op fun b => (next b).then Q
  | .draw size weights next, Q => .draw size weights fun i => (next i).then Q
  | .emit label src next, Q => .emit label src (next.then Q)
  | .loop count body rest, Q => .loop count body (rest.then Q)

example {n : ℕ} (observations : Label n → ℝ) (s : OracleState n) :
    execution observations .halt s = PMF.pure s := rfl

example {n : ℕ} (observations : Label n → ℝ) (a : Label n) :
    execution observations (oracleSteps [.query 0 a,.query 1 a])
      ⟨0,[],[],0,false⟩ =
    PMF.pure ⟨Function.update (Function.update 0 0 (observations a)) 1 (observations a),
      [a,a],[],2,false⟩ := rfl


/-- Relocate a decoder's private RAM into its public workspace; loads and stores
retain relative array addressing (2007.07901 pp.14-15, Decode subroutine). -/
def OracleInstruction.relocate {n : ℕ} (shift : ℕ) :
    OracleInstruction n → OracleInstruction n
  | .constant dst value => .constant (shift+dst) value
  | .add dst a b => .add (shift+dst) (shift+a) (shift+b)
  | .sub dst a b => .sub (shift+dst) (shift+a) (shift+b)
  | .mul dst a b => .mul (shift+dst) (shift+a) (shift+b)
  | .div dst a b => .div (shift+dst) (shift+a) (shift+b)
  | .load dst base index => .load (shift+dst) (shift+base) (shift+index)
  | .store base index src => .store (shift+base) (shift+index) (shift+src)
  | .query dst address => .query (shift+dst) address
  | .compare a b => .compare (shift+a) (shift+b)

/-- Relocation is computed from elementary code, not an arbitrary decoder map
(2007.07901 pp.14-15). -/
def OracleProgram.relocate {n : ℕ} (shift : ℕ) : OracleProgram n → OracleProgram n
  | .halt => .halt
  | .fail => .fail
  | .step op next => .step (op.relocate shift) fun b => (next b).relocate shift
  | .draw size weights next => .draw size weights fun i => (next i).relocate shift
  | .emit label src next => .emit label (shift+src) (next.relocate shift)
  | .loop count body rest => .loop count (body.relocate shift) (rest.relocate shift)

/-- Executable decoder interface stores coded sign inputs in addresses 0..P2-1
and decoded 2n bits in addresses P2..P2+2n-1. It supplies lawful syntax only;
being a correct linear-time decoder is supporting construction work
(2007.07901 pp.14-15). -/
def OracleProgram.QueryFree {n : ℕ} : OracleProgram n → Prop
  | .halt => True
  | .fail => True
  | .step op next =>
      (match op with | .query _ _ => False | _ => True) ∧ ∀ b, (next b).QueryFree
  | .draw _ _ next => ∀ i, (next i).QueryFree
  | .emit _ _ next => next.QueryFree
  | .loop _ body rest => body.QueryFree ∧ rest.QueryFree

example {n : ℕ} (shift : ℕ) :
    (OracleProgram.halt (n:=n)).relocate shift = .halt := rfl


/-- Private binary-decoder memory discipline. All accessed addresses are below
the supplied workspace; noisy reads, sparse emission and dynamic addresses are
excluded in this private subroutine (2007.07901 pp.14-15).
This is syntax legality, not decoder correctness or a runtime bound. -/
def OracleProgram.Confined {n : ℕ} (bound : ℕ) : OracleProgram n → Prop
  | .halt => True
  | .fail => True
  | .step op next =>
      (match op with
        | .constant dst _ => dst < bound
        | .add dst a b | .sub dst a b | .mul dst a b | .div dst a b =>
            dst < bound ∧ a < bound ∧ b < bound
        | .compare a b => a < bound ∧ b < bound
        | .load _ _ _ | .store _ _ _ | .query _ _ => False) ∧
      ∀ b, (next b).Confined bound
  | .draw _ _ next => ∀ i, (next i).Confined bound
  | .emit _ _ _ => False
  | .loop _ body rest => body.Confined bound ∧ rest.Confined bound

end QAlgorithms.SparsePauliNoise


