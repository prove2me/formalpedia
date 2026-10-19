-- Prove2me | Definitions.Def_QAlgorithms_Defs_ClassicalDecoderMachines
-- name    : QAlgorithms_Defs_ClassicalDecoderMachines
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:29:14.407799+00:00
-- url     : https://prove2.me/theorems/80aaa0d4-7179-4e91-9485-2b4364ff1ee8
-- title:
--   ClassicalDecoderMachines
-- statement:
--   ClassicalDecoderMachines
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ClassicalDecoderMachines.lean

import Definitions.Def_QAlgorithms_Defs_ExpanderCodeDecoding
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.ExpanderCodes

/-- Uniform-cost RAM instruction set; 1504.00822 pp.6,8.
Each indexed access, arithmetic operation, allocation and output word costs one;
scans and maximization must be programmed. -/
inductive WordInstruction where
  | constant (dst value : ℕ)
  | load (dst address : ℕ)
  | store (address src : ℕ)
  | add (dst a b : ℕ)
  | sub (dst a b : ℕ)
  | mul (dst a b : ℕ)
  | div (dst a b : ℕ)
  | xor (dst a b : ℕ)
  | compare (a b yes no : ℕ)
  | jump (pc : ℕ)
  | allocate (words : ℕ)
  | emit (src : ℕ)
  | finish (success : Bool)

/-- Word-machine state; 1504.00822 p.8. Output is emitted word by word. -/
structure WordState where
  memory : ℕ → ℕ
  pc : ℕ
  allocated : ℕ
  output : List ℕ
  halted : Option Bool
  steps : ℕ

/-- Concrete decoder program independent of the unknown error; 1504.00822 pp.6–8.
Agreement with small-set-flip and linear runtime are conclusions, not fields. -/
structure DecoderImplementation where
  instructions : List WordInstruction

/-- One charged RAM transition; 1504.00822 p.8. Invalid PC/division halts with failure. -/
def wordTransition (P : DecoderImplementation) (s : WordState) : WordState :=
  if s.halted.isSome then s else
  let t := {s with pc := s.pc+1, steps := s.steps+1}
  let set := fun dst value => {t with memory := Function.update s.memory dst value}
  match P.instructions[s.pc]? with
  | none => {t with halted := some false}
  | some (.constant dst value) => set dst value
  | some (.load dst address) => set dst (s.memory (s.memory address))
  | some (.store address src) => set (s.memory address) (s.memory src)
  | some (.add dst a b) => set dst (s.memory a+s.memory b)
  | some (.sub dst a b) => set dst (s.memory a-s.memory b)
  | some (.mul dst a b) => set dst (s.memory a*s.memory b)
  | some (.div dst a b) => if s.memory b = 0 then {t with halted := some false}
      else set dst (s.memory a/s.memory b)
  | some (.xor dst a b) => set dst (Nat.xor (s.memory a) (s.memory b))
  | some (.compare a b yes no) => {t with pc := if s.memory a ≤ s.memory b then yes else no}
  | some (.jump pc) => {t with pc := pc}
  | some (.allocate words) => {t with allocated := s.allocated+words}
  | some (.emit src) => {t with output := s.output ++ [s.memory src]}
  | some (.finish success) => {t with halted := some success}

/-- Full transition trajectory on the encoded adjacency-list/syndrome input;
1504.00822 pp.6,8. Divergence means no finite trajectory state halts. -/
def decoderExecution (P : DecoderImplementation) (input : List ℕ) : ℕ → WordState
  | 0 => ⟨fun i => input.getD i 0,0,input.length,[],none,0⟩
  | t+1 => wordTransition P (decoderExecution P input t)

/-- Canonical labelled adjacency-list and syndrome input; 1504.00822 pp.4,6,8.
The header gives both part sizes and degrees, followed by each labelled neighbor list
and the two row-major syndrome bit arrays. Hidden errors are absent. -/
def decoderInput {nA nB : ℕ} (G : BipartiteData nA nB)
    (s : ((Fin nA × Fin nB) → ZMod 2) × ((Fin nB × Fin nA) → ZMod 2)) : List ℕ :=
  [nA,nB,G.degreeA,G.degreeB] ++
  ((List.finRange nA).flatMap fun a =>
    (List.finRange nB).filterMap fun b => if G.adjacent a b then some b.val else none) ++
  ((List.finRange nB).flatMap fun b =>
    (List.finRange nA).filterMap fun a => if G.adjacent a b then some a.val else none) ++
  (List.ofFn fun i : Fin (nA*nB) => (s.1 (finProdFinEquiv.symm i)).val) ++
  (List.ofFn fun i : Fin (nB*nA) => (s.2 (finProdFinEquiv.symm i)).val)

/-- Decode the emitted correction arrays; 1504.00822 pp.6–8.
A nonhalting/failed or malformed result is failure. Successful output has exactly
two physical-coordinate arrays, variable-variable summand before check-check. -/
def decoderOutput (nA nB : ℕ) (s : WordState) :
    Option (Error ((Fin nA × Fin nA) ⊕ (Fin nB × Fin nB))) :=
  let length := nA*nA+nB*nB
  if s.halted = some true ∧ s.output.length = 2*length ∧
      (∀ bit ∈ s.output, bit ≤ 1) then
    let e := HypergraphProduct.coordinateEquiv nA nA nB nB
    some (fun q => (s.output.getD (e q).val 0 : ZMod 2),
      fun q => (s.output.getD (length+(e q).val) 0 : ZMod 2))
  else none

/-- Halting time, infinity for divergence; 1504.00822 p.8. -/
def decoderTime (P : DecoderImplementation) (input : List ℕ) : ℕ∞ :=
  ⨅ t : {t : ℕ // (decoderExecution P input t).halted.isSome}, (t.val : ℕ∞)

example (input : List ℕ) :
    (decoderExecution ⟨[.finish true]⟩ input 1).steps = 1 ∧
      (decoderExecution ⟨[.finish true]⟩ input 1).halted = some true := by
  simp [decoderExecution, wordTransition]

end QAlgorithms.ExpanderCodes


