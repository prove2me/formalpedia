-- Prove2me | Definitions.Def_SeedRecyclingDL_Codes_FieldExecution
-- name    : SeedRecyclingDL_Codes_FieldExecution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:53.945195+00:00
-- url     : https://prove2.me/theorems/38e71b44-a28f-46a7-8db6-97defee0fbce
-- title:
--   Elementary field programs and the C.5 computation interfaces
-- statement:
--   A field program is a finite list of elementary register, memory, arithmetic, comparison, input/output, and control instructions. Its arithmetic operations are field addition, multiplication, and inversion; roots, polynomial gcds, tags, and code tables are not instructions. A field execution counts these arithmetic operations and has an actual finite halting run. Separate bit-program claims use the published charged RAM.
--
--   Polynomial inputs are coefficient lists. Bad-list inputs explicitly include the field descriptor, payload, and every competitor-list entry. Their multiplicities remain charged. The total seed bound is
--   $$m+b+(L'+1)(m^2+2^{b-r})b^2+(s+1)b\log_2(s+2).$$
--
--   This layer separates field-operation analysis from the bit-level realization and does not assume either efficient algorithm exists.
-- source:
--   Quan D. Bui, Manabu Hagiwara, Shuche Wang, Van Khu Vu, STOC 2027 submission #1449 (October 2026), Appendix C.1–C.3, PDF pp. 19–21 (printed pp. 17–19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1449.pdf

import Definitions.Def_SeedRecyclingDL_Codes_Execution

set_option autoImplicit false

noncomputable section

namespace SeedRecyclingDL.Codes

/-- Fixed elementary field-register language; no polynomial, root, sorting,
tagging or code-family instructions. The bit realization is a separate conclusion. -/
inductive FieldInstruction where
  | natural (i : EditMulticoloring.Code.RAM.Instruction)
  | zero (d : ℕ)
  | one (d : ℕ)
  | copy (d a : ℕ)
  | add (d a b : ℕ)
  | multiply (d a b : ℕ)
  | invert (d a : ℕ)
  | load (d address : ℕ)
  | store (address a : ℕ)
  | read (d : ℕ)
  | emit (a : ℕ)
  | compare (d a b : ℕ)
  | jumpZero (a pc : ℕ)

structure FieldState (F : Type) where
  natural : MachineState
  registers : ℕ → F
  memory : ℕ → F
  cursor : ℕ
  output : List F
  operations : ℕ

def fieldInitial {F : Type} [Field F] (n : ℕ) : FieldState F :=
  ⟨EditMulticoloring.Code.RAM.initial n, fun _ => 0, fun _ => 0, 0, [], 0⟩

def fieldStep {F : Type} [Field F] (P : List FieldInstruction)
    (index : F → ℕ) (input : List ℕ) (fields : List F) (s : FieldState F) : FieldState F := by
  classical
  exact if s.natural.status.isSome then s else
    let k := s.natural.pc
    let base := {s with natural := {s.natural with pc := k + 1}}
    let reg := fun d v => Function.update s.registers d v
    match P[k]? with
    | none => {base with natural := {base.natural with status := some false}}
    | some (.natural i) =>
      let p := List.replicate k (.jump 0) ++ [i]
      {s with natural := EditMulticoloring.Code.RAM.step p (tape input) s.natural}
    | some (.zero d) => {base with registers := reg d 0}
    | some (.one d) => {base with registers := reg d 1}
    | some (.copy d a) => {base with registers := reg d (s.registers a)}
    | some (.add d a b) =>
      {base with registers := reg d (s.registers a + s.registers b), operations := s.operations + 1}
    | some (.multiply d a b) =>
      {base with registers := reg d (s.registers a * s.registers b), operations := s.operations + 1}
    | some (.invert d a) =>
      {base with registers := reg d (s.registers a)⁻¹, operations := s.operations + 1}
    | some (.load d a) => {base with registers := reg d (s.memory (s.natural.registers a))}
    | some (.store a r) =>
      {base with memory := Function.update s.memory (s.natural.registers a) (s.registers r)}
    | some (.read d) =>
      {base with registers := reg d (fields[s.cursor]?.getD 0), cursor := s.cursor + 1}
    | some (.emit a) => {base with output := s.output ++ [s.registers a]}
    | some (.compare d a b) =>
      {base with natural := {base.natural with registers := (EditMulticoloring.Code.RAM.setReg base.natural d (if index (s.registers a) < index (s.registers b) then 1 else 0))}}
    | some (.jumpZero a pc) =>
      {base with natural := {base.natural with pc := if s.registers a = 0 then pc else k + 1}}

def fieldRun {F : Type} [Field F] (P : List FieldInstruction) (index : F → ℕ) (input : List ℕ) (fields : List F) :
    ℕ → FieldState F → FieldState F
  | 0, s => s
  | fuel + 1, s => fieldRun P index input fields fuel (fieldStep P index input fields s)

def FieldExecutes {F : Type} [Field F] [Fintype F] (pres : FieldPresentation F) (P : List FieldInstruction)
    (n : ℕ) (input : List ℕ) (fields result : List F) (bound : ℝ) : Prop :=
  ∃ fuel : ℕ, let final := fieldRun P (fieldIndex pres) input fields fuel (fieldInitial n)
    final.natural.status = some true ∧ final.output = result ∧ (final.operations : ℝ) ≤ bound

def coefficientList {F : Type} [Field F] (R : Polynomial F) : List F :=
  List.ofFn fun i : Fin (R.natDegree + 1) => R.coeff i.val

def rootInput {F : Type} [Field F] [Fintype F]
    (P : FieldPresentation F) (R : Polynomial F) : List ℕ :=
  fieldDescriptor P ++ [R.natDegree] ++ (coefficientList R).map (fieldIndex P)


def badListInput {F : Type} [Field F] [Fintype F]
    (P : FieldPresentation F) (m r : ℕ) (x : Word) (competitors : List Word) : List ℕ :=
  fieldDescriptor P ++ [m, r] ++ packedWord x ++ [competitors.length] ++ packedWords competitors

def seedFieldInputs {F : Type} [Field F] [Fintype F]
    (P : FieldPresentation F) (m : ℕ) (x : Word) (competitors : List Word) : List F :=
  P.generator :: ((x :: competitors).flatMap fun u =>
    (List.range (blockCount m P.k)).map fun i => (payloadPolynomial P m u).coeff i)

def seedBitBound (m b r entries s : ℕ) : ℝ :=
  (m : ℝ) + b + (entries + 1 : ℕ) * ((m : ℝ) ^ 2 + (2 : ℝ) ^ (b - r)) * (b : ℝ) ^ 2 +
    (s + 1 : ℕ) * (b : ℝ) * log₂ (s + 2)

end SeedRecyclingDL.Codes


