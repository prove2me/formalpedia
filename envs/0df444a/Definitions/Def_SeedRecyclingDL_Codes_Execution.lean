-- Prove2me | Definitions.Def_SeedRecyclingDL_Codes_Execution
-- name    : SeedRecyclingDL_Codes_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:52.430247+00:00
-- url     : https://prove2.me/theorems/6dc208d0-222c-4d8a-9946-57340f607597
-- title:
--   Charged setup, shared public memory, and resumed executions
-- statement:
--   Finite programs reuse the published RAM instructions, states, transitions, and accumulated bit charges. Setup begins with zero working memory and must construct the exact modulus descriptors and greedy tables required by its variant. Online operations retain that memory in place, protect it at every intermediate step, initialize the finite register footprint with an explicit charge, and start fresh input/output state and a fresh counter.
--
--   Execution predicates require a finite halting run with its actual output and actual accumulated cost. The main code predicate requires injectivity, disjoint DL output balls, systematic payload bits, full-message recovery, and exact payload recovery. No correctness or efficiency certificate is an input to the headline theorem.
--
--   **Formalization Note** Words returned in natural cells use length and binary value. Main decoders, generic decoders, and bootstrap family interfaces use raw bit streams for their inputs and returned words. Public cells occupy even addresses; odd addresses provide fresh scratch space without advice-size address overhead.
-- source:
--   Quan D. Bui, Manabu Hagiwara, Shuche Wang, Van Khu Vu, STOC 2027 submission #1449 (October 2026), Appendix C.1, PDF pp. 19–20 (printed pp. 17–18); Appendix D.2, PDF p. 25 (printed p. 23); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1449.pdf

import Definitions.Def_SeedRecyclingDL_Codes_Construction

set_option autoImplicit false

noncomputable section

namespace SeedRecyclingDL.Codes

abbrev Program := EditMulticoloring.Code.RAM.Program
abbrev MachineState := EditMulticoloring.Code.RAM.State

/-- Finite alphabets serve only to carry arbitrary-precision natural input cells.
The same finite instruction program works at every alphabet size. -/
def tape (xs : List ℕ) : List (Fin (xs.foldl max 0 + 1)) :=
  xs.map fun x => ⟨min x (xs.foldl max 0), Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

def packedWord (u : Word) : List ℕ := [u.length, value u]

def packedWords (us : List Word) : List ℕ := us.flatMap packedWord

def Executes (P : Program) (n : ℕ) (input : List ℕ) (result : Option (List ℕ)) (bound : ℝ) : Prop :=
  EditMulticoloring.Code.RAM.Executes P n (tape input) result bound

def Halts (P : Program) (n : ℕ) (input : List ℕ) (result : Option (List ℕ)) : Prop :=
  ∃ bound : ℝ, Executes P n input result bound

def fieldDescriptor {F : Type} [Field F] [Fintype F] (P : FieldPresentation F) : List ℕ :=
  [P.p, P.k] ++ (List.ofFn P.coefficients).map Fin.val

def setupCells (data : ℕ → FieldData) (v : Variant) (t n : ℕ) : List ℕ :=
  let outer := fieldDescriptor (data n).presentation
  match v with
  | .greedy => outer ++ packedWords (dlGreedyTable t (greedySuffix t n))
  | .bootstrapped =>
    let N := suffixLength t n .bootstrapped
    outer ++ fieldDescriptor (data N).presentation ++
      packedWords (dlGreedyTable t (greedySuffix t N))

def SetupState (cells : List ℕ) (s : MachineState) : Prop :=
  s.status = some true ∧ s.registers 1 = cells.length ∧
  ∀ i : ℕ, s.memory i = if i % 2 = 0 then cells[i / 2]?.getD 0 else 0

def SetupExecutes (P : Program) (n : ℕ) (cells : List ℕ) (s : MachineState) (bound : ℝ) : Prop :=
  ∃ fuel : ℕ, s = EditMulticoloring.Code.RAM.run P ([] : Word) fuel
    (EditMulticoloring.Code.RAM.initial n) ∧ SetupState cells s ∧ (s.cost : ℝ) ≤ bound

/-- Registers and tape/output cursors start afresh. Public memory is retained in
place; there is no uncharged table copy. Initialization has an explicit charge. -/
def resumed (n : ℕ) (s : MachineState) (initializationCharge : ℕ) : MachineState :=
  { pc := 0
    registers := fun i => if i = 0 then n else if i = 1 then s.registers 1 else 0
    memory := s.memory
    cursor := 0
    output := []
    status := none
    cost := initializationCharge + EditMulticoloring.Code.RAM.bits n +
      EditMulticoloring.Code.RAM.bits (s.registers 1) }

def instructionRegisters : EditMulticoloring.Code.RAM.Instruction → List ℕ
  | .literal d _ => [d]
  | .copy d a => [d, a]
  | .arithmetic _ d a b => [d, a, b]
  | .load d a => [d, a]
  | .store a r => [a, r]
  | .read d => [d]
  | .emit a => [a]
  | .jumpZero a _ => [a]
  | _ => []

def initializationCharge (P : Program) : ℕ :=
  let K := (P.flatMap instructionRegisters).foldl max 1
  (K + 1) * (EditMulticoloring.Code.RAM.bits K + 1)

def ResumedExecutes (P : Program) (n : ℕ) (s : MachineState)
    (input : List ℕ) (result : Option (List ℕ)) (bound : ℝ) : Prop :=
  ∃ fuel : ℕ,
    let start := resumed n s (initializationCharge P)
    let final := EditMulticoloring.Code.RAM.run P (tape input) fuel start
    (match result with
      | none => final.status = some false
      | some out => final.status = some true ∧ final.output = out) ∧
    (final.cost : ℝ) ≤ bound ∧
    ∀ j ≤ fuel, ∀ i < s.registers 1,
      (EditMulticoloring.Code.RAM.run P (tape input) j start).memory (2 * i) = s.memory (2 * i)

structure Programs where
  setup : Program
  encoder : Program
  decoder : Program
  payload : Program

def onlineBound (C : ℝ) (t n : ℕ) : ℝ := C * (n : ℝ) ^ (2 * t + 2) * (log₂ n) ^ 2
def payloadBound (C : ℝ) (t n : ℕ) : ℝ := C * (n : ℝ) ^ (t + 1) * log₂ n

def ExplicitVariant (data : ℕ → FieldData) (progs : Programs) (v : Variant)
    (t n : ℕ) (C Cpayload : ℝ) (setupBound : ℝ) : Prop :=
  ∃ saved : MachineState,
    SetupExecutes progs.setup n (setupCells data v t n) saved setupBound ∧
    (∀ mu : Word, mu.length = messageLength v t n →
      ResumedExecutes progs.encoder n saved (mu.map Fin.val)
        (some ((finalEncode data v t n mu).map Fin.val)) (onlineBound C t n)) ∧
    (∀ y : Word,
      ResumedExecutes progs.decoder n saved (y.map Fin.val)
        ((finalDecode data v t n y).map (List.map Fin.val)) (onlineBound C t n)) ∧
    (∀ y : Word,
      ResumedExecutes progs.payload n saved (y.map Fin.val)
        ((finalPayload data v t n y).map (List.map Fin.val)) (payloadBound Cpayload t n))

def finalCode (data : ℕ → FieldData) (v : Variant) (t n : ℕ) : Set Word :=
  {c | ∃ mu : Word, mu.length = messageLength v t n ∧ c = finalEncode data v t n mu}

def FinalCorrect (data : ℕ → FieldData) (v : Variant) (t n : ℕ) : Prop :=
  (∀ mu : Word, mu.length = messageLength v t n → (finalEncode data v t n mu).length = n) ∧
  (∀ mu mu' : Word, mu.length = messageLength v t n → mu'.length = messageLength v t n →
    finalEncode data v t n mu = finalEncode data v t n mu' → mu = mu') ∧
  Corrects (dlChannel t) n (finalCode data v t n) ∧
  (∀ mu : Word, mu.length = messageLength v t n →
    (finalEncode data v t n mu).take (n - suffixLength t n v) = mu.take (n - suffixLength t n v)) ∧
  ∀ mu y : Word, mu.length = messageLength v t n →
    Reaches t (finalEncode data v t n mu) y →
    finalDecode data v t n y = some mu ∧
    finalPayload data v t n y = some (mu.take (n - suffixLength t n v))

end SeedRecyclingDL.Codes


