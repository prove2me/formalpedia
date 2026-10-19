-- Prove2me | Definitions.Def_QAlgorithms_Defs_ShadowLearnerPrograms
-- name    : QAlgorithms_Defs_ShadowLearnerPrograms
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:38.119414+00:00
-- url     : https://prove2.me/theorems/70b9bb90-b733-4709-a059-39df9cba8486
-- title:
--   ShadowLearnerPrograms
-- statement:
--   ShadowLearnerPrograms
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ShadowLearnerPrograms.lean

import Definitions.Def_QAlgorithms_Defs_DirichletShadowLearning
noncomputable section

namespace QAlgorithms.GroundStateLearning

attribute [local instance] Classical.propDecidable

/-- Elementary real RAM instructions for loading training coordinates, six-valued
Pauli labels and observable entries, and explicitly evaluating Fourier terms
(2106.12627 pp.35-36, F42-F47). Cosine is elementary; a whole kernel is not. -/
inductive LearnerInstruction where
  | constant (dst : ℕ) (value : ℝ)
  | coordinate (dst src : ℕ)
  | label (dst src : ℕ)
  | observable (dst src : ℕ)
  | add (dst a b : ℕ)
  | sub (dst a b : ℕ)
  | mul (dst a b : ℕ)
  | div (dst a b : ℕ)
  | cosine (dst a : ℕ)
  | load (dst base index : ℕ)
  | store (base index src : ℕ)

/-- Deterministic finite programs over addressed memory, with finite loops and
comparisons, chosen before training draws (2106.12627 F42-F47). -/
inductive LearnerProgram where
  | halt
  | step (op : LearnerInstruction) (next : LearnerProgram)
  | compare (a b : ℕ) (yes no : LearnerProgram)
  | loop (count : ℕ) (body rest : LearnerProgram)

/-- Computed memory, touched addresses and executed work; a zero sample divisor fails
rather than returning a spurious prediction (2106.12627 F43-F47). -/
structure LearnerState where
  memory : ℕ → ℝ
  stored : Finset ℕ
  work : ℕ
  failed : Bool

/-- Each explicit arithmetic, load/store or cosine costs one operation.
Training labels and local entries are supplied data, not an expectation oracle
(2106.12627 pp.35-36). -/
def LearnerInstruction.execute (coordinates : ℕ → ℝ) (labels : ℕ → Fin 6)
    (observableEntries : ℕ → ℝ) (s : LearnerState) : LearnerInstruction → LearnerState :=
  if s.failed then fun _ => s else
  let st := {s with work := s.work+1}
  let set := fun dst value => { st with memory := Function.update s.memory dst value, stored := insert dst s.stored }
  fun op => match op with
    | .constant dst value => set dst value
    | .coordinate dst src => set dst (coordinates src)
    | .label dst src => set dst (labels src).val
    | .observable dst src => set dst (observableEntries src)
    | .add dst a b => set dst (s.memory a+s.memory b)
    | .sub dst a b => set dst (s.memory a-s.memory b)
    | .mul dst a b => set dst (s.memory a*s.memory b)
    | .div dst a b => if s.memory b = 0 then {st with failed := true}
        else set dst (s.memory a/s.memory b)
    | .cosine dst a => set dst (Real.cos (s.memory a))
    | .load dst base index => set dst (s.memory (base+⌊s.memory index⌋₊))
    | .store base index src => set (base+⌊s.memory index⌋₊) (s.memory src)

/-- Computed deterministic RAM execution. Every finite-frequency kernel must be
compiled into its component arithmetic and cosine instructions
(2106.12627 pp.35-36, F42-F47). -/
def learnerExecution (coordinates : ℕ → ℝ) (labels : ℕ → Fin 6)
    (observableEntries : ℕ → ℝ) : LearnerProgram → LearnerState → LearnerState
  | .halt, s => s
  | .step op next, s =>
      learnerExecution coordinates labels observableEntries next
        (op.execute coordinates labels observableEntries s)
  | .compare a b yes no, s =>
      if s.memory a ≤ s.memory b then
        learnerExecution coordinates labels observableEntries yes {s with work := s.work+1}
      else learnerExecution coordinates labels observableEntries no {s with work := s.work+1}
  | .loop count body rest, s =>
      learnerExecution coordinates labels observableEntries rest
        ((List.range count).foldl
          (fun state _ => learnerExecution coordinates labels observableEntries body state) s)

example (coordinates : ℕ → ℝ) (labels : ℕ → Fin 6) (entries : ℕ → ℝ) (s : LearnerState) :
    learnerExecution coordinates labels entries .halt s = s := rfl

example (coordinates : ℕ → ℝ) (labels : ℕ → Fin 6) (entries : ℕ → ℝ) :
    (learnerExecution coordinates labels entries (.step (.div 0 1 2) .halt)
      ⟨0,∅,0,false⟩).failed = true := by
  simp [learnerExecution,LearnerInstruction.execute]

end QAlgorithms.GroundStateLearning


