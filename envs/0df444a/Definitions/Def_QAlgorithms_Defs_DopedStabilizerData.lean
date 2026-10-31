-- Prove2me | Definitions.Def_QAlgorithms_Defs_DopedStabilizerData
-- name    : QAlgorithms_Defs_DopedStabilizerData
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T04:10:45.114105+00:00
-- url     : https://prove2.me/theorems/36ab66e5-feb3-404c-91af-d3d2b3ba4a22
-- title:
--   prove2quantum library: Defs.DopedStabilizerData
-- statement:
--   Shared definitions of the prove2quantum Lean library (`QAlgorithms.Defs.DopedStabilizerData`), reused by its paper formalizations.
--
--   - `PreparationStep`: Clifford/T preparation instructions on named wires (2305.15398 pp.1-3, §2).
--   - `PreparationWord`: The preparation word is unknown to the learner (2305.15398 pp.1-3, §2).
--   - `PreparationWord.unitary`: Concrete chronological matrix action of a preparation word (2305.15398 p.3).
--   - `PreparationWord.tCount`: Number of T applications, counted from syntax (2305.15398 p.3).
--   - `IsTDoped`: Normalized t-doped stabilizer states, with global phase represented by density equality (2305.15398 pp.1-3, §2).
--   - `unsignedStabilizer`: Full unsigned stabilizer labels; eigenvalue signs are kept separate (2305.15398 p.2, Eq.(1)).
--   - `pauliSupport`: Nonzero Pauli support of the state (2305.15398 pp.2-3, Eqs.(2)-(3)).
--   - `labelCoset`: Label coset with scalar phases removed (2305.15398 pp.2-3, Eq.(2)).
--   - `badCosets`: Computed nonidentity cosets in the Pauli support; duplicate cosets are removed as sets (2305.15398 pp.2-3, Eqs.(2)-(3)).
-- source:
--   prove2quantum Lean library, module QAlgorithms.Defs.DopedStabilizerData

import Definitions.Def_QAlgorithms_Defs_ProjectiveCliffords
import Definitions.Def_QAlgorithms_Defs_StabilizerLearning

noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.DopedTomography

/-- Clifford/T preparation instructions on named wires (2305.15398 pp.1-3, §2). -/
inductive PreparationStep (n : ℕ) where
  | clifford (U : Clifford.normalizer n)
  | tgate (q : Fin n)

/-- The preparation word is unknown to the learner (2305.15398 pp.1-3, §2). -/
abbrev PreparationWord (n : ℕ) := List (PreparationStep n)

/-- Concrete chronological matrix action of a preparation word (2305.15398 p.3). -/
def PreparationWord.unitary {n : ℕ} (word : PreparationWord n) : Matrix (Qubits n) (Qubits n) ℂ :=
  (word.map fun step => match step with
    | .clifford U => (U.val : Matrix _ _ ℂ)
    | .tgate q => qubitOp1 gateT q).reverse.prod

/-- Number of T applications, counted from syntax (2305.15398 p.3). -/
def PreparationWord.tCount {n : ℕ} (word : PreparationWord n) : ℕ :=
  word.countP fun step => match step with | .clifford _ => false | .tgate _ => true

/-- Normalized t-doped stabilizer states, with global phase represented by density equality
(2305.15398 pp.1-3, §2). -/
def IsTDoped {n : ℕ} (t : ℕ) (psi : EuclideanSpace ℂ (Qubits n)) : Prop :=
  IsState psi ∧ ∃ word : PreparationWord n, word.tCount = t ∧
    pureDensity psi = pureDensity (act word.unitary (zeroKet n))

/-- Full unsigned stabilizer labels; eigenvalue signs are kept separate
(2305.15398 p.2, Eq.(1)). -/
def unsignedStabilizer {n : ℕ} (psi : EuclideanSpace ℂ (Qubits n)) (_state : IsState psi) :
    Finset (Fin n → Stabilizer.Pauli) :=
  Finset.univ.filter fun P => act (pauliOps P) psi = psi ∨ act (pauliOps P) psi = -psi

/-- Nonzero Pauli support of the state (2305.15398 pp.2-3, Eqs.(2)-(3)). -/
def pauliSupport {n : ℕ} (psi : EuclideanSpace ℂ (Qubits n)) (_state : IsState psi) :
    Finset (Fin n → Stabilizer.Pauli) :=
  Finset.univ.filter fun P => (pauliOps P*pureDensity psi).trace.re ≠ 0

/-- Label coset with scalar phases removed (2305.15398 pp.2-3, Eq.(2)). -/
def labelCoset {n : ℕ} (H : Finset (Fin n → Stabilizer.Pauli)) (P : Fin n → Stabilizer.Pauli) :
    Finset (Fin n → Stabilizer.Pauli) := H.image (Clifford.phaseFreeProduct P)

/-- Computed nonidentity cosets in the Pauli support; duplicate cosets are removed as sets
(2305.15398 pp.2-3, Eqs.(2)-(3)). -/
def badCosets {n : ℕ} (psi : EuclideanSpace ℂ (Qubits n)) (state : IsState psi) :
    Finset (Finset (Fin n → Stabilizer.Pauli)) :=
  ((pauliSupport psi state).image (labelCoset (unsignedStabilizer psi state))).erase
    (unsignedStabilizer psi state)

example (n : ℕ) : PreparationWord.unitary ([] : PreparationWord n) = 1 := rfl

example (n : ℕ) : PreparationWord.tCount ([] : PreparationWord n) = 0 := rfl

example (n : ℕ) : IsTDoped 0 (zeroKet n) := by
  refine ⟨by simp [IsState, zeroKet, ket], [], rfl, ?_⟩
  simp [PreparationWord.unitary, act]

end QAlgorithms.DopedTomography


