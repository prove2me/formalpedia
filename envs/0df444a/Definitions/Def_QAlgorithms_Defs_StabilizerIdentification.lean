-- Prove2me | Definitions.Def_QAlgorithms_Defs_StabilizerIdentification
-- name    : QAlgorithms_Defs_StabilizerIdentification
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:14:46.802237+00:00
-- url     : https://prove2.me/theorems/42d58140-dd38-4b96-a680-0b4e67743e48
-- title:
--   StabilizerIdentification
-- statement:
--   StabilizerIdentification
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\StabilizerIdentification.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
noncomputable section

open QAlgorithms.Stabilizer

namespace QAlgorithms.StabilizerLearning

variable {n m d k b w M K N c out : ℕ}

/-- The complete finite set of all tableaux, with an explicit failure label.
Multiple labels for the same physical state all count as success
(2609.10974 pp.2,5,13). -/
abbrev IdentificationLabel (n : ℕ) :=
  Option (Fin n → ZMod 4 × (Fin n → Stabilizer.Pauli))

/-- Convert the finite label to the frozen Pauli tableau, 2609.10974 p.5. -/
def labelTableau {n : ℕ} (T : Fin n → ZMod 4 × (Fin n → Stabilizer.Pauli)) : Tableau n :=
  fun i => ⟨(T i).1, (T i).2⟩

/-- Unrestricted, phase-invariant, worst-case stabilizer identification
POVM on t copies (2609.10974 pp.2,5,13). -/
def IsIdentificationPOVM (n t : ℕ) (delta : ℝ)
    (M : IdentificationLabel n → Matrix (Fin t → Qubits n) (Fin t → Qubits n) ℂ) : Prop :=
  IsPOVM M ∧ ∀ psi : EuclideanSpace ℂ (Qubits n), IsStabilizerState psi →
    (open Classical in
      povmEventProb M (pureDensity (tensorPow t psi)) (fun o => match o with
        | none => False
        | some T => IsValidTableau (labelTableau T) ∧
            tableauProjector (labelTableau T) = pureDensity psi)) ≥ 1 - delta

/-- Minimum number of copies over all identification measurements,
2609.10974 p.2. No feasible count gives infinity, never zero. -/
def copyComplexity (n : ℕ) (delta : ℝ) : ℕ∞ :=
  sInf {k : ℕ∞ | ∃ t : ℕ, k = t ∧
    ∃ M : IdentificationLabel n → Matrix (Fin t → Qubits n) (Fin t → Qubits n) ℂ,
      IsIdentificationPOVM n t delta M}

/-- Sanity check for the modeled source objects (arxiv-2609.10974v1, PDF pp.2,5,13). -/
example (n : ℕ) (delta : ℝ)
    (h : ∀ t M, ¬ IsIdentificationPOVM n t delta M) :
    copyComplexity n delta = ⊤ := by
  have he : {k : ℕ∞ | ∃ t : ℕ, k = t ∧
    ∃ M : IdentificationLabel n → Matrix (Fin t → Qubits n) (Fin t → Qubits n) ℂ,
      IsIdentificationPOVM n t delta M} = ∅ := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨t, _, M, hM⟩
    exact h t M hM
  simp [copyComplexity, he]

/-- Sanity check for the modeled source objects (arxiv-2609.10974v1, PDF pp.2,5,13). -/
example (psi : EuclideanSpace ℂ (Qubits 1)) (z : Fin 0 → Qubits 1) :
    tensorPow 0 psi z = 1 := by simp [tensorPow]

end QAlgorithms.StabilizerLearning


