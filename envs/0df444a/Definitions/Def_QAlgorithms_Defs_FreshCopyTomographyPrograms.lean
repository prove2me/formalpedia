-- Prove2me | Definitions.Def_QAlgorithms_Defs_FreshCopyTomographyPrograms
-- name    : QAlgorithms_Defs_FreshCopyTomographyPrograms
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T04:14:36.836421+00:00
-- url     : https://prove2.me/theorems/f9834cc4-aaf9-4f7c-bd17-491aacedb124
-- title:
--   prove2quantum library: Defs.FreshCopyTomographyPrograms
-- statement:
--   Shared definitions of the prove2quantum Lean library (`QAlgorithms.Defs.FreshCopyTomographyPrograms`), reused by its paper formalizations.
--
--   - `BellLabel`: Phase-free Bell labels (2305.15398 p.5, Eqs.(9)-(10)).
--   - `bellVector`: Bell basis vector (I tensor P)|Phi>, with normalized maximally entangled state (2305.15398 p.5, §4).
--   - `bellInstrument`: Projective Bell instrument: a single Kraus operator |P><P| for each phase-free label. The basis is computed from Paulis, not chosen from the unknown state (2305.15398 p.5). Completeness of this explicit family is supporting verification, not an accuracy field.
--   - `bellShot`: Actual Bell probability on two fresh copies of the same rotated state; neither copy is replaced by a conjugate (2305.15398 p.5, Eq.(10)).
--   - `pauliProjector`: Single-copy Pauli projectors, with true representing +1 (2305.15398 p.4, stabilizer test).
--   - `pauliShot`: Actual one-copy Pauli shot after a known Clifford rotation (2305.15398 pp.4,6). No access to an exact expectation oracle is granted.
--   - `CopyClassicalInstruction`: Explicit elementary classical register operations, not arbitrary real maps at unit cost (2305.15398 pp.4,6, generator extraction and tableau manipulation).
--   - `CopyClassicalInstruction.run`: Computed classical transition and branch flag; one executed instruction costs one additional operation (2305.15398 pp.4,6).
--   - `CopyProgram`: Finite adaptive fresh-copy program with explicit elementary classical work. Bell nodes consume two copies and Pauli nodes one. Report leaves are fixed finite code, not a true-state certified report (2305.15398 pp.4-6).
--   - `CopyLeaf`: Branch data: optional report, counters (Bell outcomes, Pauli shots, additional work), and actual Born weight (2305.15398 p.6, resource paragraph).
--   - `copyProgramLaw`: Computed fresh-copy program law. The separate counters retain failed reports. No probability, tomography or resource guarantees are assumed (2305.15398 pp.4-6).
--   - `CopyLeaf.copies`: Physical copies are computed from separate fresh-shot counters (2305.15398 p.6: a Bell outcome is obtained from two copies).
-- source:
--   prove2quantum Lean library, module QAlgorithms.Defs.FreshCopyTomographyPrograms

import Definitions.Def_QAlgorithms_Defs_DopedPauliDescriptions
import Definitions.Def_QAlgorithms_Defs_FiniteVectorSamplingPrograms

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix

namespace QAlgorithms.DopedTomography

/-- Phase-free Bell labels (2305.15398 p.5, Eqs.(9)-(10)). -/
abbrev BellLabel (n : ℕ) := Fin n → Stabilizer.Pauli

/-- Bell basis vector (I tensor P)|Phi>, with normalized maximally entangled state
(2305.15398 p.5, §4). -/
def bellVector {n : ℕ} (P : BellLabel n) : EuclideanSpace ℂ (Qubits n × Qubits n) :=
  act (Matrix.kronecker (1 : Matrix (Qubits n) (Qubits n) ℂ) (pauliOps P)) (maxEntangled n)

/-- Projective Bell instrument: a single Kraus operator |P><P| for each phase-free label.
The basis is computed from Paulis, not chosen from the unknown state (2305.15398 p.5).
Completeness of this explicit family is supporting verification, not an accuracy field. -/
def bellInstrument {n : ℕ} (P : BellLabel n) :
    Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ :=
  pureDensity (bellVector P)

/-- Actual Bell probability on two fresh copies of the same rotated state; neither copy
is replaced by a conjugate (2305.15398 p.5, Eq.(10)). -/
def bellShot {n : ℕ} (psi : EuclideanSpace ℂ (Qubits n)) (_state : IsState psi)
    (U : Matrix.unitaryGroup (Qubits n) ℂ) (P : BellLabel n) : ℝ :=
  let phi := act (U : Matrix _ _ ℂ) psi
  effectProb (bellInstrument P) (pureDensity (tensorVec phi phi))

/-- Single-copy Pauli projectors, with true representing +1 (2305.15398 p.4, stabilizer test). -/
def pauliProjector {n : ℕ} (P : BellLabel n) (plus : Bool) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  (2⁻¹ : ℂ) • (1+(if plus then (1 : ℂ) else -1) • pauliOps P)

/-- Actual one-copy Pauli shot after a known Clifford rotation (2305.15398 pp.4,6).
No access to an exact expectation oracle is granted. -/
def pauliShot {n : ℕ} (psi : EuclideanSpace ℂ (Qubits n)) (_state : IsState psi)
    (U : Clifford.normalizer n) (P : BellLabel n) (plus : Bool) : ℝ :=
  effectProb (pauliProjector P plus) (pureDensity (act (U.val : Matrix _ _ ℂ) psi))

/-- Explicit elementary classical register operations, not arbitrary real maps at unit cost
(2305.15398 pp.4,6, generator extraction and tableau manipulation). -/
inductive CopyClassicalInstruction where
  | constant (dst value : ℕ)
  | add (dst a b : ℕ)
  | xor (dst a b : ℕ)
  | load (dst address : ℕ)
  | store (address src : ℕ)
  | compare (a b : ℕ)

/-- Computed classical transition and branch flag; one executed instruction costs one
additional operation (2305.15398 pp.4,6). -/
def CopyClassicalInstruction.run (memory : ℕ → ℕ) :
    CopyClassicalInstruction → Bool × (ℕ → ℕ)
  | .constant dst value => (false,Function.update memory dst value)
  | .add dst a b => (false,Function.update memory dst (memory a+memory b))
  | .xor dst a b => (false,Function.update memory dst (Nat.xor (memory a) (memory b)))
  | .load dst address => (false,Function.update memory dst (memory (memory address)))
  | .store address src => (false,Function.update memory (memory address) (memory src))
  | .compare a b => (decide (memory a ≤ memory b),memory)

/-- Finite adaptive fresh-copy program with explicit elementary classical work. Bell nodes
consume two copies and Pauli nodes one. Report leaves are fixed finite code, not a
true-state certified report (2305.15398 pp.4-6). -/
inductive CopyProgram (n : ℕ) where
  | output (D : Option (Description n))
  | bell (U : Clifford.normalizer n) (next : BellLabel n → CopyProgram n)
  | pauli (U : Clifford.normalizer n) (P : BellLabel n) (next : Bool → CopyProgram n)
  | random (size : ℕ) (weights : PMF (Fin size)) (next : Fin size → CopyProgram n)
  | classical (op : CopyClassicalInstruction) (next : Bool → CopyProgram n)

/-- Branch data: optional report, counters (Bell outcomes, Pauli shots, additional work),
and actual Born weight (2305.15398 p.6, resource paragraph). -/
abbrev CopyLeaf (n : ℕ) := (Option (Description n) × (Fin 3 → ℕ)) × ℝ

/-- Computed fresh-copy program law. The separate counters retain failed reports.
No probability, tomography or resource guarantees are assumed (2305.15398 pp.4-6). -/
def copyProgramLaw {n : ℕ} (psi : EuclideanSpace ℂ (Qubits n)) (state : IsState psi) :
    CopyProgram n → (ℕ → ℕ) → List (CopyLeaf n)
  | .output D, _ => [((D,0),1)]
  | .bell U next, memory => (Finset.univ.toList : List (BellLabel n)).flatMap fun P =>
      (copyProgramLaw psi state (next P) memory).map fun l =>
        ((l.1.1,l.1.2+Pi.single 0 1),bellShot psi state U.val P*l.2)
  | .pauli U P next, memory => [false,true].flatMap fun b =>
      (copyProgramLaw psi state (next b) memory).map fun l =>
        ((l.1.1,l.1.2+Pi.single 1 1),pauliShot psi state U P b*l.2)
  | .random _ weights next, memory => (List.finRange _).flatMap fun i =>
      (copyProgramLaw psi state (next i) memory).map fun l => (l.1,(weights i).toReal*l.2)
  | .classical op next, memory =>
      let result := op.run memory
      (copyProgramLaw psi state (next result.1) result.2).map fun l =>
        ((l.1.1,l.1.2+Pi.single 2 1),l.2)

/-- Physical copies are computed from separate fresh-shot counters
(2305.15398 p.6: a Bell outcome is obtained from two copies). -/
def CopyLeaf.copies {n : ℕ} (l : CopyLeaf n) : ℕ := 2*l.1.2 0+l.1.2 1

example {n : ℕ} (psi : EuclideanSpace ℂ (Qubits n)) (state : IsState psi) (memory : ℕ → ℕ) :
    copyProgramLaw psi state (.output none) memory = [((none,0),1)] := rfl

example {n : ℕ} (P : BellLabel n) :
    pauliProjector P true+pauliProjector P false = 1 := by
  ext a b
  simp [pauliProjector, Matrix.one_apply]
  split_ifs <;> ring

example : CopyLeaf.copies (⟨⟨none,![1,0,0]⟩,1⟩ : CopyLeaf 0) = 2 := rfl

end QAlgorithms.DopedTomography


