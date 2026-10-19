-- Prove2me | Definitions.Def_QAlgorithms_Defs_MitigationPhysicalExperiments
-- name    : QAlgorithms_Defs_MitigationPhysicalExperiments
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:19:56.22782+00:00
-- url     : https://prove2.me/theorems/f25b156a-6050-4902-bf2b-976e71cc14dd
-- title:
--   MitigationPhysicalExperiments
-- statement:
--   MitigationPhysicalExperiments
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\MitigationPhysicalExperiments.lean

import Definitions.Def_QAlgorithms_Defs_MitigationDecompositions
import Definitions.Def_QAlgorithms_Defs_FiniteNoisyCircuits
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.ErrorMitigation

/-- A concrete selected experiment; each Bool instrument's true branch is the accepted
operation. The other branch is retained. All data are fixed before outcomes
(1712.09271 pp.4--6,19). -/
structure PhysicalExperiment (n : ℕ) where
  preparation : Matrix (Qubits n) (Qubits n) ℂ
  density : IsDensityMatrix preparation
  operations : List (CopyMeasurements.QuantumInstrument (Qubits n) Bool)
  readout : ObservableMeasurement (Qubits n)

/-- The accepted and rejected densities, computed by chronological instruments
(1712.09271 p.5). Rejected branches never undergo acceptance normalization. -/
def instrumentWord {I : Type*} [Fintype I] [DecidableEq I] :
    List (CopyMeasurements.QuantumInstrument I Bool) →
      Matrix I I ℂ → Matrix I I ℂ × Matrix I I ℂ
  | [], rho => (rho,0)
  | M::rest, rho =>
      let tail := instrumentWord rest (CopyMeasurements.instrumentBranch M true rho)
      (tail.1,CopyMeasurements.instrumentBranch M false rho+tail.2)

/-- Occurrence-specific calibrated mitigation operation. Inverse correction is
always immediately after the native operation; compensation chooses the native
operation or one basis operation (1712.09271 pp.5--6,18--19). -/
inductive MitigationStage (n : ℕ) : ℕ → Type where
  | inverse {c : ℕ} (native : CopyMeasurements.QuantumInstrument (Qubits n) Bool)
      (nativeChannel : IsChannel (CopyMeasurements.instrumentBranch native true))
      (correction : Fin c → CopyMeasurements.QuantumInstrument (Qubits n) Bool) :
      MitigationStage n c
  | compensation {c : ℕ} (native : CopyMeasurements.QuantumInstrument (Qubits n) Bool)
      (nativeChannel : IsChannel (CopyMeasurements.instrumentBranch native true))
      (basis : Fin c → CopyMeasurements.QuantumInstrument (Qubits n) Bool) :
      MitigationStage n (c+1)

/-- Construct the actual chronological word for a selected calibrated stage. Native
compensation is choice zero, whose coefficient is lambda (1712.09271 pp.5--6,19). -/
def stageWord {n c : ℕ} : MitigationStage n c → Fin c →
    List (CopyMeasurements.QuantumInstrument (Qubits n) Bool)
  | .inverse native _ correction, choice => [native,correction choice]
  | .compensation native _ basis, choice =>
      if h : choice.val = 0 then [native] else
        [basis ⟨choice.val-1,by have := choice.isLt; omega⟩]

/-- Public physical experiment template and coefficient data. Slots represent the
preparation, each calibrated gate/correction (memory included), and observation;
full choices are products of these finite indices (1712.09271 pp.4,18--19).
`physical` contains only actual preparation/instrument/POVM data, never reconstruction
or unbiasedness guarantees. -/
structure MitigationDesign (n : ℕ) where
  slots : ℕ
  choices : Fin slots → ℕ
  nonempty : ∀ j, 0 < choices j
  coefficient : (j : Fin slots) → Fin (choices j) → ℝ
  preparationSlot : Fin slots
  observationSlot : Fin slots
  preparations : Fin (choices preparationSlot) → Matrix (Qubits n) (Qubits n) ℂ
  preparationDensity : ∀ i, IsDensityMatrix (preparations i)
  stages : List ((j : Fin slots) × MitigationStage n (choices j))
  observations : Fin (choices observationSlot) → ObservableMeasurement (Qubits n)
  usesAll : (preparationSlot :: stages.map Sigma.fst ++ [observationSlot]).Perm (List.finRange slots)
  productPreparations : ∀ choice, ∃ localState : Fin n → Matrix Bool Bool ℂ,
    (∀ j, IsDensityMatrix (localState j)) ∧
    preparations choice = Matrix.of (fun x y => ∏ j, localState j (x j) (y j))

/-- Construct the preparation, occurrence-specific chronological native/correction words,
and observable measurement from the selected indices (1712.09271 pp.4--6,19).
A compensation choice contains either the native instrument or the local basis word;
an inverse choice contains the native instrument followed immediately by its correction.
Products of one-qubit preparations and observations may be used as the finite frames. -/
def modifiedCircuit {n : ℕ} (D : MitigationDesign n)
    (choice : (j : Fin D.slots) → Fin (D.choices j)) : PhysicalExperiment n where
  preparation := D.preparations (choice D.preparationSlot)
  density := D.preparationDensity _
  operations := D.stages.flatMap fun stage => stageWord stage.2 (choice stage.1)
  readout := D.observations (choice D.observationSlot)

/-- Full accepted readout and rejected mass of the selected physical circuit
(1712.09271 p.5). `none` is rejection and contributes zero to estimation.
arxiv-1712.09271v2 PDF p.4; arxiv-1712.09271v2 PDF p.6; arxiv-1712.09271v2 PDF p.19. -/
def executeModifiedCircuit {n : ℕ} (E : PhysicalExperiment n) :
    Option (Fin E.readout.outcomes) → ℝ
  | none => (instrumentWord E.operations E.preparation).2.trace.re
  | some o => effectProb (E.readout.effect o) (instrumentWord E.operations E.preparation).1

/-- Sanity check for the source model (arxiv-1712.09271v2 PDF p.4). -/
example {I : Type*} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) :
    instrumentWord [] rho = (rho,0) := rfl

end QAlgorithms.ErrorMitigation


