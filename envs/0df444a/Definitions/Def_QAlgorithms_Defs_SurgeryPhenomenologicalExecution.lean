-- Prove2me | Definitions.Def_QAlgorithms_Defs_SurgeryPhenomenologicalExecution
-- name    : QAlgorithms_Defs_SurgeryPhenomenologicalExecution
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:32:10.39398+00:00
-- url     : https://prove2.me/theorems/c25e45c9-822b-4ff6-a5d7-a06b630d65f2
-- title:
--   SurgeryPhenomenologicalExecution
-- statement:
--   SurgeryPhenomenologicalExecution
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SurgeryPhenomenologicalExecution.lean

import Definitions.Def_QAlgorithms_Defs_SurgeryLogicalMeasurements
import Definitions.Def_QAlgorithms_Defs_DirichletShadowLearning
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Surgery

/-- One physical stabilizer-measurement layer with an explicit Pauli list and a
syndrome-round marker (2510.14895 pp.19,23,60,71). -/
structure MeasurementLayer (q : ℕ) where
  checks : List (Fin q → Stabilizer.Pauli)
  syndrome : Bool
  origin : Option ℕ := none
  active : Finset (Fin q) := Finset.univ

/-- A schedule with specified retained memory wires, initial plus ancillas, chronological
check layers, and the classical syndrome frame computed from the reported record. The program
contains physical operators, never a target-channel or distance promise
(2510.14895 pp.19,23,60,71).
arxiv-2510.14895v1 PDF p.2; arxiv-2510.14895v1 PDF p.19; arxiv-2510.14895v1 PDF p.23; arxiv-2510.14895v1 PDF p.60; arxiv-2510.14895v1 PDF p.71. -/
structure PhenomenologicalSchedule (n : ℕ) where
  ancillas : ℕ
  layers : List (MeasurementLayer (n+ancillas))
  frame : List Bool → List Bool

/-- The actual original-X-check frame update from the degree-zero attaching matrix:
new anticipated syndrome = old syndrome + h0 times the ancilla X-readout bits.
This is a classical frame, not a physical Pauli applied to memory
(2510.14895 p.23, Remark 3.11; p.76). -/
def updateSyndromeFrame {A C : BasedBinaryComplex} (h : BasedChainMap A C)
    (old : Basis C 0 → ZMod 2) (ancilla : Basis A 0 → ZMod 2) : Basis C 0 → ZMod 2 :=
  old+(component h 0).mulVec ancilla

/-- Projector associated with the eigenvalue (-1)^b (2510.14895 pp.13,19). -/
def checkProjector {q : ℕ} (P : Fin q → Stabilizer.Pauli) (b : Bool) :
    Matrix (Qubits q) (Qubits q) ℂ :=
  (2⁻¹ : ℂ) • (1+(if b then (-1 : ℂ) else 1) • pauliOps P)

/-- Actual available data sites at each layer; after the final layer only retained
memory wires remain. Unprepared or retired ancillas have no phenomenological fault
location (2510.14895 pp.60--62,71,82). -/
def activeWires {n : ℕ} (S : PhenomenologicalSchedule n) (t : ℕ) : Finset (Fin (n+S.ancillas)) :=
  if h : t < S.layers.length then (S.layers[t]).active else
    Finset.univ.map ⟨Fin.castAdd S.ancillas,Fin.castAdd_injective _ _⟩

/-- Source phenomenological faults: one Pauli per data site between layers, and one
reported-outcome flip per check. Y is one Pauli fault (2510.14895 pp.60--62). -/
structure ScheduleFault (n : ℕ) (S : PhenomenologicalSchedule n) where
  data : Fin (S.layers.length+1) → Fin (n+S.ancillas) → Stabilizer.Pauli
  flip : Fin (S.layers.flatMap MeasurementLayer.checks).length → Bool
  located : ∀ t q, q ∉ activeWires S t.val → data t q = Stabilizer.Pauli.I

/-- Complete no-fault assignment (2510.14895 pp.60--62). -/
def noFault {n : ℕ} (S : PhenomenologicalSchedule n) : ScheduleFault n S :=
  ⟨fun _ _ => Stabilizer.Pauli.I,fun _ => false,by simp⟩

/-- Sequential subnormalized projective branches, retaining reported outcomes;
no conditioning by a possibly zero branch probability (2510.14895 pp.19,60,71). -/
def measureChecks {q : ℕ} (flip : ℕ → Bool) :
    List (Fin q → Stabilizer.Pauli) → ℕ → List Bool → Matrix (Qubits q) (Qubits q) ℂ →
      List (List Bool × Matrix (Qubits q) (Qubits q) ℂ)
  | [], _, record, rho => [(record,rho)]
  | P::rest, k, record, rho => [false,true].flatMap fun b =>
      measureChecks flip rest (k+1) (record++[xor b (flip k)])
        (conjSuperop (checkProjector P b) rho)

/-- The chronological noisy layer interpreter (2510.14895 pp.19,60,71). -/
def runLayers {q : ℕ} (data : ℕ → Fin q → Stabilizer.Pauli) (flip : ℕ → Bool) :
    List (MeasurementLayer q) → ℕ → ℕ → List Bool → Matrix (Qubits q) (Qubits q) ℂ →
      List (List Bool × Matrix (Qubits q) (Qubits q) ℂ)
  | [], t, _, record, rho => [(record,conjSuperop (pauliOps (data t)) rho)]
  | layer::rest, t, k, record, rho =>
      (measureChecks flip layer.checks k record (conjSuperop (pauliOps (data t)) rho)).flatMap
        fun branch => runLayers data flip rest (t+1) (k+layer.checks.length) branch.1 branch.2

/-- Execute plus preparation, chronological projectors, faults, destructive ancilla
readout (contained in the public layers), partial trace, and the reported-record classical frame (available as `S.frame record`).
The result is a list of record/subnormalized retained-memory operators, extending to
references by the frozen idTensorSuperop construction (2510.14895 pp.19,23,60,71).
arxiv-2510.14895v1 PDF p.2; arxiv-2510.14895v1 PDF p.19; arxiv-2510.14895v1 PDF p.23; arxiv-2510.14895v1 PDF p.60; arxiv-2510.14895v1 PDF p.71. -/
def executeSchedule {n : ℕ} (S : PhenomenologicalSchedule n) (fault : ScheduleFault n S)
    (rho : Matrix (Qubits n) (Qubits n) ℂ) :
    List (List Bool × Matrix (Qubits n) (Qubits n) ℂ) :=
  let plus := pureDensity (act (hadamardN S.ancillas) (zeroKet S.ancillas))
  let initial := (Matrix.kronecker rho plus).submatrix
    (qubitsAppendEquiv n S.ancillas) (qubitsAppendEquiv n S.ancillas)
  let data := fun t => if h : t < S.layers.length+1 then fault.data ⟨t,h⟩ else fun _ => Stabilizer.Pauli.I
  let flip := fun k => if h : k < (S.layers.flatMap MeasurementLayer.checks).length then fault.flip ⟨k,h⟩ else false
  (runLayers data flip S.layers 0 0 [] initial).map fun branch =>
    (branch.1,traceRight (branch.2.submatrix (qubitsAppendEquiv n S.ancillas).symm
        (qubitsAppendEquiv n S.ancillas).symm))

/-- Sanity check for the source model (arxiv-2510.14895v1 PDF p.2). -/
example {q : ℕ} (rho : Matrix (Qubits q) (Qubits q) ℂ) :
    measureChecks (fun _ => false) [] 0 [] rho = [([],rho)] := rfl

end QAlgorithms.Surgery


