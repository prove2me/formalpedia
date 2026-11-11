-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T20:03:45.582468+00:00
-- url     : https://prove2.me/theorems/ddf106d7-e24a-469b-80f0-5f1ba48b95fe
-- title:
--   Logical Defect Storage
-- statement:
--   Definitions and structural lemmas for Logical Defect Storage, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26LogicalDefectStorage
open Classical Semantics BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
section Embedding
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [FiniteQuantumSystem K]
end Embedding
variable (S : OddScale) (n : Nat)
local instance _p2m_local_instance_444300d501_96 : Fintype (BDL26TransposedStoppedDecoder.XSyndromeDomain S n) := Fintype.ofFinite _
local instance _p2m_local_instance_444300d501_97 : Fintype (BDL26TransposedStoppedDecoder.ZSyndromeDomain S n) := Fintype.ofFinite _
abbrev Rate := BDL26CSSDaviesLocality.CouplingIndex S (n+2) →
  BDL26CSSDaviesLocality.Frequency S (n+2) → ℝ
abbrev logical := dressedPauliPair S n
abbrev projector := BDL26LogicalDefectProtection.protectedProjector S n
abbrev reference (beta : ℝ) := gibbs S (n+2) beta
abbrev encoder (beta : ℝ) := BDL26PairedDecoderGibbs.encoding S n beta
abbrev decoder := BDL26PairedDecoderChannel.readout S n
abbrev observable (eta : DensityOperator Qubit.QubitSpace) := (logical S n).encodedObservable eta
abbrev jumps (rate : Rate S n) := BDL26BoundedRateDavies.jump S (n+2) rate
def evolution (rate : Rate S n) (t : ℝ) (ht : 0 ≤ t) :
    QuantumChannel (Register S n) (Register S n) :=
  finiteLindbladEvolutionChannel (hamiltonian S (n+2)) (jumps S n rate)
    (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2)) t ht
def g (rate : Rate S n) : ℝ :=
  selfAdjointTraceNormOneToOne (BDL26BoundedRateDavies.dissipator S (n+2) rate)
def mass (beta : ℝ) : ℝ := clbtGibbsTailMass (projector S n) (reference S n beta)
def xMass (beta : ℝ) : ℝ := BDL26TwoSectorBadProjector.pX S (n+2) beta
  (BDL26LogicalDefectProtection.badX S n)
def zMass (beta : ℝ) : ℝ := BDL26TwoSectorBadProjector.pZ S (n+2) beta
  (BDL26LogicalDefectProtection.badZ S n)
def qubits : ℝ := Fintype.card (Physical S (n+2))
def encodedError (rate : Rate S n) (beta : ℝ) (eta : DensityOperator Qubit.QubitSpace)
    (t : ℝ) (ht : 0 ≤ t) : ℝ :=
  traceNorm (((evolution S n rate t ht).mapDensity ((encoder S n beta).mapDensity eta)).toOperator -
    ((encoder S n beta).mapDensity eta).toOperator)
def decodedError (rate : Rate S n) (beta : ℝ) (eta : DensityOperator Qubit.QubitSpace)
    (t : ℝ) (ht : 0 ≤ t) : ℝ :=
  traceNorm (((decoder S n).mapDensity
    ((evolution S n rate t ht).mapDensity ((encoder S n beta).mapDensity eta))).toOperator - eta.toOperator)
def peierlsScale (k : Nat) : ℝ := Real.rpow 2 (-((2^(k-1) : Nat) : ℝ))
end QEC.Coding.BDL26LogicalDefectStorage
end


