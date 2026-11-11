-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T15:08:37.787176+00:00
-- url     : https://prove2.me/theorems/08308b55-e672-45c0-af96-5cad8bae6bee
-- title:
--   Paired Decoder Phase
-- statement:
--   Definitions and structural lemmas for Paired Decoder Phase, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26PairedDecoderPhase
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26TransposedStoppedDecoder
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators
variable (S : OddScale) (n : Nat)
abbrev Visible := BDL26TwoSectorBadProjector.JointImage S (n + 2)
local instance _p2m_local_instance_6635fd3be7_27 : Fintype (XSyndromeDomain S n) := Fintype.ofFinite _
local instance _p2m_local_instance_6635fd3be7_28 : Fintype (ZSyndromeDomain S n) := Fintype.ofFinite _
abbrev code := binaryCSSStabilizerCodeOfParityChecks
  (zSyndrome S (n + 2)) (xSyndrome S (n + 2)) (row_orthogonal S (n + 2))
abbrev atom (s : Visible S n) : Operator (Qubit.QubitRegister (Physical S (n + 2))) :=
  projector S (n + 2)
    (CSSGibbs.realizableEmbedding (zSyndrome S (n + 2)) (xSyndrome S (n + 2)) s)
abbrev correction (s : Visible S n) := pairedCorrection S n s.1 s.2
abbrev residual (s : Visible S n) (E : Binary (Physical S (n + 2))) :=
  pairedResidual S n s.1 s.2 E
abbrev translation (E : Binary (Physical S (n + 2))) :=
  CSSGibbs.jointTranslation (zSyndrome S (n + 2)) (xSyndrome S (n + 2)) E
def phaseOperator (logical : Binary (Physical S (n + 2))) :
    Operator (Qubit.QubitRegister (Physical S (n + 2))) :=
  ∑ s : Visible S n, commutationPhase (correction S n s) logical • atom S n s
def dressed (logical : Binary (Physical S (n + 2))) :
    Operator (Qubit.QubitRegister (Physical S (n + 2))) :=
  toHermitianQubitOperator logical * phaseOperator S n logical
def singletonBackground (q : Physical S (n + 2)) : Visible S n :=
  (⟨zSyndrome S (n + 2) (Pi.single q 1), ⟨Pi.single q 1, rfl⟩⟩,
   ⟨xSyndrome S (n + 2) (Pi.single q 1), ⟨Pi.single q 1, rfl⟩⟩)
def bridgeError (s t : Visible S n) : Binary (Physical S (n + 2)) :=
  binaryMul (correction S n t) (correction S n s)
end QEC.Coding.BDL26PairedDecoderPhase
end


