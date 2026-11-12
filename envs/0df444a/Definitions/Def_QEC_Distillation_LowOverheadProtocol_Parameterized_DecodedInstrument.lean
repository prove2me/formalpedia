-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T16:57:45.442047+00:00
-- url     : https://prove2.me/theorems/6426b4cc-96ee-446a-979e-03a8e89ba9a7
-- title:
--   Decoded Instrument
-- statement:
--   Definitions and structural lemmas for Decoded Instrument, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrument.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Decoder
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
local instance instDecodedInstrumentClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
abbrev resourcePostselectionRawIndex {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) : Type :=
  Sigma fun _ : Fin ((resourceConsumerChannel h hdegree).chosenKrausCount) =>
    Syndrome w r m
noncomputable def resourcePostselectionInstrument {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    FiniteInstrument (resourcePostselectionRawIndex h hdegree)
      (Sigma fun _ : PUnit => DistillationOutcome)
      (PhysicalRegister m w) (PhysicalRegister m w) :=
  (QuantumChannel.toFiniteInstrument (resourceConsumerChannel h hdegree)).bindDependent
    (fun _ => postselectionInstrument h)
abbrev decodedRawIndex {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) : Type :=
  Sigma fun _ : resourcePostselectionRawIndex h hdegree =>
    Fin ((decoderChannel h).chosenKrausCount)
noncomputable def decodedRawInstrument {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    FiniteInstrument (decodedRawIndex h hdegree)
      (Sigma fun _ : (Sigma fun _ : PUnit => DistillationOutcome) => PUnit)
      (PhysicalRegister m w) (LogicalRegister m w) :=
  (resourcePostselectionInstrument h hdegree).bindDependent
    (fun _ => QuantumChannel.toFiniteInstrument (decoderChannel h))
noncomputable def decodedInstrument {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    FiniteInstrument (decodedRawIndex h hdegree) DistillationOutcome
      (PhysicalRegister m w) (LogicalRegister m w) where
  kraus := (decodedRawInstrument h hdegree).kraus
  observe := fun index => (postselectionInstrument h).observe index.1.2
end HH18Parameterized
end Distillation
end QEC


