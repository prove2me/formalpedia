-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Postselection
-- name    : QEC_Distillation_LowOverheadProtocol_Core_Postselection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T16:43:23.606001+00:00
-- url     : https://prove2.me/theorems/42d44597-d75f-43da-b040-0745c191eff6
-- title:
--   Postselection
-- statement:
--   Definitions and structural lemmas for Postselection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Postselection.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SyndromeDecoding
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Postselection
open Coding Semantics
open Coding.PauliSymplectic
open HH18SyndromeDecoding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
def syndromeOutcome (syndrome : Syndrome) : DistillationOutcome :=
  if syndrome = HH18PuncturedReedMuller.allPositiveSyndrome 0 1 4 then
    .accepted
  else
    .rejected
noncomputable def postselectionInstrument :
    FiniteInstrument Syndrome DistillationOutcome PhysicalRegister PhysicalRegister where
  kraus := jointStabilizerKrausFamily
    (HH18PuncturedReedMuller.checkGenerator 0 1 4)
    (HH18PuncturedReedMuller.checkGenerator_commutes
      HH18NoisyInput.hh18_15_1_0_admissible)
  observe := syndromeOutcome
noncomputable def rawPostselectionBranch (outcome : DistillationOutcome)
    (input : Operator PhysicalRegister) : Operator PhysicalRegister :=
  postselectionInstrument.branchOperator outcome input
noncomputable def rawPostselectionEndpoint (outcome : DistillationOutcome)
    (rho : DensityOperator PhysicalRegister) : Operator PhysicalRegister :=
  rawPostselectionBranch outcome rho.toOperator
noncomputable def postselectionWeight (outcome : DistillationOutcome)
    (rho : DensityOperator PhysicalRegister) : Real :=
  postselectionInstrument.bornWeight outcome rho
noncomputable def postselectionConditional (rho : DensityOperator PhysicalRegister)
    (outcome : DistillationOutcome)
    (hpos : 0 < postselectionWeight outcome rho) :
    DensityOperator PhysicalRegister :=
  postselectionInstrument.conditionalDensity outcome rho hpos
end HH18Postselection
end Distillation
end QEC


