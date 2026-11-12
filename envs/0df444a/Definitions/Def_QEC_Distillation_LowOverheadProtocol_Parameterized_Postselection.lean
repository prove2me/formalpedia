-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Postselection
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_Postselection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:41:14.564476+00:00
-- url     : https://prove2.me/theorems/c01373b7-3032-4f46-a4c3-b05606655c54
-- title:
--   Postselection
-- statement:
--   Definitions and structural lemmas for Postselection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Syndrome
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
universe u
def syndromeOutcome (w r m : Nat) (syndrome : Syndrome w r m) :
    DistillationOutcome :=
  if syndrome = HH18PuncturedReedMuller.allPositiveSyndrome w r m then
    .accepted
  else
    .rejected
noncomputable def postselectionInstrument {w r m : Nat} (h : Admissible w r m) :
    FiniteInstrument (Syndrome w r m) DistillationOutcome
      (PhysicalRegister m w) (PhysicalRegister m w) where
  kraus := (fullSyndromeInstrument h).kraus
  observe := syndromeOutcome w r m
noncomputable def rawPostselectionBranch {w r m : Nat} (h : Admissible w r m)
    (outcome : DistillationOutcome) (input : Operator (PhysicalRegister m w)) :
    Operator (PhysicalRegister m w) :=
  (postselectionInstrument h).branchOperator outcome input
noncomputable def rawPostselectionEndpoint {w r m : Nat} (h : Admissible w r m)
    (outcome : DistillationOutcome) (rho : DensityOperator (PhysicalRegister m w)) :
    Operator (PhysicalRegister m w) :=
  rawPostselectionBranch h outcome rho.toOperator
noncomputable def postselectionWeight {w r m : Nat} (h : Admissible w r m)
    (outcome : DistillationOutcome) (rho : DensityOperator (PhysicalRegister m w)) :
    Real :=
  (postselectionInstrument h).bornWeight outcome rho
noncomputable def postselectionConditional {w r m : Nat} (h : Admissible w r m)
    (rho : DensityOperator (PhysicalRegister m w)) (outcome : DistillationOutcome)
    (hpositive : 0 < postselectionWeight h outcome rho) :
    DensityOperator (PhysicalRegister m w) :=
  (postselectionInstrument h).conditionalDensity outcome rho hpositive
noncomputable def rawAcceptedEndpoint {w r m : Nat} (h : Admissible w r m)
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w) :
    Operator (PhysicalRegister m w) :=
  rawSyndromeBranch h error outcomes
    (HH18PuncturedReedMuller.allPositiveSyndrome w r m)
noncomputable def rawRejectedEndpoint {w r m : Nat} (h : Admissible w r m)
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w) :
    Operator (PhysicalRegister m w) :=
  ∑ syndrome : Syndrome w r m,
    if syndrome = HH18PuncturedReedMuller.allPositiveSyndrome w r m then
      0
    else
      rawSyndromeBranch h error outcomes syndrome
end HH18Parameterized
end Distillation
end QEC


