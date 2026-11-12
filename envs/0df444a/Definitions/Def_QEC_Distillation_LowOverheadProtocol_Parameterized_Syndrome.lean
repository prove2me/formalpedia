-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Syndrome
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_Syndrome
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:39:01.284375+00:00
-- url     : https://prove2.me/theorems/5d475670-3e52-4b98-9286-77857678162c
-- title:
--   Syndrome
-- statement:
--   Definitions and structural lemmas for Syndrome, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Syndrome.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SitewiseInjection
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
abbrev CheckIndex (w r m : Nat) :=
  Sum (HH18PuncturedReedMuller.ZCheckIndex w r m)
    (HH18PuncturedReedMuller.XCheckIndex w r m)
abbrev Syndrome (w r m : Nat) := JointSyndrome (CheckIndex w r m)
def errorPauli {m w : Nat} (error : PhysicalErrorWord m w) :
    Binary (PhysicalSite m w) :=
  cssZCheck error
def measuredSyndrome (w r m : Nat) (error : PhysicalErrorWord m w) :
    Syndrome w r m :=
  fun check =>
    if stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator w r m check)
        (errorPauli error) = 0 then
      StabilizerOutcome.positive
    else
      StabilizerOutcome.negative
def Accepts (w r m : Nat) (error : PhysicalErrorWord m w) : Prop :=
  measuredSyndrome w r m error =
    HH18PuncturedReedMuller.allPositiveSyndrome w r m
def fullSyndromeInstrument {w r m : Nat} (h : Admissible w r m) :
    FiniteInstrument (Syndrome w r m) (Syndrome w r m)
      (PhysicalRegister m w) (PhysicalRegister m w) :=
  jointStabilizerInstrument
    (HH18PuncturedReedMuller.checkGenerator w r m)
    (HH18PuncturedReedMuller.checkGenerator_commutes h)
noncomputable def errorBranchOperator {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) : Operator (PhysicalRegister m w) :=
  (InnerProductSpace.rankOne Complex
    (HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree))
    (HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree))).toLinearMap
noncomputable def injectedBranchOperator {w r m : Nat}
    (h : Admissible w r m) (error : PhysicalErrorWord m w)
    (outcomes : InjectionOutcomeWord m w) :
    Operator (PhysicalRegister m w) :=
  (InnerProductSpace.rankOne Complex
    (sitewiseCorrectedTInvAttempt error outcomes (encodedLogicalPlus h))
    (sitewiseCorrectedTInvAttempt error outcomes (encodedLogicalPlus h))).toLinearMap
noncomputable def rawSyndromeBranch {w r m : Nat}
    (h : Admissible w r m) (error : PhysicalErrorWord m w)
    (outcomes : InjectionOutcomeWord m w)
    (syndrome : Syndrome w r m) : Operator (PhysicalRegister m w) :=
  (fullSyndromeInstrument h).branchOperator syndrome
    (injectedBranchOperator h error outcomes)
end HH18Parameterized
end Distillation
end QEC


