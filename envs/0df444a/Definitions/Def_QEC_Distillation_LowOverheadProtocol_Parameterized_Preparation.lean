-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Preparation
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_Preparation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:32:53.549057+00:00
-- url     : https://prove2.me/theorems/9aa52437-198a-4bbe-9de1-c95ae8e10149
-- title:
--   Preparation
-- statement:
--   Definitions and structural lemmas for Preparation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Preparation.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
noncomputable def resourceSiteEquiv (m w : Nat) :
    PhysicalSite m w ≃ Fin (physicalInputCount m w) :=
  Fintype.equivFin (PhysicalSite m w)
noncomputable def noisyResources (m w : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    ResourceInput (physicalInputCount m w) QubitSpace :=
  HH18NoisyInput.noisyTInvResources (physicalInputCount m w) epsilon
def independentInputModel (m w : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    IndependentInputErrorModel (physicalInputCount m w) QubitSpace where
  rate := fun _ => epsilon.1
  rate_nonneg := fun _ => epsilon.property.1
  rate_le_one := fun _ => by linarith [epsilon.property.2]
  admissible := fun rate inputs =>
    (∀ slot, rate slot = epsilon.1) ∧ inputs = noisyResources m w epsilon
noncomputable def noisyInput (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (m w : Nat) : DensityOperator (PhysicalRegister m w) :=
  HH18NoisyInput.hh18NoisyInput epsilon m w
end HH18Parameterized
end Distillation
end QEC


