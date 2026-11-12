-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T17:46:47.171334+00:00
-- url     : https://prove2.me/theorems/522cc66a-c37c-455d-aada-d90ab32e7284
-- title:
--   Depth Two Routing
-- statement:
--   Definitions and structural lemmas for Depth Two Routing, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPort
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

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
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
abbrev depthTwoParentOutputSlots (m w : Nat) :=
  Fin (physicalInputCount m w) × LogicalSite m w
abbrev depthTwoChildInputSlots (m w : Nat) :=
  LogicalSite m w × Fin (physicalInputCount m w)
def depthTwoRouting (m w : Nat) :
    depthTwoParentOutputSlots m w ≃ depthTwoChildInputSlots m w :=
  DependentBatch.parentPortTranspose
    (Fin (physicalInputCount m w)) (LogicalSite m w)
def depthTwoChildInputSlot (m w : Nat) (child : LogicalSite m w)
    (parent : Fin (physicalInputCount m w)) : depthTwoChildInputSlots m w :=
  depthTwoRouting m w (DependentBatch.childInputSlot child parent)
noncomputable def selectedLogicalPortNextInputRate {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2) :
    HH18NoisyInput.DiagonalErrorRate :=
  ⟨selectedLogicalPortRawError h hdegree epsilon port,
    selectedLogicalPortRawError_nonneg h hdegree epsilon port, hhalf⟩
noncomputable def selectedLogicalPortDephasedNextInput {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    DensityOperator QubitSpace :=
  (OneQubitMagic.phaseShiftTransport (Real.pi / 2)).symm.conjDensity
    (selectedLogicalPortDephasedOutput h hdegree epsilon port)
noncomputable def depthTwoFreshParentRun {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (_parent : Fin (physicalInputCount m w)) :=
  resourceDecodedRun h hdegree (noisyResources m w epsilon)
noncomputable def depthTwoFreshParentDephasedOutput {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (source : depthTwoParentOutputSlots m w) : DensityOperator QubitSpace :=
  aBasisDephasing.mapDensity
    ((selectedLogicalPortTransport m w source.2).conjDensity
      ((selectedLogicalPortSubsystem m w source.2).selectedPartialTraceFromRegister.mapDensity
        (depthTwoFreshParentRun h hdegree epsilon source.1).acceptedOutput))
noncomputable def depthTwoFreshParentNextInput {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (source : depthTwoParentOutputSlots m w) : DensityOperator QubitSpace :=
  (OneQubitMagic.phaseShiftTransport (Real.pi / 2)).symm.conjDensity
    (depthTwoFreshParentDephasedOutput h hdegree epsilon source)
noncomputable def depthTwoChildResources {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (_hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2) :
    ResourceInput (physicalInputCount m w) QubitSpace :=
  fun parent => depthTwoFreshParentNextInput h hdegree epsilon
    ((depthTwoRouting m w).symm (depthTwoChildInputSlot m w child parent))
noncomputable def depthTwoChildRun {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2) :=
  resourceDecodedRun h hdegree (depthTwoChildResources h hdegree epsilon child hhalf)
noncomputable def depthTwoChildSelectedPortOutput {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2)
    (port : LogicalSite m w) : DensityOperator QubitSpace :=
  (selectedLogicalPortTransport m w port).conjDensity
    ((selectedLogicalPortSubsystem m w port).selectedPartialTraceFromRegister.mapDensity
      (depthTwoChildRun h hdegree epsilon child hhalf).acceptedOutput)
noncomputable def depthTwoChildSelectedPortRawError {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2)
    (port : LogicalSite m w) : ℝ :=
  aBasisInstrument.bornWeight .negative
    (depthTwoChildSelectedPortOutput h hdegree epsilon child hhalf port)
end HH18Parameterized
end Distillation
end QEC


