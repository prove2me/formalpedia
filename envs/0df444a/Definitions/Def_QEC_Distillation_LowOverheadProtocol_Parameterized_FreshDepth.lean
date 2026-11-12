-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T17:49:12.181413+00:00
-- url     : https://prove2.me/theorems/62a0bd9d-56e7-47db-813d-b0425f1508a4
-- title:
--   Fresh Depth
-- statement:
--   Definitions and structural lemmas for Fresh Depth, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
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
abbrev routedDepthInputSlots (m w depth : Nat) :=
  Fin depth → Fin (physicalInputCount m w)
abbrev routedDepthOutputSlots (m w depth : Nat) :=
  Fin depth → LogicalSite m w
def routedDepthOutputPathEmpty (m w : Nat) : routedDepthOutputSlots m w 0 :=
  fun index => Fin.elim0 index
def routedDepthOutputPathAppend (m w depth : Nat)
    (path : routedDepthOutputSlots m w depth) (port : LogicalSite m w) :
    routedDepthOutputSlots m w (depth + 1) :=
  Fin.lastCases port path
def routedDepthSuccessorRouting (m w depth : Nat) :
    routedDepthOutputSlots m w depth × depthTwoParentOutputSlots m w ≃
      routedDepthOutputSlots m w depth × depthTwoChildInputSlots m w :=
  Equiv.prodCongr (Equiv.refl _) (depthTwoRouting m w)
def routedDepthChildInputSlot (m w depth : Nat)
    (pathPrefix : routedDepthOutputSlots m w depth) (child : LogicalSite m w)
    (parent : Fin (physicalInputCount m w)) :
    routedDepthOutputSlots m w depth × depthTwoChildInputSlots m w :=
  routedDepthSuccessorRouting m w depth
    (pathPrefix, DependentBatch.childInputSlot child parent)
inductive RoutedDepthState {w r m : Nat} (h : Admissible w r m)
    (hdegree : 3 * r < m) (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (depth : Nat) → routedDepthOutputSlots m w depth →
      HH18NoisyInput.DiagonalErrorRate → Type
  | root : RoutedDepthState h hdegree epsilon 0
      (routedDepthOutputPathEmpty m w) epsilon
  | succ {depth : Nat} {path : routedDepthOutputSlots m w depth}
      {rate : HH18NoisyInput.DiagonalErrorRate}
      (previous : RoutedDepthState h hdegree epsilon depth path rate)
      (port : LogicalSite m w)
      (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
      RoutedDepthState h hdegree epsilon (depth + 1)
        (routedDepthOutputPathAppend m w depth path port)
        (selectedLogicalPortNextInputRate h hdegree rate port hhalf)
noncomputable def routedDepthActualRun {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (_state : RoutedDepthState h hdegree epsilon depth path rate) :
    DistillationRun QubitSpace (PhysicalRegister m w) (LogicalRegister m w) :=
  resourceDecodedRun h hdegree (noisyResources m w rate)
noncomputable def routedDepthFreshParentPool {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate) :
    Fin (physicalInputCount m w) →
      DistillationRun QubitSpace (PhysicalRegister m w) (LogicalRegister m w) :=
  fun _parent => routedDepthActualRun h hdegree state
noncomputable def routedDepthFreshParentDephasedOutput {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (source : depthTwoParentOutputSlots m w) : DensityOperator QubitSpace :=
  aBasisDephasing.mapDensity
    ((selectedLogicalPortTransport m w source.2).conjDensity
      ((selectedLogicalPortSubsystem m w source.2).selectedPartialTraceFromRegister.mapDensity
        (routedDepthFreshParentPool h hdegree state source.1).acceptedOutput))
noncomputable def routedDepthFreshParentNextInput {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (source : depthTwoParentOutputSlots m w) : DensityOperator QubitSpace :=
  (OneQubitMagic.phaseShiftTransport (Real.pi / 2)).symm.conjDensity
    (routedDepthFreshParentDephasedOutput h hdegree state source)
noncomputable def routedDepthChildResources {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (port : LogicalSite m w)
    (_hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    ResourceInput (physicalInputCount m w) QubitSpace :=
  fun parent => routedDepthFreshParentNextInput h hdegree state
    ((depthTwoRouting m w).symm (depthTwoChildInputSlot m w port parent))
noncomputable def routedDepthChildRun {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    DistillationRun QubitSpace (PhysicalRegister m w) (LogicalRegister m w) :=
  resourceDecodedRun h hdegree (routedDepthChildResources h hdegree state port hhalf)
end HH18Parameterized
end Distillation
end QEC


