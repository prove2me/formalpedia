-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T19:34:49.937499+00:00
-- url     : https://prove2.me/theorems/ea12d8ae-f066-487d-858d-a5bfabbb673c
-- title:
--   Path Yield
-- statement:
--   Definitions and structural lemmas for Path Yield, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
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
def routedDepthOutputPathPrefix (m w depth : Nat)
    (path : routedDepthOutputSlots m w depth) (stage : Fin (depth + 1)) :
    routedDepthOutputSlots m w stage.1 :=
  fun index => path ⟨index.1,
    Nat.lt_of_lt_of_le index.2 (Nat.le_of_lt_succ stage.2)⟩
def routedDepthPathStagePath (m w depth : Nat)
    (path : routedDepthOutputSlots m w depth) (stage : Fin depth) :
    routedDepthOutputSlots m w stage.1 :=
  routedDepthOutputPathPrefix m w depth path stage.castSucc
noncomputable def routedDepthPathStageRun {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) (stage : Fin depth) :
    DistillationRun QubitSpace (PhysicalRegister m w) (LogicalRegister m w) :=
  routedDepthPathActualRun h hdegree epsilon hsmall stage.1
    (routedDepthPathStagePath m w depth path stage)
noncomputable def routedDepthPathStageYield {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) (stage : Fin depth) :
    NNReal :=
  ⟨(routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).successProbability,
    (routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).success_nonneg⟩
noncomputable def routedDepthPathYieldFactor {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) : NNReal :=
  ∏ stage : Fin depth, routedDepthPathStageYield h hdegree epsilon hsmall depth path stage
noncomputable def routedDepthPooledAcceptedOutput {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) : NNReal :=
  ∑ path : routedDepthOutputSlots m w depth,
    routedDepthPathYieldFactor h hdegree epsilon hsmall depth path
noncomputable def routedDepthPooledYield {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) : NNReal :=
  routedDepthPooledAcceptedOutput h hdegree epsilon hsmall depth /
    Fintype.card (routedDepthOutputSlots m w depth)
noncomputable def routedDepthTypedSuccessfulOutputCost {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) : ℝ :=
  DependentBatch.typedSuccessfulOutputCost (routedDepthInputSlots m w depth)
    (routedDepthOutputSlots m w depth)
    (routedDepthPooledYield h hdegree epsilon hsmall depth)
end HH18Parameterized
end Distillation
end QEC


