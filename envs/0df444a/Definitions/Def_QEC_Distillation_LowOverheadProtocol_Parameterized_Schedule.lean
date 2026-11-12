-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T19:47:41.54408+00:00
-- url     : https://prove2.me/theorems/caeb03ad-59b6-4280-9512-443db0843a59
-- title:
--   Schedule
-- statement:
--   Definitions and structural lemmas for Schedule, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthOutputSlots_nonempty

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
abbrev routedDepthScheduleInputSlots (m w depth : Nat) :=
  routedDepthInputSlots m w depth
abbrev routedDepthScheduleOutputSlots (m w depth : Nat) :=
  routedDepthOutputSlots m w depth
noncomputable def routedDepthScheduleActualOutputError {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) : ℝ := by
  classical
  exact Finset.univ.sup'
    ⟨(routedDepthOutputSlots_nonempty m w depth).some, Finset.mem_univ _⟩
    fun path => (routedDepthPathRate h hdegree epsilon hsmall depth path).1
noncomputable def routedDepthScheduleTargetError (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat) : ℝ :=
  (routedDepthIterationScale w r m * epsilon.1) ^ (codeDistance r w ^ depth)
abbrev routedDepthScheduleExpectedYield {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) : NNReal :=
  routedDepthPooledYield h hdegree epsilon hsmall depth
abbrev routedDepthScheduleSuccessfulOutputCost {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) : ℝ :=
  routedDepthTypedSuccessfulOutputCost h hdegree epsilon hsmall depth
noncomputable def routedDepthScheduleGamma (w r m : Nat) : ℝ :=
  Real.log ((physicalInputCount m w : ℝ) / logicalOutputCount m w) /
    Real.log (codeDistance r w)
noncomputable def routedDepthScheduleLogGrowthBase (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  -Real.log (routedDepthIterationScale w r m * epsilon.1)
noncomputable def routedDepthScheduleCostCoefficient {w r m : Nat}
    (_h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  (6 / 5 : ℝ) /
    Real.rpow (routedDepthScheduleLogGrowthBase w r m epsilon)
      (routedDepthScheduleGamma w r m)
end HH18Parameterized
end Distillation
end QEC


