-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
-- name    : LIDT_MIPStarRE_LDT_Basic_MeasurementLift
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:55:28.427983+00:00
-- url     : https://prove2.me/theorems/1ccc10d7-6bb5-4a34-bcf7-e56cd2a7ec4f
-- title:
--   LIDT definitions: LDT / Basic / MeasurementLift
-- statement:
--   This bundle defines the canonical embeddings of a measurement into the left or right register of a bipartite tensor product. These lifted families are the basic interfaces for comparing local measurements with bipartite strategy operators.
--
--   Principal definitions:
--   - `leftLiftedMeasurement`: places each measurement effect on the left tensor factor.
--   - `rightLiftedMeasurement`: places each measurement effect on the right tensor factor.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/MeasurementLift.lean#L17-L37

-- Generated from MIPStarRE/LDT/Basic/MeasurementLift.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

namespace LIDT

/-!
# Measurement lift infrastructure for the low individual degree test

Measurement-level tensor-factor lifts built from the submeasurement placement API.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- Lift a measurement to the left tensor factor of `ιA × ιB`. -/
def leftLiftedMeasurement {α : Type*}
    {ιA ιB : Type*} [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α ιA) :
    Measurement α (ιA × ιB) :=
  { toSubMeas := leftPlacedSubMeas (ιB := ιB) A.toSubMeas
    total_eq_one :=
      Eq.trans rfl <|
        Eq.trans (congrArg (leftTensor (ι₂ := ιB)) A.total_eq_one)
          (leftTensor_one (ι₁ := ιA) (ι₂ := ιB)) }

/-- Lift a measurement to the right tensor factor of `ιA × ιB`. -/
def rightLiftedMeasurement {α : Type*}
    {ιA ιB : Type*} [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α ιB) :
    Measurement α (ιA × ιB) :=
  { toSubMeas := rightPlacedSubMeas (ιA := ιA) A.toSubMeas
    total_eq_one :=
      Eq.trans rfl <|
        Eq.trans (congrArg (rightTensor (ι₁ := ιA)) A.total_eq_one)
          (rightTensor_one (ι₁ := ιA) (ι₂ := ιB)) }

end MIPStarRE.LDT

end

end LIDT


