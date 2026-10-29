-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
-- name    : LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:45:16.67496+00:00
-- url     : https://prove2.me/theorems/b3e5b205-e16a-4b0a-b772-480df5c10530
-- title:
--   LIDT definitions: LDT / Preliminaries / SwitchSandwichPrep / ApproxDelta
-- statement:
--   This bundle defines the left and right overlap gaps used in the approximate missing-mass switch-sandwich preparation. The two quantities isolate the directional missing-mass terms before the main Cauchy-Schwarz and sandwich estimates are applied.
--
--   Principal definitions:
--   - `question_overlap_gap_left`: the left directional overlap gap.
--   - `question_overlap_gap_right`: the right directional overlap gap.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/SwitchSandwichPrep/ApproxDelta.lean#L25-L175

-- Generated from MIPStarRE/LDT/Preliminaries/SwitchSandwichPrep/ApproxDelta.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Switch-sandwich preparation: `approx_δ` overlap gaps

Pointwise overlap-gap estimates used to bound the switch-sandwich approximation
error under `approx_δ` families.

## References

- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

lemma question_overlap_gap_left
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B : SubMeas Outcome ι) :
    |(∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)) -
        ∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)| ≤
      Real.sqrt (qSDD ψ A B) := by
  let diagA : Error := ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
  have hdiagA_le_one : diagA ≤ 1 := by
    simpa [diagA] using subMeas_diagMass_le_one ψ hψ A
  have haux :
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * A.outcome a)| ≤
        Real.sqrt (qSDD ψ A B) * Real.sqrt diagA := by
    calc
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * A.outcome a)|
        ≤ ∑ a : Outcome, |ev ψ ((A.outcome a - B.outcome a) * A.outcome a)| := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Outcome,
            Real.sqrt (ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))) *
              Real.sqrt (ev ψ (A.outcome a * A.outcome a)) := by
            refine Finset.sum_le_sum ?_
            intro a _
            have hherm : (A.outcome a - B.outcome a)ᴴ = A.outcome a - B.outcome a := by
              simp [SubMeas.outcome_hermitian]
            simpa [hherm, SubMeas.outcome_hermitian] using
              ev_abs_mul_le_sqrt ψ (A.outcome a - B.outcome a) (A.outcome a)
      _ ≤ Real.sqrt
            (∑ a : Outcome,
              ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))) *
          Real.sqrt diagA := by
            simpa [diagA] using
              Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
                (f := fun a =>
                  ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a)))
                (g := fun a => ev ψ (A.outcome a * A.outcome a))
                (fun a => ev_adjoint_self_nonneg ψ _)
                (fun a => by
                  simpa [SubMeas.outcome_hermitian] using
                    ev_adjoint_self_nonneg ψ (A.outcome a))
      _ = Real.sqrt (qSDD ψ A B) * Real.sqrt diagA := by
            simp [qSDD, qSDDCore, diagA]
  have hsqrtA : Real.sqrt diagA ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdiagA_le_one
  have haux' :
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * A.outcome a)| ≤
        Real.sqrt (qSDD ψ A B) := by
    calc
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * A.outcome a)|
        ≤ Real.sqrt (qSDD ψ A B) * Real.sqrt diagA := haux
      _ ≤ Real.sqrt (qSDD ψ A B) * 1 := by
            exact mul_le_mul_of_nonneg_left hsqrtA (Real.sqrt_nonneg _)
      _ = Real.sqrt (qSDD ψ A B) := by ring
  convert haux' using 1
  refine congrArg abs ?_
  calc
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a) -
        ∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)
      = ∑ a : Outcome,
          (ev ψ (A.outcome a * A.outcome a) -
            ev ψ (A.outcome a * B.outcome a)) := by
              rw [← Finset.sum_sub_distrib]
    _ = ∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * A.outcome a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          have hcomm :
              ev ψ (B.outcome a * A.outcome a) = ev ψ (A.outcome a * B.outcome a) := by
            exact ev_mul_comm_of_psd ψ _ _ (B.outcome_pos a) (A.outcome_pos a)
          calc
            ev ψ (A.outcome a * A.outcome a) - ev ψ (A.outcome a * B.outcome a)
              = ev ψ (A.outcome a * A.outcome a) - ev ψ (B.outcome a * A.outcome a) := by
                  rw [hcomm]
            _ = ev ψ (A.outcome a * A.outcome a - B.outcome a * A.outcome a) := by
                  rw [(ev_sub ψ (A.outcome a * A.outcome a) (B.outcome a * A.outcome a)).symm]
            _ = ev ψ ((A.outcome a - B.outcome a) * A.outcome a) := by
                  simp [sub_mul]

lemma question_overlap_gap_right
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B : SubMeas Outcome ι) :
    |(∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)) -
        ∑ a : Outcome, ev ψ (B.outcome a * B.outcome a)| ≤
      Real.sqrt (qSDD ψ A B) := by
  let diagB : Error := ∑ a : Outcome, ev ψ (B.outcome a * B.outcome a)
  have hdiagB_le_one : diagB ≤ 1 := by
    simpa [diagB] using subMeas_diagMass_le_one ψ hψ B
  have haux :
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * B.outcome a)| ≤
        Real.sqrt (qSDD ψ A B) * Real.sqrt diagB := by
    calc
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * B.outcome a)|
        ≤ ∑ a : Outcome, |ev ψ ((A.outcome a - B.outcome a) * B.outcome a)| := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Outcome,
            Real.sqrt (ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))) *
              Real.sqrt (ev ψ (B.outcome a * B.outcome a)) := by
            refine Finset.sum_le_sum ?_
            intro a _
            have hherm : (A.outcome a - B.outcome a)ᴴ = A.outcome a - B.outcome a := by
              simp [SubMeas.outcome_hermitian]
            simpa [hherm, SubMeas.outcome_hermitian] using
              ev_abs_mul_le_sqrt ψ (A.outcome a - B.outcome a) (B.outcome a)
      _ ≤ Real.sqrt
            (∑ a : Outcome,
              ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))) *
          Real.sqrt diagB := by
            simpa [diagB] using
              Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
                (f := fun a =>
                  ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a)))
                (g := fun a => ev ψ (B.outcome a * B.outcome a))
                (fun a => ev_adjoint_self_nonneg ψ _)
                (fun a => by
                  simpa [SubMeas.outcome_hermitian] using
                    ev_adjoint_self_nonneg ψ (B.outcome a))
      _ = Real.sqrt (qSDD ψ A B) * Real.sqrt diagB := by
            simp [qSDD, qSDDCore, diagB]
  have hsqrtB : Real.sqrt diagB ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdiagB_le_one
  have haux' :
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * B.outcome a)| ≤
        Real.sqrt (qSDD ψ A B) := by
    calc
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * B.outcome a)|
        ≤ Real.sqrt (qSDD ψ A B) * Real.sqrt diagB := haux
      _ ≤ Real.sqrt (qSDD ψ A B) * 1 := by
            exact mul_le_mul_of_nonneg_left hsqrtB (Real.sqrt_nonneg _)
      _ = Real.sqrt (qSDD ψ A B) := by ring
  convert haux' using 1
  refine congrArg abs ?_
  calc
    ∑ a : Outcome, ev ψ (A.outcome a * B.outcome a) -
        ∑ a : Outcome, ev ψ (B.outcome a * B.outcome a)
      = ∑ a : Outcome,
          (ev ψ (A.outcome a * B.outcome a) -
            ev ψ (B.outcome a * B.outcome a)) := by
              rw [← Finset.sum_sub_distrib]
    _ = ∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * B.outcome a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          have hcomm :
              ev ψ (A.outcome a * B.outcome a) = ev ψ (B.outcome a * A.outcome a) := by
            exact ev_mul_comm_of_psd ψ _ _ (A.outcome_pos a) (B.outcome_pos a)
          calc
            ev ψ (A.outcome a * B.outcome a) - ev ψ (B.outcome a * B.outcome a)
              = ev ψ (A.outcome a * B.outcome a - B.outcome a * B.outcome a) := by
                  rw [(ev_sub ψ (A.outcome a * B.outcome a) (B.outcome a * B.outcome a)).symm]
            _ = ev ψ ((A.outcome a - B.outcome a) * B.outcome a) := by
                  simp [sub_mul]



end MIPStarRE.LDT.Preliminaries

end

end LIDT


