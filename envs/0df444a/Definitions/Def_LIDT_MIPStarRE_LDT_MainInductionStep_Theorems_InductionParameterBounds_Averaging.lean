-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_Averaging
-- name    : LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_Averaging
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:44:56.234112+00:00
-- url     : https://prove2.me/theorems/22ab3371-5f0b-40d7-91f8-154db06b6027
-- title:
--   LIDT definitions: LDT / MainInductionStep / Theorems / InductionParameterBounds / Averaging
-- statement:
--   This bundle supplies the averaging inequalities needed when slice errors are conditioned on a height in the main induction step. Jensen's inequality moves fractional powers through a uniform average, while the other bounds absorb the slice-conditioning loss into the successor dimension parameter.
--
--   Principal definitions:
--   - `avgOver_uniform_rpow_one_div_le_rpow_avg`: For nonnegative $f$ on a nonempty finite set and $n\ge1$, $\mathbb E[f^{1/n}]\le(\mathbb E f)^{1/n}$.
--   - `m_mul_sliceConditioningLoss_rpow_le_next_m_mul_rpow`: If $x\ge0$ and $0\le c\le1$, then $m\,\operatorname{rpow}(\lambda x,c)\le(m+1)\operatorname{rpow}(x,c)$ for the slice-conditioning loss $\lambda=(m+1)/m$.
--   - `m_sq_mul_sliceConditioningLoss_rpow_le_next_sq_mul_rpow`: The same comparison with the squared dimension factors $m^2$ and $(m+1)^2$.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MainInductionStep/Theorems/InductionParameterBounds/Averaging.lean#L27-L110

-- Generated from MIPStarRE/LDT/MainInductionStep/Theorems/InductionParameterBounds/Averaging.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionPMF
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_Preliminaries
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

/-!
# Section 6 — Induction Parameter Averaging Bounds

This file contains the uniform Jensen estimate used for averaged slice errors,
together with the
`sliceConditioningLoss` comparisons which replace the ambient factor `m` by
`m + 1` in the induction step.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

/-- Jensen's inequality for `Real.rpow (1/n)` against a uniform distribution:
the average of `(f a)^{1/n}` is at most `(average f)^{1/n}`. This is the
workhorse used inside each of the averaged-slice bounds (`average_slice…_le`)
to push `rpow (1/32)` or `rpow (1/1024)` through a uniform `avgOver` on
`Fq params`. -/
lemma avgOver_uniform_rpow_one_div_le_rpow_avg
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → Error) (n : ℕ) (hn : 1 ≤ n) (hf : ∀ a, 0 ≤ f a) :
    avgOver (uniformDistribution α)
        (fun a => Real.rpow (f a) (1 / (n : Error))) ≤
      Real.rpow (avgOver (uniformDistribution α) f) (1 / (n : Error)) := by
  rw [avgOver_uniform_eq_pmf_realWeightedSum, avgOver_uniform_eq_pmf_realWeightedSum]
  exact PMF.realWeightedSum_rpow_one_div_le_rpow
    (p := PMF.uniformOfFintype α) (f := f) (n := n) hn hf

/-- Internal helper: `m · (sliceConditioningLoss · x)^c ≤ m_next · x^c` for `c ≤ 1`.

Exposed for cross-module use in `AvgSliceErrors`. -/
lemma m_mul_sliceConditioningLoss_rpow_le_next_m_mul_rpow
    (params : Parameters) {x c : Error}
    (hx : 0 ≤ x) (_hc_nonneg : 0 ≤ c) (hc_le_one : c ≤ 1) :
    (params.m : Error) * Real.rpow (sliceConditioningLoss params * x) c ≤
      (params.next.m : Error) * Real.rpow x c := by
  have hm0 : (params.m : Error) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt params.hm
  have hloss_nonneg : 0 ≤ sliceConditioningLoss params := by
    unfold sliceConditioningLoss
    positivity
  have hloss_ge_one : (1 : Error) ≤ sliceConditioningLoss params := by
    unfold sliceConditioningLoss
    have hm_pos : (0 : Error) < (params.m : Error) := by
      exact_mod_cast params.hm
    have hnum_ge : (params.m : Error) ≤ ((params.m + 1 : ℕ) : Error) := by
      exact_mod_cast Nat.le_succ params.m
    exact (one_le_div₀ hm_pos).2 hnum_ge
  have hloss_rpow_le :
      Real.rpow (sliceConditioningLoss params) c ≤ sliceConditioningLoss params := by
    calc
      Real.rpow (sliceConditioningLoss params) c
          ≤ Real.rpow (sliceConditioningLoss params) 1 := by
            exact Real.rpow_le_rpow_of_exponent_le hloss_ge_one hc_le_one
      _ = sliceConditioningLoss params := by simp
  calc
    (params.m : Error) * Real.rpow (sliceConditioningLoss params * x) c
      = (params.m : Error) *
          (Real.rpow (sliceConditioningLoss params) c * Real.rpow x c) := by
            rw [show Real.rpow (sliceConditioningLoss params * x) c =
                Real.rpow (sliceConditioningLoss params) c * Real.rpow x c by
                exact Real.mul_rpow hloss_nonneg hx]
    _ ≤ (params.m : Error) * (sliceConditioningLoss params * Real.rpow x c) := by
          gcongr
          exact Real.rpow_nonneg hx c
    _ = (params.next.m : Error) * Real.rpow x c := by
          have hnext_eq : (params.next.m : Error) = ((params.m + 1 : ℕ) : Error) := by
            norm_num [Parameters.next]
          rw [hnext_eq]
          unfold sliceConditioningLoss
          field_simp [hm0]
/-- Internal helper: `m² · (sliceConditioningLoss · x)^c ≤ m_next² · x^c` for `c ≤ 1`.

Exposed for cross-module use in `AvgSliceErrors`. -/
lemma m_sq_mul_sliceConditioningLoss_rpow_le_next_sq_mul_rpow
    (params : Parameters) {x c : Error}
    (hx : 0 ≤ x) (hc_nonneg : 0 ≤ c) (hc_le_one : c ≤ 1) :
    ((params.m : Error) ^ (2 : ℕ)) * Real.rpow (sliceConditioningLoss params * x) c ≤
      ((params.next.m : Error) ^ (2 : ℕ)) * Real.rpow x c := by
  have hm_le_next : (params.m : Error) ≤ (params.next.m : Error) := by
    exact_mod_cast Nat.le_succ params.m
  calc
    ((params.m : Error) ^ (2 : ℕ)) * Real.rpow (sliceConditioningLoss params * x) c
      = (params.m : Error) *
          ((params.m : Error) * Real.rpow (sliceConditioningLoss params * x) c) := by
            ring
    _ ≤ (params.m : Error) * ((params.next.m : Error) * Real.rpow x c) := by
          exact mul_le_mul_of_nonneg_left
            (m_mul_sliceConditioningLoss_rpow_le_next_m_mul_rpow params hx hc_nonneg hc_le_one)
            (by positivity)
    _ ≤ ((params.next.m : Error) ^ (2 : ℕ)) * Real.rpow x c := by
          have hcoef :
              (params.m : Error) * (params.next.m : Error) ≤
                ((params.next.m : Error) ^ (2 : ℕ)) := by
            nlinarith
          have hrpow_nonneg : 0 ≤ Real.rpow x c := Real.rpow_nonneg hx c
          simpa [mul_assoc] using (mul_le_mul_of_nonneg_right hcoef hrpow_nonneg)

end MIPStarRE.LDT.MainInductionStep

end

end LIDT


