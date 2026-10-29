-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionPMF
-- name    : LIDT_MIPStarRE_LDT_Basic_DistributionPMF
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:54:30.675449+00:00
-- url     : https://prove2.me/theorems/5cd28dda-9803-4fe5-b5c4-828815a8c91e
-- title:
--   LIDT definitions: LDT / Basic / DistributionPMF
-- statement:
--   This bundle connects the project's finite-support distribution averages with Mathlib's finite probability-mass-function expectations. It is the bridge used whenever LDT averaging notation is rewritten in standard probability form.
--
--   Principal definitions:
--   - `avgOver_uniform_eq_pmf_realWeightedSum`: the uniform `avgOver` of a scalar family equals its real-weighted expectation under the uniform PMF on the finite index type.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/DistributionPMF.lean#L94-L101

-- Generated from MIPStarRE/LDT/Basic/DistributionPMF.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

/-!
# PMF expectations associated to project distributions

This module relates the project `Distribution` averaging notation to the finite
expectation `PMF.realWeightedSum` on Mathlib probability mass functions.  The
statements keep the project-facing averages available while allowing later
probability arguments to cite the associated Mathlib `PMF` object directly.
The module-valued finite-sum algebra for uniform project distributions lives in
`MIPStarRE.LDT.Basic.DistributionUniformSums`; this file records the additional
comparison with `PMF.realWeightedSum`.

## Main declarations

* `avgOver_eq_toPMF_realWeightedSum`
* `averageOperatorOverDistribution_eq_toPMF_realWeightedSum`
* `Distribution.weightedSumLinearMap_eq_toPMF_realWeightedSum`
* `Distribution.weightedSumLinearMap_eq_toPMF_realWeightedSumLinearMap`
* `uniformDistribution_sum_smul_eq_pmf_realWeightedSum`
* `avgOver_uniform_eq_pmf_realWeightedSum`
* `averageOperatorOverDistribution_uniform_eq_pmf_realWeightedSum`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Distribution





end Distribution







/-- The uniform average is the finite expectation against Mathlib's uniform
probability mass function. -/
theorem avgOver_uniform_eq_pmf_realWeightedSum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (f : α → Error) :
    avgOver (uniformDistribution α) f =
      PMF.realWeightedSum (PMF.uniformOfFintype α) f := by
  simpa [PMF.realWeightedSum, avgOver, smul_eq_mul] using
    uniformDistribution_sum_smul_eq_pmf_sum (α := α) (f := f)



end MIPStarRE.LDT

end

end LIDT


