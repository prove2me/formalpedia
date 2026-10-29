-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
-- name    : LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:02:39.978767+00:00
-- url     : https://prove2.me/theorems/499f4e32-7399-4ba4-9589-8b115878add8
-- title:
--   LIDT definitions: LDT / Commutativity / Transport / FullSlice / Machinery / Marginalization / Core
-- statement:
--   This bundle isolates the two collision residuals that arise when tensor-valued full-slice expressions are marginalized over one slice coordinate. The residuals expose distinct polynomial pairs that agree at a sampled point, so the low-degree collision estimate can bound each by $md/q$.
--
--   Principal definitions:
--   - `fullSliceBABAxCollisionFactored`: The $x$-marginalization residual, a sum over distinct polynomial pairs whose values collide at a point, with a polynomial outcome sandwiched between the corresponding left outcomes and paired with a right outcome.
--   - `fullSliceABAByCollisionFactored`: The analogous $y$-marginalization residual, using the point-evaluated left family as the outer sandwich and colliding polynomial pairs on the right.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Commutativity/Transport/FullSlice/Machinery/Marginalization/Core.lean#L32-L86

-- Generated from MIPStarRE/LDT/Commutativity/Transport/FullSlice/Machinery/Marginalization/Core.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic

namespace LIDT

namespace MIPStarRE.LDT.Commutativity
end MIPStarRE.LDT.Commutativity
namespace MIPStarRE.LDT.CommutativityPoints
end MIPStarRE.LDT.CommutativityPoints
namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Full-slice tensor marginalization core

Collision residuals, postprocessing expansions, and tensor marginalization
core bounds for the `BABA` and `ABAB` full-slice tensor averages.

Ex-private definitions are tensor-form machinery per architecture decision
#713; downstream code should use the scalar public API exposed by the
full-slice transport theorems.

## References

- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Factored collision residual for the x-marginalization tensor step.

After expanding the first evaluated family in paper `eq:gcom4-diff`, the remaining
error is this nonnegative sum over pairs of distinct polynomial outcomes whose
values collide at the sampled point `u`. -/
noncomputable def fullSliceBABAxCollisionFactored
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (xy : FullSliceQuestion params) : Error :=
  let A : SubMeas (Polynomial params) ι := (family.meas xy.1).toSubMeas
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  ∑ gg : Polynomial params × Polynomial params, ∑ h : Polynomial params,
    (if gg.1 = gg.2 then 0 else
      avgOver (uniformDistribution (Point params))
        (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) *
      ev strategy.state
        (leftTensor (ι₂ := ι) (B.outcome h * A.outcome gg.1 * B.outcome h) *
          rightTensor (ι₁ := ι) (A.outcome gg.2))



/-- Factored collision residual for the y-marginalization tensor step.

Here the outer sandwich is the already x-evaluated family
`G^x_[g(u)=a]`, while the colliding polynomial pair is on the `y` side. -/
noncomputable def fullSliceABAByCollisionFactored
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (u : Point params) (xy : FullSliceQuestion params) : Error :=
  let A : SubMeas (Fq params) ι :=
    evaluateAt params u ((family.meas xy.1).toSubMeas)
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  ∑ hh : Polynomial params × Polynomial params, ∑ a : Fq params,
    (if hh.1 = hh.2 then 0 else
      avgOver (uniformDistribution (Point params))
        (fun v => if hh.1 v = hh.2 v then (1 : Error) else 0)) *
      ev strategy.state
        (leftTensor (ι₂ := ι) (A.outcome a * B.outcome hh.1 * A.outcome a) *
          rightTensor (ι₁ := ι) (B.outcome hh.2))

























end MIPStarRE.LDT.Commutativity

end

end LIDT


