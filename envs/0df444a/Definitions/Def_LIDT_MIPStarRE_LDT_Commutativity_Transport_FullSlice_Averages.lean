-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
-- name    : LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:59:07.441981+00:00
-- url     : https://prove2.me/theorems/46e3bdc7-b42d-4e22-adb2-b0ee36e0c759
-- title:
--   LIDT definitions: LDT / Commutativity / Transport / FullSlice / Averages
-- statement:
--   This bundle defines the zero family and scalar or tensor averages used to transport commutativity estimates from full slices to evaluated slices. It includes ABA and ABAB expressions, their tensor variants, and the corresponding X-evaluated BAB tensor average.
--
--   Principal definitions:
--   - `zeroFullSliceOpFamily`: the neutral full-slice operator family.
--   - `fullSliceABAAvg`: the full-slice ABA scalar average.
--   - `fullSliceABABAvg`: the full-slice ABAB scalar average.
--   - `evaluatedSliceABAAvg`: the evaluated-slice ABA scalar average.
--   - `evaluatedSliceABABAvg`: the evaluated-slice ABAB scalar average.
--   - `fullSliceBABAtensorAvg`: the full-slice BAB tensor average.
--   - `evaluatedSliceABABtensorAvg`: the evaluated-slice ABA tensor average.
--   - `xEvaluatedSliceBABAtensorAvg`: the X-evaluated BAB tensor average.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Commutativity/Transport/FullSlice/Averages.lean#L130-L412

-- Generated from MIPStarRE/LDT/Commutativity/Transport/FullSlice/Averages.lean by skeleton subtraction.
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
# Full-slice averages and index equivalences

Zero-family definition, shared average-reindexing helpers, and averaged scalar
and tensor quantities for the full-slice outcome space, together with
data-reindexing equivalences.

The tensor-form averages are internal to the scalar/tensor comparison recorded
in `docs/decisions/713-scalar-tensor-decision.md`; downstream code should use
the scalar public API.

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



/-- The zero operator family on the full-slice outcome space. -/
noncomputable def zeroFullSliceOpFamily
    (params : Parameters) [FieldModel params.q] :
    OpFamily (FullSliceOutcome params) (ι × ι) where
  outcome := fun _ => 0
  total := 0

/-- Full-slice ABA scalar average: `E_{x,y} ∑_{g,h} ⟨ψ| G^x_g G^y_h G^x_g ⊗ I |ψ⟩`.

Full-polynomial analog of the evaluated `evaluatedSliceABATerm` (line 664);
obtained from it by replacing the evaluated outcomes `a,b` with polynomial
outcomes `g,h` summed over `FullSliceOutcome`. -/
noncomputable def fullSliceABAAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (FullSliceQuestion params))
    (fun xy =>
      ∑ gh : FullSliceOutcome params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            ((family.meas xy.1).toSubMeas.outcome gh.1 *
              (family.meas xy.2).toSubMeas.outcome gh.2 *
              (family.meas xy.1).toSubMeas.outcome gh.1)))

/-- Full-slice ABAB scalar average:
`E_{x,y} ∑_{g,h} ⟨ψ| G^x_g G^y_h G^x_g G^y_h ⊗ I |ψ⟩`. -/
noncomputable def fullSliceABABAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (FullSliceQuestion params))
    (fun xy =>
      ∑ gh : FullSliceOutcome params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            ((family.meas xy.1).toSubMeas.outcome gh.1 *
              (family.meas xy.2).toSubMeas.outcome gh.2 *
              (family.meas xy.1).toSubMeas.outcome gh.1 *
              (family.meas xy.2).toSubMeas.outcome gh.2)))

/-- Evaluated-slice ABA scalar average:
`E_{u,v,x,y} ∑_{a,b} ⟨ψ| G^x_[g(u)=a] G^y_[h(v)=b] G^x_[g(u)=a] ⊗ I |ψ⟩`.

Averaged analog of `evaluatedSliceABATerm` (line 664) over the full slice
question. -/
noncomputable def evaluatedSliceABAAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (EvaluatedSliceQuestion params))
    (fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        evaluatedSliceABATerm params strategy family q ab)

/-- Evaluated-slice ABAB scalar average:
`E_{u,v,x,y} ∑_{a,b} ⟨ψ| G^x_[g(u)=a] G^y_[h(v)=b] G^x_[g(u)=a] G^y_[h(v)=b] ⊗ I |ψ⟩`. -/
noncomputable def evaluatedSliceABABAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (EvaluatedSliceQuestion params))
    (fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        evaluatedSliceABABTerm params strategy family q ab)

/-- Full-slice `BAB ⊗ A` tensor average
(paper `eq:gcom4` RHS, `commutativity-G.tex` line 334):
`E_{x,y} ∑_{g,h} ⟨ψ| G^y_h G^x_g G^y_h ⊗ G^x_g |ψ⟩`.

This is the manifestly-PSD tensor-form partner of `fullSliceABAAvg` used by the
marginalization step: each summand factors as `V† V` with
`V = (G^x_g G^y_h) ⊗ √(G^x_g)`, so the outer absolute value drops and the
Schwartz–Zippel collision bound applies per outcome. This tensor-form average
is internal to the scalar public API recorded by decision #713. -/
noncomputable def fullSliceBABAtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (FullSliceQuestion params))
    (fun xy =>
      ∑ gh : FullSliceOutcome params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((family.meas xy.2).toSubMeas.outcome gh.2 *
                (family.meas xy.1).toSubMeas.outcome gh.1 *
                (family.meas xy.2).toSubMeas.outcome gh.2) *
            rightTensor (ι₁ := ι)
              ((family.meas xy.1).toSubMeas.outcome gh.1)))



/-- Evaluated-slice `ABA ⊗ B` tensor average (evaluated-side analogue of
`fullSliceABABtensorAvg`):
`E_{u,v,x,y} ∑_{a,b} ⟨ψ|
   G^x_[g(u)=a] G^y_[h(v)=b] G^x_[g(u)=a]
     ⊗ G^y_[h(v)=b] |ψ⟩`.

This is the second tensor-form endpoint in paper `commutativity-G.tex` lines
356-360.  The scalar-to-tensor comparison
`evaluatedSliceABAB_scalar_to_ABABtensor` reaches it by moving the trailing
`G^y_[h(v)=b]` factor from the left register to the right register.

The shared tensor endpoint is defined here so the evaluated-side transport
lemmas can use the same notation as the full-slice transport lemmas. -/
noncomputable def evaluatedSliceABABtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (EvaluatedSliceQuestion params))
    (fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((evaluatedSliceFirstFactor params family q).outcome ab.1 *
                (evaluatedSliceSecondFactor params family q).outcome ab.2 *
                (evaluatedSliceFirstFactor params family q).outcome ab.1) *
            rightTensor (ι₁ := ι)
              ((evaluatedSliceSecondFactor params family q).outcome ab.2)))


/-- X-evaluated `BAB ⊗ A` tensor average.

This is the intermediate obtained from `fullSliceBABAtensorAvg` after
postprocessing only the first/full-`x` polynomial outcome by a sampled point
`u : Point params`; the second/`y` polynomial outcome remains full.  The
x-side tensor marginalization lemma below identifies its difference from the
full tensor average with `fullSliceBABAxCollisionFactored`. -/
noncomputable def xEvaluatedSliceBABAtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (FullSliceQuestion params))
    (fun xy =>
      avgOver (uniformDistribution (Point params))
        (fun u =>
          let A : SubMeas (Fq params) ι :=
            evaluateAt params u ((family.meas xy.1).toSubMeas)
          let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
          ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (B.outcome h * A.outcome a * B.outcome h) *
                rightTensor (ι₁ := ι) (A.outcome a))))

/-- X-evaluated, y-full ABAB scalar average.

This is the scalar endpoint in the display from `eq:evaluate-gcom-at-points` to
`eq:don't-understand-the-numbering-system`: the `x` polynomial outcome has been
postprocessed at `u`, but the second `closenessOfIP` move has not yet transferred
the trailing `G^y_h` to the right register. -/
noncomputable def xEvaluatedFullSliceABABAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (Point params × FullSliceQuestion params))
    (fun ux =>
      let A : SubMeas (Fq params) ι :=
        evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
      let B : SubMeas (Polynomial params) ι := (family.meas ux.2.2).toSubMeas
      ∑ ah : Fq params × Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            (A.outcome ah.1 * B.outcome ah.2 * A.outcome ah.1 * B.outcome ah.2)))

/-- X-evaluated, y-full `ABA ⊗ B` tensor average.

This is the y-side intermediate in paper `eq:evaluate-gcom-at-points-part-dos`:
the first/`x` family has already been postprocessed at `u`, while the second/`y`
family still ranges over full polynomial outcomes.  The y-side tensor
marginalization lemma below compares this to `evaluatedSliceABABtensorAvg`. -/
noncomputable def xEvaluatedFullSliceABABtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (Point params × FullSliceQuestion params))
    (fun ux =>
      let A : SubMeas (Fq params) ι :=
        evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
      let B : SubMeas (Polynomial params) ι := (family.meas ux.2.2).toSubMeas
      ∑ ah : Fq params × Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι) (A.outcome ah.1 * B.outcome ah.2 * A.outcome ah.1) *
            rightTensor (ι₁ := ι) (B.outcome ah.2)))

/-- Reindex mixed x-evaluated data `(u, x, y)` as `(appendPoint u x, y)`. -/
 def xEvaluatedQuestionPointNextEquiv
    (params : Parameters) [FieldModel params.q] :
    Point params × FullSliceQuestion params ≃ Point params.next × Fq params where
  toFun := fun ux => (appendPoint params ux.1 ux.2.1, ux.2.2)
  invFun := fun wy => (truncatePoint params wy.1, (pointHeight params wy.1, wy.2))
  left_inv := fun ⟨u, x, _⟩ =>
    Prod.ext (truncatePoint_appendPoint params u x)
      (Prod.ext (pointHeight_appendPoint params u x) rfl)
  right_inv := fun ⟨w, _⟩ => Prod.ext ((pointNextEquiv params).left_inv w) rfl





/-- Reindex evaluated-slice questions as `((u, (x, y)), v)`.

This product order is tailored to the y-marginalization expansion: the residual
is indexed by the already x-evaluated data `(u, x, y)`, and the remaining uniform
average is over the y-evaluation point `v`. -/
def evaluatedSliceQuestionYDataEquiv
    (params : Parameters) [FieldModel params.q] :
    EvaluatedSliceQuestion params ≃
      (Point params × FullSliceQuestion params) × Point params where
  toFun := fun q =>
    ((truncatePoint params q.1, fullSliceQuestionOfEvaluatedSlice params q),
      truncatePoint params q.2)
  invFun := fun r =>
    (appendPoint params r.1.1 r.1.2.1, appendPoint params r.2 r.1.2.2)
  left_inv := fun ⟨u, v⟩ =>
    Prod.ext ((CommutativityPoints.pointNextEquiv params).left_inv u)
      ((CommutativityPoints.pointNextEquiv params).left_inv v)
  right_inv := fun ⟨⟨u, x, y⟩, v⟩ =>
    Prod.ext
      (Prod.ext (truncatePoint_appendPoint params u x)
        (Prod.ext (pointHeight_appendPoint params u x) (pointHeight_appendPoint params v y)))
      (truncatePoint_appendPoint params v y)

end MIPStarRE.LDT.Commutativity

end

end LIDT


