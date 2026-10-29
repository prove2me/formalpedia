-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Base
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Base
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:04:16.404594+00:00
-- url     : https://prove2.me/theorems/01e7b4b3-eead-4972-bcf4-8b2f7ec0b0e9
-- title:
--   LIDT definitions: LDT / SelfImprovement / MatrixRealization / Base
-- statement:
--   This bundle defines the finite-matrix realization of the self-improvement semidefinite program. It packages explicit strict primal and dual witnesses, averaged point operators, objective contributions, and the feasibility bounds needed by the matrix proof.
--
--   Principal definitions:
--   - `MatrixSdpRealization`: the concrete finite-dimensional matrix model of the SDP data.
--   - `matrixSdpStrictPrimalSubmeasurement`: the explicit strict-feasible primal submeasurement with uniform identity effects.
--   - `matrixSdpStrictDualWitness`: the explicit strict-feasible dual operator.
--   - `matrixAveragedPointOperatorContribution`: the point-conditioned operator contribution for one polynomial outcome.
--   - `matrixAveragedPointOperator`: the averaged operator associated with that polynomial outcome.
--   - `matrixSdpPrimalContributionOperator`: the product of the primal effect and its averaged point operator.
--   - `matrixSdpPrimalObjective`: the real trace-pairing objective summed over polynomial outcomes.
--   - `MatrixSdpFeasibleBounds`: the record of the explicit matrix-level feasibility bounds.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/MatrixRealization/Base.lean#L30-L259

-- Generated from MIPStarRE/LDT/SelfImprovement/MatrixRealization/Base.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_NaimarkCore
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 9 — Matrix realization

Concrete finite-dimensional matrix realizations of the self-improvement SDP data.

## References

- `references/ldt-paper/self_improvement.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.Quantum
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

universe u

/-- A concrete finite-dimensional matrix realization of the SDP data. -/
structure MatrixSdpRealization (params : Parameters) [FieldModel params.q] where
  space : FiniteHilbertSpace.{u}
  state : PositiveMatrixState space
  pointMeasurement : Point params → MatrixSubmeasurement (Fq params) space

/-- The constant strict primal effects have total mass `(1/2)I` in the concrete
matrix realization. -/
private theorem matrixSdpStrictPrimalConstantSum (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∑ _ : Polynomial params, sdpStrictPrimalWeight params •
        (1 : MatrixOperator model.space) =
      ((1 / 2 : Error) • (1 : MatrixOperator model.space)) := by
  exact sdpStrictPrimalConstantSum (ι := model.space.carrier) params

private theorem sdpStrictPrimalEffect_nonneg (params : Parameters)
    [FieldModel params.q] (space : FiniteHilbertSpace.{u}) :
    0 ≤ sdpStrictPrimalWeight params • (1 : MatrixOperator space) := by
  unfold sdpStrictPrimalWeight; positivity

private theorem errorHalf_smul_one_le_one (space : FiniteHilbertSpace.{u}) :
    (1 / 2 : Error) • (1 : MatrixOperator space) ≤ 1 := by
  have hhalf : (1 / 2 : Error) ≤ 1 := by norm_num
  simpa using smul_le_smul_of_nonneg_right hhalf
    (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : MatrixOperator space))

/-- The matrix-level strict-feasible primal witness
`T_g = (2 |\polyfunc{m}{q}{d}|)^{-1} I`. -/
noncomputable def matrixSdpStrictPrimalSubmeasurement (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space where
  effect := fun _ => sdpStrictPrimalWeight params • (1 : MatrixOperator model.space)
  pos := fun _ => by
    exact sdpStrictPrimalEffect_nonneg params model.space
  sum_le_one := by
    exact (le_of_eq (matrixSdpStrictPrimalConstantSum params model)).trans
      (errorHalf_smul_one_le_one model.space)



/-- Paper origin: `references/ldt-paper/self_improvement.tex:168-176`
(`\label{lem:sdp}` strict feasible dual witness `Z = 2I`);
blueprint `\label{lem:sdp-matrix-feasible-bounds}`.

The paper's matrix-level strict-feasible dual witness `Z = 2I`. -/
noncomputable def matrixSdpStrictDualWitness {params : Parameters} [FieldModel params.q]
    (model : MatrixSdpRealization params) : MatrixOperator model.space :=
  (2 : Error) • (1 : MatrixOperator model.space)



/-- The matrix-level strict-feasible dual witness dominates the identity. -/
theorem one_le_matrixSdpStrictDualWitness {params : Parameters} [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    (1 : MatrixOperator model.space) ≤ matrixSdpStrictDualWitness model := by
  exact one_le_sdpStrictDualWitness (ι := model.space.carrier)

/-- The concrete operator `A^u_{g(u)}` entering the SDP average. -/
noncomputable def matrixAveragedPointOperatorContribution (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (g : Polynomial params) (u : Point params) : MatrixOperator model.space :=
  (model.pointMeasurement u).effect (g u)

/-- The concrete averaged operator `A_g = E_u A^u_{g(u)}`.

This is defined through the project-wide distributional average
`averageOperatorOverDistribution` so that the submeasurement averaging lemmas
apply directly.  The operator is used only in this matrix realization layer. -/
noncomputable def matrixAveragedPointOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (g : Polynomial params) : MatrixOperator model.space :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (matrixAveragedPointOperatorContribution params model g)

/-- The averaged point operator `A_g` is bounded by the identity. -/
theorem matrixAveragedPointOperator_le_one (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (g : Polynomial params) :
    matrixAveragedPointOperator params model g ≤ 1 := by
  unfold matrixAveragedPointOperator matrixAveragedPointOperatorContribution
  exact averageOperatorOverDistribution_uniform_le_one
    (fun u => (model.pointMeasurement u).effect (g u))
    (fun u => by
      calc
        (model.pointMeasurement u).effect (g u)
            ≤ ∑ a : Fq params, (model.pointMeasurement u).effect a :=
              Finset.single_le_sum
                (fun a _ => (model.pointMeasurement u).pos a)
                (Finset.mem_univ (g u))
        _ ≤ 1 := (model.pointMeasurement u).sum_le_one)

/-- The averaged point operator `A_g` is positive semidefinite. -/
theorem matrixAveragedPointOperator_nonneg (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (g : Polynomial params) :
    0 ≤ matrixAveragedPointOperator params model g := by
  unfold matrixAveragedPointOperator matrixAveragedPointOperatorContribution
  exact averageOperatorOverDistribution_nonneg (uniformDistribution (Point params))
    (fun u => (model.pointMeasurement u).effect (g u))
    (fun u => (model.pointMeasurement u).pos (g u))

/-- The concrete primal contribution `T_g A_g`. -/
noncomputable def matrixSdpPrimalContributionOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (g : Polynomial params) : MatrixOperator model.space :=
  (T.effect g) * matrixAveragedPointOperator params model g

/-- The concrete primal objective `Σ_g Re Tr(T_g A_g)`. -/
noncomputable def matrixSdpPrimalObjective (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) : Error :=
  Complex.re (Matrix.trace (∑ g : Polynomial params,
    matrixSdpPrimalContributionOperator params model T g))

/-- The concrete dual objective `Re Tr(Z)`. -/
noncomputable def matrixSdpDualObjective {params : Parameters} [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) : Error :=
  Complex.re (Matrix.trace Z)

/-- The concrete dual slack operator `Z - A_g`. -/
noncomputable def matrixSdpDualSlackOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (g : Polynomial params) : MatrixOperator model.space :=
  Z - matrixAveragedPointOperator params model g

/-- The matrix-level strict-feasible dual witness `2I` dominates every averaged
point operator. -/
theorem matrixSdpStrictDualWitness_dualFeasible (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model (matrixSdpStrictDualWitness model) g := by
  intro g
  exact sub_nonneg.mpr
    (le_trans (matrixAveragedPointOperator_le_one params model g)
      (one_le_matrixSdpStrictDualWitness model))



/-- Dual feasibility already implies that the dual operator is positive
semidefinite, since every averaged point operator `A_g` is positive. -/
theorem matrixSdpDualPositive_of_dualFeasible (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g) :
    0 ≤ Z := by
  -- Any polynomial would suffice here; the distinguished one is only a
  -- convenient fixed element of the finite polynomial type.
  let g0 : Polynomial params := sdpDistinguishedPolynomial params
  have hAg_nonneg : 0 ≤ matrixAveragedPointOperator params model g0 :=
    matrixAveragedPointOperator_nonneg params model g0
  have hAg_le_Z : matrixAveragedPointOperator params model g0 ≤ Z :=
    sub_nonneg.mp (by simpa [matrixSdpDualSlackOperator] using hdual g0)
  exact hAg_nonneg.trans hAg_le_Z

/-- Matrix-level record of the explicit feasible bounds used in the SDP argument.

The uniform primal family has total `(1/2)I`, while the dual witness `2I`
dominates the identity and is dual feasible. Positivity of the dual witness is
derivable from dual feasibility and the positivity of the averaged point
operators. These are the non-strict matrix inequalities currently recorded in
Lean; the structure is not an optimality statement and does not include
complementary slackness. -/
structure MatrixSdpFeasibleBounds (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) : Prop where
  primalTotalHalf :
    ∑ g : Polynomial params, T.effect g =
      ((1 / 2 : Error) • (1 : MatrixOperator model.space))
  dualDominatesIdentity : (1 : MatrixOperator model.space) ≤ Z
  dualFeasible :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model Z g
  dualSlackDominatesIdentity :
    ∀ g : Polynomial params,
      (1 : MatrixOperator model.space) ≤ matrixSdpDualSlackOperator params model Z g




end MIPStarRE.LDT.SelfImprovement

end

end LIDT


