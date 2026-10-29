-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_InputSdp
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_InputSdp
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:09:29.225465+00:00
-- url     : https://prove2.me/theorems/a19d4849-7eb2-4284-91b3-1540ed94200d
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / HelperCompleteness / InputSdp
-- statement:
--   This bundle supplies the overlap and dual-mass calculations for the completeness part of the self-improvement helper. It reindexes polynomial outcomes by their value at a point, identifies the resulting expression with matching mass, and then uses SDP dual feasibility and complementary slackness.
--
--   Principal definitions:
--   - `input_consistency_match_mass_lower_bound`: Converts input point consistency into a lower bound on the averaged matching mass.
--   - `input_sdp_overlap_fiberwise_sum_eq`: Reindexes a polynomial-outcome sum by the value of the polynomial at a fixed point.
--   - `input_sdp_bracketed_sum_eq_match_mass`: Identifies the bracketed fiber sum with the point-versus-polynomial matching mass.
--   - `input_match_mass_eq_sdp_overlap`: Rewrites the averaged input overlap as $\sum_g\langle\psi,A_g\otimes G_g\rangle$.
--   - `sdp_overlap_le_dual_mass`: Dual feasibility bounds this SDP overlap by the dual mass $\langle\psi,Z\otimes I\rangle$.
--   - `input_consistency_dual_mass_lower_bound`: Transfers the input-consistency lower bound to the dual mass.
--   - `sdp_complementary_slackness_sum_eq_dual_mass`: Uses complementary slackness to identify the relevant averaged sum with the dual mass.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/InputSdp.lean#L36-L325

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/InputSdp.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_DataProcessing
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_CommonHelpers
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Final
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Helper
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Helper completeness: input consistency and the SDP bridge

This file contains the part of the helper-completeness argument which relates
input consistency, SDP dual feasibility, and complementary slackness.  These
lemmas correspond to the lower-bound calculation at the end of the completeness
proof in `references/ldt-paper/self_improvement.tex`, lines 406--414.

## References

- `references/ldt-paper/self_improvement.tex` lines 406--414
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The incoming consistency of the original polynomial measurement gives the
matching-mass lower bound used in the helper-stage completeness proof.

This is the last step of the proof of
`references/ldt-paper/self_improvement.tex`, lines 407--414: after evaluating
the original input measurement `G` at a random point, `ConsRel ... nu` says the
off-diagonal mass is at most `nu`, hence the diagonal matching mass is at least
`1 - nu`. The blueprint mirror is
`blueprint/src/chapter/ch07_self_improvement.tex`, lines 137--142. -/
theorem input_consistency_match_mass_lower_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : Measurement (Polynomial params) ι)
    (nu : Error)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    1 - nu ≤
      avgOver (uniformDistribution (Point params)) (fun u =>
        qBipartiteMatchMass strategy.state
          ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
          ((polynomialEvaluationFamily params G.toSubMeas) u)) := by
  refine cons_rel_uniform_full_total_match_mass_lower_bound
    strategy.state strategy.isNormalized
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    (polynomialEvaluationFamily params G.toSubMeas) nu ?_ ?_ hcons
  · intro u
    exact (strategy.pointMeasurement u).total_eq_one
  · intro u
    simpa [polynomialEvaluationFamily, evaluateAt, postprocess_total] using G.total_eq_one

/-- Reindex a polynomial sum by the value of the polynomial at a fixed point.

This is the finite fiber decomposition used in the input-mass SDP bridge. The
lemma keeps the `Finset.sum_fiberwise` invocation separate from the tensor
algebra in `input_match_mass_eq_sdp_overlap`. -/
private lemma input_sdp_overlap_fiberwise_sum_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (u : Point params) :
    (∑ g : Polynomial params,
        ev strategy.state
          (opTensor (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
            (G.outcome g))) =
      ∑ a : Fq params,
        ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
          ev strategy.state
            (opTensor (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
              (G.outcome g)) := by
  classical
  simpa using polynomial_sum_fiberwise params u
    (fun g =>
      ev strategy.state
        (opTensor (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
          (G.outcome g)))

/-- The bracketed fiber expression is exactly the bipartite matching mass of
the point measurement against the polynomial measurement evaluated at `u`. -/
private lemma input_sdp_bracketed_sum_eq_match_mass
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (u : Point params) :
    (∑ a : Fq params,
        ev strategy.state
          (opTensor ((strategy.pointMeasurement u).outcome a)
            (∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
              G.outcome g))) =
      qBipartiteMatchMass strategy.state
        ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
        ((polynomialEvaluationFamily params G) u) := by
  classical
  unfold qBipartiteMatchMass
  refine Finset.sum_congr rfl ?_
  intro a _
  simp only [IdxProjMeas.toIdxSubMeas]
  rw [polynomialEvaluationFamily, evaluateAt, SubMeas.postprocess_outcome]

/-- Reindex the averaged input-consistency overlap as the SDP overlap
`Σ_g ⟨ψ, A_g ⊗ G_g⟩`.

This is the algebraic content of `references/ldt-paper/self_improvement.tex`,
lines 410--411: the pointwise match mass
`E_u Σ_a ⟨ψ, A^u_a ⊗ G_[g(u)=a] ψ⟩` is the same expression as
`Σ_g ⟨ψ, (E_u A^u_{g(u)}) ⊗ G_g ψ⟩`, after reindexing by the value of `g` at
`u`. The blueprint mirror is
`blueprint/src/chapter/ch07_self_improvement.tex`, lines 137--141. -/
theorem input_match_mass_eq_sdp_overlap
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        qBipartiteMatchMass strategy.state
          ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
          ((polynomialEvaluationFamily params G) u)) =
      ∑ g : Polynomial params,
        ev strategy.state
          (opTensor (averagedPointOperator params strategy g) (G.outcome g)) := by
  classical
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
        qBipartiteMatchMass strategy.state
          ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
          ((polynomialEvaluationFamily params G) u))
        =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ g : Polynomial params,
          ev strategy.state
            (opTensor (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
              (G.outcome g))) := by
        refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
        intro u
        symm
        calc
          ∑ g : Polynomial params,
              ev strategy.state
                (opTensor (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
                  (G.outcome g))
            =
          ∑ a : Fq params,
              ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
                ev strategy.state
                  (opTensor ((strategy.pointMeasurement u).outcome a) (G.outcome g)) := by
              rw [input_sdp_overlap_fiberwise_sum_eq]
              refine Finset.sum_congr rfl ?_
              intro a _
              refine Finset.sum_congr rfl ?_
              intro g hg
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
              simp [pointConditionedOutcomeOperatorAtPolynomial, hg]
          _ =
          ∑ a : Fq params,
              ev strategy.state
                (opTensor ((strategy.pointMeasurement u).outcome a)
                  (∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
                    G.outcome g)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [opTensor_sum_right_finset]
              exact (ev_finset_sum strategy.state _ _).symm
          _ =
          qBipartiteMatchMass strategy.state
            ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
            ((polynomialEvaluationFamily params G) u) := by
              exact input_sdp_bracketed_sum_eq_match_mass params strategy G u
    _ =
      ∑ g : Polynomial params,
        ev strategy.state
          (opTensor (averagedPointOperator params strategy g) (G.outcome g)) := by
        rw [avgOver_sum]
        refine Finset.sum_congr rfl ?_
        intro g _
        exact (ev_opTensor_averageOperatorOverDistribution_left strategy.state
          (uniformDistribution (Point params))
          (pointConditionedOutcomeOperatorAtPolynomial params strategy g)
          (G.outcome g)).symm

/-- Dual feasibility upper-bounds the SDP overlap by the dual mass
`⟨ψ, Z ⊗ I ψ⟩`.

This formalizes `references/ldt-paper/self_improvement.tex`, lines 408--410:
since `G` is a submeasurement, `Z ⊗ I` dominates `Z ⊗ G`, and since the SDP
dual is feasible, each `Z` dominates the averaged point operator
`E_u A^u_{g(u)}`. -/
theorem sdp_overlap_le_dual_mass
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (hZ : 0 ≤ Z)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ sdpDualSlackOperator params strategy Z g) :
    (∑ g : Polynomial params,
        ev strategy.state
          (opTensor (averagedPointOperator params strategy g) (G.outcome g))) ≤
      ev strategy.state (leftTensor (ι₂ := ι) Z) := by
  classical
  calc
    (∑ g : Polynomial params,
        ev strategy.state
          (opTensor (averagedPointOperator params strategy g) (G.outcome g)))
        ≤
      ∑ g : Polynomial params,
        ev strategy.state (opTensor Z (G.outcome g)) := by
        refine Finset.sum_le_sum ?_
        intro g _
        apply ev_mono
        exact opTensor_mono_left
          (sub_nonneg.mp (by simpa [sdpDualSlackOperator] using hdual g))
          (G.outcome_pos g)
    _ = ev strategy.state (opTensor Z G.total) := by
        rw [← G.sum_eq_total]
        rw [opTensor_sum_right_univ]
        exact (ev_sum strategy.state _).symm
    _ ≤ ev strategy.state (leftTensor (ι₂ := ι) Z) := by
        exact ev_mono strategy.state _ _
          (opTensor_le_leftTensor hZ G.total_le_one)

/-- The input-consistency lower bound, after the SDP reindexing and dual
feasibility steps, gives the lower bound on the dual mass used in helper
completeness.

This packages `references/ldt-paper/self_improvement.tex`, lines 406--412,
without asserting the later Cauchy--Schwarz comparison from `Hhat` to `Z` or any
of the projective final-fields transport handled by PR #1071. -/
theorem input_consistency_dual_mass_lower_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : Measurement (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (nu : Error)
    (hZ : 0 ≤ Z)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ sdpDualSlackOperator params strategy Z g)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    1 - nu ≤ ev strategy.state (leftTensor (ι₂ := ι) Z) := by
  calc
    1 - nu
        ≤ avgOver (uniformDistribution (Point params)) (fun u =>
            qBipartiteMatchMass strategy.state
              ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
              ((polynomialEvaluationFamily params G.toSubMeas) u)) :=
          input_consistency_match_mass_lower_bound params strategy G nu hcons
    _ =
      ∑ g : Polynomial params,
        ev strategy.state
          (opTensor (averagedPointOperator params strategy g) (G.outcome g)) :=
          input_match_mass_eq_sdp_overlap params strategy G.toSubMeas
    _ ≤ ev strategy.state (leftTensor (ι₂ := ι) Z) :=
          sdp_overlap_le_dual_mass params strategy G.toSubMeas Z hZ hdual

/-- Complementary slackness converts the averaged-point sum to the dual mass.

This is the exact algebraic replacement used at the end of
`references/ldt-paper/self_improvement.tex`, lines 397--403: after the
Cauchy--Schwarz moves have produced
`Σ_h ⟨ψ, T_h · (E_u A^u_{h(u)}) ⊗ I ψ⟩`, complementary slackness replaces
`T_h · (E_u A^u_{h(u)})` by `T_h · Z`, and the primal completeness
`Σ_h T_h = I` reduces the sum to `⟨ψ, Z ⊗ I ψ⟩`. -/
theorem sdp_complementary_slackness_sum_eq_dual_mass
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (hT_total : T.total = 1)
    (hcomp :
      ∀ h : Polynomial params,
        sdpComplementarySlacknessEquation params strategy T Z h) :
    (∑ h : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            (T.outcome h * averagedPointOperator params strategy h))) =
      ev strategy.state (leftTensor (ι₂ := ι) Z) := by
  calc
    (∑ h : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            (T.outcome h * averagedPointOperator params strategy h)))
        =
      ∑ h : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι) (T.outcome h * Z)) := by
        refine Finset.sum_congr rfl ?_
        intro h _
        rw [← hcomp h]
    _ =
      ev strategy.state
        (leftTensor (ι₂ := ι)
          (∑ h : Polynomial params, T.outcome h * Z)) := by
        rw [← ev_finset_sum]
        congr 1
        rw [leftTensor_finset_sum]
    _ =
      ev strategy.state
        (leftTensor (ι₂ := ι) (T.total * Z)) := by
        rw [← Finset.sum_mul, T.sum_eq_total]
    _ = ev strategy.state (leftTensor (ι₂ := ι) Z) := by
        rw [hT_total, Matrix.one_mul]
end MIPStarRE.LDT.SelfImprovement

end

end LIDT


