-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_ScalarChain
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_ScalarChain
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:13:32.679262+00:00
-- url     : https://prove2.me/theorems/92cd65fd-8ab8-483b-8b7b-9c475914cb57
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / AddInUDiagonalAndDefs / ScalarChain
-- statement:
--   This bundle defines the selected and averaged scalar Cauchy-Schwarz chains for add-in-$u$. The four transitions move right point projectors to the left and then replace one evaluation point by another, with endpoint identities connecting the chain to matching-mass quantities.
--
--   Principal definitions:
--   - `addInUSelectedCSChainQ0` through `addInUSelectedCSChainQ4`: The selected endpoint and its four successive transport stages.
--   - `addInUCSChainQ0` through `addInUCSChainQ4`: The corresponding averaged chain with the sandwiched family.
--   - `addInUSelectedCSChainQ0_eq_leftQuantity_averagedSandwiched`: Identifies the selected left endpoint with the averaged-sandwich left quantity.
--   - `addInUSelectedCSChainQ4_eq_rightQuantity`: Identifies the selected right endpoint with the right quantity.
--   - `add_in_u_cs_chain_q0_eq_match_mass`: Rewrites the averaged left endpoint as diagonal matching mass.
--   - `add_in_u_cs_chain_q4_eq_simplified_rhs`: Collapses the raw right endpoint using projectivity.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUDiagonalAndDefs/ScalarChain.lean#L31-L495

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUDiagonalAndDefs/ScalarChain.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_DataProcessing
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Selection
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
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Scalar chain for the diagonal add-in-u transfer

This module contains the selected and diagonal Q₀--Q₄ scalar chains used for the
projection-simplified diagonal add-in-`u` transfer, together with the endpoint
identifications needed by the helper strong-self-consistency proof.

## References

- `references/ldt-paper/self_improvement.tex` lines 247--252
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
/-! ### Scalar chain for the projection-simplified diagonal add-in-u transfer -/

/-- Strong self-consistency for the point measurement, pulled back to the second
coordinate of the independent `(u, v)` average used by the add-in-`u` scalar
chain.

This is the distributional self-consistency input for the `A^v_{h(v)}` moves in
`self_improvement.tex`, lines 255--297: the point measurement sampled at `v`
has the same `2δ` left/right state-dependent distance after the product average
over `(u, v)`. -/
lemma addInU_pointMeasurement_snd_selfConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (delta : Error)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    SDDRel strategy.state (uniformDistribution (Point params × Point params))
      (IdxSubMeas.liftLeft
        (fun uv : Point params × Point params =>
          (strategy.pointMeasurement uv.2).toSubMeas))
      (IdxSubMeas.liftRight
        (fun uv : Point params × Point params =>
          (strategy.pointMeasurement uv.2).toSubMeas))
      (2 * delta) := by
  classical
  have hssc_pair :
      BipartiteSSCRel strategy.state
        (uniformDistribution (Point params × Point params))
        (fun uv : Point params × Point params =>
          (strategy.pointMeasurement uv.2).toSubMeas)
        delta := by
    rcases hssc with ⟨hssc⟩
    constructor
    calc
      avgOver (uniformDistribution (Point params × Point params))
          (fun uv : Point params × Point params =>
            qBipartiteSSCDefect strategy.state
              ((strategy.pointMeasurement uv.2).toSubMeas))
        =
          avgOver (uniformDistribution (Point params))
            (fun v : Point params =>
              qBipartiteSSCDefect strategy.state
                ((strategy.pointMeasurement v).toSubMeas)) := by
            exact avgOver_uniform_snd
              (α := Point params) (β := Point params)
              (fun v : Point params =>
                qBipartiteSSCDefect strategy.state
                  ((strategy.pointMeasurement v).toSubMeas))
      _ ≤ delta := by
            simpa [bipartiteSSCError, IdxProjMeas.toIdxSubMeas] using hssc
  have hraw :=
    Preliminaries.twoNotionsOfSelfConsistencyAfterEvaluation
      strategy.state strategy.permInvState
      (uniformDistribution (Point params × Point params))
      (fun uv : Point params × Point params =>
        (strategy.pointMeasurement uv.2).toSubMeas)
      delta
      (fun _uv (a : Fq params) => a)
      hssc_pair
  simpa using hraw

/-- The grouped tensor mass over a fiber `h(v)=a` is a contraction.

This is the submeasurement bound used inside the first Cauchy--Schwarz square
root in `self_improvement.tex`, lines 267--272: after grouping by the value
`a = h(v)`, the selected operators
`H^u_h ⊗ T_h` are dominated by the total mass of the sandwiched polynomial
submeasurement at `u`, hence by `I`. -/
lemma addInU_filtered_sandwiched_tensor_sum_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (u v : Point params) (a : Fq params) :
    ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h v = a),
        opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
          (T.outcome h) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  exact SubMeas.opTensor_sum_filter_le_one
    (sandwichedPolynomialSubMeasAt params strategy T u)
    T
    (fun h : Polynomial params => h v = a)

/-! ### Selection-parametrized add-in-u scalar chain

The paper proves `lem:add-in-u` for an arbitrary outcome family `M` and
selection `S_u ⊆ 𝒪 × polyfunc`.  The diagonal helper strong-self-consistency
application below is one specialization of this statement.  The following
definitions record the same five scalar quantities before specializing to the
diagonal case, so that the off-diagonal point-consistency selection can reuse
the Cauchy--Schwarz chain rather than restating the transfer hypothesis. -/

/-- The selected-chain left endpoint `Q₀`.

For a selected pair `(o, h) ∈ S_u`, this is the expectation of
`M^u_o ⊗ H^v_h`, where `H^v_h = A^v_{h(v)} T_h A^v_{h(v)}`. -/
noncomputable def addInUSelectedCSChainQ0
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ ah ∈ addInUSelectionPairs params S uv.1,
      ev strategy.state
        (opTensor ((M uv.1).outcome ah.1)
          ((sandwichedPolynomialSubMeasAt params strategy T uv.2).outcome ah.2)))

/-- The selected-chain scalar `Q₁`, after moving the right point projector
`A^v_{h(v)}` to the left tensor factor once. -/
noncomputable def addInUSelectedCSChainQ1
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ ah ∈ addInUSelectionPairs params S uv.1,
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
      ev strategy.state
        (opTensor (Av * (M uv.1).outcome ah.1) (T.outcome ah.2 * Av)))

/-- The selected-chain scalar `Q₂`, after moving both right point projectors to
the left tensor factor. -/
noncomputable def addInUSelectedCSChainQ2
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ ah ∈ addInUSelectionPairs params S uv.1,
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
      ev strategy.state
        (opTensor (Av * (M uv.1).outcome ah.1 * Av) (T.outcome ah.2)))

/-- The selected-chain scalar `Q₃`, after replacing the first point projector
at `v` by the corresponding point projector at `u`. -/
noncomputable def addInUSelectedCSChainQ3
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ ah ∈ addInUSelectionPairs params S uv.1,
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
      ev strategy.state
        (opTensor (Au * (M uv.1).outcome ah.1 * Av) (T.outcome ah.2)))

/-- The selected-chain scalar `Q₄`, after replacing both point projectors at
`v` by the corresponding point projectors at `u`. -/
noncomputable def addInUSelectedCSChainQ4
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ ah ∈ addInUSelectionPairs params S uv.1,
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
      ev strategy.state
        (opTensor (Au * (M uv.1).outcome ah.1 * Au) (T.outcome ah.2)))

/-- The selected-chain endpoint `Q₀` is the generic add-in-u left quantity when
the second measurement is the averaged sandwiched polynomial submeasurement. -/
theorem addInUSelectedCSChainQ0_eq_leftQuantity_averagedSandwiched
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    addInULeftQuantity params strategy M
        (averagedSandwichedPolynomialSubMeas params strategy T)
        S =
      addInUSelectedCSChainQ0 params strategy M T S := by
  classical
  change avgOver (uniformDistribution (Point params)) (fun u =>
      ev strategy.state
        (addInULeftOperatorAtPoint params strategy M
          (averagedSandwichedPolynomialSubMeas params strategy T) S u)) =
    addInUSelectedCSChainQ0 params strategy M T S
  unfold addInULeftOperatorAtPoint addInUSelectedCSChainQ0
  rw [avgOver_uniform_prod (α := Point params) (β := Point params)
    (f := fun u v =>
      ∑ ah ∈ addInUSelectionPairs params S u,
        ev strategy.state
          (opTensor ((M u).outcome ah.1)
            ((sandwichedPolynomialSubMeasAt params strategy T v).outcome ah.2)))]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  calc
    ev strategy.state
        (∑ ah ∈ addInUSelectionPairs params S u,
          opTensor ((M u).outcome ah.1)
            ((averagedSandwichedPolynomialSubMeas params strategy T).outcome ah.2))
        =
      ∑ ah ∈ addInUSelectionPairs params S u,
        ev strategy.state
          (opTensor ((M u).outcome ah.1)
            ((averagedSandwichedPolynomialSubMeas params strategy T).outcome ah.2)) := by
        rw [ev_finset_sum]
    _ =
      ∑ ah ∈ addInUSelectionPairs params S u,
        avgOver (uniformDistribution (Point params)) (fun v =>
          ev strategy.state
            (opTensor ((M u).outcome ah.1)
              ((sandwichedPolynomialSubMeasAt params strategy T v).outcome ah.2))) := by
        refine Finset.sum_congr rfl ?_
        intro ah _
        simpa [averagedSandwichedPolynomialSubMeas, sandwichedPolynomialSubMeasAt] using
          ev_opTensor_averageOperatorOverDistribution_right strategy.state
            (uniformDistribution (Point params))
            ((M u).outcome ah.1)
            (fun v => (sandwichedPolynomialSubMeasAt params strategy T v).outcome ah.2)
    _ =
      avgOver (uniformDistribution (Point params)) (fun v =>
        ∑ ah ∈ addInUSelectionPairs params S u,
          ev strategy.state
            (opTensor ((M u).outcome ah.1)
              ((sandwichedPolynomialSubMeasAt params strategy T v).outcome ah.2))) := by
        exact (MIPStarRE.LDT.avgOver_finset_sum (uniformDistribution (Point params))
          (addInUSelectionPairs params S u)
          (fun v ah =>
            ev strategy.state
              (opTensor ((M u).outcome ah.1)
                ((sandwichedPolynomialSubMeasAt params strategy T v).outcome ah.2)))).symm

/-- The selected-chain endpoint `Q₄` is the generic add-in-u right quantity. -/
theorem addInUSelectedCSChainQ4_eq_rightQuantity
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    addInURightQuantity params strategy M T S =
      addInUSelectedCSChainQ4 params strategy M T S := by
  classical
  change avgOver (uniformDistribution (Point params)) (fun u =>
      ev strategy.state
        (addInURightOperatorAtPoint params strategy M T S u)) =
    addInUSelectedCSChainQ4 params strategy M T S
  unfold addInURightOperatorAtPoint addInUSelectedCSChainQ4
  rw [avgOver_uniform_prod (α := Point params) (β := Point params)
    (f := fun u _ =>
      ∑ ah ∈ addInUSelectionPairs params S u,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 u
        ev strategy.state
          (opTensor (Au * (M u).outcome ah.1 * Au) (T.outcome ah.2)))]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  rw [ev_finset_sum]
  exact (avgOver_uniform_const
    (∑ ah ∈ addInUSelectionPairs params S u,
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 u
      ev strategy.state
        (opTensor (Au * (M u).outcome ah.1 * Au) (T.outcome ah.2)))).symm

/-- The expanded left endpoint `Q₀` of the four-step scalar chain in
`self_improvement.tex`, lines 247--252, after setting `M^u = H^u` and averaging
the second tensor factor `H = E_v H^v`. -/
noncomputable def addInUCSChainQ0
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : Polynomial params,
      ev strategy.state
        (opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
          ((sandwichedPolynomialSubMeasAt params strategy T uv.2).outcome h)))

/-- The scalar `Q₁` obtained from `Q₀` by moving the right point projection
`A^v_{h(v)}` to the left tensor factor; this is the target of
`eq:move-one`. -/
noncomputable def addInUCSChainQ1
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : Polynomial params,
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      ev strategy.state
        (opTensor (Av * (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
          (T.outcome h * Av)))

/-- The scalar `Q₂` obtained from `Q₁` by moving the second right point
projection to the left tensor factor; this is the target of `eq:move-another`. -/
noncomputable def addInUCSChainQ2
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : Polynomial params,
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      ev strategy.state
        (opTensor (Av * (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h *
            Av)
          (T.outcome h)))

/-- The scalar `Q₃` obtained from `Q₂` by replacing the first point projection
`A^v_{h(v)}` by `A^u_{h(u)}`; this is the target of `eq:change-one`. -/
noncomputable def addInUCSChainQ3
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : Polynomial params,
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      ev strategy.state
        (opTensor (Au * (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h *
            Av)
          (T.outcome h)))

/-- The scalar `Q₄` obtained from `Q₃` by replacing the second point projection
`A^v_{h(v)}` by `A^u_{h(u)}`; after the projection collapse, this is the
projection-simplified right endpoint of the diagonal add-in-u transfer. -/
noncomputable def addInUCSChainQ4
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : Polynomial params,
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      ev strategy.state
        (opTensor (Au * (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h *
            Au)
          (T.outcome h)))

/-- The expanded chain endpoint `Q₀` is the existing diagonal match-mass left
side used by `selfConsistencyDiagonalAddInU_of_simplifiedTransfer`. -/
lemma add_in_u_cs_chain_q0_eq_match_mass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) =
      addInUCSChainQ0 params strategy T := by
  classical
  calc
    qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T)
        =
      ∑ h : Polynomial params,
        avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (uniformDistribution (Point params)) (fun v =>
            ev strategy.state
              (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                ((sandwichedPolynomialSubMeasAt params strategy T v).outcome h)))) := by
        unfold qBipartiteMatchMass averagedSandwichedPolynomialSubMeas
        refine Finset.sum_congr rfl ?_
        intro h _
        rw [ev_opTensor_averageOperatorOverDistribution_left]
        refine avgOver_congr _ _ _ ?_
        intro u
        simpa [sandwichedPolynomialSubMeasAt] using
          ev_opTensor_averageOperatorOverDistribution_right strategy.state
            (uniformDistribution (Point params))
            ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
            (fun v => (sandwichedPolynomialSubMeasAt params strategy T v).outcome h)
    _ = addInUCSChainQ0 params strategy T := by
        symm
        unfold addInUCSChainQ0
        rw [avgOver_uniform_prod (α := Point params) (β := Point params)
          (f := fun u v =>
            ∑ h : Polynomial params,
              ev strategy.state
                (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                  ((sandwichedPolynomialSubMeasAt params strategy T v).outcome h)))]
        calc
          avgOver (uniformDistribution (Point params)) (fun u =>
              avgOver (uniformDistribution (Point params)) (fun v =>
                ∑ h : Polynomial params,
                  ev strategy.state
                    (opTensor
                      ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                      ((sandwichedPolynomialSubMeasAt params strategy T v).outcome h))))
              =
            avgOver (uniformDistribution (Point params)) (fun u =>
              ∑ h : Polynomial params,
                avgOver (uniformDistribution (Point params)) (fun v =>
                  ev strategy.state
                    (opTensor
                      ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                      ((sandwichedPolynomialSubMeasAt params strategy T v).outcome h)))) := by
              refine avgOver_congr _ _ _ ?_
              intro u
              rw [avgOver_sum]
          _ =
            ∑ h : Polynomial params,
              avgOver (uniformDistribution (Point params)) (fun u =>
                avgOver (uniformDistribution (Point params)) (fun v =>
                  ev strategy.state
                    (opTensor
                      ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                      ((sandwichedPolynomialSubMeasAt params strategy T v).outcome h)))) := by
              rw [avgOver_sum]

/-- The raw chain endpoint `Q₄` collapses to the projection-simplified scalar
right side used by `selfConsistencyDiagonalAddInU_of_simplifiedTransfer`. -/
lemma add_in_u_cs_chain_q4_eq_simplified_rhs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUCSChainQ4 params strategy T =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h))) := by
  classical
  calc
    addInUCSChainQ4 params strategy T =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
              (T.outcome h))) := by
        unfold addInUCSChainQ4
        refine avgOver_congr _ _ _ ?_
        intro uv
        refine Finset.sum_congr rfl ?_
        intro h _
        have hproj :
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 *
              pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 =
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 := by
          simpa [pointConditionedOutcomeOperatorAtPolynomial] using
            (strategy.pointMeasurement uv.1).proj (h uv.1)
        have hcollapse :
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 *
                (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 =
              (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h := by
          change
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 *
                (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 *
                  T.outcome h *
                  pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1) *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 =
              pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 *
                T.outcome h *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
          exact proj_outer_sandwich_eq _ _ hproj
        simp [hcollapse]
    _ =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h))) := by
        exact avgOver_uniform_fst (α := Point params) (β := Point params)
          (fun u =>
            ∑ h : Polynomial params,
              ev strategy.state
                (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                  (T.outcome h)))


end MIPStarRE.LDT.SelfImprovement

end

end LIDT


