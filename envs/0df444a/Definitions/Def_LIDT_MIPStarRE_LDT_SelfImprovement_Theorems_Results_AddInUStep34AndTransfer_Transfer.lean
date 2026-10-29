-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Transfer
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Transfer
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:34:17.254254+00:00
-- url     : https://prove2.me/theorems/8b440bf4-7c3b-4568-a2b6-a558a8cb2068
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / AddInUStep34AndTransfer / Transfer
-- statement:
--   This bundle assembles the Step 3 and Step 4 add-in-u transfer estimates and their error reductions.
--
--   Principal definitions:
--   - `add_in_u_simplified_transfer_of_cs_chain`: transfers the simplified Cauchy-Schwarz chain.
--   - `add_in_u_selected_transfer_of_cs_chain`: transfers the selected chain.
--   - `two_sqrt_two_mul_add_two_sqrt_le_four_sqrt`: absorbs the square-root constants.
--   - `two_mul_delta_le_selfImprovementVarianceError`: relates the doubled consistency error to the variance error.
--   - `two_sqrt_two_delta_add_two_sqrt_selfImprovementVarianceError_le_addInUError`: bounds the combined add-in-u error.
--   - `add_in_u_simplified_transfer_of_cs_chain_sqrt_form`: gives the square-root form of the transfer.
--   - `selfConsistencyDiagonalAddInU_of_simplifiedTransfer`: derives the diagonal self-consistency consequence.
--   - `helper_mass_sub_release_eq_polynomial_off_diagonal`: identifies the residual mass difference.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Transfer.lean#L32-L522

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Transfer.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Foundations
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Matrix
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Results
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_AlgebraicIdentity
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Averaging
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_CollisionExpansion
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_MainTheorems
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_PolynomialSumBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransportSum
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Point
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_PointLine
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Utilities
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_SumForm
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
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
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_CanonicalPrimal
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Saturated
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Basic
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Separation
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Witness
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Residual
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_ScalarChain
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Selection
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Raw
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Selected
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Factored
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Selected
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Variance
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_CommonHelpers
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Bracketed
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_FiberBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_InputSdp
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Linearized
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SdpMatrixBridge
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Final
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Helper
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteConicDuality
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
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Add-in-u scalar transfer and off-diagonal expansion

Assembly of the four add-in-u scalar moves, the elementary arithmetic
absorption from the paper, and the residual off-diagonal expansion used by the
helper strong self-consistency argument.

## References

- `references/ldt-paper/self_improvement.tex` lines 341--343
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

/-- Assemble the projection-simplified scalar transfer from the four scalar
chain moves. The analytic work remains exactly the four bounds
`Q₀ ≈ Q₁`, `Q₁ ≈ Q₂`, `Q₂ ≈ Q₃`, and `Q₃ ≈ Q₄`, plus the final arithmetic
absorption into `addInUError`. -/
lemma add_in_u_simplified_transfer_of_cs_chain
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (η01 η12 η23 η34 : Error)
    (h01 :
      |addInUCSChainQ0 params strategy T - addInUCSChainQ1 params strategy T| ≤ η01)
    (h12 :
      |addInUCSChainQ1 params strategy T - addInUCSChainQ2 params strategy T| ≤ η12)
    (h23 :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤ η23)
    (h34 :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤ η34)
    (hsum : η01 + η12 + η23 + η34 ≤ addInUError params eps delta) :
    |qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) -
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h)))| ≤ addInUError params eps delta := by
  let Q0 := addInUCSChainQ0 params strategy T
  let Q1 := addInUCSChainQ1 params strategy T
  let Q2 := addInUCSChainQ2 params strategy T
  let Q3 := addInUCSChainQ3 params strategy T
  let Q4 := addInUCSChainQ4 params strategy T
  have htriangle :
      |Q0 - Q4| ≤ |Q0 - Q1| + |Q1 - Q2| + |Q2 - Q3| + |Q3 - Q4| := by
    calc
      |Q0 - Q4| = |(Q0 - Q1) + (Q1 - Q2) + (Q2 - Q3) + (Q3 - Q4)| := by
        ring_nf
      _ ≤ |Q0 - Q1| + |Q1 - Q2| + |Q2 - Q3| + |Q3 - Q4| := by
        have h1 := abs_add_le ((Q0 - Q1) + (Q1 - Q2) + (Q2 - Q3)) (Q3 - Q4)
        have h2 := abs_add_le ((Q0 - Q1) + (Q1 - Q2)) (Q2 - Q3)
        have h3 := abs_add_le (Q0 - Q1) (Q1 - Q2)
        linarith
  calc
    |qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) -
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h)))|
        = |Q0 - Q4| := by
          rw [add_in_u_cs_chain_q0_eq_match_mass,
            ← add_in_u_cs_chain_q4_eq_simplified_rhs]
    _ ≤ |Q0 - Q1| + |Q1 - Q2| + |Q2 - Q3| + |Q3 - Q4| := htriangle
    _ ≤ η01 + η12 + η23 + η34 := by
      linarith
    _ ≤ addInUError params eps delta := hsum

/-- Assemble the selected add-in-`u` scalar transfer from the four selected
scalar chain moves.

This is the selection-parametrized counterpart of
`add_in_u_simplified_transfer_of_cs_chain`.  The endpoints are the theorem-side
generic add-in-u quantities rather than the diagonal match-mass and simplified
release quantities. -/
lemma add_in_u_selected_transfer_of_cs_chain
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (η01 η12 η23 η34 : Error)
    (h01 :
      |addInUSelectedCSChainQ0 params strategy M T S -
        addInUSelectedCSChainQ1 params strategy M T S| ≤ η01)
    (h12 :
      |addInUSelectedCSChainQ1 params strategy M T S -
        addInUSelectedCSChainQ2 params strategy M T S| ≤ η12)
    (h23 :
      |addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S| ≤ η23)
    (h34 :
      |addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ4 params strategy M T S| ≤ η34)
    (hsum : η01 + η12 + η23 + η34 ≤ addInUError params eps delta) :
    |addInULeftQuantity params strategy M
        (averagedSandwichedPolynomialSubMeas params strategy T) S -
      addInURightQuantity params strategy M T S| ≤ addInUError params eps delta := by
  let Q0 := addInUSelectedCSChainQ0 params strategy M T S
  let Q1 := addInUSelectedCSChainQ1 params strategy M T S
  let Q2 := addInUSelectedCSChainQ2 params strategy M T S
  let Q3 := addInUSelectedCSChainQ3 params strategy M T S
  let Q4 := addInUSelectedCSChainQ4 params strategy M T S
  have htriangle :
      |Q0 - Q4| ≤ |Q0 - Q1| + |Q1 - Q2| + |Q2 - Q3| + |Q3 - Q4| := by
    calc
      |Q0 - Q4| = |(Q0 - Q1) + (Q1 - Q2) + (Q2 - Q3) + (Q3 - Q4)| := by
        ring_nf
      _ ≤ |Q0 - Q1| + |Q1 - Q2| + |Q2 - Q3| + |Q3 - Q4| := by
        have h1 := abs_add_le ((Q0 - Q1) + (Q1 - Q2) + (Q2 - Q3)) (Q3 - Q4)
        have h2 := abs_add_le ((Q0 - Q1) + (Q1 - Q2)) (Q2 - Q3)
        have h3 := abs_add_le (Q0 - Q1) (Q1 - Q2)
        linarith
  calc
    |addInULeftQuantity params strategy M
        (averagedSandwichedPolynomialSubMeas params strategy T) S -
      addInURightQuantity params strategy M T S|
        = |Q0 - Q4| := by
          rw [addInUSelectedCSChainQ0_eq_leftQuantity_averagedSandwiched,
            addInUSelectedCSChainQ4_eq_rightQuantity]
    _ ≤ |Q0 - Q1| + |Q1 - Q2| + |Q2 - Q3| + |Q3 - Q4| := htriangle
    _ ≤ η01 + η12 + η23 + η34 := by
      linarith
    _ ≤ addInUError params eps delta := hsum

/-- Reusable numerical absorption: whenever `2 a ≤ b`, the four-term sum
`2 √(2 a) + 2 √b` collapses into `4 √b`. This is the schematic shape of the
paper's closing absorption step in the proof of `lem:add-in-u`
(`self_improvement.tex:341--342`). -/
lemma two_sqrt_two_mul_add_two_sqrt_le_four_sqrt
    {a b : Error} (hab : 2 * a ≤ b) :
    2 * Real.sqrt (2 * a) + 2 * Real.sqrt b ≤ 4 * Real.sqrt b := by
  have hsqrt : Real.sqrt (2 * a) ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
  linarith

/-- Paper-side comparison `2 δ ≤ ζ_variance` from the closing line of the proof
of `lem:add-in-u` (`self_improvement.tex:342`,
`blueprint/src/chapter/ch07_self_improvement.tex:494`). Since
`ζ_variance = 24 m (ε + δ + m d / q)` and `m ≥ 1`, the term `24 m δ` already
exceeds `2 δ` whenever `eps, delta ≥ 0`. -/
lemma two_mul_delta_le_selfImprovementVarianceError
    (params : Parameters)
    [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    2 * delta ≤ selfImprovementVarianceError params eps delta := by
  have hm : (1 : Error) ≤ (params.m : Error) := by
    have hm_nat : (1 : ℕ) ≤ params.m := params.hm
    exact_mod_cast hm_nat
  have hm_nonneg : (0 : Error) ≤ (params.m : Error) := by linarith
  have hdq_nonneg : (0 : Error) ≤ ((params.d : Error) / (params.q : Error)) :=
    div_nonneg (by exact_mod_cast Nat.zero_le _) (le_of_lt params.q_cast_pos)
  rw [selfImprovementVarianceError_eq]
  calc
    2 * delta
        ≤ 24 * delta := by linarith
    _ = 24 * (1 : Error) * delta := by ring
    _ ≤ 24 * (params.m : Error) * delta := by
        have : (0 : Error) ≤ ((params.m : Error) - 1) * delta :=
          mul_nonneg (by linarith) hdelta
        nlinarith
    _ ≤ 24 * (params.m : Error) *
          (eps + delta +
            ((params.m : Error) * ((params.d : Error) / (params.q : Error)))) := by
        have h24m : (0 : Error) ≤ 24 * (params.m : Error) := by nlinarith
        have hmdq_nonneg :
            (0 : Error) ≤ (params.m : Error) *
              ((params.d : Error) / (params.q : Error)) :=
          mul_nonneg hm_nonneg hdq_nonneg
        nlinarith [mul_nonneg h24m heps, mul_nonneg h24m hmdq_nonneg]

/-- Arithmetic absorption used by `add_in_u_simplified_transfer_of_cs_chain`:
the four step-bound sum `2 √(2 δ) + 2 √(ζ_variance)` is dominated by
`addInUError = 4 ζ_variance^{1/2}` (`self_improvement.tex:341--342`,
`blueprint/src/chapter/ch07_self_improvement.tex:492--494`). This is the
arithmetic side condition that lets the step bounds with the paper-faithful
`Real.sqrt` shape (companion issues #1089 and #1090) discharge the `hsum`
hypothesis of `add_in_u_simplified_transfer_of_cs_chain`. -/
lemma two_sqrt_two_delta_add_two_sqrt_selfImprovementVarianceError_le_addInUError
    (params : Parameters)
    [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    2 * Real.sqrt (2 * delta) +
        2 * Real.sqrt (selfImprovementVarianceError params eps delta) ≤
      addInUError params eps delta := by
  have hbase :=
    two_sqrt_two_mul_add_two_sqrt_le_four_sqrt
      (two_mul_delta_le_selfImprovementVarianceError params eps delta heps hdelta)
  simpa [addInUError, Real.sqrt_eq_rpow] using hbase

/-- Wrapper composing `add_in_u_simplified_transfer_of_cs_chain` with the
arithmetic absorption: when the four chain step bounds have the paper-faithful
shapes `√(2 δ)`, `√(2 δ)`, `√(ζ_variance)`, `√(ζ_variance)`, the
projection-simplified transfer holds with the displayed
`addInUError = 4 ζ_variance^{1/2}`. The four hypotheses match the targets of
companion issues #1089 (Step 1/2) and #1083/#1088/#1090 (Step 3/4). -/
lemma add_in_u_simplified_transfer_of_cs_chain_sqrt_form
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (T : SubMeas (Polynomial params) ι)
    (h01 :
      |addInUCSChainQ0 params strategy T - addInUCSChainQ1 params strategy T| ≤
        Real.sqrt (2 * delta))
    (h12 :
      |addInUCSChainQ1 params strategy T - addInUCSChainQ2 params strategy T| ≤
        Real.sqrt (2 * delta))
    (h23 :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta))
    (h34 :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta)) :
    |qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) -
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h)))| ≤ addInUError params eps delta := by
  have hsum :
      Real.sqrt (2 * delta) + Real.sqrt (2 * delta) +
          Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (selfImprovementVarianceError params eps delta) ≤
        addInUError params eps delta := by
    have htwo :=
      two_sqrt_two_delta_add_two_sqrt_selfImprovementVarianceError_le_addInUError
        params eps delta heps hdelta
    linarith
  exact add_in_u_simplified_transfer_of_cs_chain params strategy eps delta T
    (Real.sqrt (2 * delta)) (Real.sqrt (2 * delta))
    (Real.sqrt (selfImprovementVarianceError params eps delta))
    (Real.sqrt (selfImprovementVarianceError params eps delta))
    h01 h12 h23 h34 hsum

-- This lemma combines the two local-variance Cauchy--Schwarz replacements
-- with the scalar add-in-u transfer inequality.




/-- Specialization of `selfConsistencyDiagonalAddInU_of_transfer` to the
projection-simplified scalar transfer hypothesis.

Compared to `selfConsistencyDiagonalAddInU_of_transfer`, the hypothesis is
stated against the cleaner right-hand side `E_u Σ_h ⟨ψ, H^u_h ⊗ T_h ψ⟩`
obtained after collapsing the outer projection factors of
`eq:release-the-kraken` via `proj_outer_sandwich_eq`. The conclusion is
identical and can therefore feed the same diagonal helper-SSC application;
the simplification reduces the Cauchy--Schwarz/global-variance comparison
(`self_improvement.tex:247--343`) to a transfer in the simpler shape. -/
lemma selfConsistencyDiagonalAddInU_of_simplifiedTransfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (htransfer :
      |qBipartiteMatchMass strategy.state
          (averagedSandwichedPolynomialSubMeas params strategy T)
          (averagedSandwichedPolynomialSubMeas params strategy T) -
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h : Polynomial params,
            ev strategy.state
              (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                (T.outcome h)))| ≤ addInUError params eps delta) :
    |qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) -
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
          ev strategy.state
            (opTensor (Au * (sandwichedPolynomialSubMeasAt params strategy T u).outcome h * Au)
              (T.outcome h)))| ≤ addInUError params eps delta := by
  -- Both RHS shapes are equal to the underlying `addInURightQuantity`, so the
  -- full paper RHS (`eq:release-the-kraken`) equals the projection-collapsed
  -- RHS used in `htransfer`.
  have hRHS_eq :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
          ev strategy.state
            (opTensor (Au * (sandwichedPolynomialSubMeasAt params strategy T u).outcome h * Au)
              (T.outcome h)))
        = avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h : Polynomial params,
            ev strategy.state
              (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                (T.outcome h))) :=
    (addInURightQuantity_selfConsistencySelection_eq_release
        params strategy T).symm.trans
      (addInURightQuantity_selfConsistencySelection_eq_simplified
        params strategy T)
  rw [hRHS_eq]
  exact htransfer

/-- Exact residual-side expansion for the helper strong self-consistency proof.

For the averaged helper `Hhat = E_u H^u` produced from the primal measurement
`T`, the difference between the helper left mass and the released diagonal
add-in-`u` right-hand side is precisely the contribution of the off-diagonal
polynomial pairs `(h',h)` with `h' ≠ h`:

`E_u \sum_h \sum_{h'≠h} ⟨ψ, H^u_{h'} ⊗ T_h ψ⟩`.

This is the exact algebraic opening of the Lean residual
`helper_left_mass - release-the-kraken`; the later Cauchy--Schwarz,
Schwartz--Zippel, point-consistency, and self-consistency estimates are the
remaining inequalities that bound this off-diagonal expression in the proof of
`item:self-improvement-self`.

This Lean identity expands the helper left mass minus the released diagonal
right-hand side directly.  It therefore differs from the paper's intermediate
``threw-in-`h'`'' expression, where the off-diagonal helper operator is still
sandwiched by `A^u_{h(u)}`. -/
theorem helper_mass_sub_release_eq_polynomial_off_diagonal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι) :
    subMeasMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas).liftLeft -
      addInURightQuantity params strategy
        (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
        T.toSubMeas
        (selfConsistencyAddInUSelection params) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
            ev strategy.state
              (opTensor
                ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
                (T.toSubMeas.outcome h))) := by
  classical
  have hmass :
      subMeasMass strategy.state
          (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas).liftLeft =
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h' : Polynomial params,
            ∑ h : Polynomial params,
              ev strategy.state
                (opTensor
                  ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
                  (T.toSubMeas.outcome h))) := by
    have hmass0 :
        subMeasMass strategy.state
            (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas).liftLeft =
          avgOver (uniformDistribution (Point params)) (fun u =>
            ∑ h' : Polynomial params,
              ev strategy.state
                (leftTensor (ι₂ := ι)
                  (sandwichedPolynomialOutcomeOperatorAt
                    params strategy T.toSubMeas u h'))) := by
      simpa using helper_mass_eq_avg_pointwise_sandwich_sum
        params strategy T.toSubMeas
    rw [hmass0]
    refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
    intro u
    refine Finset.sum_congr rfl ?_
    intro h' _
    have hTsum :
        (∑ h : Polynomial params, T.toSubMeas.outcome h) =
          (1 : MIPStarRE.Quantum.Op ι) := by
      rw [T.toSubMeas.sum_eq_total, T.total_eq_one]
    calc
      ev strategy.state
          (leftTensor (ι₂ := ι)
            (sandwichedPolynomialOutcomeOperatorAt params strategy T.toSubMeas u h'))
          =
        ev strategy.state
          (opTensor
            ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
            (1 : MIPStarRE.Quantum.Op ι)) := by
          rfl
      _ =
        ev strategy.state
          (opTensor
            ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
            (∑ h : Polynomial params, T.toSubMeas.outcome h)) := by
          rw [hTsum]
      _ =
        ev strategy.state
          (∑ h : Polynomial params,
            opTensor
              ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
              (T.toSubMeas.outcome h)) := by
          rw [← opTensor_sum_right_univ]
      _ =
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor
              ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
              (T.toSubMeas.outcome h)) := by
          rw [ev_sum]
  have hrelease :
      addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
          T.toSubMeas
          (selfConsistencyAddInUSelection params) =
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h : Polynomial params,
            ev strategy.state
              (opTensor
                ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h)
                (T.toSubMeas.outcome h))) :=
    addInURightQuantity_selfConsistencySelection_eq_simplified
      params strategy T.toSubMeas
  rw [hmass, hrelease, ← avgOver_sub]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  have hswap :
      (∑ h' : Polynomial params,
          ∑ h : Polynomial params,
            ev strategy.state
              (opTensor
                ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
                (T.toSubMeas.outcome h))) =
        ∑ h : Polynomial params,
          ∑ h' : Polynomial params,
            ev strategy.state
              (opTensor
                ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
                (T.toSubMeas.outcome h)) := by
    rw [Finset.sum_comm]
  rw [hswap]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun h _ =>
    (Finset.sum_erase_eq_sub (s := Finset.univ) (a := h)
      (f := fun h' =>
        ev strategy.state
          (opTensor
            ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
            (T.toSubMeas.outcome h))) (Finset.mem_univ h)).symm

end MIPStarRE.LDT.SelfImprovement

end

end LIDT


