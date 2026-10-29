-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_CSSetup
-- name    : LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_CSSetup
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:39:32.080931+00:00
-- url     : https://prove2.me/theorems/76268abf-152e-47a2-9a4e-a5d58e2a9b9f
-- title:
--   LIDT definitions: LDT / Pasting / ComparisonLemmas / LdSandwichLineOnePoint / CSSetup
-- statement:
--   This bundle sets up the two Cauchy-Schwarz moves in the line-one-point sandwich comparison. It defines the linear consistency defect, the original, intermediate, and moved scalar sums, and the records containing the raw qSDD bound, contraction facts, and absolute-value route.
--
--   Principal definitions:
--   - `qBipartiteLinearConsDefect`: The total-minus-matching defect before taking its nonnegative part.
--   - `ldSandwichLineOnePoint_prefix_sourceOutcomeSum`: The expanded scalar for the original prefix order.
--   - `ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum`: The intermediate scalar after the first Cauchy-Schwarz move.
--   - `ldSandwichLineOnePoint_prefix_movedOutcomeSum`: The scalar after the second move and prefix reordering.
--   - `LdSandwichLineOnePointOutcomeSumCSRoute`: The one-sided route relating the three scalar sums.
--   - `LdSandwichLineOnePointOutcomeSumCSAbsBounds`: The two absolute-value bounds.
--   - `LdSandwichLineOnePointCSFacts`: The raw qSDD, contraction, and regrouping facts needed by both moves.
--   - `LdSandwichLineOnePointAdjointRawCoreBound`: The adjoint-oriented raw squared-distance bound used as input.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/CSSetup.lean#L27-L697

-- Generated from MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/CSSetup.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_HEvalTransport
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_MainChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Y
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_BackChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Chain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_FlatChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Lifting
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_Endpoint
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_EndpointEquivs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_PrefixMoved
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Core_LdGbcon
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_ScalarTerms
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_Split
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Centers
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Terms
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
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

open scoped _root_.Matrix

namespace LIDT

namespace MIPStarRE.LDT
end MIPStarRE.LDT
namespace MIPStarRE.LDT.Commutativity
end MIPStarRE.LDT.Commutativity
namespace MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace MIPStarRE.LDT.CommutativityPoints
end MIPStarRE.LDT.CommutativityPoints
namespace MIPStarRE.LDT.Pasting
end MIPStarRE.LDT.Pasting
namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 12 pasting: line one-point transport — Cauchy-Schwarz setup

Internal helper module; part of the file-split for `#1127`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The linear (pre-`max`) form of the bipartite consistency defect.

Internal helper for the `LdSandwichLineOnePoint` Cauchy--Schwarz setup;
exposed for a future file-split (`#1127`). -/
noncomputable def qBipartiteLinearConsDefect {Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas Outcome ιA) (B : SubMeas Outcome ιB) : Error :=
  ev ψ (opTensor A.total B.total) - qBipartiteMatchMass ψ A B







/-- The original expanded off-diagonal scalar in `ld-pasting.tex:960--963`.

This is the source side after deleting extraneous tail coordinates and expanding
the linear consistency defect as `Σ_a ⟨ψ|A_a ⊗ (I-B_a)|ψ⟩`. -/
noncomputable def ldSandwichLineOnePoint_prefix_sourceOutcomeSum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ a : Fq params,
      ev strategy.state
        (opTensor
          (((ldSandwichLineOnePointPrefixOriginalFamily params family hi) q).outcome
            (some a))
          (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
            (some a))))

/-- The intermediate scalar after the first Cauchy--Schwarz move
`ld-pasting.tex:964--986` (`eq:gonna-need-a-bigger-cauchy-schwarz`).

For an original-order prefix outcome `gs`, `orderedHalf` is
`G^{x_<i}_{g_<i} G^{x_i}_{g_i}` while `rotatedHalf` is
`G^{x_i}_{g_i} G^{x_<i}_{g_<i}`.  The first CS move replaces only the left half
of the sandwich, leaving `orderedHalf†` on the right. -/
noncomputable def ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1),
      match Option.map (fun g : Polynomial params => g q.1)
          (gs ⟨i, Nat.lt_succ_self i⟩) with
      | none => 0
      | some a =>
          let orderedHalf := gHatHalfProductOutcomeOperator params family (i + 1)
            (fun j => q.2 ⟨j.1, by omega⟩) gs
          let rotatedHalf := gHatHalfProductOutcomeOperator params family (i + 1)
            ((pointTupleLastFrontEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))
            ((gHatTupleOutcomeLastFrontEquiv params i) gs)
          ev strategy.state
            (opTensor (rotatedHalf * orderedHalfᴴ)
              (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
                (some a))))

/-- The target expanded off-diagonal scalar after the two CS moves.

This is the moved-prefix side.  The separate endpoint/prefix-completeness
collapse to `ldGbcon` is the already-proved
`ldSandwichLineOnePointPrefixMoved_eq_endpoint`, corresponding to
`ld-pasting.tex:1011--1024`. -/
noncomputable def ldSandwichLineOnePoint_prefix_movedOutcomeSum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ a : Fq params,
      ev strategy.state
        (opTensor
          (((ldSandwichLineOnePointPrefixMovedFamily params family hi) q).outcome
            (some a))
          (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
            (some a))))

/-- Paper-faithful split of the remaining off-diagonal CS route.

The fields isolate the two uses of `Preliminaries.closenessOfIP` /
`Preliminaries.closenessOfIPAdjoint` in `ld-pasting.tex:964--1010`.  The endpoint
collapse after these fields is already packaged by
`ldSandwichLineOnePointPrefixMoved_eq_endpoint` (`ld-pasting.tex:1011--1024`). -/
structure LdSandwichLineOnePointOutcomeSumCSRoute
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) : Prop where
  /-- First CS move, paper lines `964--986` and label
  `eq:gonna-need-a-bigger-cauchy-schwarz`: move the selected `G` to the left of
  the prefix in the left half of the sandwich. -/
  firstCauchySchwarz :
    ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy family hi ≤
      ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi +
        Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1))
  /-- Second CS move, paper lines `987--1010` and label `eq:even-bigger-CS`:
  move the selected `G` through the adjoint/right half, reaching the moved-prefix
  scalar. -/
  secondCauchySchwarz :
    ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi ≤
      ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi +
        Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1))

/-- Absolute-value form of the two off-diagonal Cauchy--Schwarz moves.

This is the direct output shape of `Preliminaries.closenessOfIPAdjoint` and
`Preliminaries.closenessOfIP`: each field compares the two adjacent scalar
averages from `ld-pasting.tex:964--1010` with error `√ν₄`.  The one-sided route
used downstream is only an arithmetic consequence of these absolute-value
bounds. -/
structure LdSandwichLineOnePointOutcomeSumCSAbsBounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) : Prop where
  /-- First CS move in the exact absolute-value form of `prop:closeness-of-ip`,
  paper lines `964--986` and label `eq:gonna-need-a-bigger-cauchy-schwarz`. -/
  firstAbs :
    |ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy family hi -
      ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi| ≤
      Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1))
  /-- Second CS move in the exact absolute-value form of `prop:closeness-of-ip`,
  paper lines `987--1010` and label `eq:even-bigger-CS`. -/
  secondAbs :
    |ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi -
      ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi| ≤
      Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1))

/-- Ordered half-product appearing in the line-one-point CS step. -/
noncomputable def ldSandwichLineOnePointCS_orderedHalf
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) : MIPStarRE.Quantum.Op ι :=
  gHatHalfProductOutcomeOperator params family (i + 1)
    (fun j => q.2 ⟨j.1, by omega⟩) gs

/-- Rotated half-product appearing after moving the selected slice to the front. -/
noncomputable def ldSandwichLineOnePointCS_rotatedHalf
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) : MIPStarRE.Quantum.Op ι :=
  gHatHalfProductOutcomeOperator params family (i + 1)
    ((pointTupleLastFrontEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))
    ((gHatTupleOutcomeLastFrontEquiv params i) gs)

/-- Right-hand complement selected by the completed polynomial outcome. -/
noncomputable def ldSandwichLineOnePointCS_rightComplement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ}
    (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) : MIPStarRE.Quantum.Op ι :=
  match Option.map (fun g : Polynomial params => g q.1)
      (gs ⟨i, Nat.lt_succ_self i⟩) with
  | none => 0
  | some a =>
      1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome (some a)

/-- Raw ordered left tensor family used in the generic CS proposition. -/
noncomputable def ldSandwichLineOnePointCS_Aord
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    SandwichedLineQuestion params k → GHatTupleOutcome params (i + 1) →
      MIPStarRE.Quantum.Op (ι × ι) := fun q gs =>
  leftTensor (ι₂ := ι) (ldSandwichLineOnePointCS_orderedHalf params family hi q gs)

/-- Raw rotated left tensor family used in the generic CS proposition. -/
noncomputable def ldSandwichLineOnePointCS_Arot
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    SandwichedLineQuestion params k → GHatTupleOutcome params (i + 1) →
      MIPStarRE.Quantum.Op (ι × ι) := fun q gs =>
  leftTensor (ι₂ := ι) (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)

/-- The adjoint of the ordered raw CS family, as an indexed operator family. -/
noncomputable def ldSandwichLineOnePointCS_AordAdjointFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k)
      (GHatTupleOutcome params (i + 1)) (ι × ι) :=
  fun q =>
    { outcome := fun gs =>
        (ldSandwichLineOnePointCS_Aord params family hi q gs)ᴴ
      total := 0 }

/-- The adjoint of the rotated raw CS family, as an indexed operator family. -/
noncomputable def ldSandwichLineOnePointCS_ArotAdjointFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k)
      (GHatTupleOutcome params (i + 1)) (ι × ι) :=
  fun q =>
    { outcome := fun gs =>
        (ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ
      total := 0 }

/-- Raw left family for the adjoint-oriented CS input, indexed by original outcomes. -/
noncomputable def ldSandwichLineOnePointAdjointRawLeftFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (_hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k) (GHatTupleOutcome params (i + 1)) (ι × ι) :=
  fun q =>
    { outcome := fun gs =>
        (gHatHalfSandwichLeft params family (i + 1)
          ((pointTupleLastReverseEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))).outcome
          ((gHatTupleOutcomeLastReverseEquiv params i) gs)
      total := (gHatHalfSandwichLeft params family (i + 1)
        ((pointTupleLastReverseEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))).total }

/-- Raw right family for the adjoint-oriented CS input, indexed by original outcomes. -/
noncomputable def ldSandwichLineOnePointAdjointRawRightFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (_hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k) (GHatTupleOutcome params (i + 1)) (ι × ι) :=
  fun q =>
    { outcome := fun gs =>
        (gHatHalfSandwichRight params family (i + 1)
          ((pointTupleLastReverseEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))).outcome
          ((gHatTupleOutcomeLastReverseEquiv params i) gs)
      total := (gHatHalfSandwichRight params family (i + 1)
        ((pointTupleLastReverseEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))).total }









/-- The $C$ family for the first, right-action CS move. -/
noncomputable def ldSandwichLineOnePointCS_Cfirst
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    SandwichedLineQuestion params k → GHatTupleOutcome params (i + 1) → Unit →
      MIPStarRE.Quantum.Op (ι × ι) := fun q gs _ =>
  opTensor (ldSandwichLineOnePointCS_orderedHalf params family hi q gs)ᴴ
    (ldSandwichLineOnePointCS_rightComplement params strategy family q gs)

/-- The $C$ family for the second, left-action CS move. -/
noncomputable def ldSandwichLineOnePointCS_Csecond
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    SandwichedLineQuestion params k → GHatTupleOutcome params (i + 1) → Unit →
      MIPStarRE.Quantum.Op (ι × ι) := fun q gs _ =>
  opTensor (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)
    (ldSandwichLineOnePointCS_rightComplement params strategy family q gs)

/-- Raw scalar on the source side of the first CS application. -/
noncomputable def ldSandwichLineOnePointCS_firstSourceRaw
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1), ∑ u : Unit,
      ev strategy.state
        (ldSandwichLineOnePointCS_Aord params family hi q gs *
          ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u))

/-- Raw scalar on the target side of the first CS application. -/
noncomputable def ldSandwichLineOnePointCS_firstTargetRaw
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1), ∑ u : Unit,
      ev strategy.state
        (ldSandwichLineOnePointCS_Arot params family hi q gs *
          ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u))

/-- Raw scalar on the source side of the second CS application. -/
noncomputable def ldSandwichLineOnePointCS_secondSourceRaw
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1), ∑ u : Unit,
      ev strategy.state
        (ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u *
          (ldSandwichLineOnePointCS_Aord params family hi q gs)ᴴ))

/-- Raw scalar on the target side of the second CS application. -/
noncomputable def ldSandwichLineOnePointCS_secondTargetRaw
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1), ∑ u : Unit,
      ev strategy.state
        (ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u *
          (ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ))

/-- Exact low-level facts needed to turn the generic `closenessOfIP*` lemmas into
`ld-pasting.tex:964--1010` for the line-one-point statement.

This record separates the generic CS theorem instantiation (proved below) from
the paper-specific facts:

* the adjoint-oriented raw square-distance bound corresponding to the first square
  root in lines 974--985 and reused in lines 1005--1010;
* the two unit-side measurement-completeness bounds from lines 986 and 1008;
* the algebraic regrouping/reindexing that identifies the raw CS scalars with the
  existing source, intermediate, and moved outcome sums.

The construction lemma below proves the unit bounds and regrouping equalities;
the remaining live analytic endpoint is the adjoint-oriented raw-core estimate
recorded by `LdSandwichLineOnePointAdjointRawCoreBound`. -/
structure LdSandwichLineOnePointCSFacts
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) : Prop where
  adjointRawCore :
    avgOver (uniformDistribution (SandwichedLineQuestion params k))
      (fun q => qSDDCore strategy.state
        (fun gs : GHatTupleOutcome params (i + 1) =>
          (ldSandwichLineOnePointCS_Aord params family hi q gs)ᴴ)
        (fun gs : GHatTupleOutcome params (i + 1) =>
          (ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ)) ≤
      commuteGHalfSandwichError params gamma zeta (i + 1)
  firstUnitBound :
    ∀ q, ∑ gs : GHatTupleOutcome params (i + 1),
      (∑ u : Unit, ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u)ᴴ *
        (∑ u : Unit, ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u) ≤ 1
  secondUnitBound :
    ∀ q, ∑ gs : GHatTupleOutcome params (i + 1),
      (∑ u : Unit, ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u) *
        (∑ u : Unit, ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u)ᴴ ≤ 1
  source_eq_firstSourceRaw :
    ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy family hi =
      ldSandwichLineOnePointCS_firstSourceRaw params strategy family hi
  afterFirst_eq_firstTargetRaw :
    ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi =
      ldSandwichLineOnePointCS_firstTargetRaw params strategy family hi
  afterFirst_eq_secondSourceRaw :
    ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi =
      ldSandwichLineOnePointCS_secondSourceRaw params strategy family hi
  moved_eq_secondTargetRaw :
    ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi =
      ldSandwichLineOnePointCS_secondTargetRaw params strategy family hi

/-- The adjoint-oriented raw commutator square-distance bound used by the two
Cauchy--Schwarz applications in the proof of `lem:ld-sandwich-line-one-point`.

The surrounding endpoint expansions and option-valued match-mass identities are
proved directly where they are used; this structure records only the nontrivial
orientation of the half-sandwich commutation estimate. -/
structure LdSandwichLineOnePointAdjointRawCoreBound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) : Prop where
  bound :
    avgOver (uniformDistribution (SandwichedLineQuestion params k))
      (fun q => qSDDCore strategy.state
        (fun gs : GHatTupleOutcome params (i + 1) =>
          (ldSandwichLineOnePointCS_Aord params family hi q gs)ᴴ)
        (fun gs : GHatTupleOutcome params (i + 1) =>
          (ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ)) ≤
      commuteGHalfSandwichError params gamma zeta (i + 1)




end MIPStarRE.LDT.Pasting

end

end LIDT


