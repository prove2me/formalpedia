-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
-- name    : LIDT_MIPStarRE_LDT_Pasting_Statements
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:54:40.21474+00:00
-- url     : https://prove2.me/theorems/2cb4afdc-2fea-4020-be79-12f30d991508
-- title:
--   LIDT definitions: LDT / Pasting / Statements
-- statement:
--   This bundle collects the statement records for the Ld pasting construction and its commutativity consequences. It packages the main pasting conclusion, submeasurement conclusion, complete and incomplete self-consistency, switcheroo, commuting-with-G results, and the facts about the completed family.
--
--   Principal definitions:
--   - `LdPastingConclusion`: the main Ld pasting conclusion.
--   - `LdPastingSubMeasConclusion`: the pasted submeasurement conclusion.
--   - `GCompleteSelfConsistencyStatement`: the complete-family self-consistency statement.
--   - `GBotSelfConsistencyStatement`: the bottom-family self-consistency corollary.
--   - `CommutativitySwitcherooStatement`: the commutativity switcheroo statement.
--   - `CommutingWithGCompleteStatement`: the complete-family commuting statement.
--   - `CommutingWithGIncompleteStatement`: the incomplete-family commuting statement.
--   - `GHatFactsStatement`: the self-consistency and commutation facts for the completed family.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Pasting/Statements.lean#L31-L525

-- Generated from MIPStarRE/LDT/Pasting/Statements.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
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
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

/-!
# Section 12 — Statements

This file records the Section 12 pasting conclusions as reusable proposition-valued
structures. It gives the displayed error formulas and the statement structures for the
switcheroo, completed-family, half-sandwich, recurrence, Chernoff, and final pasting steps.

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

/-- The final completeness lower bound used in the pasting statements. -/
noncomputable def ldPastingCompletenessLowerBound (params : Parameters)
    (kappa nu : Error) (k : ℕ) : Error :=
  1 - kappa * (1 + 1 / (100 * (params.m : Error))) - nu -
    Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))

/-- Displayed error term for `lem:commutativity-switcheroo`. -/
noncomputable def commutativitySwitcherooError
    (zeta omega chi : Error) : Error :=
  6 * Real.rpow zeta (1 / (2 : Error)) +
    6 * Real.rpow omega (1 / (2 : Error)) +
    4 * Real.rpow chi (1 / (2 : Error))

/-- Displayed error term for `cor:commuting-with-G-complete`. -/
noncomputable def commutingWithGCompleteError (params : Parameters)
    (gamma zeta : Error) : Error :=
  36 * (params.m : Error) *
    (Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)))

/-- Displayed error term for `cor:commuting-with-G-incomplete`. -/
noncomputable def commutingWithGIncompleteError (params : Parameters)
    (gamma zeta : Error) : Error :=
  commutingWithGCompleteError params gamma zeta

/-- Displayed error term for the pairwise complete-part commutation bound used in
`cor:G-hat-facts`.

This is exactly the upstream `thm:com-main` error term. The proof of
`cor:G-hat-facts` only weakens the exponent to `1/16` after adding the three
incomplete-part commutation contributions. -/
noncomputable def pairwiseCompletePartCommutationError (params : Parameters)
    (gamma zeta : Error) : Error :=
  Commutativity.comMainError params gamma zeta

/-- Displayed self-consistency error for `\widehat G`. -/
def gHatSelfConsistencyError (zeta : Error) : Error :=
  2 * zeta

/-- Displayed commutation error for `\widehat G`. -/
noncomputable def gHatCommutationError (params : Parameters)
    (gamma zeta : Error) : Error :=
  138 * (params.m : Error) *
    (Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)))

/-- Displayed error term for commuting past `k` completed slices. -/
noncomputable def commuteGHalfSandwichError (params : Parameters)
    (gamma zeta : Error) (k : ℕ) : Error :=
  426 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
    (Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)))

/-- Displayed error term for `lem:ld-sandwich-line-one-point`. -/
noncomputable def ldSandwichLineOnePointError (params : Parameters)
    (eps delta gamma zeta : Error) (k : ℕ) : Error :=
  43 * (k : Error) * (params.m : Error) *
    (Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))

/-- Displayed error term for `lem:h-b-consistency`. -/
noncomputable def hBConsistencyError (params : Parameters)
    (eps delta gamma zeta : Error) (k : ℕ) : Error :=
  44 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
    (Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))

/-- Displayed error term for `lem:over-all-outcomes`. -/
noncomputable def overAllOutcomesError (params : Parameters)
    (eps delta gamma zeta : Error) (k : ℕ) : Error :=
  46 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
    (Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))

/-- Corrected error term for `lem:from-H-to-G`.

The paper states a linear-in-`k` `ν₈`, but its proof first accumulates
`k · (2√(2ζ) + 2√ν₄(k))`; since `ν₄(k)` already contains `k²`, the commutation
contribution is quadratic in `k`.  The Lean statement follows the proof's
literal telescope and uses the corrected quadratic bound. -/
noncomputable def fromHToGError (params : Parameters)
    (gamma zeta : Error) (k : ℕ) : Error :=
  46 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
    (Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))

/-- The per-step recurrence loss from the proof of `lem:from-H-to-G`. -/
noncomputable def fromHToGRecurrenceError (params : Parameters)
    (gamma zeta : Error) (k : ℕ) : Error :=
  2 * Real.rpow (2 * zeta) (1 / (2 : Error)) +
    2 * Real.rpow (commuteGHalfSandwichError params gamma zeta k) (1 / (2 : Error))

/-- Literal telescope error from `references/ldt-paper/ld-pasting.tex:1372`.

The following paper line drops a factor of `k` from the commutation contribution;
Lean keeps the iterated adjacent-step bound and absorbs it into the corrected
quadratic `fromHToGError`. -/
noncomputable def fromHToGPaperTotalError (params : Parameters)
    (gamma zeta : Error) (k : ℕ) : Error :=
  (k : Error) * fromHToGRecurrenceError params gamma zeta k

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:12-50`
(`\label{thm:ld-pasting}`), conclusion in `\label{item:ld-pasting-N-consistency}`
(lines 45-49).

Analytic conclusion for `thm:ld-pasting` once a witness `H` has been fixed.

The theorem `ldPastingNontrivial` separately records that the chosen witness is the
canonical construction `constructedPastedMeasurement params family k`, so this
structure stores only the quantitative conclusion from the paper. -/
structure LdPastingConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (H : Measurement (Polynomial params.next) ι)
    (eps delta gamma kappa zeta : Error) (k : ℕ) : Prop where
  -- Naming note: this is not a `ν` field from the paper. The point-consistency
  -- bound here continues to use the induction-section error term, while `ν`
  -- tracks the completeness loss below.
  pointConsistency :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next H.toSubMeas)
      (MainInductionStep.ldPastingInInductionError params k
        eps delta gamma kappa zeta)

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:118-131`
(`\label{lem:ld-pasting-sub-measurement}`).

Analytic conclusion for `lem:ld-pasting-sub-measurement` once a witness `H`
has been fixed.

The theorem `ldPastingSubMeas` separately records that the chosen witness is the
canonical construction `constructedPastedSubMeas params family k`, so this
structure stores only the quantitative properties proved about that witness. -/
structure LdPastingSubMeasConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (H : SubMeas (Polynomial params.next) ι)
    (eps delta gamma kappa zeta : Error) (k : ℕ) : Prop where
  -- Naming note: this is not a `ν` field from the paper. The point-consistency
  -- bound here is the paper's intermediate `ν`, while the completeness field
  -- carries the missing-mass term needed for the final `σ` after completion.
  pointConsistency :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next H)
      (MainInductionStep.ldPastingInInductionNu params k
        eps delta gamma zeta)
  completeness :
    CompletenessAtLeast strategy.state H.liftLeft
      (ldPastingCompletenessLowerBound params kappa
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) k)

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:514-536`
(`\label{lem:g-complete-self-consistency}`); the `\widehat G` rewrite at
`eq:gselfconall` (`references/ldt-paper/ld-pasting.tex:821`) is the family of
self-consistency bounds compared against here.

Lean statement for `lem:g-complete-self-consistency`.
`ψbi` is the bipartite state on `d * d` (passed as `strategy.state`
by callers). -/
structure GCompleteSelfConsistencyStatement (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (zeta : Error) : Prop where
  /--
  Stores self-consistency of the full slice family `family.meas` because the
  `cor:G-hat-facts` decomposition expands `\widehat G` self-consistency into the
  original slice-family term plus the incomplete part, not the postprocessed
  complete-part family.
  -/
  completePartSelfConsistency :
    SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
      (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas))
      zeta

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:537-558`
(`\label{cor:g-bot-self-consistency}`); incomplete-part complement of
`\label{lem:g-complete-self-consistency}` and the
`eq:gselfconall` self-consistency family at line 821.

Lean statement for `cor:g-bot-self-consistency`. -/
structure GBotSelfConsistencyStatement (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (zeta : Error) : Prop where
  incompletePartSelfConsistency :
    SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (incompletePartLeftFamily params family)
      (incompletePartRightFamily params family)
      zeta

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:560-720`
(`\label{lem:commutativity-switcheroo}`).

Lean statement for `lem:commutativity-switcheroo`. -/
structure CommutativitySwitcherooStatement {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (zeta omega chi : Error) : Prop where
  aggregateCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (switcherooAggregateLeft params family M)
      (switcherooAggregateRight params family M)
      (commutativitySwitcherooError zeta omega chi)

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:721-774`
(`\label{cor:commuting-with-G-complete}`).

Lean statement for `cor:commuting-with-G-complete`. -/
structure CommutingWithGCompleteStatement (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) : Prop where
  pairwiseCompletePartCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι) <|
          orderedProductOpFamily
            ((family.meas q.1).toSubMeas)
            ((family.meas q.2).toSubMeas))
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι) <|
          reversedProductOpFamily
            ((family.meas q.1).toSubMeas)
            ((family.meas q.2).toSubMeas))
      (pairwiseCompletePartCommutationError params gamma zeta)
  pointWithCompletePartCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (completePartPointProductLeft params family)
      (completePartPointProductRight params family)
      (commutingWithGCompleteError params gamma zeta)
  completePartCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (completePartTotalProductLeft params family)
      (completePartTotalProductRight params family)
      (commutingWithGCompleteError params gamma zeta)

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:775-816`
(`\label{cor:commuting-with-G-incomplete}`).

Lean statement for `cor:commuting-with-G-incomplete`. -/
structure CommutingWithGIncompleteStatement (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) : Prop where
  pointWithIncompletePartCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (incompletePartPointProductLeft params family)
      (incompletePartPointProductRight params family)
      (commutingWithGIncompleteError params gamma zeta)
  incompletePartCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (incompletePartTotalProductLeft params family)
      (incompletePartTotalProductRight params family)
      (commutingWithGIncompleteError params gamma zeta)

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:817-862`
(`\label{cor:G-hat-facts}`); the displayed `\widehat G` self-consistency and
commutation lines `eq:gselfconall` and `eq:gcomall` are at lines 821 and 823.

Lean statement for `cor:G-hat-facts`. -/
structure GHatFactsStatement (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) : Prop where
  completedSelfConsistency :
    SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)
  completedCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:872-917`
(`\label{lem:commute-g-half-sandwich}`).

Lean statement for `lem:commute-g-half-sandwich`. -/
structure CommuteGHalfSandwichStatement (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (k : ℕ) : Prop where
  repeatedCommutation :
    SDDOpRel ψbi
      (uniformDistribution (PointTuple params k))
      (gHatHalfSandwichLeft params family k)
      (gHatHalfSandwichRight params family k)
      (commuteGHalfSandwichError params gamma zeta k)

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:918-1040`
(`\label{lem:ld-sandwich-line-one-point}`).

Lean statement for `lem:ld-sandwich-line-one-point`. -/
structure LdSandwichLineOnePointStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error)
    (k i : ℕ) : Prop where
  linePointComparison :
    ConsRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointLeftFamily params strategy family k i)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (ldSandwichLineOnePointError params eps delta gamma zeta k)

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:1041-1140`
(`\label{lem:h-b-consistency}`).

Lean statement for `lem:h-b-consistency`. -/
structure HBConsistencyStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ) : Prop where
  lineConsistency :
    ConsRel strategy.state
      (uniformDistribution (VerticalLineQuestion params))
      (hRestrictionToVerticalLine params
        (constructedPastedSubMeas params family k))
      (verticalLineMeasurementFamily params strategy)
      (hBConsistencyError params eps delta gamma zeta k)

/-- Scalar expectation of the pasted submeasurement mass appearing on the
left-hand side of `lem:over-all-outcomes`. -/
noncomputable def overAllOutcomesPastedMass (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) : Error :=
  subMeasMass strategy.state ((constructedPastedSubMeas params family k).liftLeft)

/-- Scalar expectation of the all-outcomes expansion on the right-hand side of
`lem:over-all-outcomes`. -/
noncomputable def overAllOutcomesExpansionMass (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) : Error :=
  subMeasMass strategy.state ((IdxSubMeas.liftLeft
    (allOutcomesExpansionFamily params strategy family k)) ())

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:1141-1294`
(`\label{lem:over-all-outcomes}`).

Lean statement for `lem:over-all-outcomes`.

The paper's displayed statement is a scalar approximation of expectation values,
not a stronger `≈_δ` relation between already-collapsed `Unit`-indexed
submeasurements.  Accordingly, this structure stores only the absolute-value bound
between the pasted mass and the all-outcomes expansion mass. -/
structure OverAllOutcomesStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ) : Prop where
  totalOutcomeExpansion :
    |overAllOutcomesPastedMass params strategy family k -
        overAllOutcomesExpansionMass params strategy family k| ≤
      overAllOutcomesError params eps delta gamma zeta k

/-- Scalar expectation of one per-tail contribution in `lem:from-H-to-G`.

This is the single-`τ_{≥ℓ}` term appearing inside the aggregate stage mass from
`references/ldt-paper/ld-pasting.tex`, equation
`eq:i-think-this-is-what-i'm-supposed-to-prove-2` (lines 1386–1391), and the
mirrored blueprint discussion in `blueprint/src/chapter/ch09_pasting.tex`.
The parameter `prefixLen` is the Lean 0-based stage index. In the ambient
`k`-step recurrence, the remaining tail length is `tailLen = k - prefixLen`. -/
noncomputable def fromHToGTailStageMass (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) : Error :=
  ev ψbi (((fromHToGTailStageFamily params family prefixLen τtail) ()).total)

/-- Scalar expectation of the full Lean stage-`ℓ` quantity from `lem:from-H-to-G`.

This is the aggregate quantity displayed in
`references/ldt-paper/ld-pasting.tex`, equation
`eq:i-think-this-is-what-i'm-supposed-to-prove-2` (lines 1386–1391), and in the
matching blueprint section `blueprint/src/chapter/ch09_pasting.tex`.
Lean uses 0-based indexing: stage `ℓ` here corresponds to the paper's stage
`ℓ + 1`, so the remaining tail has length `k - ℓ`. Accordingly, this sums over
all remaining tail types `τ_{≥ℓ} ∈ {0,1}^{k-ℓ}`, while the next Lean stage
`ℓ + 1` sums over the shorter tails `τ_{>ℓ}`. -/
noncomputable def fromHToGStageMass (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) : Error :=
  ∑ τtail : GHatType (k - ℓ),
    fromHToGTailStageMass params ψbi family ℓ τtail

/-- Scalar expectation of the left-hand side of `lem:from-H-to-G`, i.e. the
uniform average of the eligible pasted-sandwich total mass. -/
noncomputable def fromHToGAllOutcomesMass (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k : ℕ) : Error :=
  subMeasMass ψbi ((IdxSubMeas.liftLeft
    (allOutcomesExpansionFamily params strategy family k)) ())

/-- Scalar expectation of the Bernoulli-tail polynomial `F(G)` on the bipartite
state from `lem:from-H-to-G`. -/
noncomputable def fromHToGBernoulliTailMass (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k : ℕ) : Error :=
  subMeasMass ψbi ((IdxSubMeas.liftRight
    (bernoulliTailFromFamily params family k)) ())

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:1295-1670`
(`\label{lem:from-H-to-G}`).

Lean statement for `lem:from-H-to-G`.

The paper's displayed statement is a scalar approximation of expectation values,
not a new `≈_δ` relation between submeasurements.  Accordingly, this statement
stores only the final all-outcomes vs. Bernoulli-tail comparison; the
adjacent-stage estimates are recorded by the internal construction lemmas. -/
structure FromHToGStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (k : ℕ) : Prop where
  bernoulliPolynomialRewrite :
    |fromHToGAllOutcomesMass params strategy ψbi family k -
        fromHToGBernoulliTailMass params ψbi family k| ≤
      fromHToGError params gamma zeta k

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:1671-1798`
(`\label{lem:chernoff-bernoulli-matrix}`); the operator-Chernoff inequality is
proved by applying continuous functional calculus to the scalar tail polynomial
and the scalar Chernoff bound `eq:by-chernoff` at line 1739.

Lean statement for `lem:chernoff-bernoulli-matrix`. -/
structure ChernoffBernoulliMatrixStatement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (theta : Error) (k degree : ℕ) (X : MIPStarRE.Quantum.Op ι) (kappa : Error)
    (hXpsd : 0 ≤ X)
    (hXleOne : X ≤ 1) : Prop where
  matrixTailBound :
    CompletenessAtLeast ψ
      (bernoulliTailSubMeas k degree X hXpsd hXleOne)
      (1 - kappa / (1 - theta) - Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2))

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:1799-1849`
(`\label{cor:ld-pasting-N-completeness}`).

Lean statement for `cor:ld-pasting-N-completeness`. -/
structure LdPastingNCompletenessStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (kappa nu : Error) (k : ℕ) : Prop where
  completenessBound :
    CompletenessAtLeast strategy.state
      (constructedPastedSubMeas params family k).liftLeft
      (ldPastingCompletenessLowerBound params kappa nu k)

end MIPStarRE.LDT.Pasting

end

end LIDT


