-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
-- name    : LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:52:34.304118+00:00
-- url     : https://prove2.me/theorems/5591adba-0290-4304-9875-0011ca6c1f0c
-- title:
--   LIDT definitions: LDT / Pasting / Sandwich / PastedFamilies
-- statement:
--   This bundle defines the families produced by the sandwich and interpolation stages of the pasting construction. It packages recurrence weights, globally consistent interpolation operators, eligible sandwich submeasurements, the completed pasted measurement, fallback outcomes, averaged slice candidates, and the vertical-line family.
--
--   Principal definitions:
--   - `fromHToGRecurrenceWeight`: the recurrence weight for the remaining tuple tail.
--   - `pastedInterpolationFamily`: the interpolated family restricted to globally consistent polynomial outcomes.
--   - `averagedEligibleSandwichSubMeas`: the averaged eligible sandwiched submeasurement.
--   - `constructedPastedSubMeas`: the pasted submeasurement produced by sandwich and interpolation.
--   - `pastedFallbackOutcome`: the polynomial receiving completion mass.
--   - `constructedPastedMeasurement`: the completed pasted measurement.
--   - `averagedSliceAppendedSubMeas`: the degree-zero candidate obtained from averaged slice answers.
--   - `verticalLineMeasurementFamily`: the vertical axis-parallel measurement family.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Pasting/Sandwich/PastedFamilies.lean#L26-L334

-- Generated from MIPStarRE/LDT/Pasting/Sandwich/PastedFamilies.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
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
# Section 12 — Sandwich constructions: pasted families

Pasted interpolation families, recurrence weights, and final operator families.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Source-style recurrence weight `S_{τtail}` from `lem:from-H-to-G`.

The parameter `prefixLen` is the number of type bits already converted into the
Bernoulli polynomial.  This is exactly `truncatedTypeSums` specialized to the
averaged complete operator `G = E_x ∑_g G^x_g`. -/
noncomputable def fromHToGRecurrenceWeight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (prefixLen : ℕ) {tailLen : ℕ}
    (τtail : GHatType tailLen) : MIPStarRE.Quantum.Op ι :=
  truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail

/-- The interpolated operator `H^{x_1,\dots,x_k}_h` restricted to tuples that are
globally consistent with a single polynomial.

The paper's definition (`references/ldt-paper/ld-pasting.tex` lines 474–495) sums
only tuples `(g_1,…,g_k)` in `Global_τ(x)` — those consistent with a single
polynomial `h` — and then interpolates. The `|τ| ≥ d+1` eligibility filter is
applied by `interpolationEligibleSandwichFamily`; this definition additionally
restricts to globally consistent tuples via `IsGloballyConsistent`.
Consequently, `pastedInterpolationFamily` is supported only on tuples satisfying
both restrictions, and any fallback or default value in
`interpolateCompletedSlices` is irrelevant off that restricted support. -/
noncomputable def pastedInterpolationFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (Polynomial params.next) ι :=
  fun xs =>
    postprocess
      (restrictSubMeas
        (interpolationEligibleSandwichFamily params family k xs)
        (IsGloballyConsistent params xs))
      (interpolateCompletedSlices params k xs)

/-- The averaged sandwiched family restricted to outcome tuples of type `τ`
with `|τ| ≥ d+1`, as in `lem:over-all-outcomes`. -/
noncomputable def averagedEligibleSandwichSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    SubMeas (GHatTupleOutcome params k) ι :=
  averageIdxSubMeas
    (uniformDistribution (PointTuple params k))
    (interpolationEligibleSandwichFamily params family k)
    (uniformDistribution_weight_sum_le_one (PointTuple params k))

/-- The specific pasted submeasurement constructed from the sandwich/interpolation scheme. -/
noncomputable def constructedPastedSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) : SubMeas (Polynomial params.next) ι :=
  averageIdxSubMeas
    (distinctTupleDistribution params k)
    (pastedInterpolationFamily params family k)
    (distinctTupleDistribution_weight_sum_le_one params k)

/-- The distinguished fallback polynomial `h₀` that receives the completion mass. -/
noncomputable def pastedFallbackOutcome (params : Parameters) [FieldModel params.q] :
    Polynomial params.next :=
  fallbackInterpolatedPolynomial params

/-- The specific pasted measurement obtained by completing the constructed pasted submeasurement.

The paper adds all missing mass `I - H_total` to a single distinguished polynomial
outcome `h₀` (the fallback interpolant).  So the outcome operator for `h₀` becomes
`H_{h₀} + (I - H_total)` while all other outcomes keep their original operators, and
the total is genuinely the identity `I`. -/
noncomputable def constructedPastedMeasurement (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) : Measurement (Polynomial params.next) ι :=
  Preliminaries.completeAtOutcome
    (constructedPastedSubMeas params family k)
    (pastedFallbackOutcome params)

/-- Degree-zero candidate pasted submeasurement obtained by averaging the slice
family and viewing each slice polynomial as a polynomial in one more variable.

Paper origin: `references/ldt-paper/ld-pasting.tex:12-55`.  This is a
Lean-only construction for the `d = 0` branch of `thm:ld-pasting`, where the
ordinary interpolation construction is not available because `d + 1 = 1`
collapses the distinct-height argument.  It introduces no additional
hypothesis. -/
noncomputable def averagedSliceAppendedSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) : SubMeas (Polynomial params.next) ι :=
  postprocess family.averagedSubMeas
    (fun g => Polynomial.appendAtHeight params g zeroCoord)



/-- Placeholder family for the vertical axis-parallel line measurement `B^u_f`. -/
noncomputable def verticalLineMeasurementFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxSubMeas (VerticalLineQuestion params) (AxisLinePolynomial params.next) ι :=
  fun u =>
    let ℓ : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := lastCoord params }
    (strategy.axisParallelMeasurement ℓ).toSubMeas



/-- Pull back the vertical-line answer family along `truncatePoint`, then read
its line polynomial at the lifted point's final coordinate. -/
noncomputable def liftedVerticalLineAnswerFamily
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  fun u =>
    postprocess
      (verticalLineMeasurementFamily params strategy (truncatePoint params u))
      (fun f => f (pointHeight params u))



/-- Explicit value extracted from the `i`-th genuine slice outcome at the test point.

The paper's one-point sandwich comparison only sums over tuples with
`g_i ≠ ⊥`; the `none` mass is therefore removed before postprocessing. -/
noncomputable def ldSandwichLineOnePointLeftFamily (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
  fun q =>
    postprocess
      (restrictSubMeas (gHatSandwichFamily params family k q.2)
        (fun gs => if h : i < k then (gs ⟨i, h⟩).isSome = true else False))
      (fun gs => if h : i < k then Option.map (fun g => g q.1) (gs ⟨i, h⟩) else none)

/-- Explicit value extracted from the vertical line measurement `B^u` at the slice height `x_i`. -/
noncomputable def ldSandwichLineOnePointRightFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (_family : IdxPolyFamily params ι)
    (k i : ℕ) : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
  fun q =>
    postprocess (verticalLineMeasurementFamily params strategy q.1) (fun f =>
      if h : i < k then
        some (f (q.2 ⟨i, h⟩))
      else
        none)

/-- Restrict a global polynomial-valued submeasurement to the vertical line through `u`. -/
noncomputable def hRestrictionToVerticalLine (params : Parameters) [FieldModel params.q]
    (H : SubMeas (Polynomial params.next) ι) :
    IdxSubMeas (VerticalLineQuestion params) (AxisLinePolynomial params.next) ι :=
  fun u =>
    let verticalLine : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := ⟨params.m, Nat.lt_succ_self params.m⟩ }
    postprocess H (fun h => Polynomial.restrictToAxisParallelLine params.next h verticalLine)

/-- Collapse a submeasurement to its `Unit`-valued total operator. -/
noncomputable def pastedMeasurementTotal
    {α : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (H : SubMeas α ι) : IdxSubMeas Unit Unit ι :=
  constSubMeasFamily (postprocess H (fun _ => ()))

/-- The expansion over all outcome types `τ`, written as the
total mass of the averaged sandwich family restricted to `|τ| ≥ d+1`. -/
noncomputable def allOutcomesExpansionFamily (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas Unit Unit ι :=
  pastedMeasurementTotal (averagedEligibleSandwichSubMeas params family k)

/-- The one-outcome submeasurement whose unique effect is the Bernoulli-tail
operator of `X`. -/
noncomputable def bernoulliTailSubMeas {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k degree : ℕ) (X : MIPStarRE.Quantum.Op ι)
    (hXpsd : 0 ≤ X) (hXleOne : X ≤ 1) : SubMeas Unit ι :=
  SubMeas.singleOutcome (bernoulliTailOperator k degree X)
    (bernoulliTailOperator_nonneg k degree X hXpsd hXleOne)
    (bernoulliTailOperator_le_one k degree X hXpsd hXleOne)

@[simp] theorem bernoulliTailSubMeas_outcome {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k degree : ℕ) (X : MIPStarRE.Quantum.Op ι)
    (hXpsd : 0 ≤ X) (hXleOne : X ≤ 1) (u : Unit) :
    (bernoulliTailSubMeas k degree X hXpsd hXleOne).outcome u =
      bernoulliTailOperator k degree X :=
  rfl

@[simp] theorem bernoulliTailSubMeas_total {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k degree : ℕ) (X : MIPStarRE.Quantum.Op ι)
    (hXpsd : 0 ≤ X) (hXleOne : X ≤ 1) :
    (bernoulliTailSubMeas k degree X hXpsd hXleOne).total =
      bernoulliTailOperator k degree X :=
  rfl

/-- The Bernoulli-tail polynomial in the averaged complete operator `G = E_x \sum_g G^x_g`. -/
noncomputable def bernoulliTailFromFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas Unit Unit ι :=
  constSubMeasFamily <|
    bernoulliTailSubMeas k params.d (IdxPolyFamily.averagedSubMeas family).total
      (IdxPolyFamily.averagedSubMeas family).total_nonneg
      (IdxPolyFamily.averagedSubMeas family).total_le_one

/-- Average the sandwiched completed-slice family over tuples whose completed/
incomplete pattern is exactly `τtail`.

This is the paper's operator
$$
\mathbb E_{x_{\ge \ell}} \sum_{g_{\ge \ell} \in \mathsf{Outcomes}_{\tau_{\ge \ell}}}
  \widehat H^{x_{\ge \ell}}_{g_{\ge \ell}},
$$
written in the existing `SubMeas Unit` API so that its total operator is the
relevant suffix-stage matrix.  Unlike the old `fromHToG` recurrence families,
this keeps the `\widehat H^{x_{\ge \ell}}_{g_{\ge \ell}}` suffix visible instead
of collapsing immediately to the full `k`-step total mass.

When this is used in `fromHToG`, the suffix length is `tailLen = k - ℓ`, and
the expectation is the paper's independent uniform average over the remaining
slice points `x_{≥ℓ}`. -/
noncomputable def averagedSandwichByTypeSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (tailLen : ℕ) (τtail : GHatType tailLen) :
    SubMeas Unit ι :=
  open Classical in
    averageIdxSubMeas
      (uniformDistribution (PointTuple params tailLen))
      (fun xs =>
        postprocess
          (restrictSubMeas
            (gHatSandwichFamily params family tailLen xs)
            (fun gs => gs ∈ outcomesByType τtail))
          (fun _ => ()))
      (uniformDistribution_weight_sum_le_one (PointTuple params tailLen))

/-- The stage-`ℓ` suffix family from the proof of `lem:from-H-to-G`, for a fixed
remaining tail type `τ_{≥ℓ}`.

This is the operator-valued quantity displayed termwise in
`references/ldt-paper/ld-pasting.tex`, equation
`eq:i-think-this-is-what-i'm-supposed-to-prove-2` (lines 1386–1391), and in the
parallel blueprint discussion in `blueprint/src/chapter/ch09_pasting.tex`.
The parameter `prefixLen` is the Lean 0-based stage index. In the ambient
`k`-step recurrence where this family is used, the remaining tail length is
`tailLen = k - prefixLen`, so Lean stage `prefixLen` corresponds to the paper's
stage `prefixLen + 1`.

Concretely, this records
$$
\mathbb E_{x_{\ge \ell}} \sum_{g_{\ge \ell} \in \mathsf{Outcomes}_{\tau_{\ge \ell}}}
  \widehat H^{x_{\ge \ell}}_{g_{\ge \ell}} \otimes S_{\tau_{\ge \ell}}.
$$ -/
noncomputable def fromHToGTailStageFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    IdxOpFamily Unit Unit (ι × ι) :=
  fun _ =>
    let base := averagedSandwichByTypeSubMeas params family tailLen τtail
    let weight := fromHToGRecurrenceWeight params family prefixLen τtail
    { outcome := fun _ =>
        leftTensor (ι₂ := ι) base.total * rightTensor (ι₁ := ι) weight
      total := leftTensor (ι₂ := ι) base.total * rightTensor (ι₁ := ι) weight }

end MIPStarRE.LDT.Pasting

end

end LIDT


