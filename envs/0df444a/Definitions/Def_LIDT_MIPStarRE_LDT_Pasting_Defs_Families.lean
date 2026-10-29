-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
-- name    : LIDT_MIPStarRE_LDT_Pasting_Defs_Families
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:37:52.814227+00:00
-- url     : https://prove2.me/theorems/d2590fc3-e39d-41d1-8d8e-1414c287552e
-- title:
--   LIDT definitions: LDT / Pasting / Defs / Families
-- statement:
--   This bundle defines the completed slice families used in LDT pasting. It formalizes global consistency and interpolation of completed slice outcomes, separates successful and failure parts, and constructs the completed G-hat measurement and its left and right tensor families.
--
--   Principal definitions:
--   - `IsGloballyConsistent`: A tuple of genuine slice polynomials agrees with one polynomial in the successor space at the selected distinct heights.
--   - `isGloballyConsistent_decidablePred`: The classical decision predicate for global consistency.
--   - `globallyConsistentWitness`: A selected global polynomial witnessing consistency.
--   - `interpolateCompletedSlices`: Interpolates an eligible completed-slice tuple into a successor polynomial.
--   - `completePartSubMeas`: The submeasurement formed from successful genuine polynomial outcomes.
--   - `incompletePartSubMeas`: The residual submeasurement formed from failure outcomes.
--   - `gHatIdxMeas`: Completes each slice family with a failure outcome.
--   - `completePartLeftFamily`: Places the complete slice part on the left register for tensor comparisons.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Pasting/Defs/Families.lean#L21-L179

-- Generated from MIPStarRE/LDT/Pasting/Defs/Families.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

/-!
# Section 12 — Definitions: consistency and families

Global-consistency predicates and the completed-slice family constructions.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A completed-slice tuple `gs` is globally consistent at evaluation
points `xs` if there exists a single polynomial `h` in `m+1` variables
whose restriction to each genuine slice height `xᵢ` agrees with the
corresponding slice polynomial `gᵢ`.

This matches the paper's `Global_τ(x)` predicate from
`references/ldt-paper/ld-pasting.tex` lines 1123-1131. -/
def IsGloballyConsistent (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k) : Prop :=
  ∃ h : Polynomial params.next,
    ∀ i : Fin k, ∀ (hi : (gs i).isSome = true),
      (Polynomial.restrictAtHeight params h (xs i)).poly =
        ((gs i).get hi).poly

/-- `IsGloballyConsistent params xs` is only classically decidable.
The predicate quantifies over a witness polynomial in the ambient global polynomial
space, so there is no finitary decision procedure to search for such a witness.
This nonconstructive instance is used only for finite `restrictSubMeas` filters. -/
noncomputable instance isGloballyConsistent_decidablePred
    (params : Parameters) [FieldModel params.q] {k : ℕ}
    (xs : PointTuple params k) :
    DecidablePred (IsGloballyConsistent params xs) :=
  fun _gs => Classical.dec _





/-- Paper origin: `references/ldt-paper/ld-pasting.tex:1131-1135`
(definition of `\mathsf{Global}_{\tau}(x)`).

Choose a witness polynomial for a globally consistent tuple. -/
noncomputable def globallyConsistentWitness (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (gs : GHatTupleOutcome params k)
    (hGlobal : IsGloballyConsistent params xs gs) : Polynomial params.next :=
  open Classical in
    Classical.choose hGlobal

/-- Recover a global polynomial from a completed-slice tuple.

On the actual pasting path this map is only applied after restricting to tuples in
`Global_τ(x)` with `|τ| ≥ d+1`, so the ineligible branch lies outside the support
of `pastedInterpolationFamily`. We nevertheless make the nonempty ineligible branch
honest: for globally consistent tuples of length `k + 1` that fail the eligibility
cutoff, we return a chosen witness polynomial rather than a placeholder.

The empty-tuple branch keeps the distinguished fallback outcome `h₀`, matching the
completion outcome used in `constructedPastedMeasurement`.

In the eligible branch we still keep the explicit interpolation support witness: a
chosen subset `σ ⊆ support(gs)` of size `d+1` is packaged together with its proof
fields and then passed to `interpolateCompletedSlicesFromSupport`. -/
noncomputable def interpolateCompletedSlices (params : Parameters) [FieldModel params.q] :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → Polynomial params.next
  | 0, _xs, _gs => fallbackInterpolatedPolynomial params
  | _ + 1, xs, gs =>
      if hEligible : InterpolationEligible params gs then
        let supportData := interpolationSupportWitness gs hEligible
        interpolateCompletedSlicesFromSupport params xs gs
          supportData.support supportData.subset_support supportData.card_eq
      else if hGlobal : IsGloballyConsistent params xs gs then
        globallyConsistentWitness params xs gs hGlobal
      else
        fallbackInterpolatedPolynomial params

/-- Aggregate the polynomial outcomes of `G^x` into its complete part `G^x`. -/
noncomputable def completePartSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) : SubMeas Unit ι :=
  postprocess ((family.meas x).toSubMeas) (fun _ => ())

/-- The total operator of the complete part is the original slice total. -/
@[simp] theorem completePartSubMeas_total (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    (completePartSubMeas params family x).total = (family.meas x).total := by
  simp [completePartSubMeas, postprocess_total]

/-- The unique outcome of the complete part equals its total operator. -/
@[simp] theorem completePartSubMeas_outcome_unit (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    (completePartSubMeas params family x).outcome () =
      (completePartSubMeas params family x).total := by
  rw [← (completePartSubMeas params family x).sum_eq_total]
  simp [completePartSubMeas]

/-- Placeholder for the incomplete part `G^x_⊥ = I - G^x`. -/
noncomputable def incompletePartSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) : SubMeas Unit ι :=
  let X := 1 - (completePartSubMeas params family x).total
  SubMeas.singleOutcome X
    (sub_nonneg.mpr (completePartSubMeas params family x).total_le_one)
    (sub_le_self _ (completePartSubMeas params family x).total_nonneg)

/-- Complete each projective slice submeasurement by adjoining the failure outcome. -/
noncomputable def gHatIdxMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxMeas (Fq params) (GHatOutcome params) ι :=
  fun x => completeSubMeas ((family.meas x).toSubMeas)

/-- Each completed `\widehat G` outcome is projective. -/
theorem gHatIdxMeas_proj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) (g : GHatOutcome params) :
    (gHatIdxMeas params family x).outcome g * (gHatIdxMeas params family x).outcome g =
      (gHatIdxMeas params family x).outcome g := by
  cases g with
  | none =>
      let T := (family.meas x).total
      change (1 - T) * (1 - T) = 1 - T
      have hTT : T * T = T := by
        simpa [T] using ProjSubMeas.total_proj (family.meas x)
      calc
        (1 - T) * (1 - T) = 1 - T - T + T * T := by
          noncomm_ring
        _ = 1 - T := by
          rw [hTT]
          abel
  | some p =>
      simp [gHatIdxMeas, completeSubMeas, (family.meas x).proj p]

/-- Left tensor-placement for the complete part `G^x`
on the bipartite space `d * d`. -/
noncomputable def completePartLeftFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) (completePartSubMeas params family x)

/-- Right tensor-placement for the complete part `G^x`
on the bipartite space `d * d`. -/
noncomputable def completePartRightFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) (completePartSubMeas params family x)

/-- Left tensor-placement for the incomplete part `G^x_⊥`
on the bipartite space `d * d`. -/
noncomputable def incompletePartLeftFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) (incompletePartSubMeas params family x)

/-- Right tensor-placement for the incomplete part `G^x_⊥`
on the bipartite space `d * d`. -/
noncomputable def incompletePartRightFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) (incompletePartSubMeas params family x)

end MIPStarRE.LDT.Pasting

end

end LIDT


