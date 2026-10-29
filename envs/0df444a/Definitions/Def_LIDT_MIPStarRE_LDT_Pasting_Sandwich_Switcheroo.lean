-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
-- name    : LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:41:51.684792+00:00
-- url     : https://prove2.me/theorems/a5689ef9-9e9b-45b2-ab79-64cd0d15cbbe
-- title:
--   LIDT definitions: LDT / Pasting / Sandwich / Switcheroo
-- statement:
--   This bundle defines the operator families used in the switcheroo contraction and sandwich estimates. It includes left and right self-consistency placements, ordered point products, aggregate families, and complete-part products for comparing completed-slice factors across tensor registers.
--
--   Principal definitions:
--   - `switcherooSelfConsistencyLeft`: the left tensor placement of the auxiliary family.
--   - `switcherooSelfConsistencyRight`: the right tensor placement of the auxiliary family.
--   - `switcherooPointProductLeft`: the ordered point-product family.
--   - `switcherooPointProductRight`: the reversed point-product family.
--   - `switcherooAggregateLeft`: the left aggregate family.
--   - `switcherooAggregateRight`: the right aggregate family.
--   - `completePartPointProductLeft`: the left complete-part product family.
--   - `completePartPointProductRight`: the right complete-part product family.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Pasting/Sandwich/Switcheroo.lean#L22-L262

-- Generated from MIPStarRE/LDT/Pasting/Sandwich/Switcheroo.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

/-!
# Section 12 — Sandwich constructions: switcheroo families

Switcheroo, complete-part, and half-product operator families.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Left tensor-placement for the auxiliary family `M^x_o`. -/
def switcherooSelfConsistencyLeft {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxSubMeas (SliceQuestion params) Outcome (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) ((M x).toSubMeas)

/-- Right tensor-placement for the auxiliary family `M^x_o`. -/
def switcherooSelfConsistencyRight {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxSubMeas (SliceQuestion params) Outcome (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) ((M x).toSubMeas)

/-- Concrete hypothesis family for `G^x_g M^y_o`. -/
noncomputable def switcherooPointProductLeft
    {Outcome : Type*} [Fintype Outcome] (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params × Outcome) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      orderedProductOpFamily
        ((family.meas q.1).toSubMeas)
        ((M q.2).toSubMeas)

/-- Concrete hypothesis family for `M^y_o G^x_g` on the
`Polynomial params × Outcome` outcome type. -/
noncomputable def switcherooPointProductRight
    {Outcome : Type*} [Fintype Outcome] (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params × Outcome) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily
        ((family.meas q.1).toSubMeas)
        ((M q.2).toSubMeas)

/-- Concrete aggregate family for `G^x M^y_o`. -/
noncomputable def switcherooAggregateLeft {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxOpFamily (SlicePairQuestion params) Outcome (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (completePartSubMeas params family q.1)
        ((M q.2).toSubMeas)

/-- Concrete aggregate family for `M^y_o G^x`. -/
noncomputable def switcherooAggregateRight {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxOpFamily (SlicePairQuestion params) Outcome (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        ((M q.2).toSubMeas)
        (completePartSubMeas params family q.1)

/-- Concrete family for `G^x_g G^y`. -/
noncomputable def completePartPointProductLeft (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        ((family.meas q.1).toSubMeas)
        (completePartSubMeas params family q.2)

/-- Concrete family for `G^y G^x_g`. -/
noncomputable def completePartPointProductRight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (completePartSubMeas params family q.2)
        ((family.meas q.1).toSubMeas)

/-- Concrete family for `G^x G^y`. -/
noncomputable def completePartTotalProductLeft (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) Unit (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        (completePartSubMeas params family q.1)
        (completePartSubMeas params family q.2)

/-- Concrete family for `G^y G^x`. -/
noncomputable def completePartTotalProductRight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) Unit (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (completePartSubMeas params family q.2)
        (completePartSubMeas params family q.1)

/-- Concrete family for `G^x_g G^y_⊥`. -/
noncomputable def incompletePartPointProductLeft (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        ((family.meas q.1).toSubMeas)
        (incompletePartSubMeas params family q.2)

/-- Concrete family for `G^y_⊥ G^x_g`. -/
noncomputable def incompletePartPointProductRight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (incompletePartSubMeas params family q.2)
        ((family.meas q.1).toSubMeas)

/-- Concrete family for `G^x_⊥ G^y_⊥`. -/
noncomputable def incompletePartTotalProductLeft (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) Unit (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        (incompletePartSubMeas params family q.1)
        (incompletePartSubMeas params family q.2)

/-- Concrete family for `G^y_⊥ G^x_⊥`. -/
noncomputable def incompletePartTotalProductRight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) Unit (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (incompletePartSubMeas params family q.2)
        (incompletePartSubMeas params family q.1)

/-- Left tensor-placement for `\widehat G^x_g`. -/
noncomputable def gHatSelfConsistencyLeftFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) (GHatOutcome params) (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) ((gHatIdxMeas params family x).toSubMeas)

/-- Right tensor-placement for `\widehat G^x_g`. -/
noncomputable def gHatSelfConsistencyRightFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) (GHatOutcome params) (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) ((gHatIdxMeas params family x).toSubMeas)

/-- Concrete family for the pairwise product `\widehat G^x_g \widehat G^y_h`. -/
noncomputable def gHatPairProductLeft (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (GHatOutcome params × GHatOutcome params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      orderedProductOpFamily
        ((gHatIdxMeas params family q.1).toSubMeas)
        ((gHatIdxMeas params family q.2).toSubMeas)

/-- Concrete family for the reversed pairwise product `\widehat G^y_h \widehat G^x_g`. -/
noncomputable def gHatPairProductRight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (GHatOutcome params × GHatOutcome params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily
        ((gHatIdxMeas params family q.1).toSubMeas)
        ((gHatIdxMeas params family q.2).toSubMeas)

/-- The ordered half-product `\widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k}`. -/
noncomputable def gHatHalfProductOutcomeOperator (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → MIPStarRE.Quantum.Op ι
  | 0, _xs, _gs =>
      1
  | k + 1, xs, gs =>
      ((gHatIdxMeas params family (xs 0)).toSubMeas).outcome (gs 0) *
        gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) (gHatTupleOutcomeTail gs)

/-- The total half-product
`\sum_{g_1,\dots,g_k} \widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k}`. -/
noncomputable def gHatHalfProductTotalOperator (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → MIPStarRE.Quantum.Op ι
  | 0, _xs =>
      1
  | k + 1, xs =>
      ((gHatIdxMeas params family (xs 0)).toSubMeas).total *
        gHatHalfProductTotalOperator params family k (pointTupleTail xs)

/-- The cyclically rotated half-product
`\widehat G^{x_2}_{g_2} \cdots \widehat G^{x_k}_{g_k} \widehat G^{x_1}_{g_1}`. -/
noncomputable def gHatRotatedHalfProductOutcomeOperator (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → MIPStarRE.Quantum.Op ι
  | 0, _xs, _gs =>
      1
  | k + 1, xs, gs =>
      gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) (gHatTupleOutcomeTail gs) *
        ((gHatIdxMeas params family (xs 0)).toSubMeas).outcome (gs 0)

/-- The total cyclically rotated half-product. -/
noncomputable def gHatRotatedHalfProductTotalOperator (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → MIPStarRE.Quantum.Op ι
  | 0, _xs =>
      1
  | k + 1, xs =>
      gHatHalfProductTotalOperator params family k (pointTupleTail xs) *
        ((gHatIdxMeas params family (xs 0)).toSubMeas).total

/-- Splitting a nonempty completed-outcome tuple into its first outcome and tail. -/
def gHatTupleOutcomeConsEquiv' (params : Parameters) [FieldModel params.q] (k : ℕ) :
    GHatTupleOutcome params (k + 1) ≃ GHatOutcome params × GHatTupleOutcome params k where
  toFun gs := (gs 0, gHatTupleOutcomeTail gs)
  invFun p := Fin.cons p.1 p.2
  left_inv gs := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv p := by
    cases p
    rfl

/-- The total operator of the ordered half-product is always the identity. -/
lemma gHatHalfProductTotalOperator_eq_one (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ k (xs : PointTuple params k), gHatHalfProductTotalOperator params family k xs = 1
  | 0, _xs => by
      simp [gHatHalfProductTotalOperator]
  | k + 1, xs => by
      rw [gHatHalfProductTotalOperator]
      simp [gHatIdxMeas, completeSubMeas,
        gHatHalfProductTotalOperator_eq_one params family k (pointTupleTail xs)]



end MIPStarRE.LDT.Pasting

end

end LIDT


