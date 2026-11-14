-- Prove2me | Definitions.Def_OAIQ246W001
-- name    : OAIQ246W001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T07:12:45.900363+00:00
-- url     : https://prove2.me/theorems/18712b75-c315-4b01-9b4f-745fed815d0b
-- title:
--   Definitions bundle OAIQ246W001 of the split of OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any` and `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite`, carved from OpenAI's openai/math development (OpenAI, *Weak pure infiniteness and O-infinity absorption (result family 303)*, OpenAI Math Release, September 25, 2026, result family 303, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 277 declarations of OpenAI's Lean: 123 definitions, 1 inductive type or structure, 29 instances and 124 theorems. The definitions and types are `OAI.WeakPureInfiniteness.FreeLetter`, `OAI.WeakPureInfiniteness.FreeTwo`, `OAI.WeakPureInfiniteness.GroupHilbert`, `OAI.WeakPureInfiniteness.HilbertValued.HilbertSum`, `OAI.WeakPureInfiniteness.HilbertValued.fellUnitary`, `OAI.WeakPureInfiniteness.HilbertValued.l2Diagonal`, `OAI.WeakPureInfiniteness.HilbertValued.l2Reindex`, `OAI.WeakPureInfiniteness.HilbertValued.permutationSum`, `OAI.WeakPureInfiniteness.HilbertValued.twistedRegular`, `OAI.WeakPureInfiniteness.HilbertVector`, `OAI.WeakPureInfiniteness.IsClosedInner`, `OAI.WeakPureInfiniteness.NonUnitalRepresentationIrreducible`, `OAI.WeakPureInfiniteness.OrthogonalPerturbationData`, `OAI.WeakPureInfiniteness.RepresentationInvariant`, `OAI.WeakPureInfiniteness.RepresentationIrreducible`, `OAI.WeakPureInfiniteness.SmallCStarCarrier`, `OAI.WeakPureInfiniteness.algebraPolynomial`, `OAI.WeakPureInfiniteness.algebraWord`, `OAI.WeakPureInfiniteness.algebraicIdealSpan`, `OAI.WeakPureInfiniteness.algebraicIdealSubalgebra`, `OAI.WeakPureInfiniteness.annihilatorStates`, `OAI.WeakPureInfiniteness.boundedCutFunction`, `OAI.WeakPureInfiniteness.clipFunction`, `OAI.WeakPureInfiniteness.columnCoreFunction`, `OAI.WeakPureInfiniteness.columnMetricFunction`, `OAI.WeakPureInfiniteness.completedGroupOperator`, `OAI.WeakPureInfiniteness.completedGroupUnitary`, `OAI.WeakPureInfiniteness.cstarClip`, `OAI.WeakPureInfiniteness.diagonalCoefficient`, `OAI.WeakPureInfiniteness.diagonalHom`, `OAI.WeakPureInfiniteness.extendUnitaryOn`, `OAI.WeakPureInfiniteness.fiberDiagonal`, `OAI.WeakPureInfiniteness.finiteContinuousEndAlgEquiv`, `OAI.WeakPureInfiniteness.finiteDeletion`, `OAI.WeakPureInfiniteness.finiteDiagonalVector`, `OAI.WeakPureInfiniteness.finiteGroupSpatialDiagonal`, `OAI.WeakPureInfiniteness.finiteLeftRegular`, `OAI.WeakPureInfiniteness.finiteLeftRegularIsometry`, `OAI.WeakPureInfiniteness.freeBallTranslation`, `OAI.WeakPureInfiniteness.freeFiniteQuotient` and 84 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `WeakInfiniteness_AnnihilatorStates`, `WeakInfiniteness_BoundedImplementation`, `WeakInfiniteness_CStarClosedRange`, `WeakInfiniteness_Clipping`, `WeakInfiniteness_ColumnNormalization`, `WeakInfiniteness_CuntzCopies`, `WeakInfiniteness_CutImplementation`, `WeakInfiniteness_CyclicOrbit`, `WeakInfiniteness_FellAbsorption`, `WeakInfiniteness_FiniteComparison`, `WeakInfiniteness_FiniteCoordinates`, `WeakInfiniteness_FiniteCoupling`, `WeakInfiniteness_FiniteDiagonalState`, `WeakInfiniteness_FiniteGroupTensor`, `WeakInfiniteness_FiniteUnitaryLog`, `WeakInfiniteness_FourColumnNorm`, `WeakInfiniteness_FreeFiniteQuotients`, `WeakInfiniteness_FreeFiniteRepresentations`, `WeakInfiniteness_FreeTwistedNorm`, `WeakInfiniteness_GroupRegular`, `WeakInfiniteness_Hereditary`, `WeakInfiniteness_IdealComparison`, `WeakInfiniteness_IdealSpan`, `WeakInfiniteness_InnerSubalgebras`, `WeakInfiniteness_Intertwining`, `WeakInfiniteness_InvariantSubspaces`, `WeakInfiniteness_LiftedHilbert`, `WeakInfiniteness_MatrixCutToolkit`, `WeakInfiniteness_MatrixHilbert`, `WeakInfiniteness_MatrixMaps`, `WeakInfiniteness_NonUnitalGroupTensor`, `WeakInfiniteness_NonunitalSpectralTools2`, `WeakInfiniteness_PairUnitary`, `WeakInfiniteness_PolynomialSpan`, `WeakInfiniteness_PrimitiveIdealTest`, `WeakInfiniteness_ProductRepresentation`, `WeakInfiniteness_PureStates`, `WeakInfiniteness_RectangularCStar`, `WeakInfiniteness_RectangularComparison`, `WeakInfiniteness_RectangularPolar`, `WeakInfiniteness_ReducedGroupAlgebra`, `WeakInfiniteness_ReducingColumns`, `WeakInfiniteness_ScalarDiagonal`, `WeakInfiniteness_SeparationCoverage`, `WeakInfiniteness_SeparationFourColumns`, `WeakInfiniteness_SeparationPreassembly`, `WeakInfiniteness_SeparationScalar`, `WeakInfiniteness_SmallCStar`, `WeakInfiniteness_SpectralCut`, `WeakInfiniteness_SpectralDeletion`, `WeakInfiniteness_SpectralWindows`, `WeakInfiniteness_StatePullback`, `WeakInfiniteness_SupportedCorner`, `WeakInfiniteness_SupportedExact`, `WeakInfiniteness_TensorHilbertSum`, `WeakInfiniteness_TensorIdealCut`, `WeakInfiniteness_TensorMatrixNorm`, `WeakInfiniteness_ULiftCStar`, `WeakInfiniteness_UniformModels`, `WeakInfiniteness_UnitizationExact`, `WeakInfiniteness_UniversalMapping`, `WeakInfiniteness_VectorStates`, `WeakInfiniteness_WordCompression`.
--
--   **Imports.** It imports the published bundle `Def_ExactInfiniteness`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ246W003` and `OAIQ246W004`; the statements `OAI.WeakPureInfiniteness.exists_core_perturbationData`, `OAI.WeakPureInfiniteness.exists_orthogonal_detected_pair`, `OAI.WeakPureInfiniteness.exists_separation_cores`, `OAI.WeakPureInfiniteness.exists_uniform_reducing_model` and `OAI.WeakPureInfiniteness.separation_core_comparisons`; the proofs of `OAI.WeakPureInfiniteness.exists_core_perturbationData`, `OAI.WeakPureInfiniteness.exists_orthogonal_detected_pair`, `OAI.WeakPureInfiniteness.exists_separation_cores` and `OAI.WeakPureInfiniteness.exists_uniform_reducing_model`.
-- source:
--   OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 303; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-pure-infiniteness-and-O-infinity-absorption-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_ExactInfiniteness

section
-- module Solutions.OAIQ246_WI.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
/-- d13f23b's `BorelSpace Circle`, for `circleMeasurableSpace`. -/
theorem circleBorelSpace : @BorelSpace Circle _ circleMeasurableSpace :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CStarClosedRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal

namespace WeakPureInfiniteness

lemma starHom_continuous {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) : Continuous φ := by
  let f := φ.toAlgHom.toLinearMap.mkContinuous 1 (by
    intro x
    change ‖φ x‖ ≤ 1 * ‖x‖
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le φ x)
  exact f.continuous

lemma clipScale_den_pos {M : ℝ} (hM : 0 < M) (t : ℝ) :
    0 < Real.sqrt (max (M ^ 2) t) :=
  Real.sqrt_pos.mpr ((sq_pos_of_pos hM).trans_le (le_max_left _ _))

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_PureStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology ComplexOrder

section States

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def realStateSpace : Set (WeakDual ℝ (selfAdjoint A)) :=
  {f | ‖WeakDual.toStrongDual f‖ ≤ 1 ∧ f 1=1}

variable {A}

def realStateEvaluation (b : selfAdjoint A) : WeakDual ℝ (selfAdjoint A) →L[ℝ] ℝ where
  toFun f := f b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := WeakDual.eval_continuous b

end States

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_VectorStates
attribute [-instance] _root_.OAI.WeakPureInfiniteness.completedTensorCStar _root_.OAI.WeakPureInfiniteness.hilbertOperatorsCStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology ComplexOrder InnerProductSpace

section VectorStates

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def representationVectorFunctional (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    selfAdjoint A →L[ℝ] ℝ where
  toFun b := (inner ℂ ξ (π (b : A) ξ)).re
  map_add' b c := by simp
  map_smul' r b := by
    change (inner ℂ ξ (π (r • (b : A)) ξ)).re=r • (inner ℂ ξ (π (b : A) ξ)).re
    rw [map_real_smul π (starHom_continuous π)]
    simp
  cont := by
    have hπ : Continuous π := starHom_continuous π
    fun_prop

end VectorStates

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_InvariantSubspaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def RepresentationInvariant (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : Submodule ℂ H) : Prop :=
  ∀ a : A,∀ x ∈ S,π a x ∈ S

def RepresentationIrreducible (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∀ S : Submodule ℂ H,IsClosed (S : Set H) → RepresentationInvariant π S → S=⊥ ∨ S=⊤

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_AnnihilatorStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def annihilatorStates (S : Set A) : Set (WeakDual ℝ (selfAdjoint A)) :=
  {f | f ∈ realStateSpace A ∧ ∀ x ∈ S,∀ a : A,
    f ⟨star (x*a)*(x*a),(star_mul_self_nonneg (x*a)).isSelfAdjoint⟩=0}

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_Hereditary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology

open Filter

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def principalRightIdeal (a : A) : Submodule ℂ A :=
  (LinearMap.range (LinearMap.mulLeft ℂ a)).topologicalClosure

instance instIsClosedCoeSubmoduleComplexPrincipalRightIdeal (a : A) : IsClosed (principalRightIdeal a : Set A) :=
  Submodule.isClosed_topologicalClosure _

instance instCompleteSpaceSubtypeMemSubmoduleComplexPrincipalRightIdeal (a : A) : CompleteSpace (principalRightIdeal a) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

def principalRightMap (a : A) : A →ₗ[ℂ] principalRightIdeal a :=
  (LinearMap.mulLeft ℂ a).codRestrict _ (fun b =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ b))

def sandwichSubalgebra (h : A) (hh : IsSelfAdjoint h) : NonUnitalStarSubalgebra ℂ A where
  carrier := Set.range (fun b : A => h*b*h)
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨b, rfl⟩ ⟨c, rfl⟩
    exact ⟨b+c, by noncomm_ring⟩
  smul_mem' := by
    rintro c _ ⟨b, rfl⟩
    exact ⟨c • b, by simp only [mul_smul_comm, smul_mul_assoc]⟩
  mul_mem' := by
    rintro _ _ ⟨b, rfl⟩ ⟨c, rfl⟩
    exact ⟨b*h*h*c, by noncomm_ring⟩
  star_mem' := by
    rintro _ ⟨b, rfl⟩
    exact ⟨star b, by simp only [star_mul, hh.star_eq]; noncomm_ring⟩

def hereditarySubalgebra (h : A) (hh : IsSelfAdjoint h) : NonUnitalStarSubalgebra ℂ A :=
  (sandwichSubalgebra h hh).topologicalClosure

instance instIsClosedCoeNonUnitalStarSubalgebraComplexHereditarySubalgebra (h : A) (hh : IsSelfAdjoint h) :
    IsClosed (hereditarySubalgebra h hh : Set A) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

instance instCompleteSpaceSubtypeMemNonUnitalStarSubalgebraComplexHereditarySubalgebra (h : A) (hh : IsSelfAdjoint h) : CompleteSpace (hereditarySubalgebra h hh) :=
  (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).isComplete.completeSpace_coe

def residual (e h : A) := h - e*h - h*e + e*h*e

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_RectangularCStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakPureInfiniteness

open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder


open scoped CStarAlgebra InnerProductSpace NNReal

open CStarMatrix CStarModule ContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype n] in
lemma rectangular_conjTranspose_conjTranspose (M : CStarMatrix m n A) :
    M.conjTranspose.conjTranspose = M := by
  ext i j
  simp only [CStarMatrix.conjTranspose_apply, star_star]


end WeakPureInfiniteness

end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_RectangularPolar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

local instance matrixRealModule {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {n : Type*} [Fintype n] :
    Module ℝ (CStarMatrix n n A) := Module.complexToReal _

section RectangularPolar

open scoped Topology CStarAlgebra

open Filter

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype k] in
lemma rectangular_star_mul (M : CStarMatrix m n A) (N : CStarMatrix n k A) :
    (M*N).conjTranspose = N.conjTranspose*M.conjTranspose :=
  Matrix.conjTranspose_mul _ _

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] in
lemma rectangular_mul_assoc {l : Type*} (L : CStarMatrix m n A)
    (M : CStarMatrix n k A) (N : CStarMatrix k l A) :
    (L*M)*N = L*(M*N) := Matrix.mul_assoc _ _ _

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype k] in
def rectangularLeftMap (u : CStarMatrix m n A) :
    CStarMatrix n n A →ₗ[ℂ] CStarMatrix m n A where
  toFun b := u*b
  map_add' := CStarMatrix.mul_add u
  map_smul' c b := CStarMatrix.mul_smul u c b

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype k] in
def rectangularRightIdeal (u : CStarMatrix m n A) : Submodule ℂ (CStarMatrix m n A) :=
  (rectangularLeftMap u).range.topologicalClosure

def rectangularPolar (u : CStarMatrix m n A) :
    principalRightIdeal (CFC.sqrt (u.conjTranspose*u)) →L[ℂ] CStarMatrix m n A :=
  (rectangularLeftMap u).extendOfNorm (principalRightMap (CFC.sqrt (u.conjTranspose*u)))

end RectangularPolar

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SpectralCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

open scoped Topology CStarAlgebra

def spectralRamp (θ s : ℝ) : ℝ := min 1 (max 0 ((s-θ)/θ))

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CutImplementation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology CStarAlgebra

local instance matrixRealModuleCut {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {n : Type*} [Fintype n] :
    Module ℝ (CStarMatrix n n A) := Module.complexToReal _

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_MatrixCutToolkit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology CStarAlgebra

local instance matrixRealModuleToolkit {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {n : Type*} [Fintype n] :
    Module ℝ (CStarMatrix n n A) := Module.complexToReal _

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def diagonalHom (n : ℕ) : A →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) A where
  toFun := diagonalCopies n
  map_add' a b := by
    ext i j
    simp only [diagonalCopies, CStarMatrix.ofMatrix_apply, Matrix.diagonal_apply,
      CStarMatrix.add_apply]
    split_ifs <;> simp
  map_zero' := by ext i j; simp [diagonalCopies]
  map_mul' a b := by
    change Matrix.diagonal (fun _ : Fin n => a*b) =
      Matrix.diagonal (fun _ : Fin n => a)*Matrix.diagonal (fun _ : Fin n => b)
    rw [Matrix.diagonal_mul_diagonal]
  map_smul' c a := by
    ext i j
    simp only [diagonalCopies, CStarMatrix.ofMatrix_apply, Matrix.diagonal_apply,
      CStarMatrix.smul_apply]
    split_ifs <;> simp
  map_star' a := by
    ext i j
    simp only [diagonalCopies, CStarMatrix.ofMatrix_apply, Matrix.diagonal_apply,
      CStarMatrix.star_eq_conjTranspose, CStarMatrix.conjTranspose_apply]
    split_ifs <;> simp_all

lemma diagonalCopies_nonneg (n : ℕ) {a : A} (ha : 0 ≤ a) : 0 ≤ diagonalCopies n a :=
by
  have he : diagonalCopies n a = star ((diagonalHom n) (CFC.sqrt a))*
      (diagonalHom n) (CFC.sqrt a) := by
    rw [← map_star, ← map_mul, (CFC.sqrt_nonneg a).star_eq, CFC.sqrt_mul_sqrt_self a ha]
    rfl
  rw [he]
  exact star_mul_self_nonneg _

def positiveCut (δ : ℝ) (a : A) : A := cfcₙ (fun s : ℝ => max (s-δ) 0) a

lemma positiveCut_nonneg (δ : ℝ) (a : A) : 0 ≤ positiveCut δ a :=
  cfcₙ_nonneg (fun _ _ => le_max_right _ _)

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_MatrixHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

abbrev HilbertVector (n H : Type*) [NormedAddCommGroup H] := PiLp 2 (fun _ : n => H)

def matrixAction (M : CStarMatrix m n (H →L[ℂ] H)) :
    HilbertVector n H →L[ℂ] HilbertVector m H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : m => H)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun i => ∑ j, (M i j).comp (ContinuousLinearMap.proj j)).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => H)).toContinuousLinearMap)

omit [CompleteSpace H] [Fintype m] in
@[simp]

lemma matrixAction_apply (M : CStarMatrix m n (H →L[ℂ] H))
    (x : HilbertVector n H) (i : m) : matrixAction M x i = ∑ j, M i j (x j) := by
  simp [matrixAction]

omit [CompleteSpace H] in
lemma matrixAction_add (M N : CStarMatrix m n (H →L[ℂ] H)) :
    matrixAction (M+N)=matrixAction M+matrixAction N := by
  ext x i
  simp [matrixAction_apply, Finset.sum_add_distrib]

omit [CompleteSpace H] in
lemma matrixAction_smul (c : ℂ) (M : CStarMatrix m n (H →L[ℂ] H)) :
    matrixAction (c • M)=c • matrixAction M := by
  ext x i
  simp [matrixAction_apply, Finset.smul_sum]

omit [CompleteSpace H] [Fintype m] in
lemma matrixAction_mul (M : CStarMatrix m n (H →L[ℂ] H))
    (N : CStarMatrix n k (H →L[ℂ] H)) :
    matrixAction (M*N)=(matrixAction M).comp (matrixAction N) := by
  ext x i
  simp only [matrixAction_apply, CStarMatrix.mul_apply, sum_apply,
    mul_apply_eq_comp, ContinuousLinearMap.comp_apply, map_sum]
  rw [Finset.sum_comm]

lemma matrixAction_star (M : CStarMatrix m n (H →L[ℂ] H)) :
    matrixAction M.conjTranspose=(matrixAction M).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply, matrixAction_apply, CStarMatrix.conjTranspose_apply,
    sum_inner, inner_sum, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]
  rw [Finset.sum_comm]

def matrixActionHom : CStarMatrix n n (H →L[ℂ] H) →⋆ₙₐ[ℂ]
    (HilbertVector n H →L[ℂ] HilbertVector n H) where
  toFun := matrixAction
  map_zero' := by ext x i; simp
  map_add' := matrixAction_add
  map_smul' := matrixAction_smul
  map_mul' := matrixAction_mul
  map_star' := matrixAction_star

variable {A : Type*} [NonUnitalCStarAlgebra A]

def matrixRepresentation (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (n : Type*) [Fintype n] :
    CStarMatrix n n A →⋆ₙₐ[ℂ] (HilbertVector n H →L[ℂ] HilbertVector n H) :=
  matrixActionHom.comp (CStarMatrix.mapₙₐ π)

@[simp]
lemma matrixRepresentation_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (M : CStarMatrix n n A) (x : HilbertVector n H) (i : n) :
    matrixRepresentation π n M x i = ∑ j, π (M i j) (x j) := by
  change matrixAction ((CStarMatrix.mapₙₐ π) M) x i = _
  rw [matrixAction_apply]
  rfl

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_MatrixMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra ComplexOrder

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

def rectangularMap (φ : A →⋆ₙₐ[ℂ] B) (M : CStarMatrix m n A) : CStarMatrix m n B := M.map φ

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] [Fintype m] [Fintype n] in
@[simp] lemma rectangularMap_apply (φ : A →⋆ₙₐ[ℂ] B) (M : CStarMatrix m n A) (i : m) (j : n) :
    rectangularMap φ M i j = φ (M i j) := rfl

def matrixScalarRight (M : CStarMatrix m n A) (D : CStarMatrix n k ℂ) : CStarMatrix m k A :=
  fun i j => ∑ l, D l j • M i l

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype k] in
@[simp] lemma matrixScalarRight_apply (M : CStarMatrix m n A) (D : CStarMatrix n k ℂ) (i : m) (j : k) :
    matrixScalarRight M D i j = ∑ l, D l j • M i l := rfl

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SupportedCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

variable {A : Type*} [NonUnitalCStarAlgebra A]

def supportedAlgebra (e : A) (he : IsSelfAdjoint e) : NonUnitalStarSubalgebra ℂ A where
  carrier := {z | e*z=z ∧ z*e=z}
  zero_mem' := by simp
  add_mem' hx hy := by
    change e*(_+_)=_ ∧ (_+_)*e=_
    simp only [mul_add, add_mul, hx.1, hx.2, hy.1, hy.2, and_self]
  mul_mem' hx hy := by
    constructor
    · rw [← mul_assoc, hx.1]
    · rw [mul_assoc, hy.2]
  smul_mem' c x hx := by
    change e*(c • x)=_ ∧ (c • x)*e=_
    simp only [mul_smul_comm, smul_mul_assoc, hx.1, hx.2, and_self]
  star_mem' hx := by
    constructor
    · simpa only [star_mul, he.star_eq] using congrArg star hx.2
    · simpa only [star_mul, he.star_eq] using congrArg star hx.1

lemma supportedAlgebra_closed (e : A) (he : IsSelfAdjoint e) :
    IsClosed (supportedAlgebra e he : Set A) :=
  (isClosed_eq (by fun_prop) continuous_id).inter (isClosed_eq (by fun_prop) continuous_id)

instance supportedAlgebra_complete (e : A) (he : IsSelfAdjoint e) :
    CompleteSpace (supportedAlgebra e he) := (supportedAlgebra_closed e he).completeSpace_coe

def matrixSingletonHom : CStarMatrix (Fin 1) (Fin 1) A →⋆ₙₐ[ℂ] A where
  toFun x := x 0 0
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl
  map_mul' x y := by
    change (∑ i : Fin 1, x 0 i*y i 0)=x 0 0*y 0 0
    exact Fin.sum_univ_one _

variable {n : Type*} [Fintype n]

lemma rectangular_mul_zero_support {m k : Type*} (M : CStarMatrix m n A) :
    M*(0 : CStarMatrix n k A)=0 := Matrix.mul_zero M

lemma rectangular_zero_mul_support {m k : Type*} (M : CStarMatrix n k A) :
    (0 : CStarMatrix m n A)*M=0 := Matrix.zero_mul M

lemma rectangular_mul_add_support {m k : Type*} (M : CStarMatrix m n A)
    (N P : CStarMatrix n k A) : M*(N+P)=M*N+M*P := Matrix.mul_add M N P

lemma rectangular_add_mul_support {m k : Type*} (M N : CStarMatrix m n A)
    (P : CStarMatrix n k A) : (M+N)*P=M*P+N*P := Matrix.add_mul M N P

lemma rectangular_mul_smul_support {m k : Type*} (M : CStarMatrix m n A)
    (c : ℂ) (N : CStarMatrix n k A) : M*(c • N)=c • (M*N) := Matrix.mul_smul M c N

lemma rectangular_smul_mul_support {m k : Type*} (M : CStarMatrix m n A)
    (c : ℂ) (N : CStarMatrix n k A) : (c • M)*N=c • (M*N) := Matrix.smul_mul c M N

variable [PartialOrder A] [StarOrderedRing A]

def supportedCompression (U : CStarMatrix (Fin 1) n A)
    (e : CStarMatrix n n A) (he : IsSelfAdjoint e) (hU : U.conjTranspose*U=e) :
    supportedAlgebra e he →⋆ₙₐ[ℂ] CStarMatrix (Fin 1) (Fin 1) A where
  toFun z := U*z.val*U.conjTranspose
  map_zero' := by change U*0*U.conjTranspose=0; rw [rectangular_mul_zero_support, rectangular_zero_mul_support]
  map_add' x y := by
    change U*(x.val+y.val)*U.conjTranspose=U*x.val*U.conjTranspose+U*y.val*U.conjTranspose
    rw [rectangular_mul_add_support, rectangular_add_mul_support]
  map_smul' c z := by
    change U*(c • z.val)*U.conjTranspose=c • (U*z.val*U.conjTranspose)
    rw [rectangular_mul_smul_support, rectangular_smul_mul_support]
  map_mul' x y := by
    change U*(x.val*y.val)*U.conjTranspose=(U*x.val*U.conjTranspose)*(U*y.val*U.conjTranspose)
    simp only [rectangular_mul_assoc]
    rw [← rectangular_mul_assoc U.conjTranspose U, hU,
      ← rectangular_mul_assoc e y.val, y.property.1]
  map_star' z := by
    change U*z.val.conjTranspose*U.conjTranspose=(U*z.val*U.conjTranspose).conjTranspose
    rw [rectangular_star_mul, rectangular_star_mul, rectangular_conjTranspose_conjTranspose,
      rectangular_mul_assoc]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_BoundedImplementation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology CStarAlgebra

def boundedCutFunction (r s : ℝ) : ℝ := Real.sqrt (max (s-r) 0) / max r s

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_Clipping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped ComplexOrder

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def clipFunction (t : ℝ) : ℝ := (max 1 (Real.sqrt t))⁻¹

def cstarClip (v : B) : B := v*cfc clipFunction (star v*v)

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_Intertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology CStarAlgebra

section

variable {B : Type*} [CStarAlgebra B]

local instance instAlgebraRealProd_solutions : Algebra ℝ (B × B) := Algebra.complexToReal

def intertwiningAlgebra (D : B) : StarSubalgebra ℂ (B × B) where
  carrier := {z | z.1*D=D*z.2 ∧ star D*z.1=z.2*star D}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    rintro ⟨x₁,x₂⟩ ⟨y₁,y₂⟩ ⟨hx,hx'⟩ ⟨hy,hy'⟩
    constructor <;> dsimp at *
    · simp only [add_mul,mul_add,hx,hy]
    · simp only [add_mul,mul_add,hx',hy']
  mul_mem' := by
    rintro ⟨x₁,x₂⟩ ⟨y₁,y₂⟩ ⟨hx,hx'⟩ ⟨hy,hy'⟩
    constructor <;> dsimp at *
    · rw [mul_assoc,hy,← mul_assoc,hx,mul_assoc]
    · rw [← mul_assoc,hx',mul_assoc,hy',← mul_assoc]
  algebraMap_mem' := by intro c; simp only [Set.mem_ofPred_eq,Prod.algebraMap_apply]; constructor <;> simp [Algebra.commutes]
  star_mem' := by
    rintro ⟨x₁,x₂⟩ ⟨hx,hx'⟩
    constructor <;> dsimp at *
    · simpa only [star_mul,star_star] using congrArg star hx'
    · simpa only [star_mul,star_star] using congrArg star hx

instance intertwiningAlgebra_isClosed (D : B) : IsClosed (intertwiningAlgebra D : Set (B × B)) := by
  change IsClosed {z : B × B | z.1*D=D*z.2 ∧ star D*z.1=z.2*star D}
  exact (isClosed_eq (by fun_prop) (by fun_prop)).inter (isClosed_eq (by fun_prop) (by fun_prop))

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ColumnNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology CStarAlgebra

section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def columnMetricFunction (τ s : ℝ) : ℝ := (max τ (Real.sqrt s))⁻¹

def columnCoreFunction (τ s : ℝ) : ℝ := max (Real.sqrt s-τ) 0

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CuntzCopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype n] [Fintype k] [Fintype l] in
def matrixSubmatrix (e : m → n) (f : k → l) (M : CStarMatrix n l A) : CStarMatrix m k A :=
  fun i j => M (e i) (f j)

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CyclicOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

universe u v

open scoped ComplexOrder InnerProductSpace Topology

section NonUnital

variable {A : Type u} {H : Type v} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def NonUnitalRepresentationIrreducible (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∀ S : Submodule ℂ H,IsClosed (S : Set H) →
    (∀ a : A,∀ x ∈ S,π a x ∈ S) → S=⊥ ∨ S=⊤

end NonUnital

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_GroupRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace

namespace WeakPureInfiniteness

abbrev GroupHilbert (G : Type*) : Type _ := lp (fun _ : G => ℂ) 2

variable {G K : Type*}

lemma mem_l2_reindex (e : G ≃ K) (ξ : GroupHilbert K) :
    Memℓp (fun g => ξ (e g)) 2 := by
  apply (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mpr
  have hs : Summable (fun k => ‖ξ k‖ ^ (2 : ℝ≥0∞).toReal) :=
    Memℓp.summable (by norm_num) ξ.property
  exact e.summable_iff.mpr hs

def l2Reindex (e : G ≃ K) : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert K where
  toFun ξ := ⟨fun k => ξ (e.symm k), mem_l2_reindex e.symm ξ⟩
  invFun ξ := ⟨fun g => ξ (e g), mem_l2_reindex e ξ⟩
  left_inv ξ := by ext g; simp
  right_inv ξ := by ext k; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' ξ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
    congr 1
    exact e.symm.tsum_eq (fun g => ‖ξ g‖ ^ (2 : ℝ≥0∞).toReal)

@[simp]
lemma l2Reindex_apply (e : G ≃ K) (ξ : GroupHilbert G) (k : K) :
    l2Reindex e ξ k = ξ (e.symm k) := rfl

variable [Group G]

def leftRegularIsometry : G →* (GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert G) where
  toFun s := l2Reindex (Equiv.mulLeft s)
  map_one' := by
    ext ξ g
    change ξ ((1 : G)⁻¹ * g) = ξ g
    simp
  map_mul' s t := by
    ext ξ g
    change ξ ((s * t)⁻¹ * g) = ξ (t⁻¹ * (s⁻¹ * g))
    simp [mul_assoc]

def rightRegularIsometry : G →* (GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert G) where
  toFun s := l2Reindex (Equiv.mulRight s⁻¹)
  map_one' := by
    ext ξ g
    change ξ (g * ((1 : G)⁻¹)⁻¹) = ξ g
    simp
  map_mul' s t := by
    ext ξ g
    change ξ (g * ((s * t)⁻¹)⁻¹) = ξ ((g * (s⁻¹)⁻¹) * (t⁻¹)⁻¹)
    simp [mul_assoc]

def leftRegular : G →* unitary (GroupHilbert G →L[ℂ] GroupHilbert G) :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp leftRegularIsometry

def rightRegular : G →* unitary (GroupHilbert G →L[ℂ] GroupHilbert G) :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp rightRegularIsometry

@[simp]
lemma leftRegular_apply (s g : G) (ξ : GroupHilbert G) :
    (leftRegular s : GroupHilbert G →L[ℂ] GroupHilbert G) ξ g = ξ (s⁻¹ * g) := rfl

@[simp]
lemma rightRegular_apply (s g : G) (ξ : GroupHilbert G) :
    (rightRegular s : GroupHilbert G →L[ℂ] GroupHilbert G) ξ g = ξ (g * s) := by
  change ξ (g * (s⁻¹)⁻¹) = _
  rw [inv_inv]

def groupInversion : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert G := l2Reindex (Equiv.inv G)

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FellAbsorption
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness.HilbertValued

abbrev HilbertSum (G H : Type*) [NormedAddCommGroup H] : Type _ := lp (fun _ : G => H) 2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {G K : Type*}

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma mem_l2_reindex (e : G ≃ K) (ξ : HilbertSum K H) :
    Memℓp (fun g => ξ (e g)) 2 := by
  apply (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mpr
  have hs : Summable (fun k => ‖ξ k‖ ^ (2 : ℝ≥0∞).toReal) :=
    Memℓp.summable (by norm_num) ξ.property
  exact e.summable_iff.mpr hs

def l2Reindex (e : G ≃ K) : HilbertSum G H ≃ₗᵢ[ℂ] HilbertSum K H where
  toFun ξ := ⟨fun k => ξ (e.symm k), mem_l2_reindex e.symm ξ⟩
  invFun ξ := ⟨fun g => ξ (e g), mem_l2_reindex e ξ⟩
  left_inv ξ := by ext g; simp
  right_inv ξ := by ext k; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' ξ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
    congr 1
    exact e.symm.tsum_eq (fun g => ‖ξ g‖ ^ (2 : ℝ≥0∞).toReal)

omit [CompleteSpace H] in
@[simp]

lemma l2Reindex_apply (e : G ≃ K) (ξ : HilbertSum G H) (k : K) :
    l2Reindex e ξ k = ξ (e.symm k) := rfl

section SchurBound

variable {X I : Type*} [Fintype I]

def permutationSum (e : I → X ≃ X) : HilbertSum X H →L[ℂ] HilbertSum X H :=
  ∑ i, (l2Reindex (e i)).toContinuousLinearEquiv.toContinuousLinearMap

end SchurBound

def l2Diagonal {X : Type*} (v : X → H ≃ₗᵢ[ℂ] H) :
    HilbertSum X H ≃ₗᵢ[ℂ] HilbertSum X H where
  toFun ξ := ⟨fun x => v x (ξ x), by
    apply (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mpr
    simpa only [LinearIsometryEquiv.norm_map] using
      (Memℓp.summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) ξ.property)⟩
  invFun ξ := ⟨fun x => (v x).symm (ξ x), by
    apply (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mpr
    simpa only [LinearIsometryEquiv.norm_map] using
      (Memℓp.summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) ξ.property)⟩
  left_inv ξ := by ext x; simp
  right_inv ξ := by ext x; simp
  map_add' ξ η := by ext x; exact map_add (v x) _ _
  map_smul' c ξ := by ext x; exact map_smul (v x) _ _
  norm_map' ξ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
    simp

omit [CompleteSpace H] in
@[simp]

lemma l2Diagonal_apply {X : Type*} (v : X → H ≃ₗᵢ[ℂ] H)
    (ξ : HilbertSum X H) (x : X) : l2Diagonal v ξ x = v x (ξ x) := rfl

omit [CompleteSpace H] in
@[simp]

lemma l2Diagonal_symm_apply {X : Type*} (v : X → H ≃ₗᵢ[ℂ] H)
    (ξ : HilbertSum X H) (x : X) : (l2Diagonal v).symm ξ x = (v x).symm (ξ x) := rfl

variable [Group G]

def fellUnitary (π : G →* H ≃ₗᵢ[ℂ] H) : HilbertSum G H ≃ₗᵢ[ℂ] HilbertSum G H :=
  l2Diagonal π

def twistedRegular (π : G →* H ≃ₗᵢ[ℂ] H) (s : G) :
    HilbertSum G H →L[ℂ] HilbertSum G H :=
  ((l2Reindex (Equiv.mulLeft s)).trans (l2Diagonal (fun _ => π s))).toContinuousLinearEquiv
    |>.toContinuousLinearMap

omit [CompleteSpace H] in
@[simp]

lemma twistedRegular_apply (π : G →* H ≃ₗᵢ[ℂ] H) (s g : G) (ξ : HilbertSum G H) :
    twistedRegular π s ξ g = π s (ξ (s⁻¹ * g)) := rfl

end WeakPureInfiniteness.HilbertValued
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_InnerSubalgebras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology

variable {A : Type*} [NonUnitalCStarAlgebra A]

def IsClosedInner (D : NonUnitalStarSubalgebra ℂ A) : Prop :=
    IsClosed (D : Set A) ∧ ∀ a ∈ D, ∀ b ∈ D, ∀ x : A, a*x*b ∈ D

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_RectangularComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology CStarAlgebra

local instance matrixRealModuleComparison {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {n : Type*} [Fintype n] :
    Module ℝ (CStarMatrix n n A) := Module.complexToReal _

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FiniteComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
def fiberDiagonal {m : ℕ} (x : Fin m → A) : CStarMatrix (Fin m) (Fin m) A :=
  CStarMatrix.ofMatrix (Matrix.diagonal x)

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ReducingColumns
attribute [-instance] _root_.OAI.WeakPureInfiniteness.completedTensorCStar _root_.OAI.WeakPureInfiniteness.hilbertOperatorsCStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped InnerProductSpace CStarAlgebra ComplexOrder

variable {A : Type*} [NonUnitalCStarAlgebra A]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

def rectangularRepresentation (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (M : CStarMatrix m n A) :
    HilbertVector n H →L[ℂ] HilbertVector m H := matrixAction (rectangularMap π M)

omit [Fintype m] in
@[simp] lemma rectangularRepresentation_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (M : CStarMatrix m n A) (x : HilbertVector n H) (i : m) :
    rectangularRepresentation π M x i = ∑ j, π (M i j) (x j) := by
  simp [rectangularRepresentation, matrixAction_apply]

omit [CompleteSpace H] in
def vectorTensorLinear (ξ : H) : HilbertVector n ℂ →ₗ[ℂ] HilbertVector n H where
  toFun x := WithLp.toLp 2 (fun i => x i • ξ)
  map_add' x y := by ext i; simp [add_smul]
  map_smul' c x := by ext i; simp [smul_smul]

omit [CompleteSpace H] in
def vectorTensorIsometry (ξ : H) (hξ : ‖ξ‖=1) : HilbertVector n ℂ →ₗᵢ[ℂ] HilbertVector n H where
  toLinearMap := vectorTensorLinear ξ
  norm_map' x := by
    have he : ‖vectorTensorLinear (n := n) ξ x‖^2=‖x‖^2 := by
      simp only [PiLp.norm_sq_eq_of_L2, vectorTensorLinear, LinearMap.coe_mk, AddHom.coe_mk,
        norm_smul, hξ, mul_one]
    nlinarith [norm_nonneg (vectorTensorLinear (n := n) ξ x), norm_nonneg x]

omit [CompleteSpace H] in
@[simp] lemma vectorTensorIsometry_apply (ξ : H) (hξ : ‖ξ‖=1) (x : HilbertVector n ℂ) (i : n) :
    vectorTensorIsometry ξ hξ x i = x i • ξ := rfl

def scalarMatrixAction (D : CStarMatrix m n ℂ) : HilbertVector n H →L[ℂ] HilbertVector m H :=
  rectangularRepresentation (StarAlgHom.ofId ℂ (H →L[ℂ] H)).toNonUnitalStarAlgHom D

omit [Fintype m] in
@[simp] lemma scalarMatrixAction_apply (D : CStarMatrix m n ℂ) (x : HilbertVector n H) (i : m) :
    scalarMatrixAction D x i = ∑ j, D i j • x j := by
  simp [scalarMatrixAction, Algebra.algebraMap_eq_smul_one]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FiniteCoordinates
attribute [-instance] _root_.OAI.WeakPureInfiniteness.completedTensorCStar _root_.OAI.WeakPureInfiniteness.hilbertOperatorsCStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped InnerProductSpace CStarAlgebra ComplexOrder

variable {n : Type*} [Fintype n]

def scalarActionHom : CStarMatrix n n ℂ →⋆ₙₐ[ℂ]
    (HilbertVector n ℂ →L[ℂ] HilbertVector n ℂ) :=
  matrixRepresentation (StarAlgHom.ofId ℂ (ℂ →L[ℂ] ℂ)).toNonUnitalStarAlgHom n

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorMatrixNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

section BasisTensor

variable {n H K : Type*} [Fintype n]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

lemma norm_eq_of_isometric_intertwining {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (e : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) (S : F →L[ℂ] F)
    (h : ∀ x, e (T x) = S (e x)) : ‖T‖ = ‖S‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [← e.norm_map (T x), h]
    simpa only [e.norm_map] using S.le_opNorm (e x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← h, e.norm_map, e.norm_map]
    exact T.le_opNorm x

end BasisTensor

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorIdealCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology

namespace WeakPureInfiniteness

open Filter Topology

section TensorIdealCut

variable {A : Type u} {C D : Type v} [CStarAlgebra A]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

def kernelAlgebra (q : C →⋆ₙₐ[ℂ] D) : NonUnitalStarSubalgebra ℂ C where
  carrier := {c | q c = 0}
  zero_mem' := map_zero q
  add_mem' hx hy := by change q (_+_) = 0; rw [map_add,hx,hy,add_zero]
  mul_mem' hx _ := by change q (_*_) = 0; rw [map_mul,hx,zero_mul]
  smul_mem' c _ hx := by change q (c • _) = 0; rw [map_smul,hx,smul_zero]
  star_mem' hx := by change q (star _) = 0; rw [map_star,hx,star_zero]

end TensorIdealCut

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UnitizationExact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u

noncomputable section

open scoped TensorProduct ComplexOrder ENNReal

variable {A C D : Type u} [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

def unitizationCharacter : Unitization ℂ A →⋆ₐ[ℂ] ℂ where
  toAlgHom := Unitization.fstHom ℂ A
  map_star' _ := rfl

def unitizationScalarEnd : Unitization ℂ A →⋆ₐ[ℂ] Unitization ℂ A :=
  (StarAlgHom.ofId ℂ (Unitization ℂ A)).comp unitizationCharacter

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SupportedExact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u

noncomputable section

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {n : ℕ}

omit [PartialOrder A] [StarOrderedRing A] in
instance supportedAlgebra_isClosed (e : A) (he : IsSelfAdjoint e) :
    IsClosed (supportedAlgebra e he : Set A) := supportedAlgebra_closed e he

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ReducedGroupAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace

namespace WeakPureInfiniteness

variable {G : Type u} [Group G]

instance groupHilbertNontrivial (G : Type u) [Group G] : Nontrivial (GroupHilbert G) := by
  classical
  refine ⟨⟨0, lp.single 2 (1 : G) (1 : ℂ), ?_⟩⟩
  intro h
  have h' := congrArg (fun ξ : GroupHilbert G => ξ 1) h
  simp at h'

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FiniteDiagonalState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

variable (F : Type*) [Group F] [Fintype F] [DecidableEq F]

noncomputable def finiteLeftRegularIsometry :
    F →* (EuclideanSpace ℂ F ≃ₗᵢ[ℂ] EuclideanSpace ℂ F) where
  toFun s := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.mulLeft s)
  map_one' := by
    ext ξ g
    change ξ ((1 : F)⁻¹ * g) = ξ g
    simp
  map_mul' s t := by
    ext ξ g
    change ξ ((s * t)⁻¹ * g) = ξ (t⁻¹ * (s⁻¹ * g))
    simp [mul_assoc]

noncomputable def finiteLeftRegular : F →* unitary (EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F) :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp (finiteLeftRegularIsometry F)

omit [DecidableEq F] in
@[simp]

lemma finiteLeftRegular_apply (s : F) (ξ : EuclideanSpace ℂ F) (g : F) :
    (finiteLeftRegular F s : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F) ξ g = ξ (s⁻¹ * g) := rfl

@[simp]
lemma finiteLeftRegular_single (s g : F) :
    (finiteLeftRegular F s : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F)
      (EuclideanSpace.single g (1 : ℂ)) = EuclideanSpace.single (s * g) (1 : ℂ) := by
  classical
  exact LinearIsometryEquiv.piLpCongrLeft_single (Equiv.mulLeft s) g 1

noncomputable def finiteDiagonalVector :
    EuclideanSpace ℂ F ⊗[ℂ] EuclideanSpace ℂ F :=
  ∑ g : F, EuclideanSpace.single g (1 : ℂ) ⊗ₜ[ℂ] EuclideanSpace.single g (1 : ℂ)

noncomputable def normalizedFiniteDiagonalVector :
    EuclideanSpace ℂ F ⊗[ℂ] EuclideanSpace ℂ F :=
  ((Real.sqrt (Fintype.card F : ℝ))⁻¹ : ℂ) • finiteDiagonalVector F

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_LiftedHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

universe v

instance uliftInnerProduct {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    InnerProductSpace ℂ (ULift.{v} H) where
  inner x y := inner ℂ x.down y.down
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner x.down
  conj_inner_symm x y := inner_conj_symm x.down y.down
  add_left x y z := inner_add_left x.down y.down z.down
  smul_left x y c := inner_smul_left x.down y.down c

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FiniteGroupTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

section FiniteGroupSpatial

variable {G F : Type u} [Group G] [Group F] [Fintype F] [DecidableEq F]

def finiteGroupSpatialDiagonal (_q : G →* F) :
    ULift.{u+1} (EuclideanSpace ℂ F) ⊗[ℂ] ULift.{u+1} (EuclideanSpace ℂ F) :=
  TensorProduct.congrIsometry (LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm
    (LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm (normalizedFiniteDiagonalVector F)

end FiniteGroupSpatial

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FreeFiniteQuotients
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

open FreeGroup

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def freeWordBall (m : ℕ) : Finset (FreeGroup α) := by
  classical
  exact (Finset.range (m + 1)).biUnion fun k =>
    Finset.univ.image (fun f : Fin k → α × Bool => FreeGroup.mk (List.ofFn f))

lemma mem_freeWordBall (g : FreeGroup α) (m : ℕ) :
    g ∈ freeWordBall m ↔ FreeGroup.norm g ≤ m := by
  classical
  constructor
  · intro hg
    obtain ⟨k, hk, hg'⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hg'
    exact FreeGroup.norm_mk_le.trans (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  · intro hg
    apply Finset.mem_biUnion.mpr
    refine ⟨g.toWord.length, Finset.mem_range.mpr (Nat.lt_succ_of_le hg), ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨fun i => g.toWord.get i, Finset.mem_univ _, ?_⟩
    simpa using (FreeGroup.mk_toWord (x := g))

lemma one_mem_freeWordBall (m : ℕ) : (1 : FreeGroup α) ∈ freeWordBall m := by
  rw [mem_freeWordBall]
  simp

lemma exists_freeBallTranslation (m : ℕ) (a : α) :
    ∃ σ : Equiv.Perm (freeWordBall (α := α) m),
      ∀ (x : freeWordBall (α := α) m), FreeGroup.of a * x.val ∈ freeWordBall m →
        (σ x).val = FreeGroup.of a * x.val := by
  classical
  let D := {x : freeWordBall (α := α) m // FreeGroup.of a * x.val ∈ freeWordBall m}
  let f : D → freeWordBall (α := α) m := fun x => x.val
  let g : D → freeWordBall (α := α) m := fun x => ⟨FreeGroup.of a * x.val.val, x.property⟩
  have hf : Function.Injective f := Subtype.val_injective
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact mul_left_cancel (congrArg Subtype.val h)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨σ, fun x hx => ?_⟩
  exact congrArg Subtype.val (hσ ⟨x, hx⟩)

noncomputable def freeBallTranslation (m : ℕ) (a : α) :
    Equiv.Perm (freeWordBall (α := α) m) :=
  (exists_freeBallTranslation m a).choose

noncomputable def freeFiniteQuotient (m : ℕ) :
    FreeGroup α →* Equiv.Perm (freeWordBall (α := α) m) :=
  FreeGroup.lift (freeBallTranslation m)

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ScalarDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

universe u

section DiagonalPolynomial

variable {G : Type u} [Group G]

def diagonalCoefficient : (G × G →₀ ℂ) →ₗ[ℂ] ℂ := by
  classical
  exact Finsupp.linearCombination ℂ (fun p => if p.1 = p.2 then 1 else 0)

end DiagonalPolynomial

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FreeTwistedNorm
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

abbrev FreeTwo := FreeGroup Bool

abbrev FreeLetter := Bool × Bool

def freeLetter (s : FreeLetter) : FreeTwo :=
  if s.2 then FreeGroup.of s.1 else (FreeGroup.of s.1)⁻¹

def inverseLetter (s : FreeLetter) : FreeLetter := (s.1, !s.2)

@[simp]
lemma freeLetter_inverseLetter (s : FreeLetter) :
    freeLetter (inverseLetter s) = (freeLetter s)⁻¹ := by
  rcases s with ⟨a, b⟩
  cases b <;> simp [freeLetter, inverseLetter]

@[simp]
lemma inverseLetter_inverseLetter (s : FreeLetter) :
    inverseLetter (inverseLetter s) = s := by
  rcases s with ⟨a,b⟩
  cases b <;> rfl

@[simp]
lemma toWord_freeLetter (s : FreeLetter) : (freeLetter s).toWord = [s] := by
  rcases s with ⟨a,b⟩
  cases b <;> simp [freeLetter, FreeGroup.toWord_inv, FreeGroup.invRev]

def freeTreeWeight (g : FreeTwo) : ℝ := (Real.sqrt 3) ^ (- (g.toWord.length : ℤ))

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorHilbertSum
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.uliftInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

section TensorHilbertSum

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def tensorSequence (ξ : H) : GroupHilbert G →L[ℂ] HilbertValued.HilbertSum G H :=
  lp.mapCLM 2 (fun _ => (ContinuousLinearMap.id ℂ ℂ).smulRight ξ) (norm_nonneg ξ)
    (fun _ => by simp [ContinuousLinearMap.norm_smulRight_apply])

@[simp]
lemma tensorSequence_apply (ξ : H) (η : GroupHilbert G) (g : G) :
    tensorSequence ξ η g = η g • ξ := rfl

def tensorSequenceBilinear : H →ₗ[ℂ] GroupHilbert G →ₗ[ℂ] HilbertValued.HilbertSum G H where
  toFun ξ := (tensorSequence ξ).toLinearMap
  map_add' ξ ζ := by ext η g; simp [smul_add]
  map_smul' c ξ := by ext η g; simp [smul_smul, mul_comm]

def tensorToHilbertSumMap : (H ⊗[ℂ] GroupHilbert G) →ₗ[ℂ] HilbertValued.HilbertSum G H :=
  TensorProduct.lift tensorSequenceBilinear

@[simp]
lemma tensorToHilbertSumMap_tmul (ξ : H) (η : GroupHilbert G) :
    tensorToHilbertSumMap (ξ ⊗ₜ[ℂ] η) = tensorSequence ξ η := rfl

end TensorHilbertSum

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_NonUnitalGroupTensor
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

section NonUnitalGroup

variable {A B G : Type*} [CStarAlgebra A] [CStarAlgebra B] [Group G]

def completedGroupOperator (φ : A →⋆ₙₐ[ℂ] B) (u : G →* unitary A) (g : G) : B :=
  φ (u g) + (1 - φ 1)

lemma completedGroupOperator_one (φ : A →⋆ₙₐ[ℂ] B) (u : G →* unitary A) :
    completedGroupOperator φ u 1 = 1 := by
  simp [completedGroupOperator]

lemma completedGroupOperator_mul (φ : A →⋆ₙₐ[ℂ] B) (u : G →* unitary A) (g h : G) :
    completedGroupOperator φ u (g * h) =
      completedGroupOperator φ u g * completedGroupOperator φ u h := by
  have hx (a : A) : φ a * (1 - φ 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, mul_one, sub_self]
  have hy (a : A) : (1 - φ 1) * φ a = 0 := by
    rw [sub_mul, one_mul, ← map_mul, one_mul, sub_self]
  have hc : (1 - φ 1) * (1 - φ 1) = 1 - φ 1 := by
    rw [mul_sub, mul_one, hy, sub_zero]
  simp only [completedGroupOperator, map_mul, Submonoid.coe_mul, add_mul, mul_add,
    hx, hy, hc, add_zero, zero_add]

lemma completedGroupOperator_inv (φ : A →⋆ₙₐ[ℂ] B) (u : G →* unitary A) (g : G) :
    completedGroupOperator φ u g⁻¹ = star (completedGroupOperator φ u g) := by
  simp only [completedGroupOperator, map_inv, ← Unitary.star_eq_inv, Unitary.coe_star,
    map_star, star_add, star_sub, star_one]
  have hφ : star (φ 1) = φ 1 := by rw [← map_star, star_one]
  rw [hφ]

lemma completedGroupOperator_unitary (φ : A →⋆ₙₐ[ℂ] B) (u : G →* unitary A) (g : G) :
    completedGroupOperator φ u g ∈ unitary B := by
  constructor
  · rw [← completedGroupOperator_inv, ← completedGroupOperator_mul,
      inv_mul_cancel, completedGroupOperator_one]
  · rw [← completedGroupOperator_inv, ← completedGroupOperator_mul,
      mul_inv_cancel, completedGroupOperator_one]

def completedGroupUnitary (φ : A →⋆ₙₐ[ℂ] B) (u : G →* unitary A) : G →* unitary B where
  toFun g := ⟨completedGroupOperator φ u g, completedGroupOperator_unitary φ u g⟩
  map_one' := Subtype.ext (completedGroupOperator_one φ u)
  map_mul' g h := Subtype.ext (completedGroupOperator_mul φ u g h)

end NonUnitalGroup

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ULiftCStar
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

universe u v

instance uliftStarRing {A : Type u} [Semiring A] [StarRing A] : StarRing (ULift.{v} A) where
  star x := ⟨star x.down⟩
  star_involutive x := by cases x; simp only [star_star]
  star_mul x y := by apply ULift.down_injective; exact star_mul x.down y.down
  star_add x y := by apply ULift.down_injective; exact star_add x.down y.down

instance uliftStarModule {A : Type u} [Semiring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] : StarModule ℂ (ULift.{v} A) where
  star_smul r x := by apply ULift.down_injective; exact star_smul r x.down

instance uliftCStarAlgebra {A : Type u} [CStarAlgebra A] : CStarAlgebra (ULift.{v} A) where
  norm_mul_self_le x := CStarRing.norm_mul_self_le x.down

def uliftStarAlgEquiv {A : Type u} [CStarAlgebra A] : ULift.{v} A ≃⋆ₐ[ℂ] A :=
  { ULift.algEquiv (R := ℂ) (A := A) with
    map_smul' := fun _ _ => rfl
    map_star' := fun _ => rfl }

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ProductRepresentation
attribute [-instance] _root_.OAI.WeakPureInfiniteness.completedTensorCStar _root_.OAI.WeakPureInfiniteness.hilbertOperatorsCStar _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint

namespace WeakPureInfiniteness

universe u v

section ProductRepresentation

variable {ι : Type u} {H : ι → Type v}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, CompleteSpace (H i)]

lemma mem_l2_productAction (T : lp (fun i => H i →L[ℂ] H i) ∞) (ξ : lp H 2) :
    Memℓp (fun i => T i (ξ i)) 2 := by
  apply (ξ.property.const_smul (‖T‖ : ℂ)).mono'
  intro i
  change ‖T i (ξ i)‖ ≤ ‖(‖T‖ : ℂ) • (ξ i)‖
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T)]
  exact (T i).le_opNorm (ξ i) |>.trans
    (mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero T i) (norm_nonneg _))

def productAction (T : lp (fun i => H i →L[ℂ] H i) ∞) : lp H 2 →L[ℂ] lp H 2 :=
  LinearMap.mkContinuous
    { toFun ξ := ⟨fun i => T i (ξ i), mem_l2_productAction T ξ⟩
      map_add' ξ η := by ext i; exact map_add (T i) _ _
      map_smul' c ξ := by ext i; exact map_smul (T i) _ _ }
    ‖T‖ (by
      intro ξ
      calc
        _ ≤ ‖(‖T‖ : ℂ) • ξ‖ := lp.norm_mono (by norm_num) (by
          intro i
          simp only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T)]
          exact ((T i).le_opNorm (ξ i)).trans
            (mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero T i)
              (norm_nonneg _)))
        _ = ‖(‖T‖ : ℂ)‖ * ‖ξ‖ := norm_smul _ _
        _ = ‖T‖ * ‖ξ‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T)])

@[simp] lemma productAction_apply (T : lp (fun i => H i →L[ℂ] H i) ∞)
    (ξ : lp H 2) (i : ι) : productAction T ξ i = T i (ξ i) := rfl

lemma productAction_star (T : lp (fun i => H i →L[ℂ] H i) ∞) :
    productAction (star T) = star (productAction T) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_left ℂ
  intro η
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  change (∑' i, inner ℂ (η i) (star (T i) (ξ i))) =
    ∑' i, inner ℂ (T i (η i)) (ξ i)
  apply tsum_congr
  intro i
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

def productRepresentation : lp (fun i => H i →L[ℂ] H i) ∞ →⋆ₙₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) where
  toFun := productAction
  map_zero' := by ext ξ i; simp
  map_add' S T := by ext ξ i; rfl
  map_mul' S T := by ext ξ i; rfl
  map_smul' c T := by ext ξ i; rfl
  map_star' := productAction_star

end ProductRepresentation

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FreeFiniteRepresentations
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint

namespace WeakPureInfiniteness

open FreeGroup

variable {α : Type*} [Fintype α] [DecidableEq α]

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def freeOrbitSpace (π : FreeGroup α →* H ≃ₗᵢ[ℂ] H) (m : ℕ) (ξ : H) : Submodule ℂ H :=
  Submodule.span ℂ ((fun g => π g ξ) '' (↑(freeWordBall (α := α) m) : Set (FreeGroup α)))

instance freeOrbitSpace_finite (π : FreeGroup α →* H ≃ₗᵢ[ℂ] H) (m : ℕ) (ξ : H) :
    FiniteDimensional ℂ (freeOrbitSpace π m ξ) := by
  unfold freeOrbitSpace
  exact FiniteDimensional.span_of_finite ℂ ((freeWordBall (α := α) m).finite_toSet.image _)

lemma freeOrbitSpace_mem (π : FreeGroup α →* H ≃ₗᵢ[ℂ] H) (m : ℕ) (ξ : H)
    (g : FreeGroup α) (hg : g ∈ freeWordBall m) : π g ξ ∈ freeOrbitSpace π m ξ :=
  Submodule.subset_span ⟨g,hg,rfl⟩

lemma freeOrbitSpace_base (π : FreeGroup α →* H ≃ₗᵢ[ℂ] H) (m : ℕ) (ξ : H) :
    ξ ∈ freeOrbitSpace π m ξ := by
  simpa using freeOrbitSpace_mem π m ξ 1 (one_mem_freeWordBall m)

def extendUnitaryOn (K : Submodule ℂ H) [FiniteDimensional ℂ K] (U : H ≃ₗᵢ[ℂ] H) :
    K ≃ₗᵢ[ℂ] K := by
  let S := K.comap (U.toLinearMap.comp K.subtype)
  let L : S →ₗᵢ[ℂ] K :=
    { toLinearMap :=
        { toFun := fun x => ⟨U x.val.val, x.property⟩
          map_add' := by intro x y; apply Subtype.ext; exact U.map_add _ _
          map_smul' := by intro c x; apply Subtype.ext; exact U.map_smul _ _ }
      norm_map' := fun x => U.norm_map x.val.val }
  exact L.extend.toLinearIsometryEquiv rfl

def freeFiniteRepresentation (π : FreeGroup α →* H ≃ₗᵢ[ℂ] H) (m : ℕ) (ξ : H) :
    FreeGroup α →* freeOrbitSpace π m ξ ≃ₗᵢ[ℂ] freeOrbitSpace π m ξ :=
  FreeGroup.lift (fun a => extendUnitaryOn (freeOrbitSpace π m ξ) (π (FreeGroup.of a)))

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FiniteUnitaryLog
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint

namespace WeakPureInfiniteness

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

def finiteContinuousEndAlgEquiv : (H →ₗ[ℂ] H) ≃ₐ[ℂ] (H →L[ℂ] H) :=
  { LinearMap.toContinuousLinearMap with
    map_mul' := fun _ _ => rfl
    commutes' := fun _ => rfl }

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_PairUnitary
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint

namespace WeakPureInfiniteness

universe u

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def pairUnitary (x : A) (b : Bool) : unitary A :=
  selfAdjoint.expUnitary ((2 * Real.pi) • (if b then realPart x else imaginaryPart x))

def pairGroup (x : A) : FreeGroup Bool →* unitary A :=
  FreeGroup.lift (pairUnitary x)

@[simp] lemma pairGroup_of (x : A) (b : Bool) :
    pairGroup x (FreeGroup.of b) = pairUnitary x b := by simp [pairGroup]

lemma map_pairUnitary (f : A →⋆ₐ[ℂ] B) (x : A) (b : Bool) :
    f (pairUnitary x b) = (pairUnitary (f x) b : B) := by
  cases b <;> simp only [pairUnitary, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
    selfAdjoint.expUnitary_coe]
  all_goals
    let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
    let : NormedAlgebra ℚ B := NormedAlgebra.restrictScalars ℚ ℂ B
    have hf : Continuous f := (f.toAlgHom.toLinearMap.mkContinuous 1
      (fun x => by
        change ‖f x‖ ≤ 1 * ‖x‖
        rw [one_mul]
        exact NonUnitalStarAlgHom.norm_apply_le f x)).continuous
    rw [NormedSpace.map_exp f hf]
    congr 1
    change f (I • ((2 * Real.pi) • (_ : A))) = I • ((2 * Real.pi) • (_ : B))
    rw [map_smul, ← Complex.coe_smul, map_smul]
    simp only [map_realPart, map_imaginaryPart, Complex.coe_smul]

lemma map_pairGroup (f : A →⋆ₐ[ℂ] B) (x : A) (g : FreeGroup Bool) :
    f (pairGroup x g) = (pairGroup (f x) g : B) := by
  have h : (Unitary.map ({ f.toMonoidHom with map_star' := map_star f } : A →⋆* B)).toMonoidHom.comp (pairGroup x) =
      pairGroup (f x) := by
    apply FreeGroup.ext_hom
    intro b
    apply Subtype.ext
    change f (pairGroup x (FreeGroup.of b)) = (pairGroup (f x) (FreeGroup.of b) : B)
    rw [pairGroup_of, pairGroup_of]
    exact map_pairUnitary f x b
  exact congrArg (fun ρ : FreeGroup Bool →* unitary B => (ρ g : B)) h

def logarithmContraction (S T : unitary A) : A :=
  (2 * Real.pi)⁻¹ • ((Unitary.argSelfAdjoint S : A) +
    Complex.I • (Unitary.argSelfAdjoint T : A))

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_WordCompression
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint

namespace WeakPureInfiniteness

section FiniteCompression

variable {ι S H : Type*} [Finite ι] [Finite S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def wordSpace (T : ι → H →L[ℂ] H) (ξ : S → H) : ℕ → Submodule ℂ H
  | 0 => Submodule.span ℂ (Set.range ξ)
  | m + 1 => wordSpace T ξ m ⊔ ⨆ i, (wordSpace T ξ m).map (T i).toLinearMap

instance wordSpace_finiteDimensional (T : ι → H →L[ℂ] H) (ξ : S → H) (m : ℕ) :
    FiniteDimensional ℂ (wordSpace T ξ m) := by
  induction m with
  | zero => exact FiniteDimensional.span_of_finite ℂ (Set.finite_range ξ)
  | succ m ih =>
    change FiniteDimensional ℂ
      ↥(wordSpace T ξ m ⊔ ⨆ i, (wordSpace T ξ m).map (T i).toLinearMap)
    let := ih
    infer_instance

omit [Finite ι] [Finite S] in
lemma wordSpace_mono (T : ι → H →L[ℂ] H) (ξ : S → H) : Monotone (wordSpace T ξ) := by
  apply monotone_nat_of_le_succ
  intro m
  exact le_sup_left

end FiniteCompression

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UniversalMapping
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def algebraWord (x : A) : List Bool → A
  | [] => 1
  | i :: w => (if i then x else star x) * algebraWord x w

def algebraPolynomial (x : A) (c : List Bool →₀ ℂ) : A :=
  c.sum fun w a => a • algebraWord x w

lemma map_algebraWord (φ : A →⋆ₐ[ℂ] B) (x : A) (w : List Bool) :
    φ (algebraWord x w) = algebraWord (φ x) w := by
  induction w with
  | nil => exact map_one φ
  | cons i w ih => cases i <;> simp [algebraWord, ih, map_star]

lemma map_algebraPolynomial (φ : A →⋆ₐ[ℂ] B) (x : A) (c : List Bool →₀ ℂ) :
    φ (algebraPolynomial x c) = algebraPolynomial (φ x) c := by
  simp [algebraPolynomial, Finsupp.sum, map_algebraWord]

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UniformModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped TensorProduct

section PolynomialTensorEstimate

variable {B C : Type 1} [CStarAlgebra B] [NonUnitalCStarAlgebra C]

def wordTensorCost (s : Finset (List Bool)) (c : List Bool → C) : ℝ :=
  ∑ w ∈ s, ‖c w‖ * w.length

end PolynomialTensorEstimate

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_PolynomialSpan
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

variable {A : Type*} [CStarAlgebra A]

lemma algebraWord_append (x : A) (w z : List Bool) :
    algebraWord x (w ++ z) = algebraWord x w * algebraWord x z := by
  induction w with
  | nil => simp [algebraWord]
  | cons i w ih => simp [algebraWord, ih, mul_assoc]

def wordMonoid (x : A) : Submonoid A where
  carrier := Set.range (algebraWord x)
  one_mem' := ⟨[], rfl⟩
  mul_mem' := by
    rintro _ _ ⟨w,rfl⟩ ⟨z,rfl⟩
    exact ⟨w++z, algebraWord_append x w z⟩

lemma adjoin_le_wordSpan (x : A) :
    (StarAlgebra.adjoin ℂ {x}).toSubalgebra.toSubmodule ≤
      Submodule.span ℂ (Set.range (algebraWord x)) := by
  rw [StarAlgebra.adjoin_eq_span]
  apply Submodule.span_mono
  change Submonoid.closure ({x} ∪ star {x}) ≤ wordMonoid x
  apply Submonoid.closure_le.mpr
  intro y hy
  have hy' : y = x ∨ star y = x := by simpa using hy
  rcases hy' with rfl | he
  · exact ⟨[true], by simp [algebraWord]⟩
  · exact ⟨[false], by simp [algebraWord, ← he]⟩

lemma exists_polynomial_of_mem_adjoin (x y : A) (hy : y ∈ StarAlgebra.adjoin ℂ {x}) :
    ∃ c : List Bool →₀ ℂ, algebraPolynomial x c = y :=
  Finsupp.mem_span_range_iff_exists_finsupp.mp (adjoin_le_wordSpan x hy)

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FiniteCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

structure OrthogonalPerturbationData (A : Type*) [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (n : ℕ) where
  p : A
  q : A
  h : A
  k : A
  c : A
  norm_p : ‖p‖ ≤ 1
  norm_q : ‖q‖ ≤ 1
  nonneg_p : 0 ≤ p
  nonneg_q : 0 ≤ q
  orthogonal : p*q=0
  nonneg_h : 0 ≤ h
  nonneg_k : 0 ≤ k
  nonneg_c : 0 ≤ c
  support_h : p*h=h
  support_k : q*k=k
  compare_h : CuntzSubequiv (diagonalCopies n c) (diagonalCopies 1 h)
  compare_k : CuntzSubequiv (diagonalCopies n c) (diagonalCopies 1 k)
  α : ℝ
  pos_α : 0 < α

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FourColumnNorm
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

local instance matrixRealModuleFour {j : Type*} [Fintype j] :
    Module ℝ (CStarMatrix j j A) := Module.complexToReal _

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_IdealComparison
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open Filter

open scoped Topology CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
def oneBlockColumn (e : A) : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1) A := fun _ _ => e

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_IdealSpan
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
def algebraicIdealSpan (h : A) : Submodule ℂ A :=
  Submodule.span ℂ (Set.range (fun p : A × A => p.1*h*p.2))

omit [PartialOrder A] [StarOrderedRing A] in
lemma algebraicIdealSpan_mul_left (h a : A) {x : A} (hx : x ∈ algebraicIdealSpan h) :
    a*x ∈ algebraicIdealSpan h := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨c,d⟩,rfl⟩ := hy
    exact Submodule.subset_span ⟨(a*c,d),by simp only [mul_assoc]⟩
  | zero => simpa only [mul_zero] using (algebraicIdealSpan h).zero_mem
  | add y z _ _ hy hz => simpa only [mul_add] using (algebraicIdealSpan h).add_mem hy hz
  | smul c y _ hy => simpa only [mul_smul_comm] using (algebraicIdealSpan h).smul_mem c hy

omit [PartialOrder A] [StarOrderedRing A] in
lemma algebraicIdealSpan_star (h : A) (hh : IsSelfAdjoint h) {x : A}
    (hx : x ∈ algebraicIdealSpan h) : star x ∈ algebraicIdealSpan h := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨c,d⟩,rfl⟩ := hy
    exact Submodule.subset_span ⟨(star d,star c),by
      simp only [star_mul,hh.star_eq,mul_assoc]⟩
  | zero => simpa only [star_zero] using (algebraicIdealSpan h).zero_mem
  | add y z _ _ hy hz => simpa only [star_add] using (algebraicIdealSpan h).add_mem hy hz
  | smul c y _ hy => simpa only [star_smul] using (algebraicIdealSpan h).smul_mem (star c) hy

omit [PartialOrder A] [StarOrderedRing A] in
def algebraicIdealSubalgebra (h : A) (hh : IsSelfAdjoint h) : NonUnitalStarSubalgebra ℂ A where
  toSubmodule := algebraicIdealSpan h
  mul_mem' := fun {x _} _ hy => algebraicIdealSpan_mul_left h x hy
  star_mem' := algebraicIdealSpan_star h hh

def generatedClosedIdeal (h : A) (hh : IsSelfAdjoint h) : NonUnitalStarSubalgebra ℂ A :=
  (algebraicIdealSubalgebra h hh).topologicalClosure

instance instIsClosedCoeNonUnitalStarSubalgebraComplexGeneratedClosedIdeal (h : A) (hh : IsSelfAdjoint h) : IsClosed (generatedClosedIdeal h hh : Set A) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

instance instCompleteSpaceSubtypeMemNonUnitalStarSubalgebraComplexGeneratedClosedIdeal (h : A) (hh : IsSelfAdjoint h) : CompleteSpace (generatedClosedIdeal h hh) :=
  (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).isComplete.completeSpace_coe

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SpectralDeletion
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakPureInfiniteness

open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder



open scoped BigOperators CStarAlgebra

section FiniteDeletion

variable {A : Type*} [NonUnitalCStarAlgebra A]

variable {ι κ : Type*} [Fintype ι]

def finiteDeletion (f : ι → A) (V : A) (R : ι → ι → Prop) [DecidableRel R] : A :=
  ∑ j, ∑ k, if R j k then f j*V*f k else 0

end FiniteDeletion




end WeakPureInfiniteness

end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SpectralWindows
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology

def spectralTent (t r x : ℝ) : ℝ := max (1-|x-t|/r) 0

def spectralPlateau (t r x : ℝ) : ℝ := min 1 (max 0 (2-|x-t|/r))

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_NonunitalSpectralTools2
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def unitizationSubalgebra (D : NonUnitalStarSubalgebra ℂ A) : StarSubalgebra ℂ (Unitization ℂ A) where
  carrier := {z | z.snd ∈ D}
  algebraMap_mem' z := by change (0 : A) ∈ D; exact D.zero_mem
  add_mem' ha hb := D.add_mem ha hb
  mul_mem' {a b} ha hb := by
    change a.fst • b.snd+b.fst • a.snd+a.snd*b.snd ∈ D
    exact D.add_mem (D.add_mem (D.smul_mem _ hb) (D.smul_mem _ ha)) (D.mul_mem ha hb)
  star_mem' ha := star_mem (s := D) ha

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_PrimitiveIdealTest
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology ComplexOrder InnerProductSpace CStarAlgebra

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def unitizationClosedIdeal (I : NonUnitalStarSubalgebra ℂ A) :
    NonUnitalStarSubalgebra ℂ (Unitization ℂ A) where
  carrier := {x | x.fst=0 ∧ x.snd ∈ I}
  zero_mem' := ⟨rfl,I.zero_mem⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨by simp only [Unitization.fst_add,hx.1,hy.1,add_zero],I.add_mem hx.2 hy.2⟩
  smul_mem' := by
    intro c x hx
    exact ⟨by simp only [Unitization.fst_smul,hx.1,smul_zero],I.smul_mem c hx.2⟩
  mul_mem' := by
    intro x y hx hy
    refine ⟨by simp only [Unitization.fst_mul,hx.1,zero_mul],?_⟩
    simp only [Unitization.snd_mul,hx.1,hy.1,zero_smul,zero_add]
    exact I.mul_mem hx.2 hy.2
  star_mem' := by
    intro x hx
    exact ⟨by simp only [Unitization.fst_star,hx.1,star_zero],star_mem hx.2⟩

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparationScalar
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

def separationFloor (l s : ℝ) : ℝ := max l (Real.sqrt s)

def separationR (l s : ℝ) : ℝ := Real.sqrt l / Real.sqrt (separationFloor l s)

def separationV (l s : ℝ) : ℝ := separationR l s / separationFloor l s

def separationK (l s : ℝ) : ℝ := (Real.sqrt l * Real.sqrt (separationFloor l s))⁻¹

def separationG (l s : ℝ) : ℝ := spectralRamp l (Real.sqrt s)

def separationN (l s : ℝ) : ℝ := spectralRamp (4*l) (Real.sqrt s)

def separationL (l s : ℝ) : ℝ := 1-separationN l s

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparationCoverage
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

def separationJ (l s : ℝ) : ℝ := Real.sqrt (separationFloor l s)/Real.sqrt l

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparationFourColumns
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

local instance matrixRealModuleFourAssembly {j : Type*} [Fintype j] :
    Module ℝ (CStarMatrix j j A) := Module.complexToReal _

def twoEntryRow (x y : A) : CStarMatrix (Fin 1) (Fin 2) A := fun _ j => ![x,y] j

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparationPreassembly
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def unitizedRight (a : A) (u : Unitization ℂ A) : A := ((a : Unitization ℂ A)*u).snd

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SmallCStar
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open TopologicalSpace

universe u v

def SmallCStarCarrier (A : Type u) [Small.{0} A] := Shrink.{0} A

section SmallTransport

variable (A : Type u) [CStarAlgebra A] [Small.{0} A]

def smallCStarEquiv : SmallCStarCarrier A ≃ A := (equivShrink A).symm

instance smallCStarNormedRing : NormedRing (SmallCStarCarrier A) := (smallCStarEquiv A).normedRing

instance smallCStarAlgebraStruct : Algebra ℂ (SmallCStarCarrier A) := (smallCStarEquiv A).algebra ℂ

instance smallCStarNormedSpace : NormedSpace ℂ (SmallCStarCarrier A) :=
  Equiv.normedSpace ℂ (smallCStarEquiv A)

instance smallCStarStarRing : StarRing (SmallCStarCarrier A) := (smallCStarEquiv A).starRing

instance smallCStarStarModule : StarModule ℂ (SmallCStarCarrier A) := (smallCStarEquiv A).starModule ℂ

lemma smallCStarEquiv_isometry : Isometry (smallCStarEquiv A) := by
  intro x y
  rfl

instance smallCStarComplete : CompleteSpace (SmallCStarCarrier A) :=
  (show SmallCStarCarrier A ≃ᵢ A from
    { smallCStarEquiv A with isometry_toFun := smallCStarEquiv_isometry A }).completeSpace

instance smallCStarCStar : CStarAlgebra (SmallCStarCarrier A) where
  norm_smul_le r x := by
    change ‖smallCStarEquiv A ((smallCStarEquiv A).symm (r • smallCStarEquiv A x))‖ ≤ _
    rw [Equiv.apply_symm_apply]
    exact norm_smul_le r (smallCStarEquiv A x)
  norm_mul_self_le x := by
    change ‖smallCStarEquiv A x‖ * ‖smallCStarEquiv A x‖ ≤
      ‖smallCStarEquiv A (star x*x)‖
    change ‖smallCStarEquiv A x‖ * ‖smallCStarEquiv A x‖ ≤
      ‖smallCStarEquiv A ((smallCStarEquiv A).symm
        (smallCStarEquiv A ((smallCStarEquiv A).symm (star (smallCStarEquiv A x))) * smallCStarEquiv A x))‖
    simp only [Equiv.apply_symm_apply]
    exact CStarRing.norm_mul_self_le _

def smallCStarStarAlgEquiv : SmallCStarCarrier A ≃⋆ₐ[ℂ] A :=
  { (smallCStarEquiv A).algEquiv ℂ with
    map_smul' := fun r x => by
      change smallCStarEquiv A ((smallCStarEquiv A).symm (r • smallCStarEquiv A x))=_
      exact Equiv.apply_symm_apply _ _
    map_star' := fun x => by
      change smallCStarEquiv A ((smallCStarEquiv A).symm (star (smallCStarEquiv A x)))=_
      exact Equiv.apply_symm_apply _ _ }

end SmallTransport

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_StatePullback
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def selfAdjointMap (π : A →⋆ₐ[ℂ] B) : selfAdjoint A →L[ℝ] selfAdjoint B where
  toFun b := ⟨π (b : A),b.property.map π⟩
  map_add' _ _ := Subtype.ext (map_add π _ _)
  map_smul' r b := Subtype.ext (map_real_smul π (starHom_continuous π) r (b : A))
  cont := by
    have hπ : Continuous π := starHom_continuous π
    fun_prop

def realStatePullback (π : A →⋆ₐ[ℂ] B) (f : WeakDual ℝ (selfAdjoint B)) :
    WeakDual ℝ (selfAdjoint A) :=
  StrongDual.toWeakDual ((WeakDual.toStrongDual f).comp (selfAdjointMap π))

end

end WeakPureInfiniteness
end

end OAI
end


