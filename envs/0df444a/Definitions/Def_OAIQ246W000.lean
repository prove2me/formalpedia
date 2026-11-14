-- Prove2me | Definitions.Def_OAIQ246W000
-- name    : OAIQ246W000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T07:12:25.952814+00:00
-- url     : https://prove2.me/theorems/3cb677ca-9672-4c93-bbc9-067e83f9e4bc
-- title:
--   Definitions bundle OAIQ246W000 of the split of OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any` and `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite`, carved from OpenAI's openai/math development (OpenAI, *Weak pure infiniteness and O-infinity absorption (result family 303)*, OpenAI Math Release, September 25, 2026, result family 303, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 140 declarations of OpenAI's Lean: 56 definitions, 3 inductive types or structures, 10 instances and 71 theorems. The definitions and types are `OAI.WeakPureInfiniteness.ContinuouslySupported`, `OAI.WeakPureInfiniteness.ContractionAmbient`, `OAI.WeakPureInfiniteness.ContractionRepresentation`, `OAI.WeakPureInfiniteness.CuntzAmbient`, `OAI.WeakPureInfiniteness.CuntzRepresentation`, `OAI.WeakPureInfiniteness.ElementCuntzSubequiv`, `OAI.WeakPureInfiniteness.FockSpace`, `OAI.WeakPureInfiniteness.FullGroupAlgebra`, `OAI.WeakPureInfiniteness.FullGroupAmbient`, `OAI.WeakPureInfiniteness.GroupRepresentation`, `OAI.WeakPureInfiniteness.OInfinity`, `OAI.WeakPureInfiniteness.SpatialRepresentation.precompLeft`, `OAI.WeakPureInfiniteness.UniversalContraction`, `OAI.WeakPureInfiniteness.basisTensorIsometry`, `OAI.WeakPureInfiniteness.basisTensorMap`, `OAI.WeakPureInfiniteness.clipScale`, `OAI.WeakPureInfiniteness.closedStarSpan`, `OAI.WeakPureInfiniteness.closedStarSpanCStar`, `OAI.WeakPureInfiniteness.compress`, `OAI.WeakPureInfiniteness.contractionEvaluation`, `OAI.WeakPureInfiniteness.crossTensorFirst`, `OAI.WeakPureInfiniteness.crossTensorGraph`, `OAI.WeakPureInfiniteness.crossTensorPair`, `OAI.WeakPureInfiniteness.cuntzGenerator`, `OAI.WeakPureInfiniteness.fockBasis`, `OAI.WeakPureInfiniteness.fullGroupElement`, `OAI.WeakPureInfiniteness.fullGroupEvaluation`, `OAI.WeakPureInfiniteness.fullGroupOperator`, `OAI.WeakPureInfiniteness.fullGroupSubalgebra`, `OAI.WeakPureInfiniteness.gnsCyclicVector`, `OAI.WeakPureInfiniteness.linearStarSpan`, `OAI.WeakPureInfiniteness.matrixOperator`, `OAI.WeakPureInfiniteness.minimalElementary`, `OAI.WeakPureInfiniteness.minimalElementaryLeft`, `OAI.WeakPureInfiniteness.minimalElementaryRight`, `OAI.WeakPureInfiniteness.minimalMapLeft`, `OAI.WeakPureInfiniteness.minimalMapRight`, `OAI.WeakPureInfiniteness.oInfinityEvaluation`, `OAI.WeakPureInfiniteness.oInfinityIsometry`, `OAI.WeakPureInfiniteness.oInfinitySubalgebra` and 19 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `WeakInfiniteness_AlgebraicTensorSpan`, `WeakInfiniteness_CStarClosedRange`, `WeakInfiniteness_ContinuousDeletion`, `WeakInfiniteness_CrossUniverseTensorMap`, `WeakInfiniteness_DiagonalRegular`, `WeakInfiniteness_FaithfulRepresentation`, `WeakInfiniteness_FullGroupAlgebra`, `WeakInfiniteness_LocalConnection`, `WeakInfiniteness_MatrixRepresentation`, `WeakInfiniteness_NonUnitalClosedRange`, `WeakInfiniteness_PolynomialCompression`, `WeakInfiniteness_SpatialVectorStates`, `WeakInfiniteness_States`, `WeakInfiniteness_TensorCompression`, `WeakInfiniteness_TensorCut`, `WeakInfiniteness_TensorDensity`, `WeakInfiniteness_TensorFlip`, `WeakInfiniteness_TensorFoundations`, `WeakInfiniteness_TensorFunctoriality`, `WeakInfiniteness_TensorInjectivity`, `WeakInfiniteness_TensorMatrixNorm`, `WeakInfiniteness_UniversalFreeEmbedding`, `WeakInfiniteness_WordCompression`.
--
--   **Imports.** It imports the published bundle `Def_ExactInfiniteness`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ246W003` and `OAIQ246W004`; the statements `OAI.WeakPureInfiniteness.exists_binary_splitting_over_norm_slice_any` and `OAI.WeakPureInfiniteness.separation_core_comparisons`; the proofs of `OAI.WeakPureInfiniteness.exists_core_perturbationData` and `OAI.WeakPureInfiniteness.exists_separation_cores`.
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
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib d13f23b's `MeasurableSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean): the product structure
(InvariantIsing, q251). Explicitly named: the platform's `Def_InvariantIsing` declares an anonymous copy of the same
instance. -/
instance _root_.Matrix.compatMeasurableSpace {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs <| MeasurableSpace (m → n → α)
/-- Mathlib d13f23b's `BorelSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean; InvariantIsing, q258). -/
instance _root_.Matrix.compatBorelSpace {m n α : Type*} [Countable m] [Countable n] [MeasurableSpace α]
    [TopologicalSpace α] [SecondCountableTopology α] [BorelSpace α] : BorelSpace (Matrix m n α) :=
  inferInstanceAs <| BorelSpace (m → n → α)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorFoundations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace

namespace WeakPureInfiniteness

section CompletedOperators

variable {H K L : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]
  [NormedAddCommGroup L] [NormedSpace ℂ L]

lemma completion_comp (S : K →L[ℂ] L) (T : H →L[ℂ] K) :
    (S.comp T).completion = S.completion.comp T.completion := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x => simp

lemma completion_add (S T : H →L[ℂ] K) :
    (S + T).completion = S.completion + T.completion := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x => simp [← Completion.coe_add]

lemma completion_smul (c : ℂ) (T : H →L[ℂ] K) :
    (c • T).completion = c • T.completion := by
  ext x
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq (c • T).completion.continuous
      (T.completion.continuous.const_smul c)
  | ih x => simp only [ContinuousLinearMap.completion_apply_coe,
      smul_apply, Completion.coe_smul]

lemma completion_zero : (0 : H →L[ℂ] K).completion = 0 := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x => simp

end CompletedOperators

section CompletedHilbertTensor

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma inner_mapL_star (S : H →L[ℂ] H) (T : K →L[ℂ] K) (x y : H ⊗[ℂ] K) :
    inner ℂ ((TensorProduct.mapL S T) x) y =
      inner ℂ x ((TensorProduct.mapL (star S) (star T)) y) := by
  induction x using OAI.tensorInductionOn with
  | tmul x₁ x₂ =>
    induction y using OAI.tensorInductionOn with
    | tmul y₁ y₂ =>
      simp only [TensorProduct.mapL_tmul, TensorProduct.inner_tmul,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    | add y₁ y₂ h₁ h₂ => simp only [inner_add_right, map_add, h₁, h₂]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]

lemma completion_mapL_star (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    star (TensorProduct.mapL S T).completion =
      (TensorProduct.mapL (star S) (star T)).completion := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    induction y using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih y =>
      simp only [ContinuousLinearMap.completion_apply_coe, Completion.inner_coe]
      exact inner_mapL_star S T y x

end CompletedHilbertTensor

attribute [instance] ComplexHilbert.normedAddCommGroup
  ComplexHilbert.innerProductSpace ComplexHilbert.completeSpace

section ElementaryTensors

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

@[simp]
lemma spatialElementary_zero_left (b : B) : spatialElementary (0 : A) b = 0 := by
  apply Subtype.ext
  funext π
  change (TensorProduct.mapL _ _).completion = 0
  simp [completion_zero]

@[simp]
lemma spatialElementary_zero_right (a : A) : spatialElementary a (0 : B) = 0 := by
  apply Subtype.ext
  funext π
  change (TensorProduct.mapL _ _).completion = 0
  simp [completion_zero]

lemma spatialElementary_add_left (a a' : A) (b : B) :
    spatialElementary (a + a') b = spatialElementary a b + spatialElementary a' b := by
  apply Subtype.ext
  funext π
  change (TensorProduct.mapL (π.leftRep (a + a')) (π.rightRep b)).completion =
    (TensorProduct.mapL (π.leftRep a) (π.rightRep b)).completion +
    (TensorProduct.mapL (π.leftRep a') (π.rightRep b)).completion
  rw [map_add, TensorProduct.mapL_add_left, completion_add]

lemma spatialElementary_add_right (a : A) (b b' : B) :
    spatialElementary a (b + b') = spatialElementary a b + spatialElementary a b' := by
  apply Subtype.ext
  funext π
  change (TensorProduct.mapL (π.leftRep a) (π.rightRep (b + b'))).completion =
    (TensorProduct.mapL (π.leftRep a) (π.rightRep b)).completion +
    (TensorProduct.mapL (π.leftRep a) (π.rightRep b')).completion
  rw [map_add, TensorProduct.mapL_add_right, completion_add]

lemma spatialElementary_smul_left (c : ℂ) (a : A) (b : B) :
    spatialElementary (c • a) b = c • spatialElementary a b := by
  apply Subtype.ext
  funext π
  change (TensorProduct.mapL (π.leftRep (c • a)) (π.rightRep b)).completion =
    c • (TensorProduct.mapL (π.leftRep a) (π.rightRep b)).completion
  rw [map_smul, TensorProduct.mapL_smul_left, completion_smul]

lemma spatialElementary_smul_right (c : ℂ) (a : A) (b : B) :
    spatialElementary a (c • b) = c • spatialElementary a b := by
  apply Subtype.ext
  funext π
  change (TensorProduct.mapL (π.leftRep a) (π.rightRep (c • b))).completion =
    c • (TensorProduct.mapL (π.leftRep a) (π.rightRep b)).completion
  rw [map_smul, TensorProduct.mapL_smul_right, completion_smul]

lemma spatialElementary_mul (a a' : A) (b b' : B) :
    spatialElementary (a * a') (b * b') = spatialElementary a b * spatialElementary a' b' := by
  apply Subtype.ext
  funext π
  change (TensorProduct.mapL (π.leftRep (a * a')) (π.rightRep (b * b'))).completion =
    (TensorProduct.mapL (π.leftRep a) (π.rightRep b)).completion *
    (TensorProduct.mapL (π.leftRep a') (π.rightRep b')).completion
  rw [map_mul, map_mul, TensorProduct.mapL_mul]
  exact completion_comp _ _

@[simp]
lemma spatialElementary_star (a : A) (b : B) :
    spatialElementary (star a) (star b) = star (spatialElementary a b) := by
  apply Subtype.ext
  funext π
  change (TensorProduct.mapL (π.leftRep (star a)) (π.rightRep (star b))).completion =
    star (TensorProduct.mapL (π.leftRep a) (π.rightRep b)).completion
  rw [map_star, map_star]
  exact (completion_mapL_star _ _).symm

lemma norm_spatialElementary_le (a : A) (b : B) : ‖spatialElementary a b‖ ≤ ‖a‖ * ‖b‖ := by
  apply lp.norm_le_of_forall_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro π
  change ‖(TensorProduct.mapL (π.leftRep a) (π.rightRep b)).completion‖ ≤ _
  rw [norm_completion]
  exact (TensorProduct.norm_mapL_le _ _).trans
    (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le π.leftRep a)
      (NonUnitalStarAlgHom.norm_apply_le π.rightRep b) (norm_nonneg _) (norm_nonneg _))

end ElementaryTensors

structure CuntzRepresentation where
  hilbert : ComplexHilbert.{0}
  [nontrivial : Nontrivial hilbert]
  generators : ℕ → hilbert →L[ℂ] hilbert
  relations : ∀ i j, star (generators i) * generators j = if i = j then 1 else 0

attribute [instance] CuntzRepresentation.nontrivial

abbrev CuntzAmbient :=
  lp (fun π : CuntzRepresentation => π.hilbert →L[ℂ] π.hilbert) ∞

instance instCStarAlgebraSubtypePreLpCuntzRepresentationContinuousLinearMapComplexIdCarrierHilbertMemAddSubgroupCuntzAmbient : CStarAlgebra CuntzAmbient where

lemma CuntzRepresentation.norm_generator (π : CuntzRepresentation) (i : ℕ) :
    ‖π.generators i‖ = 1 := by
  have h : ‖π.generators i‖ * ‖π.generators i‖ = 1 := by
    rw [← CStarRing.norm_star_mul_self, π.relations i i, ite_eq_left rfl, norm_one]
  nlinarith [norm_nonneg (π.generators i)]

def cuntzGenerator (i : ℕ) : CuntzAmbient :=
  ⟨fun π => π.generators i, memℓp_infty ⟨1, by
    rintro _ ⟨π, rfl⟩
    exact (π.norm_generator i).le⟩⟩

def oInfinitySubalgebra : StarSubalgebra ℂ CuntzAmbient :=
  (StarAlgebra.adjoin ℂ (Set.range cuntzGenerator)).topologicalClosure

abbrev OInfinity := oInfinitySubalgebra

open scoped InnerProductSpace

abbrev FockSpace := lp (fun _ : List ℕ => ℂ) 2

def fockBasis (w : List ℕ) : ℂ →ₗᵢ[ℂ] FockSpace where
  toLinearMap := (lp.singleContinuousLinearMap ℂ (fun _ : List ℕ => ℂ) 2 w).toLinearMap
  norm_map' z := by
    change ‖lp.single (E := fun _ : List ℕ => ℂ) 2 w z‖ = ‖z‖
    exact lp.norm_single (E := fun _ : List ℕ => ℂ) (by norm_num : (0 : ℝ≥0∞) < 2) w z

@[simp]
lemma fockBasis_apply (w : List ℕ) (z : ℂ) :
    fockBasis w z = lp.single 2 w z := rfl

def oInfinityEvaluation (π : CuntzRepresentation) :
    OInfinity →⋆ₐ[ℂ] (π.hilbert →L[ℂ] π.hilbert) where
  toFun x := x.val π
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_one' := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def oInfinityIsometry (i : ℕ) : OInfinity :=
  ⟨cuntzGenerator i, StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ _ ⟨i, rfl⟩)⟩

@[simp]
lemma oInfinityEvaluation_isometry (π : CuntzRepresentation) (i : ℕ) :
    oInfinityEvaluation π (oInfinityIsometry i) = π.generators i := rfl

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_AlgebraicTensorSpan
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

universe u v

section AlgebraicSpan

variable {A : Type*} [NonUnitalCStarAlgebra A]

def linearStarSpan (S : Set A) (hm : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    (hs : ∀ x ∈ S, star x ∈ S) : NonUnitalStarSubalgebra ℂ A where
  carrier := Submodule.span ℂ S
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' c _ hx := Submodule.smul_mem _ c hx
  mul_mem' {a} {b} ha hb := by
    change a * b ∈ Submodule.span ℂ S
    induction ha using Submodule.span_induction with
    | mem x hx =>
      induction hb using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span (hm x hx y hy)
      | zero => simp
      | add x y _ _ hpx hpy => rw [mul_add]; exact Submodule.add_mem _ hpx hpy
      | smul c x _ hpx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hpx
    | zero => simp
    | add x y _ _ hpx hpy => rw [add_mul]; exact Submodule.add_mem _ hpx hpy
    | smul c x _ hpx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hpx
  star_mem' {a} ha := by
    change star a ∈ Submodule.span ℂ S
    induction ha using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hs x hx)
    | zero => simp
    | add x y _ _ hpx hpy => rw [star_add]; exact Submodule.add_mem _ hpx hpy
    | smul c x _ hpx => rw [star_smul]; exact Submodule.smul_mem _ (star c) hpx

lemma linearStarSpan_eq_adjoin (S : Set A) (hm : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    (hs : ∀ x ∈ S, star x ∈ S) :
    linearStarSpan S hm hs = NonUnitalStarAlgebra.adjoin ℂ S := by
  apply le_antisymm
  · change Submodule.span ℂ S ≤ (NonUnitalStarAlgebra.adjoin ℂ S).toNonUnitalSubalgebra.toSubmodule
    exact Submodule.span_le.mpr (NonUnitalStarAlgebra.subset_adjoin ℂ S)
  · exact NonUnitalStarAlgebra.adjoin_le (fun _ hx => Submodule.subset_span hx)

lemma closure_adjoin_eq_closure_span (S : Set A) (hm : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    (hs : ∀ x ∈ S, star x ∈ S) :
    closure (NonUnitalStarAlgebra.adjoin ℂ S : Set A) =
      closure (Submodule.span ℂ S : Set A) := by
  rw [← linearStarSpan_eq_adjoin S hm hs]
  rfl

end AlgebraicSpan

end WeakPureInfiniteness
end

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

def clipScale (M t : ℝ) : ℝ := M / Real.sqrt (max (M ^ 2) t)

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ContinuousDeletion
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

open scoped BigOperators Topology CStarAlgebra

section CFCDeletion

variable {A : Type*} [CStarAlgebra A]

def ContinuouslySupported (U p : A) (S : Set ℝ) : Prop :=
  ∀ g : C(ℝ,ℝ), (∀ x ∈ S,g x=0) → p*cfc g U=0 ∧ cfc g U*p=0

end CFCDeletion

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_States
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

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma norm_add_one_of_nonneg [Nontrivial A] (b : A) (hb : 0 ≤ b) :
    ‖b + 1‖ = ‖b‖ + 1 := by
  apply le_antisymm
  · exact (norm_add_le _ _).trans (by rw [norm_one])
  · have hs : ‖b‖ + 1 ∈ spectrum ℝ (b + 1) := by
      simpa only [map_one, add_comm (1 : A) b] using
        (spectrum.add_mem_add_iff (R := ℝ) (a := b) (r := ‖b‖) (s := 1)).mpr
          (CStarAlgebra.norm_mem_spectrum_of_nonneg hb)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖b‖ + 1)] using
      spectrum.norm_le_norm_of_mem hs

def selfAdjointComplexification (f : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ where
  toFun a := (f (realPart a) : ℂ) + Complex.I * (f (imaginaryPart a) : ℂ)
  map_add' a b := by simp only [map_add, Complex.ofReal_add] <;> ring
  map_smul' c a := by
    simp only [realPart_smul, imaginaryPart_smul, map_sub, map_add,
      map_smul, smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
    apply Complex.ext <;> simp

omit [PartialOrder A] [StarOrderedRing A] in
lemma selfAdjointComplexification_apply (f : selfAdjoint A →ₗ[ℝ] ℝ) (b : selfAdjoint A) :
    selfAdjointComplexification f (b : A) = (f b : ℂ) := by
  have hr : realPart (b : A) = b := Subtype.ext b.property.coe_realPart
  simp [selfAdjointComplexification, hr, b.property.imaginaryPart]

lemma real_functional_nonneg (f : selfAdjoint A →L[ℝ] ℝ)
    (hf : ‖f‖ ≤ 1) (hf1 : f 1 = 1) (b : selfAdjoint A) (hb : 0 ≤ (b : A)) :
    0 ≤ f b := by
  let z : selfAdjoint A := ‖b‖ • 1 - b
  have hb' : IsSelfAdjoint (b : A) := b.property
  have hz : 0 ≤ (z : A) := by
    change 0 ≤ ‖b‖ • (1 : A) - (b : A)
    rw [sub_nonneg, ← Algebra.algebraMap_eq_smul_one]
    exact hb'.le_algebraMap_norm_self
  have hzn : ‖z‖ ≤ ‖b‖ := by
    change ‖(z : A)‖ ≤ ‖(b : A)‖
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (norm_nonneg _) hz).mpr
    change ‖b‖ • (1 : A) - (b : A) ≤ algebraMap ℝ A ‖(b : A)‖
    rw [Algebra.algebraMap_eq_smul_one]
    exact sub_le_self _ hb
  have hg : f z ≤ ‖b‖ := calc
    f z ≤ ‖f z‖ := Real.le_norm_self _
    _ ≤ ‖f‖ * ‖z‖ := f.le_opNorm z
    _ ≤ 1 * ‖b‖ := mul_le_mul hf hzn (norm_nonneg _) zero_le_one
    _ = ‖b‖ := one_mul _
  simp only [z, map_sub, map_smul, hf1, smul_eq_mul, mul_one] at hg
  linarith

def positiveComplexification (f : selfAdjoint A →L[ℝ] ℝ)
    (hf : ‖f‖ ≤ 1) (hf1 : f 1 = 1) : A →ₚ[ℂ] ℂ where
  toLinearMap := selfAdjointComplexification f.toLinearMap
  monotone' := by
    intro a b hab
    change selfAdjointComplexification f.toLinearMap a ≤ selfAdjointComplexification f.toLinearMap b
    rw [← sub_nonneg, ← map_sub]
    let z : selfAdjoint A := ⟨b-a, IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hab)⟩
    change 0 ≤ selfAdjointComplexification f.toLinearMap (z : A)
    rw [selfAdjointComplexification_apply]
    exact Complex.zero_le_real.mpr (real_functional_nonneg f hf hf1 z (sub_nonneg.mpr hab))

lemma positiveComplexification_apply (f : selfAdjoint A →L[ℝ] ℝ)
    (hf : ‖f‖ ≤ 1) (hf1 : f 1 = 1) (b : selfAdjoint A) :
    positiveComplexification f hf hf1 (b : A) = (f b : ℂ) :=
  selfAdjointComplexification_apply _ _

theorem exists_norming_positive_functional [Nontrivial A] (b : A) (hb : 0 ≤ b) :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧ f b = (‖b‖ : ℂ) := by
  let b' : selfAdjoint A := ⟨b, IsSelfAdjoint.of_nonneg hb⟩
  have hn : ‖b' + 1‖ = ‖b‖ + 1 := norm_add_one_of_nonneg b hb
  obtain ⟨f, hf, hfb⟩ := exists_dual_vector ℝ (b' + 1) (by rw [hn]; positivity)
  have hf1 : f 1 ≤ 1 := calc
    f 1 ≤ ‖f 1‖ := Real.le_norm_self _
    _ ≤ ‖f‖ * ‖(1 : selfAdjoint A)‖ := f.le_opNorm _
    _ = 1 := by rw [hf]; change 1 * ‖(1 : A)‖ = 1; simp
  have hfb' : f b' ≤ ‖b‖ := calc
    f b' ≤ ‖f b'‖ := Real.le_norm_self _
    _ ≤ ‖f‖ * ‖b'‖ := f.le_opNorm _
    _ = ‖b‖ := by rw [hf, one_mul]; rfl
  rw [map_add, hn] at hfb
  change f b' + f 1 = ‖b‖ + 1 at hfb
  have hfone : f 1 = 1 := by linarith
  have hfnorm : f b' = ‖b‖ := by linarith
  refine ⟨positiveComplexification f hf.le hfone, ?_, ?_⟩
  · change positiveComplexification f hf.le hfone ((1 : selfAdjoint A) : A) = 1
    rw [positiveComplexification_apply, hfone, Complex.ofReal_one]
  · change positiveComplexification f hf.le hfone (b' : A) = _
    rw [positiveComplexification_apply, hfnorm]

def gnsCyclicVector (f : A →ₚ[ℂ] ℂ) : f.GNS :=
  (f.toPreGNS 1 : f.GNS)

lemma norm_gnsCyclicVector (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) :
    ‖gnsCyclicVector f‖ = 1 := by
  rw [gnsCyclicVector, UniformSpace.Completion.norm_coe]
  rw [PositiveLinearMap.preGNS_norm_def]
  simp [hf]

lemma norm_gns_action_sq (f : A →ₚ[ℂ] ℂ) (a : A) :
    ‖f.gnsStarAlgHom a (gnsCyclicVector f)‖ ^ 2 = (f (star a * a)).re := by
  change ‖f.gnsNonUnitalStarAlgHom a (f.toPreGNS 1 : f.GNS)‖ ^ 2 = _
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe, UniformSpace.Completion.norm_coe]
  change ‖f.toPreGNS (a * 1)‖ ^ 2 = _
  rw [mul_one, PositiveLinearMap.preGNS_norm_def]
  apply Real.sq_sqrt
  exact (Complex.nonneg_iff.mp (f.map_nonneg (star_mul_self_nonneg a))).1

theorem exists_norming_gns [Nontrivial A] (a : A) :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧ ‖f.gnsStarAlgHom a‖ = ‖a‖ := by
  obtain ⟨f, hf, hfa⟩ := exists_norming_positive_functional (star a * a)
    (star_mul_self_nonneg a)
  refine ⟨f, hf, le_antisymm (NonUnitalStarAlgHom.norm_apply_le f.gnsNonUnitalStarAlgHom a) ?_⟩
  have hn : ‖f.gnsStarAlgHom a (gnsCyclicVector f)‖ = ‖a‖ := by
    have hs := norm_gns_action_sq f a
    rw [hfa, Complex.ofReal_re, CStarRing.norm_star_mul_self] at hs
    nlinarith [norm_nonneg (f.gnsStarAlgHom a (gnsCyclicVector f)), norm_nonneg a]
  calc
    ‖a‖ = ‖f.gnsStarAlgHom a (gnsCyclicVector f)‖ := hn.symm
    _ ≤ ‖f.gnsStarAlgHom a‖ * ‖gnsCyclicVector f‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖f.gnsStarAlgHom a‖ := by rw [norm_gnsCyclicVector f hf, mul_one]

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FaithfulRepresentation
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

open scoped ENNReal ComplexOrder InnerProductSpace

section DirectSum

variable {A : Type*} [NonUnitalCStarAlgebra A]

variable {ι : Type*} {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]

def sumRepresentation (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) :
    A →⋆ₙₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) where
  toFun a := lp.mapCLM 2 (fun i => π i a) (norm_nonneg a)
    (fun i => NonUnitalStarAlgHom.norm_apply_le (π i) a)
  map_zero' := by ext x i; simp [lp.mapCLM]
  map_add' a b := by
    ext x i
    change π i (a+b) (x i)=π i a (x i)+π i b (x i)
    rw [map_add, add_apply]
  map_smul' r a := by ext x i; simp [lp.mapCLM]
  map_mul' a b := by ext x i; simp [lp.mapCLM]
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
      lp.inner_eq_tsum, lp.inner_eq_tsum]
    apply tsum_congr
    intro i
    change inner ℂ (y i) (π i (star a) (x i))=inner ℂ (π i a (y i)) (x i)
    rw [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]

@[simp] lemma sumRepresentation_apply (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i))
    (a : A) (x : lp H 2) (i : ι) : sumRepresentation π a x i=π i a (x i) := rfl

lemma sumRepresentation_injective (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i))
    (hπ : ∀ a : A, (∀ i, π i a=0) → a=0) : Function.Injective (sumRepresentation π) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  apply hπ a
  intro i
  ext ξ
  have h := congrArg (fun T : lp H 2 →L[ℂ] lp H 2 => T (lp.single 2 i ξ) i) ha
  simpa using h

end DirectSum

universe hilbertUniverse

section GNSFaithful

variable (A : Type hilbertUniverse) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def universalGNSHilbert : ComplexHilbert.{hilbertUniverse} where
  Carrier := lp (fun f : A →ₚ[ℂ] ℂ => f.GNS) 2

def universalGNSRepresentation : A →⋆ₙₐ[ℂ]
    (universalGNSHilbert A →L[ℂ] universalGNSHilbert A) :=
  sumRepresentation (fun f : A →ₚ[ℂ] ℂ => f.gnsNonUnitalStarAlgHom)

lemma universalGNSRepresentation_injective : Function.Injective (universalGNSRepresentation A) := by
  apply sumRepresentation_injective
  intro a ha
  by_cases hA : Subsingleton A
  · exact Subsingleton.elim _ _
  · have : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
    obtain ⟨f,_,hf⟩ := exists_norming_gns a
    apply norm_eq_zero.mp
    rw [← hf]
    change ‖f.gnsNonUnitalStarAlgHom a‖=0
    rw [ha f, norm_zero]

end GNSFaithful

theorem exists_faithful_representation (A : Type hilbertUniverse) [NonUnitalCStarAlgebra A] :
    ∃ (H : ComplexHilbert.{hilbertUniverse}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), Function.Injective π := by
  let U := Unitization ℂ A
  let := CStarAlgebra.spectralOrder U
  let := CStarAlgebra.spectralOrderedRing U
  refine ⟨universalGNSHilbert U,
    (universalGNSRepresentation U).comp (Unitization.inrNonUnitalStarAlgHom ℂ A), ?_⟩
  exact (universalGNSRepresentation_injective U).comp Unitization.inr_injective

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_NonUnitalClosedRange
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

section NonUnital

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

lemma nonUnitalStarHom_continuous (φ : A →⋆ₙₐ[ℂ] B) : Continuous φ := by
  let f := (φ : A →ₗ[ℂ] B).mkContinuous 1 (by
    intro x
    change ‖φ x‖ ≤ 1 * ‖x‖
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le φ x)
  exact f.continuous

end NonUnital

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorFunctoriality
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

universe u v

section TensorFunctoriality

variable {A : Type u} {C D : Type v}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

def spatialMapRight (q : C →⋆ₙₐ[ℂ] D) : SpatialAmbient A C →⋆ₙₐ[ℂ] SpatialAmbient A D where
  toFun z := ⟨fun π => z (π.precompRight q), memℓp_infty ⟨‖z‖, by
    rintro _ ⟨π, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero z (π.precompRight q)⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp]
lemma spatialMapRight_elementary (q : C →⋆ₙₐ[ℂ] D) (a : A) (c : C) :
    spatialMapRight q (spatialElementary a c) = spatialElementary a (q c) := rfl

lemma spatialElementary_mem (a : A) (c : C) :
    spatialElementary a c ∈ minimalTensorSubalgebra A C :=
  NonUnitalStarSubalgebra.le_topologicalClosure _
    (NonUnitalStarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self (a,c)))

def minimalElementary (a : A) (c : C) : MinimalTensor A C :=
  ⟨spatialElementary a c, spatialElementary_mem a c⟩

lemma spatialMapRight_mem (q : C →⋆ₙₐ[ℂ] D) {z : SpatialAmbient A C}
    (hz : z ∈ minimalTensorSubalgebra A C) :
    spatialMapRight q z ∈ minimalTensorSubalgebra A D := by
  apply NonUnitalStarSubalgebra.topologicalClosure_minimal _
    (t := NonUnitalStarSubalgebra.comap (spatialMapRight q) (minimalTensorSubalgebra A D))
    (NonUnitalStarAlgebra.adjoin_le ?_) ?_ hz
  · rintro _ ⟨⟨a,c⟩, rfl⟩
    change spatialMapRight q (spatialElementary a c) ∈ minimalTensorSubalgebra A D
    rw [spatialMapRight_elementary]
    exact spatialElementary_mem a (q c)
  · exact isClosed_closure.preimage (nonUnitalStarHom_continuous (spatialMapRight q))

def minimalMapRight (q : C →⋆ₙₐ[ℂ] D) : MinimalTensor A C →⋆ₙₐ[ℂ] MinimalTensor A D :=
  NonUnitalStarAlgHom.codRestrict
    ((spatialMapRight q).comp (NonUnitalStarSubalgebraClass.subtype (minimalTensorSubalgebra A C)))
    (minimalTensorSubalgebra A D) (fun z => spatialMapRight_mem q z.property)

@[simp]
lemma minimalMapRight_elementary (q : C →⋆ₙₐ[ℂ] D) (a : A) (c : C) :
    minimalMapRight q (minimalElementary a c) = minimalElementary a (q c) := rfl

end TensorFunctoriality

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorCut
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

section TensorCut

variable {A : Type u} {C : Type v} [CStarAlgebra A] [NonUnitalCStarAlgebra C]

def rightElementaryHom : C →⋆ₙₐ[ℂ] MinimalTensor A C where
  toFun c := minimalElementary 1 c
  map_zero' := Subtype.ext (spatialElementary_zero_right 1)
  map_add' _ _ := Subtype.ext (spatialElementary_add_right _ _ _)
  map_smul' _ _ := Subtype.ext (spatialElementary_smul_right _ _ _)
  map_mul' x y := by
    apply Subtype.ext
    change spatialElementary 1 (x*y) = spatialElementary (1 : A) x * spatialElementary 1 y
    simpa only [one_mul] using spatialElementary_mul (1 : A) 1 x y
  map_star' x := by
    apply Subtype.ext
    change spatialElementary 1 (star x) = star (spatialElementary (1 : A) x)
    simpa only [star_one] using spatialElementary_star (1 : A) x

@[simp] lemma rightElementaryHom_apply (c : C) :
    rightElementaryHom (A := A) c = minimalElementary 1 c := rfl

end TensorCut

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_MatrixRepresentation
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

namespace WeakPureInfiniteness

section MatrixOperators

variable {n H : Type*} [Fintype n]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def matrixOperator (M : CStarMatrix n n (H →L[ℂ] H)) :
    (PiLp 2 (fun _ : n => H)) →L[ℂ] (PiLp 2 (fun _ : n => H)) :=
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => H)
  e.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun i => ∑ j, (M i j).comp (ContinuousLinearMap.proj j)).comp
      e.toContinuousLinearMap)

end MatrixOperators

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

def basisTensorMap (b : OrthonormalBasis n ℂ H) :
    PiLp 2 (fun _ : n => K) →ₗ[ℂ] H ⊗[ℂ] K where
  toFun x := ∑ i, b i ⊗ₜ[ℂ] x i
  map_add' x y := by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [TensorProduct.tmul_smul, Finset.smul_sum]

lemma basisTensorMap_inner (b : OrthonormalBasis n ℂ H)
    (x y : PiLp 2 (fun _ : n => K)) :
    inner ℂ (basisTensorMap b x) (basisTensorMap b y) = inner ℂ x y := by
  classical
  simp [basisTensorMap, sum_inner, inner_sum, TensorProduct.inner_tmul, b.inner_eq_ite,
    PiLp.inner_apply]

def basisTensorIsometry (b : OrthonormalBasis n ℂ H) :
    PiLp 2 (fun _ : n => K) →ₗᵢ[ℂ] H ⊗[ℂ] K :=
  LinearMap.isometryOfInner (E := PiLp 2 (fun _ : n => K))
    (E' := H ⊗[ℂ] K) (𝕜 := ℂ) (basisTensorMap b) (fun x y => basisTensorMap_inner b x y)

def tensorCoefficientMatrix {B : Type*} [AddCommGroup B] [Module ℂ B]
    (b : OrthonormalBasis n ℂ H) (T : H →L[ℂ] H) (a : B) : CStarMatrix n n B :=
  CStarMatrix.ofMatrix fun i j => (b.repr (T (b j)) i) • a

end BasisTensor

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorCompression
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

section FiniteTensorCompressions

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def compress (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    (T : H →L[ℂ] H) : V →L[ℂ] V :=
  V.orthogonalProjectionOnto.comp (T.comp V.subtypeL)

lemma norm_tensorSum_compress_le {ι : Type*} (s : Finset ι)
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    (T : ι → H →L[ℂ] H) (S : ι → K →L[ℂ] K) :
    ‖∑ i ∈ s, TensorProduct.mapL (compress V (T i)) (S i)‖ ≤
      ‖∑ i ∈ s, TensorProduct.mapL (T i) (S i)‖ := by
  let P := V.orthogonalProjectionOnto.rTensor K
  let J := (V.subtypeₗᵢ.rTensor K).toContinuousLinearMap
  have hP : ‖P‖ ≤ 1 := by
    apply (ContinuousLinearMap.norm_rTensor_le K _).trans
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul] using V.norm_orthogonalProjectionOnto_apply_le x
  have hJ : ‖J‖ ≤ 1 := (V.subtypeₗᵢ.rTensor K).norm_toContinuousLinearMap_le
  have he : (∑ i ∈ s, TensorProduct.mapL (compress V (T i)) (S i)) =
      P.comp ((∑ i ∈ s, TensorProduct.mapL (T i) (S i)).comp J) := by
    apply ContinuousLinearMap.ext
    intro z
    induction z using OAI.tensorInductionOn with
    | tmul v k =>
      simp only [sum_apply, TensorProduct.mapL_tmul, ContinuousLinearMap.comp_apply,
        J, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.rTensor_apply,
        LinearMap.rTensor_tmul, P, map_sum, ContinuousLinearMap.rTensor_tmul]
      rfl
    | add z w hz hw => simp only [map_add, hz, hw]
  rw [he]
  calc
    _ ≤ ‖P‖ * (‖∑ i ∈ s, TensorProduct.mapL (T i) (S i)‖ * ‖J‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖∑ i ∈ s, TensorProduct.mapL (T i) (S i)‖ * 1) :=
      mul_le_mul hP (mul_le_mul_of_nonneg_left hJ (ContinuousLinearMap.opNorm_nonneg _))
        (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (ContinuousLinearMap.opNorm_nonneg J)) zero_le_one
    _ = _ := by rw [mul_one, one_mul]

lemma norm_tensorSum_le_of_finite_compressions {ι : Type*} [Finite ι] (s : Finset ι)
    (T : ι → H →L[ℂ] H) (S : ι → K →L[ℂ] K) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (V : Submodule ℂ H) [FiniteDimensional ℂ V],
      ‖∑ i ∈ s, TensorProduct.mapL (compress V (T i)) (S i)‖ ≤ C) :
    ‖∑ i ∈ s, TensorProduct.mapL (T i) (S i)‖ ≤ C := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro z
  obtain ⟨m, ξ, η, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
  let V₀ := Submodule.span ℂ (Set.range ξ)
  let V₁ := Submodule.span ℂ (Set.range fun p : ι × Fin m => T p.1 (ξ p.2))
  let V := V₀ ⊔ V₁
  let : FiniteDimensional ℂ V₀ := FiniteDimensional.span_of_finite ℂ (Set.finite_range ξ)
  let : FiniteDimensional ℂ V₁ := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hξ (j : Fin m) : ξ j ∈ V :=
    (show V₀ ≤ V from le_sup_left) (Submodule.subset_span (Set.mem_range_self j))
  have hT (i : ι) (j : Fin m) : T i (ξ j) ∈ V :=
    (show V₁ ≤ V from le_sup_right) (Submodule.subset_span (Set.mem_range_self (i,j)))
  let v : V ⊗[ℂ] K := ∑ j, (⟨ξ j, hξ j⟩ : V) ⊗ₜ[ℂ] η j
  let J : (V ⊗[ℂ] K) →ₗᵢ[ℂ] (H ⊗[ℂ] K) := V.subtypeₗᵢ.rTensor K
  have hv : J v = ∑ j, ξ j ⊗ₜ[ℂ] η j := by
    simp only [J, v, map_sum, LinearIsometry.rTensor_apply, LinearMap.rTensor_tmul]
    rfl
  have he : J ((∑ i ∈ s, TensorProduct.mapL (compress V (T i)) (S i)) v) =
      (∑ i ∈ s, TensorProduct.mapL (T i) (S i)) (∑ j, ξ j ⊗ₜ[ℂ] η j) := by
    simp only [sum_apply, v, map_sum, TensorProduct.mapL_tmul,
      J, LinearIsometry.rTensor_apply, LinearMap.rTensor_tmul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    exact Submodule.starProjection_eq_self_iff.mpr (hT j i)
  rw [← he, J.norm_map, ← hv, J.norm_map]
  exact (ContinuousLinearMap.le_opNorm _ v).trans
    (mul_le_mul_of_nonneg_right (h V) (norm_nonneg v))

end FiniteTensorCompressions

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorFlip
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

section TensorFlip

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

lemma norm_tensorSum_flip {ι : Type*} (s : Finset ι)
    (T : ι → H →L[ℂ] H) (S : ι → K →L[ℂ] K) :
    ‖∑ i ∈ s, TensorProduct.mapL (T i) (S i)‖ =
      ‖∑ i ∈ s, TensorProduct.mapL (S i) (T i)‖ := by
  let e := TensorProduct.commIsometry ℂ H K
  have he (x : H ⊗[ℂ] K) :
      e ((∑ i ∈ s, TensorProduct.mapL (T i) (S i)) x) =
        (∑ i ∈ s, TensorProduct.mapL (S i) (T i)) (e x) := by
    induction x using OAI.tensorInductionOn with
    | tmul x y => simp [e, TensorProduct.commIsometry_apply]
    | add x y hx hy => simp only [map_add,hx,hy]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _)
    intro x
    rw [← e.norm_map ((∑ i ∈ s, TensorProduct.mapL (T i) (S i)) x), he]
    simpa using (∑ i ∈ s, TensorProduct.mapL (S i) (T i)).le_opNorm (e x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _)
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    rw [← he, e.norm_map, e.norm_map]
    exact (∑ i ∈ s, TensorProduct.mapL (T i) (S i)).le_opNorm x

end TensorFlip

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorInjectivity
attribute [-simp] _root_.OAI.WeakPureInfiniteness.rightElementaryHom_apply
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

section TensorLeft

universe leftUniverse rightUniverse

variable {A B : Type leftUniverse} {C : Type rightUniverse}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

def SpatialRepresentation.precompLeft (π : SpatialRepresentation B C)
    (φ : A →⋆ₙₐ[ℂ] B) : SpatialRepresentation A C where
  left := π.left
  right := π.right
  leftRep := π.leftRep.comp φ
  rightRep := π.rightRep

def spatialMapLeft (φ : A →⋆ₙₐ[ℂ] B) : SpatialAmbient A C →⋆ₙₐ[ℂ] SpatialAmbient B C where
  toFun z := ⟨fun π => z (π.precompLeft φ), memℓp_infty ⟨‖z‖, by
    rintro _ ⟨π, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero z _⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp] lemma spatialMapLeft_elementary (φ : A →⋆ₙₐ[ℂ] B) (a : A) (c : C) :
    spatialMapLeft φ (spatialElementary a c) = spatialElementary (φ a) c := rfl

lemma spatialMapLeft_mem (φ : A →⋆ₙₐ[ℂ] B) {z : SpatialAmbient A C}
    (hz : z ∈ minimalTensorSubalgebra A C) :
    spatialMapLeft φ z ∈ minimalTensorSubalgebra B C := by
  apply NonUnitalStarSubalgebra.topologicalClosure_minimal _
    (t := NonUnitalStarSubalgebra.comap (spatialMapLeft φ) (minimalTensorSubalgebra B C))
    (NonUnitalStarAlgebra.adjoin_le ?_) ?_ hz
  · rintro _ ⟨⟨a,c⟩, rfl⟩
    change spatialMapLeft φ (spatialElementary a c) ∈ minimalTensorSubalgebra B C
    rw [spatialMapLeft_elementary]
    exact spatialElementary_mem (φ a) c
  · exact isClosed_closure.preimage (nonUnitalStarHom_continuous (spatialMapLeft φ))

def minimalMapLeft (φ : A →⋆ₙₐ[ℂ] B) : MinimalTensor A C →⋆ₙₐ[ℂ] MinimalTensor B C :=
  NonUnitalStarAlgHom.codRestrict
    ((spatialMapLeft φ).comp (NonUnitalStarSubalgebraClass.subtype (minimalTensorSubalgebra A C)))
    (minimalTensorSubalgebra B C) (fun z => spatialMapLeft_mem φ z.property)

@[simp] lemma minimalMapLeft_elementary (φ : A →⋆ₙₐ[ℂ] B) (a : A) (c : C) :
    minimalMapLeft φ (minimalElementary a c) = minimalElementary (φ a) c := rfl

lemma spatialSum_apply {ι : Type*} (s : Finset ι) (a : ι → A) (c : ι → C)
    (π : SpatialRepresentation A C) :
    (∑ i ∈ s, spatialElementary (a i) (c i)) π =
      (∑ i ∈ s, TensorProduct.mapL (π.leftRep (a i)) (π.rightRep (c i))).completion := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,completion_zero]; rfl
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi,completion_add]
    change _ + (∑ j ∈ s, spatialElementary (a j) (c j)) π = _
    rw [ih]
    rfl

end TensorLeft

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FullGroupAlgebra
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

namespace WeakPureInfiniteness

noncomputable def closedStarSpan {B : Type*} [CStarAlgebra B] (s : Set B) :
    StarSubalgebra ℂ B := (StarAlgebra.adjoin ℂ s).topologicalClosure

lemma closedStarSpan_closed {B : Type*} [CStarAlgebra B] (s : Set B) :
    IsClosed (closedStarSpan s : Set B) := isClosed_closure

lemma subset_closedStarSpan {B : Type*} [CStarAlgebra B] (s : Set B) :
    s ⊆ closedStarSpan s := fun _ hx =>
  StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ s hx)

@[instance_reducible]
noncomputable def closedStarSpanCStar {B : Type*} [CStarAlgebra B] (s : Set B) :
    CStarAlgebra (closedStarSpan s) := by
  letI := closedStarSpan_closed s
  infer_instance

structure GroupRepresentation (G : Type u) [Group G] where
  hilbert : ComplexHilbert.{u}
  [nontrivial : Nontrivial hilbert]
  group : G →* unitary (hilbert →L[ℂ] hilbert)

attribute [instance] GroupRepresentation.nontrivial

def FullGroupAmbient (G : Type u) [Group G] : Type (u + 1) :=
  lp (fun π : GroupRepresentation G => π.hilbert →L[ℂ] π.hilbert) ∞

instance instCStarAlgebraFullGroupAmbient (G : Type u) [Group G] : CStarAlgebra (FullGroupAmbient G) := by
  unfold FullGroupAmbient
  exact { }

instance instCoeFunFullGroupAmbientForallContinuousLinearMapComplexIdCarrierHilbert (G : Type u) [Group G] : CoeFun (FullGroupAmbient G)
    (fun _ => ∀ π : GroupRepresentation G, π.hilbert →L[ℂ] π.hilbert) := ⟨fun x => x.val⟩

variable {G : Type u} [Group G]

def fullGroupOperator (g : G) : FullGroupAmbient G :=
  ⟨fun π => π.group g, memℓp_infty ⟨1, by
    rintro _ ⟨π, rfl⟩
    exact le_of_eq (CStarRing.norm_coe_unitary (π.group g))⟩⟩

lemma fullGroupOperator_one : fullGroupOperator (1 : G) = 1 := by
  apply Subtype.ext
  funext π
  change (π.group 1 : π.hilbert →L[ℂ] π.hilbert) = 1
  simp

lemma fullGroupOperator_mul (g h : G) :
    fullGroupOperator (g * h) = fullGroupOperator g * fullGroupOperator h := by
  apply Subtype.ext
  funext π
  change (π.group (g * h) : π.hilbert →L[ℂ] π.hilbert) = (π.group g : _) * π.group h
  simp

lemma fullGroupOperator_inv (g : G) : fullGroupOperator g⁻¹ = star (fullGroupOperator g) := by
  apply Subtype.ext
  funext π
  change (π.group g⁻¹ : π.hilbert →L[ℂ] π.hilbert) = star (π.group g : _)
  rw [map_inv]
  rfl

def fullGroupSubalgebra (G : Type u) [Group G] : StarSubalgebra ℂ (FullGroupAmbient G) :=
  closedStarSpan (Set.range (fullGroupOperator (G := G)))

def FullGroupAlgebra (G : Type u) [Group G] : Type (u + 1) := fullGroupSubalgebra G

instance instCStarAlgebraFullGroupAlgebra : CStarAlgebra (FullGroupAlgebra G) := closedStarSpanCStar _

def fullGroupElement (g : G) : FullGroupAlgebra G :=
  ⟨fullGroupOperator g, subset_closedStarSpan _ ⟨g, rfl⟩⟩

@[simp]
lemma fullGroupElement_one : fullGroupElement (1 : G) = 1 :=
  Subtype.ext fullGroupOperator_one

@[simp]
lemma fullGroupElement_mul (g h : G) :
    fullGroupElement (g * h) = fullGroupElement g * fullGroupElement h :=
  Subtype.ext (fullGroupOperator_mul g h)

@[simp]
lemma fullGroupElement_inv (g : G) : fullGroupElement g⁻¹ = star (fullGroupElement g) :=
  Subtype.ext (fullGroupOperator_inv g)

def fullGroupEvaluation (π : GroupRepresentation G) :
    FullGroupAlgebra G →⋆ₐ[ℂ] (π.hilbert →L[ℂ] π.hilbert) where
  toFun x := x.val π
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_one' := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]
lemma fullGroupEvaluation_element (π : GroupRepresentation G) (g : G) :
    fullGroupEvaluation π (fullGroupElement g) = π.group g := rfl

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SpatialVectorStates
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instCoeFunFullGroupAmbientForallContinuousLinearMapComplexIdCarrierHilbert
attribute [-simp] _root_.OAI.WeakPureInfiniteness.fullGroupEvaluation_element _root_.OAI.WeakPureInfiniteness.minimalMapLeft_elementary _root_.OAI.WeakPureInfiniteness.minimalMapRight_elementary _root_.OAI.WeakPureInfiniteness.rightElementaryHom_apply _root_.OAI.WeakPureInfiniteness.spatialMapLeft_elementary _root_.OAI.WeakPureInfiniteness.spatialMapRight_elementary
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

universe u v

section SpatialVectorStates

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def spatialVectorFunctional (π : SpatialRepresentation A B) (ξ : π.space) :
    SpatialAmbient A B →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun z := inner ℂ ξ (z π ξ)
      map_add' x y := by
        change inner ℂ ξ ((x π + y π) ξ) = _
        simp only [add_apply, inner_add_right]
      map_smul' c x := by
        change inner ℂ ξ (c • (x π ξ)) = c • inner ℂ ξ (x π ξ)
        exact inner_smul_right ξ (x π ξ) c }
    (‖ξ‖ * ‖ξ‖) (by
      intro z
      calc
        ‖inner ℂ ξ (z π ξ)‖ ≤ ‖ξ‖ * ‖z π ξ‖ := norm_inner_le_norm _ _
        _ ≤ ‖ξ‖ * (‖z π‖ * ‖ξ‖) := mul_le_mul_of_nonneg_left ((z π).le_opNorm ξ) (norm_nonneg _)
        _ ≤ ‖ξ‖ * (‖z‖ * ‖ξ‖) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero z π) (norm_nonneg _))
          (norm_nonneg _)
        _ = (‖ξ‖ * ‖ξ‖) * ‖z‖ := by ring)

@[simp]
lemma spatialVectorFunctional_elementary (π : SpatialRepresentation A B)
    (ξ : π.left ⊗[ℂ] π.right) (a : A) (b : B) :
    spatialVectorFunctional π (ξ : π.space) (spatialElementary a b) =
      inner ℂ ξ (TensorProduct.mapL (π.leftRep a) (π.rightRep b) ξ) := by
  change inner ℂ (ξ : Completion _) ((TensorProduct.mapL (π.leftRep a) (π.rightRep b)).completion
    (ξ : Completion _)) = _
  simp only [ContinuousLinearMap.completion_apply_coe, Completion.inner_coe]

end SpatialVectorStates

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorDensity
attribute [-simp] _root_.OAI.WeakPureInfiniteness.minimalMapLeft_elementary _root_.OAI.WeakPureInfiniteness.rightElementaryHom_apply _root_.OAI.WeakPureInfiniteness.spatialMapLeft_elementary _root_.OAI.WeakPureInfiniteness.spatialVectorFunctional_elementary
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

universe u v

section TensorContinuity

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def spatialElementaryLeft (b : B) : A →L[ℂ] SpatialAmbient A B :=
  LinearMap.mkContinuous
    { toFun a := spatialElementary a b
      map_add' a a' := spatialElementary_add_left a a' b
      map_smul' c a := spatialElementary_smul_left c a b }
    ‖b‖ (fun a => by
      change ‖spatialElementary a b‖ ≤ ‖b‖ * ‖a‖
      simpa only [mul_comm ‖b‖] using norm_spatialElementary_le a b)

def spatialElementaryRight (a : A) : B →L[ℂ] SpatialAmbient A B :=
  LinearMap.mkContinuous
    { toFun b := spatialElementary a b
      map_add' b b' := spatialElementary_add_right a b b'
      map_smul' c b := spatialElementary_smul_right c a b }
    ‖a‖ (norm_spatialElementary_le a)

@[simp] lemma spatialElementaryLeft_apply (a : A) (b : B) :
    spatialElementaryLeft b a = spatialElementary a b := rfl

@[simp] lemma spatialElementaryRight_apply (a : A) (b : B) :
    spatialElementaryRight a b = spatialElementary a b := rfl

end TensorContinuity

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_DiagonalRegular
attribute [-simp] _root_.OAI.WeakPureInfiniteness.minimalMapLeft_elementary _root_.OAI.WeakPureInfiniteness.rightElementaryHom_apply _root_.OAI.WeakPureInfiniteness.spatialMapLeft_elementary
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

namespace WeakPureInfiniteness

section ContinuousGroupCoefficients

variable {G : Type u} [Group G]

def starHomCLM {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) : A →L[ℂ] B :=
  φ.toAlgHom.toLinearMap.mkContinuous 1 (fun x => by
    change ‖φ x‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le φ x)

@[simp] lemma starHomCLM_apply {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) (x : A) : starHomCLM φ x = φ x := rfl

end ContinuousGroupCoefficients

section MinimalElementaryContinuity

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def minimalElementaryLeft (b : B) : A →L[ℂ] MinimalTensor A B :=
  LinearMap.mkContinuous
    { toFun a := minimalElementary a b
      map_add' a a' := Subtype.ext (spatialElementary_add_left a a' b)
      map_smul' c a := Subtype.ext (spatialElementary_smul_left c a b) }
    ‖b‖ (fun a => by
      change ‖spatialElementary a b‖ ≤ ‖b‖ * ‖a‖
      simpa only [mul_comm ‖b‖] using norm_spatialElementary_le a b)

def minimalElementaryRight (a : A) : B →L[ℂ] MinimalTensor A B :=
  LinearMap.mkContinuous
    { toFun b := minimalElementary a b
      map_add' b b' := Subtype.ext (spatialElementary_add_right a b b')
      map_smul' c b := Subtype.ext (spatialElementary_smul_right c a b) }
    ‖a‖ (norm_spatialElementary_le a)

@[simp] lemma minimalElementaryLeft_apply (a : A) (b : B) :
    minimalElementaryLeft b a = minimalElementary a b := rfl

@[simp] lemma minimalElementaryRight_apply (a : A) (b : B) :
    minimalElementaryRight a b = minimalElementary a b := rfl

end MinimalElementaryContinuity

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UniversalFreeEmbedding
attribute [-simp] _root_.OAI.WeakPureInfiniteness.spatialVectorFunctional_elementary
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

namespace WeakPureInfiniteness

structure ContractionRepresentation where
  hilbert : ComplexHilbert.{0}
  [nontrivial : Nontrivial hilbert]
  operator : hilbert →L[ℂ] hilbert
  norm_operator_le_one : ‖operator‖ ≤ 1

attribute [instance] ContractionRepresentation.nontrivial

def ContractionAmbient : Type 1 :=
  lp (fun π : ContractionRepresentation => π.hilbert →L[ℂ] π.hilbert) ∞

instance instCStarAlgebraContractionAmbient : CStarAlgebra ContractionAmbient := by
  unfold ContractionAmbient
  exact { }

instance instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert : CoeFun ContractionAmbient
    (fun _ => ∀ π : ContractionRepresentation, π.hilbert →L[ℂ] π.hilbert) :=
  ⟨fun z => z.val⟩

noncomputable def universalOperator : ContractionAmbient :=
  ⟨fun π => π.operator, memℓp_infty ⟨1, by
    rintro _ ⟨π, rfl⟩
    exact π.norm_operator_le_one⟩⟩

noncomputable def universalContractionSubalgebra : StarSubalgebra ℂ ContractionAmbient :=
  closedStarSpan {universalOperator}

def UniversalContraction : Type 1 := universalContractionSubalgebra

instance instCStarAlgebraUniversalContraction : CStarAlgebra UniversalContraction := closedStarSpanCStar _

noncomputable def universalContractionGenerator : UniversalContraction :=
  ⟨universalOperator, subset_closedStarSpan _ (Set.mem_singleton _)⟩

noncomputable def contractionEvaluation (π : ContractionRepresentation) :
    UniversalContraction →⋆ₐ[ℂ] (π.hilbert →L[ℂ] π.hilbert) where
  toFun x := x.val π
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_one' := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]
lemma contractionEvaluation_star (π : ContractionRepresentation) (x : UniversalContraction) :
    contractionEvaluation π (star x) = star (contractionEvaluation π x) := rfl

@[simp]
lemma contractionEvaluation_smul (π : ContractionRepresentation) (c : ℂ) (x : UniversalContraction) :
    contractionEvaluation π (c • x) = c • contractionEvaluation π x := rfl

@[simp]
lemma contractionEvaluation_generator (π : ContractionRepresentation) :
    contractionEvaluation π universalContractionGenerator = π.operator := rfl

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_WordCompression
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

section Words

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def wordEval (T : ι → E →L[ℂ] E) : List ι → E →L[ℂ] E
  | [] => ContinuousLinearMap.id ℂ E
  | i :: w => (T i).comp (wordEval T w)

end Words

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_PolynomialCompression
attribute [-simp] _root_.OAI.WeakPureInfiniteness.spatialVectorFunctional_elementary
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

noncomputable def operatorLetters {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) :
    Bool → H →L[ℂ] H := fun i => if i then T else star T

noncomputable def universalWord : List Bool → UniversalContraction
  | [] => 1
  | i :: w => (if i then universalContractionGenerator else star universalContractionGenerator) *
      universalWord w

@[simp]
lemma contractionEvaluation_word (π : ContractionRepresentation) (w : List Bool) :
    contractionEvaluation π (universalWord w) = wordEval (operatorLetters π.operator) w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    cases i <;> simp [universalWord, wordEval, operatorLetters, ih,
      ContinuousLinearMap.mul_def]

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CrossUniverseTensorMap
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

open scoped TensorProduct ENNReal

open UniformSpace Topology

universe u v w x

section

variable {A : Type u} {B : Type v} {C : Type w} {D : Type x}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

lemma minimalElementary_mul (a a' : A) (c c' : C) :
    minimalElementary (a*a') (c*c')=minimalElementary a c*minimalElementary a' c' :=
  Subtype.ext (spatialElementary_mul a a' c c')

lemma minimalElementary_star (a : A) (c : C) :
    minimalElementary (star a) (star c)=star (minimalElementary a c) :=
  Subtype.ext (spatialElementary_star a c)

variable (φ : A →⋆ₙₐ[ℂ] B) (ψ : C →⋆ₙₐ[ℂ] D)

def crossTensorPair (p : A × C) : MinimalTensor A C × MinimalTensor B D :=
  (minimalElementary p.1 p.2,minimalElementary (φ p.1) (ψ p.2))

lemma crossTensorPair_mul (p q : A × C) : crossTensorPair φ ψ (p*q)=
    crossTensorPair φ ψ p*crossTensorPair φ ψ q := by
  ext <;> simp only [crossTensorPair,Prod.fst_mul,Prod.snd_mul,map_mul,minimalElementary_mul]

lemma crossTensorPair_star (p : A × C) : crossTensorPair φ ψ (star p)=star (crossTensorPair φ ψ p) := by
  ext <;> simp only [crossTensorPair,Prod.fst_star,Prod.snd_star,map_star,minimalElementary_star]

def crossTensorGraph : NonUnitalStarSubalgebra ℂ (MinimalTensor A C × MinimalTensor B D) :=
  (NonUnitalStarAlgebra.adjoin ℂ (Set.range (crossTensorPair φ ψ))).topologicalClosure

instance crossTensorGraphCStar : NonUnitalCStarAlgebra (crossTensorGraph φ ψ) := by
  letI : IsClosed (crossTensorGraph φ ψ : Set (MinimalTensor A C × MinimalTensor B D)) := isClosed_closure
  infer_instance

def crossTensorFirst : crossTensorGraph φ ψ →⋆ₙₐ[ℂ] MinimalTensor A C where
  toFun z := z.val.1
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_LocalConnection
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

abbrev ElementCuntzSubequiv (a b : A) : Prop :=
  CuntzSubequiv (diagonalCopies 1 a) (diagonalCopies 1 b)

end

end WeakPureInfiniteness
end

end OAI
end


