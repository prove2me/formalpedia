-- Prove2me | Definitions.Def_OAIQ246W005
-- name    : OAIQ246W005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T07:20:19.139744+00:00
-- url     : https://prove2.me/theorems/7a840829-5e04-44a2-bd5f-d4ccfbafaaaf
-- title:
--   Definitions bundle OAIQ246W005 of the split of OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any` and `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite`, carved from OpenAI's openai/math development (OpenAI, *Weak pure infiniteness and O-infinity absorption (result family 303)*, OpenAI Math Release, September 25, 2026, result family 303, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 8 definitions and 5 theorems. The definitions and types are `OAI.WeakPureInfiniteness.regularPairingLeft`, `OAI.WeakPureInfiniteness.regularPairingRight`, `OAI.WeakPureInfiniteness.spatialRightMultiplierHom`, `OAI.WeakPureInfiniteness.universalContractionMap`, `OAI.WeakPureInfiniteness.universalFaithfulRepresentation`, `OAI.WeakPureInfiniteness.universalUnitalRepresentation`, `OAI.WeakPureInfiniteness.wordTensor`, `OAI.WeakPureInfiniteness.wordTensorLinear`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`WeakInfiniteness_DiagonalRegular`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/DiagonalRegular.lean), [`WeakInfiniteness_FaithfulContractions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/FaithfulContractions.lean), [`WeakInfiniteness_PolynomialSpan`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/PolynomialSpan.lean), [`WeakInfiniteness_TensorMultiplier`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/TensorMultiplier.lean), [`WeakInfiniteness_UniformModels`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/UniformModels.lean), [`WeakInfiniteness_WordTensorDensity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/WordTensorDensity.lean).
--
--   **Imports.** It imports the published bundle `Def_ExactInfiniteness`; the bundle `OAIQ246W003` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.WeakPureInfiniteness.exists_separated_supported_model_any`, `OAI.WeakPureInfiniteness.exists_uniform_gap_any` and `OAI.WeakPureInfiniteness.universal_fixed_kernel_impossible`.
-- source:
--   OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 303; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-pure-infiniteness-and-O-infinity-absorption-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W003

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_DiagonalRegular
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

section RegularPairing

variable {G : Type u} [Group G]

def regularPairingRight (a : FullGroupAlgebra G) : FullGroupAlgebra G →L[ℂ] ℂ :=
  (innerSL ℂ (regularBase (G := G))).comp
    ((fullGroupEvaluation (leftRegularRepresentation G) a).comp
      ((ContinuousLinearMap.apply ℂ (GroupHilbert G) regularBase).comp
        (starHomCLM rightGroupEvaluation)))

def regularPairingLeft (b : FullGroupAlgebra G) : FullGroupAlgebra G →L[ℂ] ℂ :=
  (innerSL ℂ (regularBase (G := G))).comp
    ((ContinuousLinearMap.apply ℂ (GroupHilbert G) (rightGroupEvaluation b regularBase)).comp
      (starHomCLM (fullGroupEvaluation (leftRegularRepresentation G))))

end RegularPairing

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FaithfulContractions
attribute [-instance] _root_.OAI.WeakPureInfiniteness.universalGraphCStar
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

def universalFaithfulRepresentation :
    UniversalContraction →⋆ₙₐ[ℂ] (universalHilbert →L[ℂ] universalHilbert) :=
  contractionAmbientRepresentation.comp
    universalContractionSubalgebra.subtype.toNonUnitalStarAlgHom

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_PolynomialSpan
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
attribute [-simp] _root_.OAI.WeakPureInfiniteness.fullToUniversal_element
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

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma universalGraphFirst_isometry (v : B) (hv : ‖v‖ ≤ 1) :
    Isometry (universalGraphFirst v) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro z
  change ‖z.val.1‖ = ‖z.val‖
  rw [Prod.norm_def, max_eq_left (universal_graph_bound v hv z.val z.property)]

lemma universalGraphFirst_surjective (v : B) (hv : ‖v‖ ≤ 1) :
    Function.Surjective (universalGraphFirst v) := by
  let : CompleteSpace (universalGraph v) := (closedStarSpan_closed _).completeSpace_coe
  let φ := universalGraphFirst v
  let S := φ.range.map universalContractionSubalgebra.subtype
  have hS : IsClosed (S : Set ContractionAmbient) := by
    have hi : Isometry (universalContractionSubalgebra.subtype.comp φ) :=
      (isometry_subtype_coe).comp (universalGraphFirst_isometry v hv)
    have he : (S : Set ContractionAmbient) = Set.range (universalContractionSubalgebra.subtype.comp φ) := by
      ext x
      simp only [S]
      change (∃ y, (∃ z, φ z = y) ∧ _ = x) ↔ ∃ z, _ = x
      constructor
      · rintro ⟨y, ⟨z,rfl⟩, rfl⟩; exact ⟨z,rfl⟩
      · rintro ⟨z,rfl⟩; exact ⟨φ z, ⟨z,rfl⟩, rfl⟩
    rw [he]
    exact hi.isClosedEmbedding.isClosed_range
  have hgen : universalOperator ∈ S := by
    refine ⟨universalContractionGenerator, ?_, rfl⟩
    exact ⟨⟨(universalContractionGenerator, v), subset_closedStarSpan _ (Set.mem_singleton _)⟩,rfl⟩
  have hs : universalContractionSubalgebra ≤ S :=
    closedStarSpan_le {universalOperator} S hS (Set.singleton_subset_iff.mpr hgen)
  intro x
  obtain ⟨y,hy,hey⟩ := hs x.property
  obtain ⟨z,hz⟩ := hy
  refine ⟨z, ?_⟩
  apply Subtype.ext
  exact (congrArg (fun y : UniversalContraction => y.val) hz).trans hey

def universalContractionMap (v : B) (hv : ‖v‖ ≤ 1) : UniversalContraction →⋆ₐ[ℂ] B :=
  ((StarAlgHom.snd ℂ UniversalContraction B).comp (universalGraph v).subtype).comp
    (StarAlgEquiv.ofBijective (universalGraphFirst v)
      ⟨(universalGraphFirst_isometry v hv).injective, universalGraphFirst_surjective v hv⟩).symm.toStarAlgHom

@[simp] lemma universalContractionMap_generator (v : B) (hv : ‖v‖ ≤ 1) :
    universalContractionMap v hv universalContractionGenerator = v := by
  let z : universalGraph v :=
    ⟨(universalContractionGenerator, v), subset_closedStarSpan _ (Set.mem_singleton _)⟩
  let e := StarAlgEquiv.ofBijective (universalGraphFirst v)
    ⟨(universalGraphFirst_isometry v hv).injective, universalGraphFirst_surjective v hv⟩
  have he : e z = universalContractionGenerator := rfl
  change (e.symm universalContractionGenerator).val.2 = v
  rw [← he, StarAlgEquiv.symm_apply_apply]

@[simp] lemma universalContractionMap_polynomial (v : B) (hv : ‖v‖ ≤ 1)
    (c : List Bool →₀ ℂ) :
    universalContractionMap v hv (algebraPolynomial universalContractionGenerator c) =
      algebraPolynomial v c := by
  rw [map_algebraPolynomial, universalContractionMap_generator]

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorMultiplier
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.instCoeFunFullGroupAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
attribute [-simp] _root_.OAI.WeakPureInfiniteness.contractionEvaluation_generator _root_.OAI.WeakPureInfiniteness.contractionEvaluation_smul _root_.OAI.WeakPureInfiniteness.contractionEvaluation_star _root_.OAI.WeakPureInfiniteness.contractionEvaluation_word _root_.OAI.WeakPureInfiniteness.fullGroupEvaluation_element _root_.OAI.WeakPureInfiniteness.minimalElementaryLeft_apply _root_.OAI.WeakPureInfiniteness.minimalElementaryRight_apply _root_.OAI.WeakPureInfiniteness.minimalMapAny_elementary _root_.OAI.WeakPureInfiniteness.minimalMapLeftAny_elementary _root_.OAI.WeakPureInfiniteness.rightElementaryHom_apply _root_.OAI.WeakPureInfiniteness.spatialElementaryLeft_apply _root_.OAI.WeakPureInfiniteness.spatialElementaryRight_apply _root_.OAI.WeakPureInfiniteness.spatialVectorFunctional_elementary
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

universe u v

noncomputable section

open scoped TensorProduct ENNReal ComplexOrder

open UniformSpace Filter Topology

variable {A B : Type u} {C D : Type v}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

def spatialRightMultiplierHom : C →⋆ₙₐ[ℂ] SpatialAmbient A C where
  toFun := spatialRightMultiplier
  map_zero' := by
    apply Subtype.ext; funext π
    change (TensorProduct.mapL _ (π.rightRep 0)).completion=0
    simp [completion_zero]
  map_add' c d := by
    apply Subtype.ext; funext π
    change (TensorProduct.mapL _ (π.rightRep (c+d))).completion=_+_
    rw [map_add, TensorProduct.mapL_add_right, completion_add]
    rfl
  map_smul' r c := by
    apply Subtype.ext; funext π
    change (TensorProduct.mapL _ (π.rightRep (r • c))).completion=r • _
    rw [map_smul, TensorProduct.mapL_smul_right, completion_smul]
    rfl
  map_mul' c d := by
    apply Subtype.ext; funext π
    change (TensorProduct.mapL (1 : π.left →L[ℂ] π.left) (π.rightRep (c*d))).completion=_*_
    rw [map_mul, ← one_mul (1 : π.left →L[ℂ] π.left), TensorProduct.mapL_mul]
    exact completion_comp _ _
  map_star' c := by
    apply Subtype.ext; funext π
    change (TensorProduct.mapL (1 : π.left →L[ℂ] π.left) (π.rightRep (star c))).completion=star _
    rw [map_star, ← star_one (π.left →L[ℂ] π.left)]
    exact (completion_mapL_star _ _).symm

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UniformModels
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.universalGraphCStar
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

lemma universalFaithfulRepresentation_one : universalFaithfulRepresentation 1 = 1 := by
  ext ξ
  rfl

def universalUnitalRepresentation :
    UniversalContraction →⋆ₐ[ℂ] (universalHilbert →L[ℂ] universalHilbert) :=
  { universalFaithfulRepresentation with
    map_one' := universalFaithfulRepresentation_one
    commutes' := fun c => by
      change universalFaithfulRepresentation (c • 1) = c • 1
      rw [map_smul, universalFaithfulRepresentation_one] }

section PolynomialTensorEstimate

variable {B C : Type 1} [CStarAlgebra B] [NonUnitalCStarAlgebra C]

def wordTensor (s : Finset (List Bool)) (c : List Bool → C) : MinimalTensor UniversalContraction C :=
  ∑ w ∈ s, minimalElementary (universalWord w) (c w)

end PolynomialTensorEstimate

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_WordTensorDensity
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

variable {C : Type*} [NonUnitalCStarAlgebra C]

def wordTensorLinear : (List Bool →₀ C) →ₗ[ℂ] MinimalTensor UniversalContraction C :=
  Finsupp.lsum ℂ (fun w => minimalElementaryRightLinear (universalWord w))

end

end WeakPureInfiniteness
end

end OAI
end


