-- Prove2me | Definitions.Def_OAIErdos3B118
-- name    : OAIErdos3B118
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T02:54:45.739002+00:00
-- url     : https://prove2.me/theorems/aa3b110e-51ea-4206-8340-29a10128f378
-- title:
--   OpenAI Erdős-3 split, definitions bundle 119 of 132
-- statement:
--   Definitions bundle 119 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B117`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 119 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.adaptedPolynomial_coordinate_totalDegree`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedMap_comap_graded`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedMap_image_graded`, `OAI.Erdos3.NilpotentLieFiltration.exists_real_quotient_fiber_polynomialOrbit_lift`, `OAI.Erdos3.NilpotentLieFiltration.gradedRefiltrationLayer_map`, `OAI.Erdos3.NilpotentLieFiltration.gradedRefiltrationLayer_map_mem`, `OAI.Erdos3.NilpotentLieFiltration.gradedRefiltrationLayer_top_kernel_eq_zero`, `OAI.Erdos3.NilpotentLieFiltration.gradedRefiltrationMap`, `OAI.Erdos3.NilpotentLieFiltration.gradedRefiltrationMap_apply`, `OAI.Erdos3.NilpotentLieFiltration.gradedRefiltrationMap_layer_surjective`, `OAI.Erdos3.NilpotentLieFiltration.gradedRefiltrationMap_mem_layer`, `OAI.Erdos3.NilpotentLieFiltration.graded_top_kernel_iff_refiltered_top_kernel`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousGradedProjection_image_eq`, `OAI.Erdos3.NilpotentLieFiltration.polynomialRationalGrid_exists_coordinates`, `OAI.Erdos3.NilpotentLieFiltration.polynomialRationalGrid_value`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSlowBound_difference`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSlowBound_dist_le`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSlowBound_value`, `OAI.Erdos3.NilpotentLieFiltration.projected_realSymbolRepresentative_mem_homogeneous_image`, `OAI.Erdos3.NilpotentLieFiltration.real_symbolPointwiseSubalgebra_map_mem`, `OAI.Erdos3.NilpotentLieFiltration.refilteredProjectionFiberEquiv`, `OAI.Erdos3.NilpotentLieFiltration.refilteredProjectionFiberEquiv_apply`, `OAI.Erdos3.NilpotentLieFiltration.refilteredProjectionFiberProduct`, `OAI.Erdos3.NilpotentLieFiltration.symbolPointwiseSubalgebra_comap`, `OAI.Erdos3.NilpotentLieFiltration.symbolPointwiseSubalgebra_map`, `OAI.Erdos3.NilpotentLieFiltration.symbolPointwiseSubalgebra_map_le`, `OAI.Erdos3.NilpotentLieFiltration.symbolPointwiseSubalgebra_mono`, `OAI.Erdos3.RationalFilteredNilmanifold.AdaptedMapGeometryData`, `OAI.Erdos3.RationalFilteredNilmanifold.AdaptedModelData.model`, `OAI.Erdos3.RationalFilteredNilmanifold.AdaptedModelData.model_layers`, `OAI.Erdos3.RationalFilteredNilmanifold.AdaptedModelData.original_dist_le`, `OAI.Erdos3.RationalFilteredNilmanifold.AdaptedModelData.recOn`, `OAI.Erdos3.RationalFilteredNilmanifold.FixedSourceAdaptedMarkGeometryData`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonFirstSpace`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonFirstSpace_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonFirstSpace_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonFirstSpace_smul`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonSecondSpace`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonSecondSpace_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonSecondSpace_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonSecondSpace_smul`, `OAI.Erdos3.RationalFilteredNilmanifold.allocatedMarkedDiagram_injective_of_top_kernel`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_adapted_model_data`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_marked_topQuotientOrbit_lift_diagram`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_marked_topQuotientOrbit_lift_of_quotient_eq`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_nativeOptionFixedSourceQuotientMarkGeometry`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_adapted_map_geometry`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_fixedSource_adapted_mark_geometry`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_polynomialSlowBound_dist_exp`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_prescribed_adapted_model`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_prescribed_marked_topQuotientOrbit_lift`, `OAI.Erdos3.RationalFilteredNilmanifold.markedTopQuotientDiagram`, `OAI.Erdos3.RationalFilteredNilmanifold.nativeOptionFixedSourceMarkExponent`, `OAI.Erdos3.RationalFilteredNilmanifold.nativeOptionFixedSourceQuotientMarkInput`, `OAI.Erdos3.RationalFilteredNilmanifold.nativeOptionFixedSourceQuotientMarkInput_bounds`, `OAI.Erdos3.RationalFilteredNilmanifold.nativeOptionFixedSourceQuotientMark_layer_surjective`, `OAI.Erdos3.RationalFilteredNilmanifold.nativeOptionFixedSourceQuotientMark_mem_layer`, `OAI.Erdos3.RationalFilteredNilmanifold.optionAdaptedModel_layers`, `OAI.Erdos3.RationalFilteredNilmanifold.optionNativeCommonPivotQuotientFast`, `OAI.Erdos3.RationalFilteredNilmanifold.optionNativeCommonPivotQuotientFast_layer_eq`, `OAI.Erdos3.RationalFilteredNilmanifold.optionNativePivotQuotientMap_layer_surjective`, `OAI.Erdos3.RationalFilteredNilmanifold.optionNativePivotQuotientMap_mem_layer`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalAdaptedLipschitzBound`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalAdaptedLipschitzBound_le_exp`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalObservable`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalObservable_adapted_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalObservable_adapted_lipschitz_of_logHeight`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalObservable_adapted_member_nets`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalObservable_adapted_unit_interval`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalObservable_apply`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalObservable_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalObservable_member_net`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalObservable_member_nets`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalObservable_piRealOrbit`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalObservable_unit_interval`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalOrbit`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalOrbit_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalOrbit_log`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalOrbit_mark_log`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalOrbit_piRealOrbit`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalOrbit_score`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalOrbit_value`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalProjection_layers`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalSpaceProjection`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalSpaceProjection_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalSpaceProjection_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.optionOriginalSpaceProjection_piRealOrbit`, `OAI.Erdos3.RationalFilteredNilmanifold.quotient_markedDiagram_injective`, `OAI.Erdos3.RationalFilteredNilmanifold.refilteredMarkedMap_layer_surjective`, `OAI.Erdos3.RationalFilteredNilmanifold.refilteredMarkedMap_mem_layer`, `OAI.Erdos3.RationalFilteredNilmanifold.topQuotientMarkedMap`, `OAI.Erdos3.RationalFilteredNilmanifold.topQuotientMarkedMap_basis_logHeight`, `OAI.Erdos3.RationalFilteredNilmanifold.topQuotientMarkedMap_layer_surjective`, `OAI.Erdos3.RationalFilteredNilmanifold.topQuotientMarkedMap_mem_layer`, `OAI.Erdos3.RationalFilteredNilmanifold.topQuotientMarkedMap_real_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.topQuotientMarkedOrbit`, `OAI.Erdos3.RationalFilteredNilmanifold.topQuotientMarkedOrbit_eq_iff`, `OAI.Erdos3.RationalFilteredNilmanifold.topQuotientMarkedOrbit_log`, `OAI.Erdos3.RationalFilteredNilmanifold.topQuotientOrbit`, `OAI.Erdos3.RationalFilteredNilmanifold.topQuotientOrbit_eval`, `OAI.Erdos3.exists_rational_polynomial_of_grid`, `OAI.Erdos3.exists_slow_polynomial_metric_budget`, `OAI.Erdos3.optionRealificationContinuousSMul`, `OAI.Erdos3.optionRealificationT2Space`, `OAI.Erdos3.optionRealificationTopologicalAddGroup`, `OAI.Erdos3.optionRealificationTopology`, `OAI.Erdos3.polynomial_integer_value_common_denominator`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B038

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StrongRefiltrationReconstruction
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (f : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

theorem symbolPointwiseSubalgebra_mono {U V : LieSubalgebra ℚ F.AssociatedGraded} (hUV : U ≤ V) :
    F.symbolPointwiseSubalgebra e ω hF w U ≤ F.symbolPointwiseSubalgebra e ω hF w V := by
  intro x hx
  exact fun α => hUV ((F.mem_symbolPointwiseSubalgebra_iff e ω hF w U x).mp hx α)

theorem symbolPointwiseSubalgebra_map_le (U : LieSubalgebra ℚ F.AssociatedGraded) :
    (F.symbolPointwiseSubalgebra e ω hF w U).map (F.filteredPolynomialSymbolMap G φ hφ w) ≤
      G.symbolPointwiseSubalgebra f ν hG w (U.map (F.associatedGradedMap G φ hφ)) := by
  rintro _ ⟨x, hx, rfl⟩
  apply (G.mem_symbolPointwiseSubalgebra_iff f ν hG w _ _).mpr
  intro α
  simp only [LieHom.coe_toLinearMap]
  have hm : F.associatedGradedMap G φ hφ (coefficients (F.gradedSymbolPolynomial e ω hF w x) α) ∈
      U.map (F.associatedGradedMap G φ hφ) :=
    ⟨_, (F.mem_symbolPointwiseSubalgebra_iff e ω hF w U x).mp hx α, rfl⟩
  rw [F.gradedSymbolPolynomial_filteredMap_coefficient G e ω hF f ν hG φ hφ w x α]
  exact hm

theorem symbolPointwiseSubalgebra_comap (U : LieSubalgebra ℚ G.AssociatedGraded) :
    (G.symbolPointwiseSubalgebra f ν hG w U).comap (F.filteredPolynomialSymbolMap G φ hφ w) =
      F.symbolPointwiseSubalgebra e ω hF w (U.comap (F.associatedGradedMap G φ hφ)) := by
  ext x
  constructor
  · intro hx
    simp only [LieSubalgebra.mem_comap] at hx
    apply (F.mem_symbolPointwiseSubalgebra_iff e ω hF w _ x).mpr
    intro α
    have hm := (G.mem_symbolPointwiseSubalgebra_iff f ν hG w U
      (F.filteredPolynomialSymbolMap G φ hφ w x)).mp hx α
    rw [F.gradedSymbolPolynomial_filteredMap_coefficient G e ω hF f ν hG φ hφ w x α] at hm
    exact hm
  · intro hx
    simp only [LieSubalgebra.mem_comap]
    apply (G.mem_symbolPointwiseSubalgebra_iff f ν hG w U _).mpr
    intro α
    have hm : F.associatedGradedMap G φ hφ (coefficients (F.gradedSymbolPolynomial e ω hF w x) α) ∈ U :=
      (F.mem_symbolPointwiseSubalgebra_iff e ω hF w _ x).mp hx α
    rw [F.gradedSymbolPolynomial_filteredMap_coefficient G e ω hF f ν hG φ hφ w x α]
    exact hm

theorem symbolPointwiseSubalgebra_map [Fintype (SymbolBasisIndex w ν)]
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule) :
    (F.symbolPointwiseSubalgebra e ω hF w U).map (F.filteredPolynomialSymbolMap G φ hφ w) =
      G.symbolPointwiseSubalgebra f ν hG w (U.map (F.associatedGradedMap G φ hφ)) := by
  classical
  apply le_antisymm (F.symbolPointwiseSubalgebra_map_le G e ω hF f ν hG φ hφ w U)
  intro x hx
  change x ∈ ((F.symbolPointwiseSubalgebra e ω hF w U).map
    (F.filteredPolynomialSymbolMap G φ hφ w)).toSubmodule
  rw [← sum_basisBlockProjection (G.polynomialSymbolBasis f ν hG w) (fun z => z.val.1) x]
  apply Submodule.sum_mem
  intro α _
  obtain ⟨v, hv, he⟩ := (G.mem_symbolPointwiseSubalgebra_iff f ν hG w _ x).mp hx α
  refine ⟨F.homogeneousSymbolLift e ω hF w α v,
    F.homogeneousSymbolLift_mem_pointwise e ω hF w U hU α v hv, ?_⟩
  change F.filteredPolynomialSymbolMap G φ hφ w (F.homogeneousSymbolLift e ω hF w α v) = _
  change F.associatedGradedMap G φ hφ v = _ at he
  rw [F.homogeneousSymbolLift_filteredMap G e ω hF f ν hG φ hφ w, he,
    G.homogeneousSymbolLift_coefficient]

theorem associatedGradedMap_image_graded (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule) :
    BasisGradedSubmodule (G.associatedGradedBasis f ν hG) ν
      (U.map (F.associatedGradedMap G φ hφ)).toSubmodule := by
  rintro j _ ⟨x, hx, rfl⟩
  exact ⟨basisGradeProjection (F.associatedGradedBasis e ω hF) ω j x, hU j x hx,
    F.associatedGradedMap_gradeProjection G e ω hF f ν hG φ hφ j x⟩

theorem associatedGradedMap_comap_graded (U : LieSubalgebra ℚ G.AssociatedGraded)
    (hU : BasisGradedSubmodule (G.associatedGradedBasis f ν hG) ν U.toSubmodule) :
    BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω
      (U.comap (F.associatedGradedMap G φ hφ)).toSubmodule := by
  intro j x hx
  change F.associatedGradedMap G φ hφ
    (basisGradeProjection (F.associatedGradedBasis e ω hF) ω j x) ∈ U
  rw [F.associatedGradedMap_gradeProjection G e ω hF f ν hG φ hφ]
  exact hU j _ hx

end Erdos3.NilpotentLieFiltration

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

variable {ι : Type v} {H : Type u} {L : ι → Type u}
  [LieRing H] [LieAlgebra ℚ H] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

theorem quotient_markedDiagram_injective {s : ℕ}
    (E : NilpotentLieFiltration H (s + 1)) (ψ : ∀ i, H →ₗ⁅ℚ⁆ L i)
    (hker : ∀ x : H, x ∈ E.layer (s + 1) → (∀ i, ψ i x = 0) → x = 0) :
    Function.Injective (optionProductMap (lieQuotientMap (E.layerIdeal (s + 1))) ψ) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply hker (x - y)
  · have hq : lieQuotientMap (E.layerIdeal (s + 1)) x =
        lieQuotientMap (E.layerIdeal (s + 1)) y := congrFun hxy none
    apply (E.mem_layerIdeal (s + 1) (x - y)).mp
    apply (lieQuotientMap_eq_zero (E.layerIdeal (s + 1)) (x - y)).mp
    rw [map_sub, hq, sub_self]
  · intro i
    have hi : ψ i x = ψ i y := congrFun hxy (some i)
    rw [map_sub, hi, sub_self]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration
open Module
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

 theorem real_symbolPointwiseSubalgebra_map_mem
    (U : LieSubalgebra ℚ F.AssociatedGraded) (x : F.RealPolynomialSymbol w)
    (hx : x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U)) :
    realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x ∈
      realificationLieSubalgebra
        (G.symbolPointwiseSubalgebra c ν hG w (U.map (F.associatedGradedMap G φ hφ))) := by
  have hmap : realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x ∈
      realificationLieSubalgebra ((F.symbolPointwiseSubalgebra b ω hF w U).map
        (F.filteredPolynomialSymbolMap G φ hφ w)) := by
    rw [realificationLieSubalgebra_map]
    exact ⟨x, hx, rfl⟩
  exact Submodule.baseChange_mono ℝ
    (F.symbolPointwiseSubalgebra_map_le G b ω hF c ν hG φ hφ w U) hmap

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (w : σ → ℕ)

theorem homogeneousGradedProjection_image_eq
    (W : LieSubalgebra ℚ F.AssociatedGraded) :
    (W.map (F.associatedGradedMap G φ hφ)).map
      (G.homogeneousAssociatedGradedEquiv c ν hG hc).toLieHom =
      W.map (F.homogeneousGradedProjection G c ν hG hc φ hφ) := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

theorem projected_realSymbolRepresentative_mem_homogeneous_image
    (W : LieSubalgebra ℚ F.AssociatedGraded) (x : F.RealPolynomialSymbol w)
    (hx : x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W))
    (u : σ → ℝ) :
    eval₂ u (G.realSymbolRepresentative c ν hG w
      (realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x)) ∈
      realificationLieSubalgebra (W.map (F.homogeneousGradedProjection G c ν hG hc φ hφ)) := by
  have hmap := F.real_symbolPointwiseSubalgebra_map_mem G b ω hF c ν hG φ hφ w W x hx
  have hvalue := (G.mem_real_symbolPointwiseSubalgebra_iff_values c ν hG w
    (W.map (F.associatedGradedMap G φ hφ))
    (realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x)).mp hmap u
  rw [G.realSymbolRepresentative_eval₂,
    ← F.homogeneousGradedProjection_image_eq G c ν hG hc φ hφ W,
    realificationLieSubalgebra_map]
  exact ⟨_, hvalue, rfl⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (b : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (b '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

include b ν hG in

theorem gradedRefiltrationLayer_map (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) (j : ℕ) :
    (F.gradedRefiltrationLayer U j).map φ.toLinearMap =
      G.gradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) j := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxF, hxU⟩ := (F.mem_gradedRefiltrationLayer U j x).mp hx
    apply (G.mem_gradedRefiltrationLayer _ j (φ x)).mpr
    refine ⟨hφ j x hxF, F.associatedGradedPieceMap j ⟨x, hxF⟩, hxU, ?_⟩
    exact F.associatedGradedMap_piece G φ hφ j ⟨x, hxF⟩
  · intro y hy
    obtain ⟨hyG, hyU⟩ := (G.mem_gradedRefiltrationLayer _ j y).mp hy
    obtain ⟨a, ha, haeq⟩ := hyU
    change F.associatedGradedMap G φ hφ a = G.associatedGradedPieceMap j ⟨y, hyG⟩ at haeq
    let a' := basisGradeProjection (F.associatedGradedBasis e ω hF) ω j a
    have ha'U : a' ∈ U := hU j a ha
    have ha'pure : basisGradeProjection (F.associatedGradedBasis e ω hF) ω j a' = a' := by
      apply (F.associatedGradedBasis e ω hF).repr.injective
      ext i
      simp only [a', basisGradeProjection_repr]
      split_ifs <;> rfl
    obtain ⟨x, hx⟩ := F.exists_associatedGradedPieceMap_of_pure e ω hF j a' ha'pure
    have hgraded : F.associatedGradedMap G φ hφ (F.associatedGradedPieceMap j x) =
        G.associatedGradedPieceMap j ⟨y, hyG⟩ := by
      rw [hx]
      change F.associatedGradedMap G φ hφ
        (basisGradeProjection (F.associatedGradedBasis e ω hF) ω j a) = _
      rw [F.associatedGradedMap_gradeProjection G e ω hF b ν hG φ hφ, haeq]
      exact G.associatedGradedPieceMap_grade_fixed b ν hG j ⟨y, hyG⟩
    have hδ : y - φ x ∈ G.layer (j + 1) := by
      apply (G.associatedGradedPieceMap_eq_zero_iff j
        ⟨y - φ x, (G.layer j).sub_mem hyG (hφ j x x.property)⟩).mp
      change G.associatedGradedPieceMap j
        (⟨y, hyG⟩ - ⟨φ x, hφ j x x.property⟩) = 0
      rw [map_sub, ← F.associatedGradedMap_piece G φ hφ j x, hgraded, sub_self]
    obtain ⟨z, hz, hzeq⟩ := hsurj (j + 1) (y - φ x) hδ
    refine ⟨(x : L) + z, (F.gradedRefiltrationLayer U j).add_mem ?_
      (F.layer_succ_le_gradedRefiltrationLayer U j hz), ?_⟩
    · exact (F.mem_gradedRefiltrationLayer U j x).mpr ⟨x.property, hx.symm ▸ ha'U⟩
    · change φ ((x : L) + z) = y
      rw [map_add, hzeq]
      abel

theorem gradedRefiltrationLayer_top_kernel_eq_zero
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (htop : ∀ a ∈ U,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω s a = a →
      F.associatedGradedMap G φ hφ a = 0 → a = 0)
    (x : L) (hx : x ∈ F.gradedRefiltrationLayer U s) (hzero : φ x = 0) : x = 0 := by
  obtain ⟨hxF, hxU⟩ := (F.mem_gradedRefiltrationLayer U s x).mp hx
  have hpiece : F.associatedGradedPieceMap s ⟨x, hxF⟩ = 0 := by
    apply htop _ hxU (F.associatedGradedPieceMap_grade_fixed e ω hF s ⟨x, hxF⟩)
    rw [F.associatedGradedMap_piece]
    have he : (⟨φ x, hφ s x hxF⟩ : G.layer s) = 0 := Subtype.ext hzero
    rw [he, map_zero]
  have hmem := (F.associatedGradedPieceMap_eq_zero_iff s ⟨x, hxF⟩).mp hpiece
  rw [F.terminal] at hmem
  exact hmem

theorem gradedRefiltrationLayer_map_mem (U : LieSubalgebra ℚ F.AssociatedGraded)
    (j : ℕ) (x : L) (hx : x ∈ F.gradedRefiltrationLayer U j) :
    φ x ∈ G.gradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) j := by
  obtain ⟨hxF, hxU⟩ := (F.mem_gradedRefiltrationLayer U j x).mp hx
  apply (G.mem_gradedRefiltrationLayer _ j (φ x)).mpr
  exact ⟨hφ j x hxF, F.associatedGradedPieceMap j ⟨x, hxF⟩, hxU,
    F.associatedGradedMap_piece G φ hφ j ⟨x, hxF⟩⟩

noncomputable def gradedRefiltrationMap (U : LieSubalgebra ℚ F.AssociatedGraded) :
    F.gradedRefiltrationSubalgebra U →ₗ⁅ℚ⁆
      G.gradedRefiltrationSubalgebra (U.map (F.associatedGradedMap G φ hφ)) where
  toLinearMap :=
    { toFun x := ⟨φ x, F.gradedRefiltrationLayer_map_mem G φ hφ U 1 x x.property⟩
      map_add' x y := Subtype.ext (map_add φ (x : L) (y : L))
      map_smul' a x := Subtype.ext (map_smul φ a (x : L)) }
  map_lie' {x y} := Subtype.ext (LieHom.map_lie φ x y)

@[simp] theorem gradedRefiltrationMap_apply (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : F.gradedRefiltrationSubalgebra U) :
    (F.gradedRefiltrationMap G φ hφ U x : M) = φ x := rfl

theorem gradedRefiltrationMap_mem_layer (U : LieSubalgebra ℚ F.AssociatedGraded)
    (j : ℕ) (x : F.gradedRefiltrationSubalgebra U)
    (hx : x ∈ (F.gradedRefiltration U).layer j) :
    F.gradedRefiltrationMap G φ hφ U x ∈
      (G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ))).layer j :=
  F.gradedRefiltrationLayer_map_mem G φ hφ U j x hx

include e ω hF b ν hG in

theorem gradedRefiltrationMap_layer_surjective (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (j : ℕ) (y : G.gradedRefiltrationSubalgebra (U.map (F.associatedGradedMap G φ hφ)))
    (hy : y ∈ (G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ))).layer j) :
    ∃ x ∈ (F.gradedRefiltration U).layer j, F.gradedRefiltrationMap G φ hφ U x = y := by
  have lift (i : ℕ) (hi : 1 ≤ i)
      (hy' : (y : M) ∈ G.gradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) i) :
      ∃ x ∈ (F.gradedRefiltration U).layer i, F.gradedRefiltrationMap G φ hφ U x = y := by
    rw [← F.gradedRefiltrationLayer_map G e ω hF b ν hG φ hφ U hU hsurj] at hy'
    obtain ⟨x, hx, hxy⟩ := hy'
    let x' : F.gradedRefiltrationSubalgebra U :=
      ⟨x, F.gradedRefiltrationLayer_antitone U hi hx⟩
    exact ⟨x', hx, Subtype.ext hxy⟩
  by_cases hj : 1 ≤ j
  · exact lift j hj hy
  · have hj0 : j = 0 := by omega
    subst j
    obtain ⟨x, hx, hxy⟩ := lift 1 le_rfl y.property
    exact ⟨x, (F.gradedRefiltration U).antitone (by omega : 0 ≤ 1) hx, hxy⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

universe u

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)

theorem allocatedMarkedDiagram_injective_of_top_kernel
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (hker : ∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) →
      φ x = 0 → x = 0) :
    Function.Injective (optionProductMap
      (lieQuotientMap (Dref.filtration.layerIdeal (s + 1)))
      (fun _ : Unit => D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)) := by
  apply quotient_markedDiagram_injective
  intro x hx hzero
  apply Subtype.ext
  apply hker (x : L)
  · rw [hDref] at hx
    exact (D.filtration.mem_gradedRefiltration_layer W (s + 1) x).mp hx
  · exact congrArg Subtype.val (hzero ())

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {J : Type v} [Fintype J] {L : Type u} {M : J → Type u} {Y : Type*}
  [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
  [LieRing Y] [LieAlgebra ℚ Y] {s d₀ dQ : ℕ} {d : J → ℕ}
  (D : RationalFilteredNilmanifold L s d₀)
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))
  (π : L →ₗ⁅ℚ⁆ Y) (eta : J → L →ₗ[ℚ] ℚ) (js : List J)
  (Q : RationalFilteredNilmanifold
    (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) s dQ)
  (hQ : Q.filtration = D.filtration.quotientLie
    (D.filtration.pivotAnnihilatorIdeal π eta js)
    (by rw [D.filtration.terminal]; exact bot_le))

include hQ

theorem optionNativePivotQuotientMap_mem_layer (k : ℕ)
    (x : ∀ i : Option J, optionLieSpace L M i)
    (hx : x ∈ (optionProduct D E).filtration.layer k) :
    optionMarkedLieMap (L := M)
      (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js)) x ∈
        (optionProduct Q E).filtration.layer k := by
  have hcoord := (mem_pi_layer (fun i => (optionFactors D E i).filtration) k x).mp hx
  apply (mem_pi_layer (fun i => (optionFactors Q E i).filtration) k _).mpr
  intro i
  cases i with
  | none =>
    change lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js) (x none) ∈
      Q.filtration.layer k
    rw [hQ]
    exact ⟨x none, hcoord none, rfl⟩
  | some j => exact hcoord (some j)

theorem optionNativePivotQuotientMap_layer_surjective (k : ℕ)
    (y : ∀ i : Option J,
      optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) M i)
    (hy : y ∈ (optionProduct Q E).filtration.layer k) :
    ∃ x ∈ (optionProduct D E).filtration.layer k,
      optionMarkedLieMap (L := M)
        (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js)) x = y := by
  have hcoord := (mem_pi_layer (fun i => (optionFactors Q E i).filtration) k y).mp hy
  have hy₀ : y none ∈ Q.filtration.layer k := hcoord none
  rw [hQ] at hy₀
  obtain ⟨x₀, hx₀, hxy₀⟩ := hy₀
  let x : ∀ i : Option J, optionLieSpace L M i
    | none => x₀
    | some j => y (some j)
  refine ⟨x, ?_, ?_⟩
  · apply (mem_pi_layer (fun i => (optionFactors D E i).filtration) k x).mpr
    intro i
    cases i with
    | none => exact hx₀
    | some j => exact hcoord (some j)
  · funext i
    cases i with
    | none => exact hxy₀
    | some j => rfl

variable (U : LieSubalgebra ℚ (optionProduct D E).filtration.AssociatedGraded)

noncomputable def optionNativeCommonPivotQuotientFast :
    LieSubalgebra ℚ (optionProduct Q E).filtration.AssociatedGraded :=
  U.map ((optionProduct D E).filtration.associatedGradedMap
    (optionProduct Q E).filtration
    (optionMarkedLieMap (L := M)
      (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js)))
    (optionNativePivotQuotientMap_mem_layer D E π eta js Q hQ))

variable {κ κQ : Type*}
  (e : Basis κ ℚ (∀ i : Option J, optionLieSpace L M i)) (μ : κ → ℕ)
  (hSource : ∀ k, (optionProduct D E).filtration.layer k =
    Submodule.span ℚ (e '' {i | k ≤ μ i}))
  (c : Basis κQ ℚ (∀ i : Option J,
    optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) M i))
  (ν : κQ → ℕ)
  (hTarget : ∀ k, (optionProduct Q E).filtration.layer k =
    Submodule.span ℚ (c '' {i | k ≤ ν i}))
  (hU : BasisGradedSubmodule
    ((optionProduct D E).filtration.associatedGradedBasis e μ hSource) μ U.toSubmodule)

include e μ hSource c ν hTarget hU in

theorem optionNativeCommonPivotQuotientFast_layer_eq (k : ℕ) :
    (optionProduct Q E).filtration.gradedRefiltrationLayer
      (optionNativeCommonPivotQuotientFast D E π eta js Q hQ U) k =
    ((optionProduct D E).filtration.gradedRefiltrationLayer U k).map
      (optionMarkedLieMap (L := M)
        (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js))).toLinearMap := by
  symm
  exact (optionProduct D E).filtration.gradedRefiltrationLayer_map
    (optionProduct Q E).filtration e μ hSource c ν hTarget
    (optionMarkedLieMap (L := M)
      (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js)))
    (optionNativePivotQuotientMap_mem_layer D E π eta js Q hQ) U hU
    (optionNativePivotQuotientMap_layer_surjective D E π eta js Q hQ) k

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (U : LieSubalgebra ℚ F.AssociatedGraded)

noncomputable abbrev refilteredProjectionFiberProduct :=
  lieQuotientFiberProduct ((F.gradedRefiltration U).layerIdeal s)
    ((G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ))).layerIdeal s)
    (F.gradedRefiltrationMap G φ hφ U)
    (F.gradedRefiltrationMap_mem_layer G φ hφ U s)

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (b : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (b '' {i | j ≤ ν i}))
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (htop : ∀ a ∈ U,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω s a = a →
      F.associatedGradedMap G φ hφ a = 0 → a = 0)

noncomputable def refilteredProjectionFiberEquiv :
    F.gradedRefiltrationSubalgebra U ≃ₗ⁅ℚ⁆ F.refilteredProjectionFiberProduct G φ hφ U :=
  (F.gradedRefiltration U).quotientFiberEquiv
    (G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ)))
    (F.gradedRefiltrationMap G φ hφ U)
    (F.gradedRefiltrationMap_mem_layer G φ hφ U)
    (fun x hx hz => Subtype.ext
      (F.gradedRefiltrationLayer_top_kernel_eq_zero G e ω hF φ hφ U htop x hx
        (congrArg Subtype.val hz)))
    (F.gradedRefiltrationMap_layer_surjective G e ω hF b ν hG φ hφ U hU hsurj s)

@[simp] theorem refilteredProjectionFiberEquiv_apply
    (x : F.gradedRefiltrationSubalgebra U) :
    (F.refilteredProjectionFiberEquiv G φ hφ U e ω hF b ν hG hU hsurj htop x).val =
      (lieQuotientMap ((F.gradedRefiltration U).layerIdeal s) x,
        F.gradedRefiltrationMap G φ hφ U x) := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.JoinedFrequencyRefilteredTop
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem graded_top_kernel_iff_refiltered_top_kernel
    {ι L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (U : LieSubalgebra ℚ F.AssociatedGraded) :
    (∀ a ∈ U, basisGradeProjection (F.associatedGradedBasis e ω hF) ω s a = a →
      F.associatedGradedMap G φ hφ a = 0 → a = 0) ↔
    (∀ x ∈ F.gradedRefiltrationLayer U s, φ x = 0 → x = 0) := by
  constructor
  · exact fun htop => F.gradedRefiltrationLayer_top_kernel_eq_zero G e ω hF φ hφ U htop
  · intro htop a ha hpure hzero
    obtain ⟨x, hx⟩ := F.exists_associatedGradedPieceMap_of_pure e ω hF s a hpure
    have hxU : (x : L) ∈ F.gradedRefiltrationLayer U s := by
      apply (F.mem_gradedRefiltrationLayer U s x).mpr
      exact ⟨x.property, hx.symm ▸ ha⟩
    have hpiece : G.associatedGradedPieceMap s ⟨φ x, hφ s x x.property⟩ = 0 := by
      rw [← F.associatedGradedMap_piece G φ hφ s x, hx]
      exact hzero
    have hφzero : φ x = 0 := by
      have hmem := (G.associatedGradedPieceMap_eq_zero_iff s
        ⟨φ x, hφ s x x.property⟩).mp hpiece
      rw [G.terminal] at hmem
      exact hmem
    have hxzero : x = 0 := Subtype.ext (htop x hxU hφzero)
    rw [← hx, hxzero, map_zero]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMarkedDiagramOrbitLift
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d n : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop) {w : σ → ℕ}

noncomputable def topQuotientOrbit (g : D.filtration.realification.PolynomialOrbit w) :
    Q.filtration.realification.PolynomialOrbit w :=
  let q := D.filtration.realQuotientPolynomialOrbit
    (D.filtration.layerIdeal (s + 1)) (t := s) le_rfl g
  NilpotentLieFiltration.polynomialOrbitOfLog q.log (by rw [hQ]; exact q.adapted)

theorem topQuotientOrbit_eval (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    Q.filtration.realification.polynomialOrbitEval w x (D.topQuotientOrbit Q hQ g) =
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
        (D.filtration.realification.polynomialOrbitEval w x g) := by
  exact D.filtration.realQuotientPolynomialOrbit_eval
    (D.filtration.layerIdeal (s + 1)) (t := s) le_rfl g x

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d n : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
    (hQ : Q.filtration = D.filtration.quotientTop) {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (G : NilpotentLieFiltration M (s + 1))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem exists_real_quotient_fiber_polynomialOrbit_lift
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (w : σ → ℕ) (pbar : F.quotientTop.realification.PolynomialOrbit w)
    (q : G.realification.PolynomialOrbit w)
    (hcompat : map
      (realLieHomToRat (realificationLieHom
        (lieQuotientProjection (F.layerIdeal (s + 1)) (G.layerIdeal (s + 1)) φ
          (hφ (s + 1))))).toLinearMap pbar.log =
      map (realLieHomToRat (realificationLieHom
        (lieQuotientMap (G.layerIdeal (s + 1))))).toLinearMap q.log) :
    ∃ p : F.realification.PolynomialOrbit w,
      map (realLieHomToRat (realificationLieHom
        (lieQuotientMap (F.layerIdeal (s + 1))))).toLinearMap p.log = pbar.log ∧
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap p.log = q.log := by
  let e := F.realificationTopQuotientEquiv
  let φR := realLieHomToRat (realificationLieHom φ)
  let hφR := F.realificationLieHom_mem_layer G φ hφ
  let pbar' : F.realification.quotientTop.PolynomialOrbit w :=
    polynomialOrbitOfLog (map e.symm.toLinearEquiv.toLinearMap pbar.log)
      (F.quotientTop.realification.adapted_map F.realification.quotientTop
        e.symm.toLinearEquiv.toLinearMap
        (fun j x hx => (F.realificationTopQuotientEquiv_mem_layer_iff j (e.symm x)).mp
          (by simpa only [e, LieEquiv.apply_symm_apply] using hx)) w pbar.adapted)
  have hcompat' : map
      (lieQuotientProjection (F.realification.layerIdeal (s + 1))
        (G.realification.layerIdeal (s + 1)) φR (hφR (s + 1))).toLinearMap pbar'.log =
      map (lieQuotientMap (G.realification.layerIdeal (s + 1))).toLinearMap q.log := by
    apply coefficients.injective
    ext a
    rw [coefficients_map, coefficients_map]
    apply G.realificationTopQuotientEquiv.injective
    change G.realificationTopQuotientEquiv
      (lieQuotientProjection (F.realification.layerIdeal (s + 1))
        (G.realification.layerIdeal (s + 1))
        (realLieHomToRat (realificationLieHom φ))
        (F.realificationLieHom_mem_layer G φ hφ (s + 1)) (coefficients pbar'.log a)) =
      G.realificationTopQuotientEquiv
        (lieQuotientMap (G.realification.layerIdeal (s + 1)) (coefficients q.log a))
    rw [F.realificationTopQuotientEquiv_projection G φ hφ,
      G.realificationTopQuotientEquiv_mk]
    have he : e (coefficients pbar'.log a) = coefficients pbar.log a := by
      change e (coefficients (map e.symm.toLinearEquiv.toLinearMap pbar.log) a) = _
      rw [coefficients_map]
      exact e.apply_symm_apply _
    change realificationLieHom
      (lieQuotientProjection (F.layerIdeal (s + 1)) (G.layerIdeal (s + 1)) φ (hφ (s + 1)))
      (e (coefficients pbar'.log a)) = _
    rw [he]
    have ha := congrArg (fun P => coefficients P a) hcompat
    simp only [coefficients_map] at ha
    exact ha
  obtain ⟨p, hpbar, hpq⟩ :=
    F.realification.exists_quotient_fiber_polynomialOrbit_lift G.realification φR hφR
      (F.realificationLieHom_layer_surjective G φ hφ hsurj (s + 1)) w pbar' q hcompat'
  have hreal : map (realLieHomToRat (realificationLieHom
      (lieQuotientMap (F.layerIdeal (s + 1))))).toLinearMap p.log = pbar.log := by
    apply coefficients.injective
    ext a
    rw [coefficients_map]
    have ha := congrArg (fun P => e (coefficients P a)) hpbar
    simp only [coefficients_map] at ha
    change realificationLieHom (lieQuotientMap (F.layerIdeal (s + 1)))
      (coefficients p.log a) = _
    refine ha.trans ?_
    change e (coefficients (map e.symm.toLinearEquiv.toLinearMap pbar.log) a) = _
    rw [coefficients_map]
    exact e.apply_symm_apply _
  exact ⟨p, hreal, hpq⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d n : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (G : NilpotentLieFiltration M (s + 1))
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ G.layer j)
    (Q : RationalFilteredNilmanifold
      (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
    (hQ : Q.filtration = D.filtration.quotientTop) {w : σ → ℕ}

theorem exists_prescribed_marked_topQuotientOrbit_lift
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : G.realification.PolynomialOrbit w)
    (hcompat : map
      (realLieHomToRat (realificationLieHom
        (lieQuotientProjection (D.filtration.layerIdeal (s + 1))
          (G.layerIdeal (s + 1)) φ (hφ (s + 1))))).toLinearMap q.log =
      map (realLieHomToRat (realificationLieHom
        (lieQuotientMap (G.layerIdeal (s + 1))))).toLinearMap marked.log) :
    ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.topQuotientOrbit Q hQ g = q ∧
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log ∧
      (∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
        (D.filtration.realification.polynomialOrbitRealEval w z g) =
          Q.filtration.realification.polynomialOrbitRealEval w z q) ∧
      ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ
        (D.filtration.realification.polynomialOrbitRealEval w z g) =
          G.realification.polynomialOrbitRealEval w z marked := by
  let q' : D.filtration.quotientTop.realification.PolynomialOrbit w :=
    polynomialOrbitOfLog q.log (by rw [← hQ]; exact q.adapted)
  obtain ⟨g, hquot, hmark⟩ :=
    D.filtration.exists_real_quotient_fiber_polynomialOrbit_lift G φ hφ hsurj w
      q' marked hcompat
  have hq : D.topQuotientOrbit Q hQ g = q := by
    apply Subtype.ext
    apply NilpotentLieBCHGroup.ext
    exact hquot
  refine ⟨g, hq, hmark, ?_, ?_⟩
  · intro z
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
      (eval₂ z g.log) = eval₂ z q.log
    change map (realLieHomToRat (realificationLieHom
      (lieQuotientMap (D.filtration.layerIdeal (s + 1))))).toLinearMap g.log =
      q.log at hquot
    rw [← hquot]
    exact (eval₂_map
      (realificationLieHom (lieQuotientMap (D.filtration.layerIdeal (s + 1)))).toLinearMap
      z g.log).symm
  · intro z
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom φ (eval₂ z g.log) = eval₂ z marked.log
    rw [← hmark]
    exact (eval₂_map (realificationLieHom φ).toLinearMap z g.log).symm

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (E : RationalFilteredNilmanifold M (s + 1) e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)

noncomputable def topQuotientMarkedMap :
    (L ⧸ D.filtration.layerIdeal (s + 1)) →ₗ⁅ℚ⁆
      (M ⧸ E.filtration.layerIdeal (s + 1)) :=
  lieQuotientProjection (D.filtration.layerIdeal (s + 1))
    (E.filtration.layerIdeal (s + 1)) φ (hφ (s + 1))

theorem topQuotientMarkedMap_real_mk (x : ℝ ⊗[ℚ] L) :
    realificationLieHom (D.topQuotientMarkedMap E φ hφ)
      (realificationLieHom (lieQuotientMap (D.filtration.layerIdeal (s + 1))) x) =
    realificationLieHom (lieQuotientMap (E.filtration.layerIdeal (s + 1)))
      (realificationLieHom φ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop)
  (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)
  (hQF : QF.filtration = E.filtration.quotientTop) {w : σ → ℕ}

include hQ hQF in
theorem topQuotientMarkedMap_mem_layer (j : ℕ)
    (x : L ⧸ D.filtration.layerIdeal (s + 1)) (hx : x ∈ Q.filtration.layer j) :
    D.topQuotientMarkedMap E φ hφ x ∈ QF.filtration.layer j := by
  rw [hQ] at hx
  rw [hQF]
  obtain ⟨z, hz, rfl⟩ := hx
  exact ⟨φ z, hφ j z hz, rfl⟩

noncomputable def topQuotientMarkedOrbit (q : Q.filtration.realification.PolynomialOrbit w) :
    QF.filtration.realification.PolynomialOrbit w :=
  polynomialOrbitOfLog
    (map (realLieHomToRat (realificationLieHom (D.topQuotientMarkedMap E φ hφ))).toLinearMap q.log)
    (Q.filtration.realification.adapted_map QF.filtration.realification _
      (Q.filtration.realificationLieHom_mem_layer QF.filtration
        (D.topQuotientMarkedMap E φ hφ)
        (D.topQuotientMarkedMap_mem_layer E φ hφ Q hQ QF hQF)) w q.adapted)

@[simp] theorem topQuotientMarkedOrbit_log (q : Q.filtration.realification.PolynomialOrbit w) :
    (D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q).log =
      map (realLieHomToRat (realificationLieHom
        (lieQuotientProjection (D.filtration.layerIdeal (s + 1))
          (E.filtration.layerIdeal (s + 1)) φ (hφ (s + 1))))).toLinearMap q.log := rfl

theorem topQuotientMarkedOrbit_eq_iff (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : E.filtration.realification.PolynomialOrbit w) :
    D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q = E.topQuotientOrbit QF hQF marked ↔
      map (realLieHomToRat (realificationLieHom
        (lieQuotientProjection (D.filtration.layerIdeal (s + 1))
          (E.filtration.layerIdeal (s + 1)) φ (hφ (s + 1))))).toLinearMap q.log =
      map (realLieHomToRat (realificationLieHom
        (lieQuotientMap (E.filtration.layerIdeal (s + 1))))).toLinearMap marked.log := by
  constructor
  · intro h
    exact congrArg (fun p => p.log) h
  · intro h
    exact Subtype.ext (NilpotentLieBCHGroup.ext h)

theorem exists_marked_topQuotientOrbit_lift_of_quotient_eq
    (hsurj : ∀ j, ∀ y ∈ E.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : E.filtration.realification.PolynomialOrbit w)
    (heq : D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q = E.topQuotientOrbit QF hQF marked) :
    ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.topQuotientOrbit Q hQ g = q ∧
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log ∧
      (∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
        (D.filtration.realification.polynomialOrbitRealEval w z g) =
          Q.filtration.realification.polynomialOrbitRealEval w z q) ∧
      ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ
        (D.filtration.realification.polynomialOrbitRealEval w z g) =
          E.filtration.realification.polynomialOrbitRealEval w z marked :=
  D.exists_prescribed_marked_topQuotientOrbit_lift E.filtration φ hφ Q hQ hsurj q marked
    ((D.topQuotientMarkedOrbit_eq_iff E φ hφ Q hQ QF hQF q marked).mp heq)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration VectorPolynomial

variable {L M ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d f nE nF : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (Fmark : RationalFilteredNilmanifold M (s + 1) f)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
  (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
  (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nE)
  (hE : E.filtration = D.filtration.gradedRefiltration W)
  (EF : RationalFilteredNilmanifold
    (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
  (hEF : EF.filtration = Fmark.filtration.gradedRefiltration
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

include hE hEF

theorem refilteredMarkedMap_mem_layer (j : ℕ)
    (x : D.filtration.gradedRefiltrationSubalgebra W) (hx : x ∈ E.filtration.layer j) :
    D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W x ∈ EF.filtration.layer j := by
  rw [hE] at hx
  rw [hEF]
  exact D.filtration.gradedRefiltrationMap_mem_layer Fmark.filtration φ hφ W j x hx

theorem refilteredMarkedMap_layer_surjective
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis b ω hD) ω W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (j : ℕ) (y : Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    (hy : y ∈ EF.filtration.layer j) :
    ∃ x ∈ E.filtration.layer j,
      D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W x = y := by
  rw [hEF] at hy
  obtain ⟨x, hx, heq⟩ := D.filtration.gradedRefiltrationMap_layer_surjective
    Fmark.filtration b ω hD c ν hF φ hφ W hW hsurj j y hy
  exact ⟨x, by rwa [hE], heq⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (E : RationalFilteredNilmanifold M (s + 1) e)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)
    (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
    (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)

theorem topQuotientMarkedMap_basis_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hQ : Q.GeometryComplexityLE p)
    (hproj : ∀ i j, rationalLogHeight (Q.basis.repr
      (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis j)) i) ≤ p)
    (hmark : ∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis i)) j) ≤ p)
    (hprojF : ∀ i j, rationalLogHeight (QF.basis.repr
      (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤ p)
    (i : Fin n) (j : Fin m) :
    rationalLogHeight (QF.basis.repr (D.topQuotientMarkedMap E φ hφ (Q.basis i)) j) ≤
      quotientInducedMapHeightBudget p := by
  exact lieQuotientProjection_basis_logHeight
    (D.filtration.layerIdeal (s + 1)) (E.filtration.layerIdeal (s + 1))
    D.basis E.basis Q.basis QF.basis φ (hφ (s + 1)) hp
    (by simpa only [Fintype.card_fin] using hD.1)
    (by simpa only [Fintype.card_fin] using hE.1)
    (by simpa only [Fintype.card_fin] using hQ.1)
    (fun i j => hproj j i) hmark (fun i j => hprojF j i) i j

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (E : RationalFilteredNilmanifold M (s + 1) e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)
  (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop)
  (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)
  (hQF : QF.filtration = E.filtration.quotientTop)

include hQ hQF in

theorem topQuotientMarkedMap_layer_surjective
    (hsurj : ∀ j, ∀ y ∈ E.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (j : ℕ) (y : M ⧸ E.filtration.layerIdeal (s + 1)) (hy : y ∈ QF.filtration.layer j) :
    ∃ x ∈ Q.filtration.layer j, D.topQuotientMarkedMap E φ hφ x = y := by
  rw [hQF] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨x, hx, hφx⟩ := hsurj j z hz
  refine ⟨lieQuotientMap (D.filtration.layerIdeal (s + 1)) x, ?_, ?_⟩
  · rw [hQ]
    exact ⟨x, hx, rfl⟩
  · exact congrArg (lieQuotientMap (E.filtration.layerIdeal (s + 1))) hφx

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (E : RationalFilteredNilmanifold M (s + 1) e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)
  (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop)
  (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)
  (hQF : QF.filtration = E.filtration.quotientTop) {w : σ → ℕ}

noncomputable def markedTopQuotientDiagram (x : D.RealGroup) : Q.Space × E.Space :=
  (QuotientGroup.mk (realificationMap
    (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := Q.filtration.lowerCentralSeries_eq_bot)
    (lieQuotientMap (D.filtration.layerIdeal (s + 1))) x),
   QuotientGroup.mk (realificationMap
    (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ x))

theorem exists_marked_topQuotientOrbit_lift_diagram
    (hsurj : ∀ j, ∀ y ∈ E.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : E.filtration.realification.PolynomialOrbit w)
    (heq : D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q = E.topQuotientOrbit QF hQF marked) :
    ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.topQuotientOrbit Q hQ g = q ∧
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log ∧
      ∀ z : σ → ℝ,
        D.markedTopQuotientDiagram E φ Q
          (D.filtration.realification.polynomialOrbitRealEval w z g) =
        ((QuotientGroup.mk (Q.filtration.realification.polynomialOrbitRealEval w z q) : Q.Space),
         (QuotientGroup.mk (E.filtration.realification.polynomialOrbitRealEval w z marked) : E.Space)) := by
  obtain ⟨g, hg, hm, hqeval, hmeval⟩ :=
    D.exists_marked_topQuotientOrbit_lift_of_quotient_eq E φ hφ Q hQ QF hQF hsurj q marked heq
  refine ⟨g, hg, hm, ?_⟩
  intro z
  simp only [markedTopQuotientDiagram, hqeval z, hmeval z]

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOptionOriginalOrbit
namespace OAI

section

universe u v

namespace Erdos3

open scoped TensorProduct

variable {ι : Type v} {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]

instance optionRealificationTopology
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] (i : Option ι) :
    TopologicalSpace (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
  cases i with
  | none => exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] L₀))
  | some i => exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] L i))

instance optionRealificationTopologicalAddGroup
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    (i : Option ι) : IsTopologicalAddGroup (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
  cases i with
  | none => exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀))
  | some i => exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] L i))

instance optionRealificationContinuousSMul
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)]
    (i : Option ι) : ContinuousSMul ℝ (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
  cases i with
  | none => exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀))
  | some i => exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] L i))

instance optionRealificationT2Space
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
    [T2Space (ℝ ⊗[ℚ] L₀)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (i : Option ι) : T2Space (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
  cases i with
  | none => exact (inferInstance : T2Space (ℝ ⊗[ℚ] L₀))
  | some i => exact (inferInstance : T2Space (ℝ ⊗[ℚ] L i))

end Erdos3

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieFiltration
open scoped TensorProduct BigOperators

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def optionOriginalSpaceProjection : (optionProduct D₀ D).Space → D₀.Space :=
  productProjection (optionFactors D₀ D) none

@[simp] theorem optionOriginalSpaceProjection_mk (z : (optionProduct D₀ D).RealGroup) :
    optionOriginalSpaceProjection D₀ D (QuotientGroup.mk z) =
      QuotientGroup.mk (productProjectionHom (optionFactors D₀ D) none z) := rfl

@[simp] theorem optionOriginalSpaceProjection_piRealOrbit {σ : Type*} {w : σ → ℕ}
    (g : ∀ i, (optionFactors D₀ D i).filtration.realification.PolynomialOrbit w)
    (x : σ → ℤ) :
    optionOriginalSpaceProjection D₀ D
      (QuotientGroup.mk ((optionProduct D₀ D).filtration.realification.polynomialOrbitEval w x
        (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g))) =
      QuotientGroup.mk (D₀.filtration.realification.polynomialOrbitEval w x (g none)) :=
  congrArg (fun z : D₀.RealGroup => (QuotientGroup.mk z : D₀.Space))
    (piRealOrbit_eval (fun i => (optionFactors D₀ D i).filtration) g x none)

noncomputable def optionOriginalObservable {P : Type*} (observable : P → D₀.Space → ℂ) :
    P → (optionProduct D₀ D).Space → ℂ :=
  fun a z => observable a (optionOriginalSpaceProjection D₀ D z)

@[simp] theorem optionOriginalObservable_apply {P : Type*}
    (observable : P → D₀.Space → ℂ) (a : P) (z : (optionProduct D₀ D).Space) :
    optionOriginalObservable D₀ D observable a z =
      observable a (optionOriginalSpaceProjection D₀ D z) := rfl

@[simp] theorem optionOriginalObservable_piRealOrbit {P σ : Type*} {w : σ → ℕ}
    (observable : P → D₀.Space → ℂ)
    (g : ∀ i, (optionFactors D₀ D i).filtration.realification.PolynomialOrbit w)
    (a : P) (x : σ → ℤ) :
    optionOriginalObservable D₀ D observable a
      (QuotientGroup.mk ((optionProduct D₀ D).filtration.realification.polynomialOrbitEval w x
        (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g))) =
      observable a (QuotientGroup.mk
        (D₀.filtration.realification.polynomialOrbitEval w x (g none))) := by
  rw [optionOriginalObservable_apply, optionOriginalSpaceProjection_piRealOrbit]

section Metric

variable [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
  [T2Space (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]

theorem optionOriginalSpaceProjection_lipschitz :
    letI := (optionProduct D₀ D).metricSpace
    letI := D₀.metricSpace
    LipschitzWith (coordinateLipschitzBound d₀
      (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1)
      (optionOriginalSpaceProjection D₀ D) := by
  exact productProjection_lipschitz (optionFactors D₀ D) none

end Metric

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem optionOriginalProjection_layers (k : ℕ)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i)
    (hx : x ∈ (optionProduct D₀ D).filtration.layer k) :
    liePiEval (R := ℚ) none x ∈ D₀.filtration.layer k :=
  (mem_pi_layer (fun i => (optionFactors D₀ D i).filtration) k x).mp hx none

noncomputable def optionOriginalOrbit {σ : Type*} {w : σ → ℕ}
    (g : (optionProduct D₀ D).filtration.realification.PolynomialOrbit w) :
    D₀.filtration.realification.PolynomialOrbit w :=
  (D₀.filtration.realification.polynomialOrbitCoordinates w).symm
    ((optionProduct D₀ D).filtration.realPolynomialGroupMap D₀.filtration
      (liePiEval none) (optionOriginalProjection_layers D₀ D) w
      ((optionProduct D₀ D).filtration.realification.polynomialOrbitCoordinates w g))

attribute [local irreducible] realPolynomialGroupMap

@[simp] theorem optionOriginalOrbit_log {σ : Type*} {w : σ → ℕ}
    (g : (optionProduct D₀ D).filtration.realification.PolynomialOrbit w) :
    (optionOriginalOrbit D₀ D g).log =
      VectorPolynomial.map ((realificationLieHom (liePiEval (R := ℚ)
        (M := optionLieSpace L₀ L) none)).toLinearMap.restrictScalars ℚ) g.log := by
  unfold optionOriginalOrbit
  rw [polynomialOrbitCoordinates_symm_log]
  exact (optionProduct D₀ D).filtration.realPolynomialGroupMap_log D₀.filtration
    (liePiEval none) (optionOriginalProjection_layers D₀ D) w
    ((optionProduct D₀ D).filtration.realification.polynomialOrbitCoordinates w g)

@[simp] theorem optionOriginalOrbit_eval {σ : Type*} {w : σ → ℕ}
    (g : (optionProduct D₀ D).filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    D₀.filtration.realification.polynomialOrbitEval w x (optionOriginalOrbit D₀ D g) =
      productProjectionHom (optionFactors D₀ D) none
        ((optionProduct D₀ D).filtration.realification.polynomialOrbitEval w x g) := by
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.eval (fun i => (x i : ℚ)) (optionOriginalOrbit D₀ D g).log =
    realificationLieHom (liePiEval none) (VectorPolynomial.eval (fun i => (x i : ℚ)) g.log)
  rw [optionOriginalOrbit_log]
  exact VectorPolynomial.eval_map _ _ _

@[simp] theorem optionOriginalOrbit_value {σ : Type*} {w : σ → ℕ}
    (g : (optionProduct D₀ D).filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    optionOriginalSpaceProjection D₀ D
      (QuotientGroup.mk ((optionProduct D₀ D).filtration.realification.polynomialOrbitEval w x g)) =
    QuotientGroup.mk (D₀.filtration.realification.polynomialOrbitEval w x
      (optionOriginalOrbit D₀ D g)) :=
  congrArg (fun z : D₀.RealGroup => (QuotientGroup.mk z : D₀.Space))
    (optionOriginalOrbit_eval D₀ D g x).symm

@[simp] theorem optionOriginalOrbit_piRealOrbit {σ : Type*} {w : σ → ℕ}
    (g : ∀ i, (optionFactors D₀ D i).filtration.realification.PolynomialOrbit w) :
    optionOriginalOrbit D₀ D (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g) =
      g none := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change (optionOriginalOrbit D₀ D (piRealOrbit
    (fun i => (optionFactors D₀ D i).filtration) g)).log = (g none).log
  exact (optionOriginalOrbit_log D₀ D
    (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g)).trans
      (piRealOrbit_project_log (fun i => (optionFactors D₀ D i).filtration) g none)

theorem optionOriginalOrbit_score {P σ T : Type*} {w : σ → ℕ}
    (g : (optionProduct D₀ D).filtration.realification.PolynomialOrbit w)
    (observable : P → D₀.Space → ℂ)
    (sites : Finset T) (physical : T → P) (point : T → σ → ℤ) (weight : T → ℂ) :
    (𝔼 t ∈ sites, weight t * optionOriginalObservable D₀ D observable (physical t)
      (QuotientGroup.mk ((optionProduct D₀ D).filtration.realification.polynomialOrbitEval w (point t) g))) =
    𝔼 t ∈ sites, weight t * observable (physical t)
      (QuotientGroup.mk (D₀.filtration.realification.polynomialOrbitEval w (point t)
        (optionOriginalOrbit D₀ D g))) := by
  simp only [optionOriginalObservable_apply, optionOriginalOrbit_value]

theorem optionOriginalOrbit_mark_log {M₀ : Type u} [LieRing M₀] [LieAlgebra ℚ M₀]
    (Fmark : NilpotentLieFiltration M₀ s) (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    {σ : Type*} {w : σ → ℕ}
    (g : (optionProduct D₀ D).filtration.realification.PolynomialOrbit w)
    (marked : ∀ i, (optionFiltrations Fmark (fun j => (D j).filtration) i).realification.PolynomialOrbit w)
    (hmark : VectorPolynomial.map
      ((realificationLieHom (optionMarkedLieMap (L := L) φ)).toLinearMap.restrictScalars ℚ) g.log =
        (piRealOrbit (optionFiltrations Fmark (fun j => (D j).filtration)) marked).log) :
    VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ)
      (optionOriginalOrbit D₀ D g).log = (marked none).log :=
  (congrArg (VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ))
    (optionOriginalOrbit_log D₀ D g)).trans
      (optionMarkedPolynomialProjection_none g.log φ Fmark (fun j => (D j).filtration) marked hmark)

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOptionFixedSourceQuotientMarkStrong
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}

structure AdaptedModelData (D : RationalFilteredNilmanifold L s d) where
  basis : Basis (Fin (finrank ℚ L)) ℚ L
  weight : Fin (finrank ℚ L) → ℕ
  layers : ∀ j, D.filtration.layer j = Submodule.span ℚ (basis '' {i | j ≤ weight i})
  grid : ℕ
  grid_pos : 0 < grid
  inner : scaledIntegerGrid grid ⊆ bchSubgroupCoordinates basis D.lattice
  outer : bchSubgroupCoordinates basis D.lattice ⊆ denominatorGrid grid

namespace AdaptedModelData

variable {D : RationalFilteredNilmanifold L s d}

noncomputable def model (F : D.AdaptedModelData) : RationalFilteredNilmanifold L s (finrank ℚ L) :=
  D.filtration.ofAdaptedBasis F.basis F.weight F.layers D.lattice F.grid F.grid_pos F.inner F.outer

theorem model_layers (F : D.AdaptedModelData) (j : ℕ) :
    F.model.filtration.layer j = Submodule.span ℚ (F.model.basis '' {i | j ≤ F.weight i}) := F.layers j

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem original_dist_le (F : D.AdaptedModelData) (H : ℕ)
    (hH : ∀ i j, RationalHeightLE (D.basis.repr (F.basis i) j) H) (x y : D.Space) :
    @dist D.Space D.metricSpace.toDist x y ≤
      coordinateLipschitzBound d (finrank ℚ L) H * @dist F.model.Space F.model.metricSpace.toDist x y := by
  have hreal (j i) : |(D.basis.baseChange ℝ).repr ((F.basis.baseChange ℝ) i) j| ≤ (H : ℝ≥0) := by
    rw [Basis.baseChange_apply, Basis.baseChange_repr_tmul]
    simpa only [Rat.smul_def, mul_one, NNReal.coe_natCast] using (hH i j).abs_real_le
  have h := NilpotentLieBCHGroup.basisQuotientDist_change_le
    (F.basis.baseChange ℝ) (D.basis.baseChange ℝ) D.realLattice
    D.realLattice_closed_discrete.1 H hreal x y
  simp only [Fintype.card_fin] at h
  convert h using 1 <;> rfl

end AdaptedModelData

theorem exists_adapted_model_data (D : RationalFilteredNilmanifold L s d)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    ∃ F : D.AdaptedModelData, F.model.GeometryComplexityLE ((p + 3) ^ 11) ∧
      ∀ i j, rationalLogHeight (D.basis.repr (F.basis i) j) ≤ p + 1 := by
  obtain ⟨b, w, N, _, _, hlayers, hb, _, hc, hN, hNp, hin, hout⟩ :=
    D.exists_controlled_adapted_basis hp hD
  let F : D.AdaptedModelData := ⟨b, w, hlayers, N, hN, hin, hout⟩
  have hp1 : 1 ≤ p + 3 := by linarith
  have hpow : p ≤ (p + 3) ^ 11 := by
    calc
      p ≤ p + 3 := by linarith
      _ = (p + 3) ^ 1 := (pow_one _).symm
      _ ≤ (p + 3) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  have hdim : (finrank ℚ L : ℝ) ≤ (p + 3) ^ 11 := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using hD.1.trans hpow
  refine ⟨F, ?_, hb⟩
  exact D.filtration.ofAdaptedBasis_geometry b w hlayers D.lattice N hN hin hout
    (by positivity) hdim
    (hNp.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hp1 (by decide : 9 ≤ 11)))) hc

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_prescribed_adapted_model {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d n : ℕ} (D : RationalFilteredNilmanifold L s d)
    (b : Basis (Fin n) ℚ L) (ω : Fin n → ℕ)
    (hF : ∀ k, D.filtration.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hb : ∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p + 1) :
    ∃ (M : ℕ) (hM : 0 < M)
      (hin : scaledIntegerGrid M ⊆ bchSubgroupCoordinates b D.lattice)
      (hout : bchSubgroupCoordinates b D.lattice ⊆ denominatorGrid M),
      (D.filtration.ofAdaptedBasis b ω hF D.lattice M hM hin hout).GeometryComplexityLE
        ((p + 4) ^ 11) := by
  obtain ⟨hdim, _hinverse, hstructure⟩ := D.basis_geometry_of_forward_height b hp hD hb
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp (p + 1)
  have hHp : (H : ℝ) ≤ Real.exp (p + 2) := by
    simpa only [show p + 1 + 1 = p + 2 by ring] using
      ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)
  have hentries : ∀ i j, RationalHeightLE (D.basis.repr (b i) j) H :=
    fun i j => rationalHeightLE_ceil_exp (hb i j)
  have hd : (Fintype.card (Fin d) : ℝ) ≤ p + 2 := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 2 by linarith)
  obtain ⟨M, hM, hMp, hin, hout⟩ := exists_basis_change_grid_exp_bound D.basis b D.lattice
    hH D.grid_pos hentries D.inner_grid D.outer_grid (by linarith : 0 ≤ p + 2) hd
    (hdim.trans (by linarith)) hHp (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
  have hbase : 1 ≤ p + 4 := by linarith
  have hpbig : p ≤ (p + 4) ^ 11 := by
    apply (show p ≤ p + 4 by linarith).trans
    simpa only [pow_one] using pow_le_pow_right₀ hbase (by decide : 1 ≤ 11)
  have hgrid : (M : ℝ) ≤ Real.exp ((p + 4) ^ 11) := by
    have hsmall : (M : ℝ) ≤ Real.exp ((p + 4) ^ 9) := by
      simpa only [show p + 2 + 2 = p + 4 by ring] using hMp
    exact hsmall.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (by decide : 9 ≤ 11)))
  refine ⟨M, hM, hin, hout, ?_⟩
  exact D.filtration.ofAdaptedBasis_geometry b ω hF D.lattice M hM hin hout
    (by positivity) (by simpa only [Fintype.card_fin] using hdim.trans hpbig) hgrid hstructure

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t d e : ℕ}

structure AdaptedMapGeometryData (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M t e) (φ : L →ₗ⁅ℚ⁆ M) (p q : ℝ) where
  source : D.AdaptedModelData
  target : E.AdaptedModelData
  budget_nonneg : 0 ≤ q
  forward_budget : p + 1 ≤ q
  source_dimension : (finrank ℚ L : ℝ) ≤ p
  target_dimension : (finrank ℚ M : ℝ) ≤ p
  source_geometry : source.model.GeometryComplexityLE q
  target_geometry : target.model.GeometryComplexityLE q
  source_forward : ∀ i j, rationalLogHeight (D.basis.repr (source.basis i) j) ≤ p + 1
  target_forward : ∀ i j, rationalLogHeight (E.basis.repr (target.basis i) j) ≤ p + 1
  source_inverse : ∀ i j, rationalLogHeight (source.basis.repr (D.basis i) j) ≤ q
  target_inverse : ∀ i j, rationalLogHeight (target.basis.repr (E.basis i) j) ≤ q
  source_structure : ∀ i j k,
    rationalLogHeight (source.basis.repr ⁅source.basis i, source.basis j⁆ k) ≤ q
  target_structure : ∀ i j k,
    rationalLogHeight (target.basis.repr ⁅target.basis i, target.basis j⁆ k) ≤ q
  entries_height : ℕ
  entries_height_pos : 0 < entries_height
  entries_bound : (entries_height : ℝ) ≤ Real.exp q
  entries : ∀ i j,
    RationalHeightLE (target.basis.repr (φ (source.basis j)) i) entries_height
  entries_logHeight : ∀ i j,
    rationalLogHeight (target.basis.repr (φ (source.basis j)) i) ≤ q

theorem exists_native_adapted_map_geometry :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
        {s t d e : ℕ} (D : RationalFilteredNilmanifold L s d)
        (E : RationalFilteredNilmanifold M t e) (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ},
        0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
        (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis i)) j) ≤ p) →
        Nonempty (D.AdaptedMapGeometryData E φ p ((p + 2) ^ C)) := by
  obtain ⟨C, hC, hbudget⟩ := exists_adaptedMapGeometryBudget_fixed_power
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ s t d e D E φ p hp hD hE hφ
  obtain ⟨source, hsource, hsourceForward⟩ := D.exists_adapted_model_data hp hD
  obtain ⟨target, htarget, htargetForward⟩ := E.exists_adapted_model_data hp hE
  obtain ⟨hsourceDim, hsourceInverse, _⟩ :=
    D.basis_geometry_of_forward_height source.basis hp hD hsourceForward
  obtain ⟨htargetDim, htargetInverse, _⟩ :=
    E.basis_geometry_of_forward_height target.basis hp hE htargetForward
  have hp1 : 0 ≤ p + 1 := by linarith
  have hmap := D.markedMap_basisChange_logHeight E source.basis target.basis φ.toLinearMap
    hp1 (hD.mono D (by linarith)) (hE.mono E (by linarith))
    hsourceForward htargetForward (fun i j => (hφ i j).trans (by linarith))
  let r := adaptedMapGeometryBudget p
  have hr : 0 ≤ r := adaptedMapGeometryBudget_nonneg hp
  have hgeomr : (p + 3) ^ 11 ≤ r := adaptedMapGeometryBudget_geometry hp
  have hinverser : (p + 4) ^ 5 ≤ r := by
    have hpow : (p + 4) ^ 5 ≤ (p + 4) ^ 11 :=
      pow_le_pow_right₀ (by linarith) (by decide)
    exact hpow.trans (adaptedMapGeometryBudget_inverse hp)
  have hmapr : adaptedMarkedMapHeightBudget (p + 1) ≤ r :=
    adaptedMapGeometryBudget_markedMap hp
  have hforwardr : p + 1 ≤ r := by
    exact (show p + 1 ≤ p + 2 by linarith).trans (adaptedMapGeometryBudget_parameter hp)
  have hrq : r ≤ (p + 2) ^ C := (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
    (hbudget p hp)
  have hsourceq := hsource.mono source.model (hgeomr.trans hrq)
  have htargetq := htarget.mono target.model (hgeomr.trans hrq)
  let H := ⌈Real.exp r⌉₊
  refine ⟨{
    source := source
    target := target
    budget_nonneg := hr.trans hrq
    forward_budget := hforwardr.trans hrq
    source_dimension := ?_
    target_dimension := ?_
    source_geometry := hsourceq
    target_geometry := htargetq
    source_forward := hsourceForward
    target_forward := htargetForward
    source_inverse := fun i j => (hsourceInverse i j).trans (hinverser.trans hrq)
    target_inverse := fun i j => (htargetInverse i j).trans (hinverser.trans hrq)
    source_structure := hsourceq.2.2.1
    target_structure := htargetq.2.2.1
    entries_height := H
    entries_height_pos := lt_of_lt_of_le Nat.zero_lt_one (one_le_ceil_exp r)
    entries_bound := (ceil_exp_le_exp_add_one hr).trans (Real.exp_le_exp.mpr (hbudget p hp))
    entries := fun i j => rationalHeightLE_ceil_exp ((hmap j i).trans hmapr)
    entries_logHeight := fun i j => (hmap j i).trans (hmapr.trans hrq)
  }⟩
  · simpa only [Fintype.card_fin] using hsourceDim
  · simpa only [Fintype.card_fin] using htargetDim

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t d f : ℕ}

structure FixedSourceAdaptedMarkGeometryData
    (D : RationalFilteredNilmanifold L s d)
    (Fmark : RationalFilteredNilmanifold M t f)
    (source : D.AdaptedModelData) (φ : L →ₗ⁅ℚ⁆ M) (p q : ℝ) where
  target : Fmark.AdaptedModelData
  target_geometry : target.model.GeometryComplexityLE q
  target_dimension : (finrank ℚ M : ℝ) ≤ p
  target_forward : ∀ i j,
    rationalLogHeight (Fmark.basis.repr (target.basis i) j) ≤ p + 1
  target_inverse : ∀ i j,
    rationalLogHeight (target.basis.repr (Fmark.basis i) j) ≤ q
  target_structure : ∀ i j k,
    rationalLogHeight (target.basis.repr ⁅target.basis i, target.basis j⁆ k) ≤ q
  entries_height : ℕ
  entries_height_pos : 0 < entries_height
  entries_bound : (entries_height : ℝ) ≤ Real.exp q
  entries : ∀ i j,
    RationalHeightLE (target.basis.repr (φ (source.basis j)) i) entries_height
  entries_logHeight : ∀ i j,
    rationalLogHeight (target.basis.repr (φ (source.basis j)) i) ≤ q

theorem exists_native_fixedSource_adapted_mark_geometry :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
        {s t d f : ℕ} (D : RationalFilteredNilmanifold L s d)
        (Fmark : RationalFilteredNilmanifold M t f)
        (source : D.AdaptedModelData) (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ},
        0 ≤ p → D.GeometryComplexityLE p → Fmark.GeometryComplexityLE p →
        (∀ i j, rationalLogHeight (D.basis.repr (source.basis i) j) ≤ p + 1) →
        (∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p) →
        Nonempty (D.FixedSourceAdaptedMarkGeometryData Fmark source φ p ((p + 2) ^ C)) := by
  obtain ⟨C, hC, hbudget⟩ := exists_adaptedMapGeometryBudget_fixed_power
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ s t d f D Fmark source φ p hp hD hF hsource hφ
  obtain ⟨target, htarget, htargetForward⟩ := Fmark.exists_adapted_model_data hp hF
  obtain ⟨htargetDim, htargetInverse, _⟩ :=
    Fmark.basis_geometry_of_forward_height target.basis hp hF htargetForward
  have hp1 : 0 ≤ p + 1 := by linarith
  have hmap := D.markedMap_basisChange_logHeight Fmark source.basis target.basis φ.toLinearMap
    hp1 (hD.mono D (by linarith)) (hF.mono Fmark (by linarith))
    hsource htargetForward (fun i j => (hφ i j).trans (by linarith))
  let r := adaptedMapGeometryBudget p
  have hr : 0 ≤ r := adaptedMapGeometryBudget_nonneg hp
  have hgeomr : (p + 3) ^ 11 ≤ r := adaptedMapGeometryBudget_geometry hp
  have hinverser : (p + 4) ^ 5 ≤ r :=
    (pow_le_pow_right₀ (by linarith : 1 ≤ p + 4) (by decide : (5 : ℕ) ≤ 11)).trans
      (adaptedMapGeometryBudget_inverse hp)
  have hmapr : adaptedMarkedMapHeightBudget (p + 1) ≤ r :=
    adaptedMapGeometryBudget_markedMap hp
  have hrq : r ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans (hbudget p hp)
  have htargetq := htarget.mono target.model (hgeomr.trans hrq)
  let H := ⌈Real.exp r⌉₊
  exact ⟨{
    target := target
    target_geometry := htargetq
    target_dimension := by simpa only [Fintype.card_fin] using htargetDim
    target_forward := htargetForward
    target_inverse := fun i j => (htargetInverse i j).trans (hinverser.trans hrq)
    target_structure := htargetq.2.2.1
    entries_height := H
    entries_height_pos := lt_of_lt_of_le Nat.zero_lt_one (one_le_ceil_exp r)
    entries_bound := (ceil_exp_le_exp_add_one hr).trans (Real.exp_le_exp.mpr (hbudget p hp))
    entries := fun i j => rationalHeightLE_ceil_exp ((hmap j i).trans hmapr)
    entries_logHeight := fun i j => (hmap j i).trans (hmapr.trans hrq)
  }⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
    [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
    {s d₀ : ℕ} {d : ι → ℕ}
    (D₀ : RationalFilteredNilmanifold L₀ s d₀)
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    {P : Type*} (observable : P → D₀.Space → ℂ)

theorem optionOriginalObservable_unit_interval
    (hunit : ∀ a y, (observable a y).im = 0 ∧
      0 ≤ (observable a y).re ∧ (observable a y).re ≤ 1) :
    ∀ a y, (optionOriginalObservable D₀ D observable a y).im = 0 ∧
      0 ≤ (optionOriginalObservable D₀ D observable a y).re ∧
      (optionOriginalObservable D₀ D observable a y).re ≤ 1 := by
  intro a y
  exact hunit a (optionOriginalSpaceProjection D₀ D y)

theorem optionOriginalObservable_member_net (sites : Set P) {n : ℕ}
    (centers : Fin n → {a : P // a ∈ sites}) (η : ℝ)
    (hnet : ∀ a ∈ sites, ∃ i, ∀ y,
      ‖observable a y - observable (centers i).val y‖ ≤ η) :
    ∀ a ∈ sites, ∃ i, ∀ y,
      ‖optionOriginalObservable D₀ D observable a y -
        optionOriginalObservable D₀ D observable (centers i).val y‖ ≤ η := by
  intro a ha
  obtain ⟨i, hi⟩ := hnet a ha
  exact ⟨i, fun y => hi (optionOriginalSpaceProjection D₀ D y)⟩

theorem optionOriginalObservable_member_nets (sites : Set P) (entropy : ℝ → ℝ)
    (hnets : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ entropy η ∧ ∃ centers : Fin n → {a : P // a ∈ sites},
        ∀ a ∈ sites, ∃ i, ∀ y,
          ‖observable a y - observable (centers i).val y‖ ≤ η) :
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ entropy η ∧ ∃ centers : Fin n → {a : P // a ∈ sites},
        ∀ a ∈ sites, ∃ i, ∀ y,
          ‖optionOriginalObservable D₀ D observable a y -
            optionOriginalObservable D₀ D observable (centers i).val y‖ ≤ η := by
  intro η hη hη1
  obtain ⟨n, hn, centers, hnet⟩ := hnets η hη hη1
  exact ⟨n, hn, centers,
    optionOriginalObservable_member_net D₀ D observable sites centers η hnet⟩

theorem optionOriginalObservable_adapted_unit_interval
    (adapted : (optionProduct D₀ D).AdaptedModelData)
    (hunit : ∀ a y, (observable a y).im = 0 ∧
      0 ≤ (observable a y).re ∧ (observable a y).re ≤ 1) :
    ∀ a (y : adapted.model.Space),
      (optionOriginalObservable D₀ D observable a y).im = 0 ∧
      0 ≤ (optionOriginalObservable D₀ D observable a y).re ∧
      (optionOriginalObservable D₀ D observable a y).re ≤ 1 :=
  optionOriginalObservable_unit_interval D₀ D observable hunit

theorem optionOriginalObservable_adapted_member_nets
    (adapted : (optionProduct D₀ D).AdaptedModelData)
    (sites : Set P) (entropy : ℝ → ℝ)
    (hnets : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ entropy η ∧ ∃ centers : Fin n → {a : P // a ∈ sites},
        ∀ a ∈ sites, ∃ i, ∀ y,
          ‖observable a y - observable (centers i).val y‖ ≤ η) :
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ entropy η ∧ ∃ centers : Fin n → {a : P // a ∈ sites},
        ∀ a ∈ sites, ∃ i, ∀ y : adapted.model.Space,
          ‖optionOriginalObservable D₀ D observable a y -
            optionOriginalObservable D₀ D observable (centers i).val y‖ ≤ η :=
  optionOriginalObservable_member_nets D₀ D observable sites entropy hnets

noncomputable def optionOriginalAdaptedLipschitzBound (ℓ : ℝ≥0) (H : ℕ) : ℝ≥0 :=
  ℓ * coordinateLipschitzBound d₀
      (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1 *
    coordinateLipschitzBound
      (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i)))
      (finrank ℚ (∀ i : Option ι, optionLieSpace L₀ L i)) H

include D₀ D in

theorem optionOriginalAdaptedLipschitzBound_le_exp (ℓ : ℝ≥0) (H : ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hd₀ : (d₀ : ℝ) ≤ p)
    (htotal : (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i)) : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (optionOriginalAdaptedLipschitzBound (L₀ := L₀) (L := L)
      (d₀ := d₀) (d := d) ℓ H : ℝ) ≤ Real.exp (p + 2 * (p + 2) ^ 2) := by
  have hfin : (finrank ℚ (∀ i : Option ι, optionLieSpace L₀ L i) : ℝ) ≤ p := by
    simpa only [finrank_eq_card_basis (optionProduct D₀ D).basis, Fintype.card_fin] using htotal
  have hproj := coordinateLipschitzBound_le_exp d₀
    (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1 hp hd₀ htotal
    (by simpa only [NNReal.coe_one] using Real.one_le_exp_iff.mpr hp)
  have hbase := coordinateLipschitzBound_le_exp
    (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i)))
    (finrank ℚ (∀ i : Option ι, optionLieSpace L₀ L i)) H hp htotal hfin hH
  calc
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ 2) * Real.exp ((p + 2) ^ 2) := by
      exact mul_le_mul (mul_le_mul hℓ hproj (NNReal.coe_nonneg _) (Real.exp_pos _).le)
        hbase (NNReal.coe_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

section Metric

variable [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    [TopologicalSpace (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
    [T2Space (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]

theorem optionOriginalObservable_lipschitz (ℓ : ℝ≥0)
    (hLip : ∀ a, letI := D₀.metricSpace; LipschitzWith ℓ (observable a)) :
    ∀ a, letI := (optionProduct D₀ D).metricSpace
      LipschitzWith (ℓ * coordinateLipschitzBound d₀
        (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1)
        (optionOriginalObservable D₀ D observable a) := by
  intro a
  let := D₀.metricSpace
  let := (optionProduct D₀ D).metricSpace
  exact (hLip a).comp (optionOriginalSpaceProjection_lipschitz D₀ D)

theorem optionOriginalObservable_adapted_lipschitz
    (adapted : (optionProduct D₀ D).AdaptedModelData) (ℓ : ℝ≥0) (H : ℕ)
    (hH : ∀ i j, RationalHeightLE ((optionProduct D₀ D).basis.repr (adapted.basis i) j) H)
    (hLip : ∀ a, letI := D₀.metricSpace; LipschitzWith ℓ (observable a)) :
    ∀ a, letI := adapted.model.metricSpace
      LipschitzWith (optionOriginalAdaptedLipschitzBound (L₀ := L₀) (L := L)
        (d₀ := d₀) (d := d) ℓ H)
        (fun y : adapted.model.Space => optionOriginalObservable D₀ D observable a y) := by
  intro a
  let := adapted.model.metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have horiginal := optionOriginalObservable_lipschitz D₀ D observable ℓ hLip a
  have hd : dist (optionOriginalObservable D₀ D observable a x)
      (optionOriginalObservable D₀ D observable a y) ≤
      ↑(ℓ * coordinateLipschitzBound d₀
        (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1) *
        @dist (optionProduct D₀ D).Space (optionProduct D₀ D).metricSpace.toDist x y := by
    let := (optionProduct D₀ D).metricSpace
    exact horiginal.dist_le_mul x y
  have hchange := adapted.original_dist_le H hH x y
  calc
    dist (optionOriginalObservable D₀ D observable a x)
        (optionOriginalObservable D₀ D observable a y) ≤
        ↑(ℓ * coordinateLipschitzBound d₀
          (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1) *
          @dist (optionProduct D₀ D).Space (optionProduct D₀ D).metricSpace.toDist x y := hd
    _ ≤ ↑(ℓ * coordinateLipschitzBound d₀
          (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1) *
        (coordinateLipschitzBound
          (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i)))
          (finrank ℚ (∀ i : Option ι, optionLieSpace L₀ L i)) H * dist x y) :=
      mul_le_mul_of_nonneg_left hchange (NNReal.coe_nonneg _)
    _ = _ := by simp only [optionOriginalAdaptedLipschitzBound, NNReal.coe_mul]; ring

theorem optionOriginalObservable_adapted_lipschitz_of_logHeight
    (adapted : (optionProduct D₀ D).AdaptedModelData) (ℓ : ℝ≥0) (height : ℝ)
    (hheight : ∀ i j,
      rationalLogHeight ((optionProduct D₀ D).basis.repr (adapted.basis i) j) ≤ height)
    (hLip : ∀ a, letI := D₀.metricSpace; LipschitzWith ℓ (observable a)) :
    ∀ a, letI := adapted.model.metricSpace
      LipschitzWith (optionOriginalAdaptedLipschitzBound (L₀ := L₀) (L := L)
        (d₀ := d₀) (d := d) ℓ ⌈Real.exp height⌉₊)
        (fun y : adapted.model.Space => optionOriginalObservable D₀ D observable a y) :=
  optionOriginalObservable_adapted_lipschitz D₀ D observable adapted ℓ
    ⌈Real.exp height⌉₊ (fun i j => rationalHeightLE_ceil_exp (hheight i j)) hLip

end Metric

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

noncomputable def nativeOptionFixedSourceMarkExponent : ℕ :=
  Classical.choose exists_native_fixedSource_adapted_mark_geometry.{u, v}

noncomputable def nativeOptionFixedSourceQuotientMarkInput (p : ℝ) : ℝ :=
  (p + 3) ^ 2 + quotientInducedMarkHeightBudget p

theorem nativeOptionFixedSourceQuotientMarkInput_bounds {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ nativeOptionFixedSourceQuotientMarkInput p ∧
    (p + 3) ^ 2 ≤ nativeOptionFixedSourceQuotientMarkInput p ∧
    quotientInducedMarkHeightBudget p ≤ nativeOptionFixedSourceQuotientMarkInput p := by
  have hinduced : 0 ≤ quotientInducedMarkHeightBudget p := by
    unfold quotientInducedMarkHeightBudget
    positivity
  have hjoint : 0 ≤ (p + 3) ^ 2 := sq_nonneg _
  dsimp [nativeOptionFixedSourceQuotientMarkInput]
  constructor
  · exact add_nonneg hjoint hinduced
  constructor <;> linarith

variable {Pivot : Type v} [Fintype Pivot]
    {L M : Type u} {Partner : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [∀ a, LieRing (Partner a)] [∀ a, LieAlgebra ℚ (Partner a)]
    {s d f dQ : ℕ} {dp : Pivot → ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (Mmark : RationalFilteredNilmanifold M s f)
    (ideal : LieIdeal ℚ L)
    (hkill : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hkill)
    (atoms : ∀ a, RationalFilteredNilmanifold (Partner a) s (dp a))
    (φ : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ ideal, φ x = 0)
    (hφ : ∀ k, ∀ x ∈ D.filtration.layer k, φ x ∈ Mmark.filtration.layer k)
    (source : (optionProduct Q atoms).AdaptedModelData)

include hQ hφ in

theorem nativeOptionFixedSourceQuotientMark_mem_layer
    (k : ℕ) (x : ∀ i : Option Pivot, optionLieSpace (L ⧸ ideal) Partner i)
    (hx : x ∈ source.model.filtration.layer k) :
    optionMarkedLieMap (L := Partner) (quotientInducedMark ideal φ hker) x ∈
      (NilpotentLieFiltration.pi
        (optionFiltrations Mmark.filtration (fun a => (atoms a).filtration))).layer k := by
  have hinduced : ∀ k, ∀ y ∈ Q.filtration.layer k,
      quotientInducedMark ideal φ hker y ∈ Mmark.filtration.layer k := by
    intro k y hy
    rw [hQ] at hy
    exact D.filtration.quotientInducedMark_mem_layer Mmark.filtration
      ideal hkill φ hker hφ k y hy
  have hfiltration : (fun i => (optionFactors Q atoms i).filtration) =
      optionFiltrations Q.filtration (fun a => (atoms a).filtration) := by
    funext i
    cases i <;> rfl
  change x ∈ (NilpotentLieFiltration.pi (fun i => (optionFactors Q atoms i).filtration)).layer k at hx
  rw [hfiltration] at hx
  exact optionMarkedLieMap_mem_layer Q.filtration Mmark.filtration
    (fun a => (atoms a).filtration) (quotientInducedMark ideal φ hker) hinduced k x hx

include hQ hφ in

theorem exists_nativeOptionFixedSourceQuotientMarkGeometry
    {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hMmark : Mmark.GeometryComplexityLE p)
    (hQgeometry : Q.GeometryComplexityLE p)
    (hAtoms : ∀ a, (atoms a).GeometryComplexityLE p)
    (hPivot : (Fintype.card Pivot : ℝ) ≤ p)
    (hprojection : ∀ i j, rationalLogHeight
      (Q.basis.repr (lieQuotientMap ideal (D.basis j)) i) ≤ p)
    (hmark : ∀ i j, rationalLogHeight (Mmark.basis.repr (φ (D.basis j)) i) ≤ p)
    (hsource : ∀ i j, rationalLogHeight
      ((optionProduct Q atoms).basis.repr (source.basis i) j) ≤ (p + 3) ^ 2 + 1) :
    ∃ markGeometry : (optionProduct Q atoms).FixedSourceAdaptedMarkGeometryData
        (optionProduct Mmark atoms) source
        (optionMarkedLieMap (L := Partner) (quotientInducedMark ideal φ hker))
        (nativeOptionFixedSourceQuotientMarkInput p)
        ((nativeOptionFixedSourceQuotientMarkInput p + 2) ^ nativeOptionFixedSourceMarkExponent.{max u v, max u v}),
      markGeometry.target.model.filtration =
        NilpotentLieFiltration.pi
          (optionFiltrations Mmark.filtration (fun a => (atoms a).filtration)) ∧
      ∀ k, ∀ x ∈ source.model.filtration.layer k,
        optionMarkedLieMap (L := Partner) (quotientInducedMark ideal φ hker) x ∈
          markGeometry.target.model.filtration.layer k := by
  have hinput := nativeOptionFixedSourceQuotientMarkInput_bounds hp
  have hinduced := D.quotientInducedMark_native_logHeight Mmark ideal Q φ hker
    hp hD hQgeometry hprojection hmark
  have hinduced0 : 0 ≤ quotientInducedMarkHeightBudget p := by
    unfold quotientInducedMarkHeightBudget
    positivity
  have hoption := optionMarkedLieMap_native_logHeight Q Mmark atoms
    (quotientInducedMark ideal φ hker) hinduced0 hinduced
  have hsourceGeo := optionProduct_geometry Q atoms hp hPivot hQgeometry hAtoms
  have htargetGeo := optionProduct_geometry Mmark atoms hp hPivot hMmark hAtoms
  obtain ⟨markGeometry⟩ :=
    (Classical.choose_spec exists_native_fixedSource_adapted_mark_geometry.{max u v, max u v}).2
      (optionProduct Q atoms) (optionProduct Mmark atoms) source
      (optionMarkedLieMap (L := Partner) (quotientInducedMark ideal φ hker))
      hinput.1
      (hsourceGeo.mono (optionProduct Q atoms) hinput.2.1)
      (htargetGeo.mono (optionProduct Mmark atoms) hinput.2.1)
      (fun i j => (hsource i j).trans (by linarith only [hinput.2.1]))
      (fun i j => (hoption j i).trans hinput.2.2)
  have hMark : markGeometry.target.model.filtration =
      NilpotentLieFiltration.pi
        (optionFiltrations Mmark.filtration (fun a => (atoms a).filtration)) := by
    change NilpotentLieFiltration.pi (fun i => (optionFactors Mmark atoms i).filtration) = _
    congr 1
    funext i
    cases i <;> rfl
  refine ⟨markGeometry, hMark, ?_⟩
  intro k x hx
  rw [hMark]
  exact D.nativeOptionFixedSourceQuotientMark_mem_layer Mmark ideal hkill Q hQ
    atoms φ hker hφ source k x hx

theorem optionAdaptedModel_layers
    (target : (optionProduct Mmark atoms).AdaptedModelData) (k : ℕ) :
    (NilpotentLieFiltration.pi
      (optionFiltrations Mmark.filtration (fun a => (atoms a).filtration))).layer k =
      Submodule.span ℚ (target.basis '' {i | k ≤ target.weight i}) := by
  have hfiltration : (fun i => (optionFactors Mmark atoms i).filtration) =
      optionFiltrations Mmark.filtration (fun a => (atoms a).filtration) := by
    funext i
    cases i <;> rfl
  have hlayers := target.layers k
  change (NilpotentLieFiltration.pi (fun i => (optionFactors Mmark atoms i).filtration)).layer k =
    Submodule.span ℚ (target.basis '' {i | k ≤ target.weight i}) at hlayers
  rw [hfiltration] at hlayers
  exact hlayers

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {Pivot : Type v} [Fintype Pivot]
    {L M : Type u} {Partner : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [∀ a, LieRing (Partner a)] [∀ a, LieAlgebra ℚ (Partner a)]
    {s d f dQ : ℕ} {dp : Pivot → ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (Mmark : RationalFilteredNilmanifold M s f)
    (ideal : LieIdeal ℚ L)
    (hkill : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hkill)
    (atoms : ∀ a, RationalFilteredNilmanifold (Partner a) s (dp a))
    (φ : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ ideal, φ x = 0)
    (source : (optionProduct Q atoms).AdaptedModelData)
    (hsurj : ∀ k, ∀ y ∈ Mmark.filtration.layer k,
      ∃ x ∈ D.filtration.layer k, φ x = y)

include hQ hsurj in

theorem nativeOptionFixedSourceQuotientMark_layer_surjective
    (k : ℕ) (y : ∀ i : Option Pivot, optionLieSpace M Partner i)
    (hy : y ∈ (NilpotentLieFiltration.pi
      (optionFiltrations Mmark.filtration (fun a => (atoms a).filtration))).layer k) :
    ∃ x ∈ source.model.filtration.layer k,
      optionMarkedLieMap (L := Partner) (quotientInducedMark ideal φ hker) x = y := by
  have hcoord := (mem_pi_layer
    (optionFiltrations Mmark.filtration (fun a => (atoms a).filtration)) k y).mp hy
  obtain ⟨x₀, hx₀, hxy₀⟩ := hsurj k (y none) (hcoord none)
  let x : ∀ i : Option Pivot, optionLieSpace (L ⧸ ideal) Partner i
    | none => lieQuotientMap ideal x₀
    | some a => y (some a)
  refine ⟨x, ?_, ?_⟩
  · change x ∈ (NilpotentLieFiltration.pi
      (fun i => (optionFactors Q atoms i).filtration)).layer k
    apply (mem_pi_layer (fun i => (optionFactors Q atoms i).filtration) k x).mpr
    intro i
    cases i with
    | none =>
      change lieQuotientMap ideal x₀ ∈ Q.filtration.layer k
      rw [hQ]
      exact ⟨x₀, hx₀, rfl⟩
    | some a => exact hcoord (some a)
  · funext i
    cases i with
    | none => exact hxy₀
    | some a => rfl

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeComparisonProjections
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (p : ℝ) (B : ℕ) (hB : 0 < B)
  (hstable : M.SquarefreeGridStable p B)
  (E : RationalFilteredNilmanifold
    (M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))
    (max s (Fintype.card (ReplicatedIndex bound))) r)
  (hEL : E.lattice = M.comparisonLattice p B hB hstable)

noncomputable def comparisonFirstSpace : E.Space → D.Space :=
  cosetMap E.realLattice D.realLattice
    (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (M.filtration.comparisonFirst (fun i : ReplicatedIndex bound => i.1)))
    (realificationMap_subgroup _ _ _ (by rw [hEL]; exact M.comparisonLattice_first p B hB hstable))

noncomputable def comparisonSecondSpace : E.Space → (M.squarefreeModel p B hB hstable).Space :=
  cosetMap E.realLattice (M.squarefreeModel p B hB hstable).realLattice
    (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := (M.squarefreeModel p B hB hstable).filtration.lowerCentralSeries_eq_bot)
      (M.filtration.comparisonSecond (fun i : ReplicatedIndex bound => i.1)))
    (realificationMap_subgroup _ _ _ (by rw [hEL]; exact M.comparisonLattice_second p B hB hstable))

theorem comparisonFirstSpace_mk (g : E.RealGroup) :
    M.comparisonFirstSpace p B hB hstable E hEL (QuotientGroup.mk g) =
      QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (M.filtration.comparisonFirst (fun i : ReplicatedIndex bound => i.1)) g) := rfl

theorem comparisonSecondSpace_mk (g : E.RealGroup) :
    M.comparisonSecondSpace p B hB hstable E hEL (QuotientGroup.mk g) =
      QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := (M.squarefreeModel p B hB hstable).filtration.lowerCentralSeries_eq_bot)
        (M.filtration.comparisonSecond (fun i : ReplicatedIndex bound => i.1)) g) := rfl

theorem comparisonFirstSpace_smul (g : E.RealGroup) (x : E.Space) :
    M.comparisonFirstSpace p B hB hstable E hEL (g • x) =
      realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (M.filtration.comparisonFirst (fun i : ReplicatedIndex bound => i.1)) g •
        M.comparisonFirstSpace p B hB hstable E hEL x := cosetMap_smul _ _ _ _ _ _

theorem comparisonSecondSpace_smul (g : E.RealGroup) (x : E.Space) :
    M.comparisonSecondSpace p B hB hstable E hEL (g • x) =
      realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := (M.squarefreeModel p B hB hstable).filtration.lowerCentralSeries_eq_bot)
        (M.filtration.comparisonSecond (fun i : ReplicatedIndex bound => i.1)) g •
        M.comparisonSecondSpace p B hB hstable E hEL x := cosetMap_smul _ _ _ _ _ _

variable
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))]

theorem comparisonFirstSpace_lipschitz
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {q : ℝ} (hq : 0 ≤ q) (hD : D.GeometryComplexityLE q) (hE : E.GeometryComplexityLE q)
    (hheight : ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ q) :
    letI := E.metricSpace
    letI := D.metricSpace
    LipschitzWith ⟨Real.exp ((q + 3) ^ 2), (Real.exp_pos _).le⟩
      (M.comparisonFirstSpace p B hB hstable E hEL) := by
  let := E.metricSpace
  let := D.metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      exact nativeMap_dist_le E D
        (M.filtration.comparisonFirst (fun i : ReplicatedIndex bound => i.1))
        (by rw [hEL]; exact M.comparisonLattice_first p B hB hstable)
        hq hE hD (fun k j => hheight j k) x y

theorem comparisonSecondSpace_lipschitz
    [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun i : ReplicatedIndex bound => i.1))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun i : ReplicatedIndex bound => i.1))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun i : ReplicatedIndex bound => i.1))]
    [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun i : ReplicatedIndex bound => i.1))]
    {q : ℝ} (hq : 0 ≤ q)
    (hA : (M.squarefreeModel p B hB hstable).GeometryComplexityLE q)
    (hE : E.GeometryComplexityLE q)
    (hheight : ∀ j k, rationalLogHeight ((M.squarefreeFinBasis p).repr (E.basis j).val.2 k) ≤ q) :
    letI := E.metricSpace
    letI := (M.squarefreeModel p B hB hstable).metricSpace
    LipschitzWith ⟨Real.exp ((q + 3) ^ 2), (Real.exp_pos _).le⟩
      (M.comparisonSecondSpace p B hB hstable E hEL) := by
  let := E.metricSpace
  let := (M.squarefreeModel p B hB hstable).metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      exact nativeMap_dist_le E (M.squarefreeModel p B hB hstable)
        (M.filtration.comparisonSecond (fun i : ReplicatedIndex bound => i.1))
        (by rw [hEL]; exact M.comparisonLattice_second p B hB hstable)
        hq hE hA (fun k j => hheight j k) x y

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialGridValues
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_slow_polynomial_metric_budget (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d n H : ℕ) (p M : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (n : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      0 ≤ M → M ≤ Real.exp ((p + 2) ^ r) →
      ∃ B : ℝ≥0, 1 ≤ B ∧
        ((s : ℝ) + 1) * ((n : ℝ) + 1) ^ s * M ≤ B ∧
        (bchBoxMetricConstant s d H B : ℝ) *
          (((s : ℝ) + 1) * ((n : ℝ) + 1) ^ s * M * n * s) ≤
            Real.exp ((p + C) ^ C) := by
  let X : Polynomial ℕ := Polynomial.X
  let P := Polynomial.C s * (X + 1) + (X + 2) ^ r
  obtain ⟨a, _, hP⟩ := exists_natPolynomial_eval_budget P
  obtain ⟨b, _, hbox⟩ := exists_bchBoxMetricConstant_exp_bound s a
  let Q := (X + Polynomial.C a + Polynomial.C b) ^ b + P + X + Polynomial.C s
  obtain ⟨C, hC, hQ⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro d n H p M hp hd hn hH hM hMp
  let q : ℝ := s * (p + 1) + (p + 2) ^ r
  have hq : 0 ≤ q := by dsimp [q]; positivity
  let B : ℝ≥0 := ⟨Real.exp q, (Real.exp_pos _).le⟩
  have hB : 1 ≤ B := Real.one_le_exp hq
  have hn1 : (n : ℝ) + 1 ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hAM : ((s : ℝ) + 1) * ((n : ℝ) + 1) ^ s * M ≤ Real.exp q := by
    calc
      _ ≤ Real.exp s * (Real.exp p) ^ s * Real.exp ((p + 2) ^ r) :=
        mul_le_mul (mul_le_mul (Real.add_one_le_exp (s : ℝ))
          (pow_le_pow_left₀ (by positivity) hn1 _) (by positivity) (Real.exp_pos _).le)
          hMp hM (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [q]; ring
  have hpA : p ≤ p + a := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hBa : (B : ℝ) ≤ Real.exp (((p + a) + 2) ^ a) := by
    apply Real.exp_le_exp.mpr
    have h := hP p hp
    have h' : q ≤ (p + a) ^ a := by simpa [P, X, q, Polynomial.eval₂_pow] using h
    exact h'.trans (pow_le_pow_left₀ (by positivity) (by linarith) _)
  have hBC : (bchBoxMetricConstant s d H B : ℝ) ≤ Real.exp ((p + a + b) ^ b) :=
    hbox d H B (p + a) (hp.trans hpA) (hd.trans hpA)
      (hH.trans (Real.exp_le_exp.mpr hpA)) hBa
  have hnexp : (n : ℝ) ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hsexp : (s : ℝ) ≤ Real.exp s := by linarith [Real.add_one_le_exp (s : ℝ)]
  refine ⟨B, hB, hAM, ?_⟩
  calc
    _ ≤ Real.exp ((p + a + b) ^ b) * (Real.exp q * Real.exp p * Real.exp s) := by
      apply mul_le_mul hBC
        (mul_le_mul (mul_le_mul hAM hnexp (Nat.cast_nonneg _) (Real.exp_pos _).le)
          hsexp (Nat.cast_nonneg _) (by positivity))
        (by positivity) (Real.exp_pos _).le
    _ = Real.exp (((p + a + b) ^ b) + q + p + s) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((p + C) ^ C) := by
      apply Real.exp_le_exp.mpr
      simpa [Q, P, X, q, Polynomial.eval₂_pow] using hQ p hp

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

theorem adaptedPolynomial_coordinate_totalDegree (hw : ∀ i, 0 < w i)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) (i : ι) :
    (coordinate (((b.baseChange ℝ).coord i).toAddMonoidHom)
      (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))).totalDegree ≤ s := by
  classical
  apply (degreeLE_one_iff_basis_totalDegree (b.baseChange ℝ) s _).mp ?_ i
  have hd := (F.realification.adaptedBCHToOrbit w g).degreeLE
  intro α hα
  apply hd α
  apply hα.trans_le
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Pi.one_apply, mul_one]
  exact Finset.sum_le_sum (fun j _ => Nat.le_mul_of_pos_right _ (hw j))

theorem polynomialSlowBound_value [Fintype σ] (hw : ∀ i, 0 < w i)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T M g) (v : σ → ℝ) (hv : ∀ i, |v i| ≤ T i) (i : ι) :
    |(b.baseChange ℝ).repr (F.adaptedPolynomialRealValueHom w v g).coord i| ≤
      ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M := by
  let P := coordinate (((b.baseChange ℝ).coord i).toAddMonoidHom)
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
  have hdegree : P.totalDegree ≤ s := F.adaptedPolynomial_coordinate_totalDegree b w hw g i
  have hcoeff (α : σ →₀ ℕ) : |P.coeff α| ≤ M / monomialScale T α := by
    dsimp only [P]
    rw [coeff_coordinate]
    exact hg α i
  have hcard : (P.support.card : ℝ) ≤ ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s := by
    exact_mod_cast polynomial_support_card_le P hdegree
  change |((b.baseChange ℝ).coord i) (eval₂ v (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)))| ≤ _
  rw [coordinate_eval₂]
  exact (abs_eval_le_scaled_box_bound P T v hT hM hcoeff hv).trans
    (mul_le_mul_of_nonneg_right hcard hM)

theorem polynomialSlowBound_difference [Fintype σ] (hw : ∀ i, 0 < w i)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T M g) (v z : σ → ℝ)
    (hv : ∀ i, |v i| ≤ T i) (hz : ∀ i, |z i| ≤ T i)
    (hvz : ∀ i, |v i - z i| ≤ T i * δ) (i : ι) :
    |(b.baseChange ℝ).repr (F.adaptedPolynomialRealValueHom w v g).coord i -
      (b.baseChange ℝ).repr (F.adaptedPolynomialRealValueHom w z g).coord i| ≤
      ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M * Fintype.card σ * s * δ := by
  let P := coordinate (((b.baseChange ℝ).coord i).toAddMonoidHom)
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
  have hdegree : P.totalDegree ≤ s := F.adaptedPolynomial_coordinate_totalDegree b w hw g i
  have hcoeff (α : σ →₀ ℕ) : |P.coeff α| ≤ M / monomialScale T α := by
    dsimp only [P]
    rw [coeff_coordinate]
    exact hg α i
  have hcard : (P.support.card : ℝ) ≤ ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s := by
    exact_mod_cast polynomial_support_card_le P hdegree
  change |((b.baseChange ℝ).coord i) (eval₂ v (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) -
    ((b.baseChange ℝ).coord i) (eval₂ z (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)))| ≤ _
  rw [coordinate_eval₂, coordinate_eval₂]
  apply (abs_eval_sub_eval_scaled_box_bound P T v z hT hM hδ hcoeff hv hz hvz hdegree).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hM) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)) hδ

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module _root_.MvPolynomial
open scoped TensorProduct

theorem exists_rational_polynomial_of_grid {σ : Type*} (P : MvPolynomial σ ℝ)
    (q : ℕ) (hq : 0 < q)
    (hP : ∀ α, ∃ a : ℤ, (a : ℝ) = (q : ℝ) * P.coeff α) :
    ∃ Q : MvPolynomial σ ℚ,
      Q.map (algebraMap ℚ ℝ) = P ∧ Q.totalDegree = P.totalDegree ∧
      ∀ α, (Q.coeff α).den ∣ q := by
  classical
  choose a ha using hP
  let Q : MvPolynomial σ ℚ := ∑ α ∈ P.support, monomial α ((a α : ℚ) / q)
  have hcoeff (α : σ →₀ ℕ) : Q.coeff α = if α ∈ P.support then (a α : ℚ) / q else 0 := by
    simp [Q, coeff_sum, coeff_monomial]
  have hcast (α : σ →₀ ℕ) : (((a α : ℚ) / q : ℚ) : ℝ) = P.coeff α := by
    push_cast
    apply (div_eq_iff (show (q : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hq.ne')).mpr
    simpa only [mul_comm] using ha α
  have hmap : Q.map (algebraMap ℚ ℝ) = P := by
    ext α
    rw [coeff_map, hcoeff]
    by_cases hα : α ∈ P.support
    · rw [if_pos hα]
      exact hcast α
    · rw [if_neg hα, map_zero, notMem_support_iff.mp hα]
  refine ⟨Q, hmap, ?_, ?_⟩
  · rw [← hmap, totalDegree, totalDegree,
      support_map_of_injective Q (algebraMap ℚ ℝ).injective]
  · intro α
    rw [hcoeff]
    split_ifs
    · have h := Rat.den_dvd (a α) (q : ℤ)
      rw [Rat.divInt_eq_div, Int.cast_natCast] at h
      exact Int.natCast_dvd_natCast.mp h
    · simp

namespace NilpotentLieFiltration

open VectorPolynomial

theorem polynomialRationalGrid_exists_coordinates {σ ι L : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) (q : ℕ) (hq : 0 < q)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w q g) :
    ∃ P : ι → MvPolynomial σ ℚ,
      (∀ i, (P i).totalDegree ≤ s) ∧ (∀ i α, ((P i).coeff α).den ∣ q) ∧
      ∀ x : σ → ℝ,
        realPolynomialBCHMap (hnil := F.realification.lowerCentralSeries_eq_bot)
          (b.baseChange ℝ) P x = F.adaptedPolynomialRealValueHom w x g := by
  classical
  let R := fun i => coordinate (((b.baseChange ℝ).coord i).toAddMonoidHom)
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
  obtain ⟨a, ha⟩ := hg
  have hR (i : ι) : ∀ α, ∃ z : ℤ, (z : ℝ) = (q : ℝ) * (R i).coeff α := by
    intro α
    refine ⟨a (α, i), ?_⟩
    dsimp only [R]
    rw [coeff_coordinate]
    exact congrFun ha (α, i)
  choose P hmap hdeg hden using fun i => exists_rational_polynomial_of_grid (R i) q hq (hR i)
  refine ⟨P, fun i => (hdeg i).le.trans (F.adaptedPolynomial_coordinate_totalDegree b w hw g i), hden, ?_⟩
  intro x
  apply NilpotentLieBCHGroup.ext
  apply (b.baseChange ℝ).equivFun.injective
  rw [realPolynomialBCHMap_coordinates]
  funext i
  change aeval x (P i) = ((b.baseChange ℝ).coord i)
    (VectorPolynomial.eval₂ x (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)))
  rw [coordinate_eval₂]
  change aeval x (P i) = MvPolynomial.eval x (R i)
  rw [← hmap i, MvPolynomial.eval_map]
  rfl

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

theorem polynomialSlowBound_dist_le (hw : ∀ i, 0 < w i)
    (H : ℕ) (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (B : ℝ≥0) (hB : 1 ≤ B)
    (hMB : ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M ≤ B)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T M g) (v z : σ → ℝ)
    (hv : ∀ i, |v i| ≤ T i) (hz : ∀ i, |z i| ≤ T i)
    (hvz : ∀ i, |v i - z i| ≤ T i * δ) :
    letI := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
    dist (F.adaptedPolynomialRealValueHom w v g) (F.adaptedPolynomialRealValueHom w z g) ≤
      (bchBoxMetricConstant s (Fintype.card ι) H B : ℝ) *
        (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M * Fintype.card σ * s) * δ := by
  let := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
  have h := dist_le_bchBoxMetricConstant (b.baseChange ℝ) (lieStructureConstants b)
    (fun i j k => (realLieBasis_structure b i j k).symm) hc B hB
    (show 0 ≤ ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M * Fintype.card σ * s * δ by positivity)
    (F.adaptedPolynomialRealValueHom w v g) (F.adaptedPolynomialRealValueHom w z g)
    (fun i => (F.polynomialSlowBound_value b w hw T hT hM g hg v hv i).trans hMB)
    (fun i => (F.polynomialSlowBound_value b w hw T hT hM g hg z hz i).trans hMB)
    (fun i => F.polynomialSlowBound_difference b w hw T hT hM hδ g hg v z hv hz hvz i)
  simpa only [mul_assoc] using h

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_polynomialSlowBound_dist_exp (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ g : (D.filtration.realification.adaptedPolynomialFiltration w).Group,
        D.filtration.PolynomialSlowBound D.basis w T (Real.exp ((p + 2) ^ r)) g →
        ∀ (v z : σ → ℝ) (δ : ℝ), 0 ≤ δ →
          (∀ i, |v i| ≤ T i) → (∀ i, |z i| ≤ T i) →
          (∀ i, |v i - z i| ≤ T i * δ) →
          letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
          dist (D.filtration.adaptedPolynomialRealValueHom w v g)
            (D.filtration.adaptedPolynomialRealValueHom w z g) ≤ Real.exp ((p + C) ^ C) * δ := by
  obtain ⟨a, _, hbound⟩ := exists_slow_polynomial_metric_budget s r
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + 1 + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D w hw p hp hD hσ T hT g hg v z δ hδ hv hz hvz
  let H := ⌈Real.exp p⌉₊
  have hpp : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  obtain ⟨B, hB, hMB, hK⟩ := hbound d (Fintype.card σ) H (p + 1)
    (Real.exp ((p + 2) ^ r)) (by linarith) (hD.1.trans hpp) (hσ.trans hpp)
    (ceil_exp_le_exp_add_one hp) (Real.exp_pos _).le
    (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) _))
  have hdist := D.filtration.polynomialSlowBound_dist_le D.basis w hw H
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)) T hT (Real.exp_pos _).le
    hδ B hB hMB g hg v z hv hz hvz
  have hK' : (bchBoxMetricConstant s (Fintype.card (Fin d)) H B : ℝ) *
      (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * Real.exp ((p + 2) ^ r) * Fintype.card σ * s) ≤
        Real.exp ((p + C) ^ C) := by
    rw [Fintype.card_fin]
    apply hK.trans (Real.exp_le_exp.mpr _)
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  exact hdist.trans (mul_le_mul_of_nonneg_right hK' hδ)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module _root_.MvPolynomial
open scoped TensorProduct

theorem polynomial_integer_value_common_denominator {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (q : ℕ)
    (hP : ∀ α, ∃ a : ℤ, (a : ℝ) = (q : ℝ) * P.coeff α) (x : σ → ℤ) :
    ∃ a : ℤ, (a : ℝ) = (q : ℝ) * eval (fun j => (x j : ℝ)) P := by
  classical
  choose a ha using hP
  refine ⟨∑ α ∈ P.support, a α * ∏ j, x j ^ α j, ?_⟩
  rw [eval_eq', Finset.mul_sum]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_prod, Int.cast_pow]
  apply Finset.sum_congr rfl
  intro α _
  rw [ha α]
  ring

namespace NilpotentLieFiltration

open VectorPolynomial

theorem polynomialRationalGrid_value {σ ι L : Type*} [Fintype σ] [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ) (q : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w q g) (x : σ → ℤ) :
    (b.baseChange ℝ).equivFun
      (F.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g).coord ∈ realDenominatorGrid q := by
  classical
  let P := fun i => coordinate (((b.baseChange ℝ).coord i).toAddMonoidHom)
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
  obtain ⟨a, ha⟩ := hg
  have hP (i : ι) : ∀ α, ∃ z : ℤ, (z : ℝ) = (q : ℝ) * (P i).coeff α := by
    intro α
    refine ⟨a (α, i), ?_⟩
    dsimp only [P]
    rw [coeff_coordinate]
    exact congrFun ha (α, i)
  choose z hz using fun i => polynomial_integer_value_common_denominator (P i) q (hP i) x
  refine ⟨z, funext fun i => ?_⟩
  change (z i : ℝ) = (q : ℝ) * ((b.baseChange ℝ).coord i)
    (eval₂ (fun j => (x j : ℝ)) (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)))
  rw [coordinate_eval₂]
  exact hz i

end NilpotentLieFiltration
end Erdos3

end

end OAI

end


