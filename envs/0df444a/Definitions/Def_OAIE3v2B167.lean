-- Prove2me | Definitions.Def_OAIE3v2B167
-- name    : OAIE3v2B167
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:41:55.364836+00:00
-- url     : https://prove2.me/theorems/3ee47dd8-e49d-46ad-9afb-f276f7ed8df3
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 169 of 311
-- statement:
--   Definitions bundle 169 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B151`, `OAIE3v2B153`, `OAIE3v2B154`, `OAIE3v2B155`, `OAIE3v2B156` of this split.
--
--   Modules: `Estimates/ExtractedInitialState.lean`, `Estimates/FastHorizontalFactorization.lean`, `Estimates/FirstCoefficientDerivativeBounds.lean`, `Estimates/GradedUnitEvaluation.lean`, `Estimates/ReducedRelativeCoefficientBounds.lean`, `Estimates/ReindexedFastCoefficientSection.lean`, `Estimates/StrongRefiltrationReconstruction.lean`, `Geometry/GradedTopCoordinates.lean`, `Geometry/RealFastCoefficientCoordinates.lean`, `Lattices/NativeIntegerAffinePullbackHom.lean`, `Linear/FastCoefficientRelativeKernel.lean`, `Linear/FullFastHorizontalSpanning.lean`, `Linear/LayerOneCoefficientBasis.lean`, `Linear/RealGradedFastCoefficientKernel.lean`, `Polynomial/FirstCoefficientPolynomialDerivative.lean`, `Polynomial/GradedPolynomialSymbolInverse.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B151
import Definitions.Def_OAIE3v2B153
import Definitions.Def_OAIE3v2B154
import Definitions.Def_OAIE3v2B155
import Definitions.Def_OAIE3v2B156

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FirstCoefficientDerivativeBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

include e ω hF

variable [Fintype σ]

theorem realAdaptedLogDerivative_mul (h : σ → ℚ)
    (P Q : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    F.realAdaptedLogDerivative h (P * Q).coord =
      F.realAdaptedLogDerivative h P.coord + dualAdjoint P (F.realAdaptedLogDerivative h Q.coord) := by
  apply F.realAdaptedPolynomialTensor_injective e ω hF (fun _ => 1)
  rw [map_add, F.realAdaptedLogDerivative_tensor, F.realAdaptedLogDerivative_tensor,
    F.realAdaptedAdjoint_tensor, F.realAdaptedLogDerivative_tensor]
  have hh := F.realification.adaptedLogDerivative_mul h
    (F.realAdaptedPolynomialGroupHom (fun _ => 1) P)
    (F.realAdaptedPolynomialGroupHom (fun _ => 1) Q)
  rw [← map_mul] at hh
  exact hh

theorem realFirstCoefficientDirectionMap_mul_rat (h : σ → ℚ)
    (P Q : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    F.realFirstCoefficientDirectionMap (P * Q).coord (fun i => (h i : ℝ)) =
      F.realFirstCoefficientDirectionMap P.coord (fun i => (h i : ℝ)) +
        F.realFirstCoefficientAdjoint (fun _ => 1) P
          (F.realFirstCoefficientDirectionMap Q.coord (fun i => (h i : ℝ))) := by
  rw [F.realFirstCoefficientDirectionMap_rat, F.realFirstCoefficientDirectionMap_rat,
    F.realFirstCoefficientDirectionMap_rat, F.realFirstCoefficientAdjoint_map, ← map_add]
  apply congrArg (F.realFirstCoefficientMap (fun _ => 1))
  exact Subtype.ext (F.realAdaptedLogDerivative_mul e ω hF h P Q)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

include e ω hF

theorem realFirstCoefficientDirectionMap_mul
    (P Q : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) (h : σ → ℝ) :
    F.realFirstCoefficientDirectionMap (P * Q).coord h =
      F.realFirstCoefficientDirectionMap P.coord h +
        F.realFirstCoefficientAdjoint (fun _ => 1) P
          (F.realFirstCoefficientDirectionMap Q.coord h) := by
  have he := realLinearMap_eq_of_rat_directions
    (F.realFirstCoefficientDirectionMap (P * Q).coord)
    (F.realFirstCoefficientDirectionMap P.coord +
      (F.realFirstCoefficientAdjoint (fun _ => 1) P).toLinearMap.comp
        (F.realFirstCoefficientDirectionMap Q.coord))
    (F.realFirstCoefficientDirectionMap_mul_rat e ω hF · P Q)
  exact DFunLike.congr_fun he h

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealFastCoefficientCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem firstCoefficientRealEquiv_coordinates (x : ℝ ⊗[ℚ] F.FirstCoefficientModule w)
    (z : FirstCoefficientIndex w ω) :
    (F.realFirstCoefficientBasis b ω hF w).repr (F.firstCoefficientRealEquiv w x) z =
      ((F.firstCoefficientBasis b ω hF w).baseChange ℝ).repr x z := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul r x =>
    obtain ⟨p, rfl⟩ := F.firstCoefficientMap_surjective w x
    have ht : r ⊗ₜ[ℚ] F.firstCoefficientMap w p =
        (F.firstCoefficientMap w).baseChange ℝ (r ⊗ₜ[ℚ] p) := rfl
    rw [ht, F.firstCoefficientRealEquiv_map]
    let q : F.realShiftedCoefficientSubmodule w 1 :=
      ⟨r ⊗ₜ[ℚ] p.val, Submodule.tmul_mem_baseChange_of_mem r p.property⟩
    change (F.realFirstCoefficientBasis b ω hF w).repr (F.realFirstCoefficientMap w q) z =
      ((F.firstCoefficientBasis b ω hF w).baseChange ℝ).repr (r ⊗ₜ[ℚ] F.firstCoefficientMap w p) z
    rw [F.realFirstCoefficientBasis_repr_map]
    change ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr (r ⊗ₜ[ℚ] p.val)
        ((firstCoefficientSurvivorEquiv w ω).symm z).val.val =
      ((F.firstCoefficientBasis b ω hF w).baseChange ℝ).repr (r ⊗ₜ[ℚ] F.firstCoefficientMap w p) z
    rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul,
      F.adaptedMonomialBasis_repr, F.firstCoefficientBasis_repr_map]
    rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.LayerOneCoefficientBasis
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem firstCoefficientHorizontal_coordinates (w : σ → ℕ)
    (x : F.FirstCoefficientModule w) (i : LayerOneBasisIndex ω) :
    (F.layerOneBasis e ω hF).repr (F.firstCoefficientHorizontal w x) i =
      (F.firstCoefficientBasis e ω hF w).repr x (F.horizontalCoefficientIndex e ω hF w i) := by
  obtain ⟨x, rfl⟩ := F.firstCoefficientMap_surjective w x
  rw [F.firstCoefficientHorizontal_map, F.layerOneBasis_repr_mk,
    F.firstCoefficientBasis_repr_map]
  rfl

theorem realFirstCoefficientHorizontal_coordinates (w : σ → ℕ)
    (x : F.RealFirstCoefficientModule w) (i : LayerOneBasisIndex ω) :
    ((F.layerOneBasis e ω hF).baseChange ℝ).repr (F.realFirstCoefficientHorizontal w x) i =
      (F.realFirstCoefficientBasis e ω hF w).repr x
        (F.horizontalCoefficientIndex e ω hF w i) := by
  obtain ⟨x, rfl⟩ := (F.firstCoefficientRealEquiv w).surjective x
  change ((F.layerOneBasis e ω hF).baseChange ℝ).repr
    ((F.firstCoefficientHorizontal w).baseChange ℝ
      ((F.firstCoefficientRealEquiv w).symm (F.firstCoefficientRealEquiv w x))) i = _
  rw [LinearEquiv.symm_apply_apply, F.firstCoefficientRealEquiv_coordinates]
  exact baseChange_coordinate_eq (F.firstCoefficientBasis e ω hF w)
    (F.layerOneBasis e ω hF) (F.firstCoefficientHorizontal w)
    (F.horizontalCoefficientIndex e ω hF w)
    (F.firstCoefficientHorizontal_coordinates e ω hF w) x i

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedRelativeCoefficientBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realFirstCoefficientAdjoint_basis_coordinate (w : σ → ℕ)
    (g : F.RealAdaptedPolynomialGroup w) (i k : FirstCoefficientIndex w ω)
    (hki : ω k.val.2 ≤ ω i.val.2) :
    (F.realFirstCoefficientBasis b ω hF w).repr
      (F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientBasis b ω hF w i)) k =
      (F.realFirstCoefficientBasis b ω hF w).repr (F.realFirstCoefficientBasis b ω hF w i) k := by
  simp only [F.realFirstCoefficientBasis_apply, F.realFirstCoefficientAdjoint_map,
    F.realFirstCoefficientBasis_repr_map, F.realShiftedMonomialBasis_coe]
  exact (F.adaptedPolynomialFiltration w).dualAdjoint_realBasis_coordinate
    (F.adaptedMonomialBasis b ω hF w) (fun z => ω z.val.2)
    (F.adaptedPolynomialFiltration_layer b ω hF w) g
    ((firstCoefficientSurvivorEquiv w ω).symm i).val.val
    ((firstCoefficientSurvivorEquiv w ω).symm k).val.val hki

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

include e ω hF

theorem realFirstCoefficientHorizontal_adjoint
    (g : F.RealAdaptedPolynomialGroup w) (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientHorizontal w (F.realFirstCoefficientAdjoint w g x) =
      F.realFirstCoefficientHorizontal w x := by
  have he : (F.realFirstCoefficientHorizontal w).comp
      (F.realFirstCoefficientAdjoint w g).toLinearMap = F.realFirstCoefficientHorizontal w := by
    apply (F.realFirstCoefficientBasis e ω hF w).ext
    intro i
    apply ((F.layerOneBasis e ω hF).baseChange ℝ).repr.injective
    ext j
    change ((F.layerOneBasis e ω hF).baseChange ℝ).repr
      (F.realFirstCoefficientHorizontal w
        (F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientBasis e ω hF w i))) j = _
    rw [F.realFirstCoefficientHorizontal_coordinates, F.realFirstCoefficientHorizontal_coordinates]
    apply F.realFirstCoefficientAdjoint_basis_coordinate e ω hF w g i
    have hi := i.property
    have hj := (F.horizontalCoefficientIndex e ω hF w j).property
    change Finsupp.weight w 0 + 1 = ω j.val at hj
    simp only [map_zero, Nat.zero_add] at hj
    change ω j.val ≤ ω i.val.2
    omega
  exact DFunLike.congr_fun he x

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastHorizontalFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem realLayerOneLieSection_coordinate
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) (i : LayerOneBasisIndex ω) :
    (e.baseChange ℝ).repr (F.realLayerOneLieSection e ω hF x) i =
      ((F.layerOneBasis e ω hF).baseChange ℝ).repr x i :=
  realSupportedQuotientSection_coordinate e (F.layer 2) {i | 2 ≤ ω i} (hF 2) x i

theorem realLayerOneLieSection_norm [Fintype ι] (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    ‖(e.baseChange ℝ).equivFun (F.realLayerOneLieSection e ω hF x)‖ =
      ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun x‖ :=
  realSupportedQuotientSection_norm e (F.layer 2) {i | 2 ≤ ω i} (hF 2) x

variable [Fintype σ]

theorem layerOnePolynomialCorrection_slow [Fintype ι]
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (ha : ∀ i, ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (a i)‖ ≤ M / T i) :
    F.PolynomialSlowBound e (fun _ => 1) T M (F.layerOnePolynomialCorrection e ω hF a) := by
  apply F.polynomialSlowBound_linear e T hT hM
  intro i j
  have h := norm_le_pi_norm ((e.baseChange ℝ).equivFun (F.realLayerOneLieSection e ω hF (a i))) j
  rw [F.realLayerOneLieSection_norm] at h
  exact h.trans (ha i)

theorem layerOnePolynomialCorrection_grid (l : ℕ)
    (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (ha : (fun z : σ × LayerOneBasisIndex ω =>
      ((F.layerOneBasis e ω hF).baseChange ℝ).repr (a z.1) z.2) ∈ realDenominatorGrid l) :
    F.PolynomialRationalGrid e (fun _ => 1) l (F.layerOnePolynomialCorrection e ω hF a) := by
  apply F.polynomialRationalGrid_linear
  classical
  obtain ⟨v, hv⟩ := ha
  refine ⟨fun z => if hz : 2 ≤ ω z.2 then 0 else v (z.1, ⟨z.2, hz⟩), ?_⟩
  funext z
  change ((if hz : 2 ≤ ω z.2 then 0 else v (z.1, ⟨z.2, hz⟩) : ℤ) : ℝ) =
    (l : ℝ) * (e.baseChange ℝ).repr (F.realLayerOneLieSection e ω hF (a z.1)) z.2
  by_cases hz : 2 ≤ ω z.2
  · rw [dif_pos hz, F.realLayerOneLieSection_coordinate_zero e ω hF _ _ hz]
    simp only [Int.cast_zero, mul_zero]
  · rw [dif_neg hz, F.realLayerOneLieSection_coordinate e ω hF _ ⟨z.2, hz⟩]
    exact congrFun hv (z.1, ⟨z.2, hz⟩)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem realLayerOneCorrection_slow [Fintype ι]
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (ha : ∀ i, ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (a i)‖ ≤ M / T i) :
    F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T M (F.realLayerOneCorrection e ω hF a).coord := by
  apply (F.realAdaptedCoefficientBound_polynomial_iff e ω hF (fun _ => 1) T hT hM _).mpr
  rw [F.realLayerOneCorrection_realize]
  exact F.layerOnePolynomialCorrection_slow e ω hF T hT hM a ha

theorem realLayerOneCorrection_grid (l : ℕ)
    (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (ha : (fun z : σ × LayerOneBasisIndex ω =>
      ((F.layerOneBasis e ω hF).baseChange ℝ).repr (a z.1) z.2) ∈ realDenominatorGrid l) :
    F.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) l (F.realLayerOneCorrection e ω hF a).coord := by
  apply (F.realAdaptedCoefficientGrid_polynomial_iff e ω hF (fun _ => 1) l _).mpr
  rw [F.realLayerOneCorrection_realize]
  exact F.layerOnePolynomialCorrection_grid e ω hF l a ha

omit [Fintype σ] in
theorem realLayerOneProjection_coordinate (x : ℝ ⊗[ℚ] L) (i : LayerOneBasisIndex ω) :
    ((F.layerOneBasis e ω hF).baseChange ℝ).repr ((F.layer 2).mkQ.baseChange ℝ x) i =
      (e.baseChange ℝ).repr x i :=
  baseChange_coordinate_eq e (F.layerOneBasis e ω hF) (F.layer 2).mkQ Subtype.val
    (F.layerOneBasis_repr_mk e ω hF) x i

theorem realAdaptedLogDerivative_constant_unit [DecidableEq σ] (i : σ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) 0 = 0) :
    coefficients (F.realAdaptedPolynomialMap (fun _ => 1)
      (F.realAdaptedLogDerivative (Pi.single i 1) x)) 0 =
      coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) (Finsupp.single i 1) := by
  have he := congrArg
    (fun q : F.realification.adaptedLieSubalgebra (fun _ : σ => 1) => coefficients q.val 0)
    (F.realAdaptedLogDerivative_tensor (Pi.single i 1) x)
  exact he.trans (F.realification.adaptedLogDerivative_constant_unit i
    (F.realAdaptedPolynomialTensor (fun _ => 1) x) hx)

include e ω hF in
theorem realFirstCoefficientDirectionMap_horizontal_unit [DecidableEq σ] (i : σ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) 0 = 0) :
    F.realFirstCoefficientHorizontal (fun _ => 1)
      (F.realFirstCoefficientDirectionMap x (Pi.single i 1)) =
      (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) (Finsupp.single i 1)) := by
  classical
  have hunit : (Pi.single i (1 : ℝ)) = (fun j => (((Pi.single i (1 : ℚ) : σ → ℚ) j) : ℝ)) := by
    ext j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  apply ((F.layerOneBasis e ω hF).baseChange ℝ).repr.injective
  ext j
  rw [F.realFirstCoefficientHorizontal_coordinates e ω hF, hunit,
    F.realFirstCoefficientDirectionMap_rat, F.realFirstCoefficientBasis_polynomial_coordinate]
  change (e.baseChange ℝ).repr (coefficients (F.realAdaptedPolynomialMap (fun _ => 1)
    (F.realAdaptedLogDerivative (Pi.single i 1) x)) 0) j.val = _
  rw [F.realAdaptedLogDerivative_constant_unit i x hx, F.realLayerOneProjection_coordinate]

theorem realLayerOneCorrection_horizontal_derivative [DecidableEq σ]
    (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2)) (i : σ) :
    F.realFirstCoefficientHorizontal (fun _ => 1)
      (F.realFirstCoefficientDirectionMap (F.realLayerOneCorrection e ω hF a).coord (Pi.single i 1)) =
      a i := by
  have hz : coefficients (F.realAdaptedPolynomialMap (fun _ => 1)
      (F.realLayerOneCorrection e ω hF a).coord) 0 = 0 := by
    rw [F.realLayerOneCorrection_log, coefficients_linearPolynomial_zero]
  rw [F.realFirstCoefficientDirectionMap_horizontal_unit e ω hF i _ hz,
    F.realLayerOneCorrection_log, coefficients_linearPolynomial_single,
    F.realLayerOneLieSection_rightInverse]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem realLayerOneGradedMap_mk (x : ℝ ⊗[ℚ] L) :
    (F.layerOneGradedMap e ω hF).baseChange ℝ ((F.layer 2).mkQ.baseChange ℝ x) =
      (F.gradedPieceProjection e ω hF 1).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      LinearMap.baseChange_tmul, F.layerOneGradedMap_mk]

theorem realLayerOneGradedMap_section (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    (F.layerOneGradedMap e ω hF).baseChange ℝ x =
      (F.gradedPieceProjection e ω hF 1).baseChange ℝ (F.realLayerOneLieSection e ω hF x) := by
  change ((F.gradedPieceProjection e ω hF 1).comp
    (supportedQuotientSection e (F.layer 2) {i | 2 ≤ ω i} (hF 2))).baseChange ℝ x = _
  rw [LinearMap.baseChange_comp]
  rfl

theorem mem_realLayerOneGradedSubmodule (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    x ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ ↔
      (F.layerOneGradedMap e ω hF).baseChange ℝ x ∈ realificationLieSubalgebra U := by
  rw [layerOneGradedSubmodule, realification_comap]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ F.AssociatedGraded)

theorem realLayerOneCorrection_mem_pointwise (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (ha : ∀ i, a i ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ) :
    F.realExtendedSymbolMap (fun _ => 1) (F.realLayerOneCorrection e ω hF a).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF (fun _ => 1) U) := by
  apply (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients e ω hF (fun _ => 1) U _).mpr
  intro α
  rw [← F.realSymbolOfPolynomial_realAdaptedPolynomialMap e ω hF,
    F.realGradedSymbolPolynomial_coefficient_of_polynomial,
    F.realLayerOneCorrection_log]
  by_cases hα : ∃ i, Finsupp.single i 1 = α
  · obtain ⟨i, rfl⟩ := hα
    rw [coefficients_linearPolynomial_single]
    simp only [Finsupp.weight_single, one_smul]
    rw [← F.realLayerOneGradedMap_section]
    exact (F.mem_realLayerOneGradedSubmodule e ω hF U (a i)).mp (ha i)
  · rw [coefficients_linearPolynomial_of_ne _ α (by simpa only [not_exists] using hα), map_zero]
    exact (realificationLieSubalgebra U).zero_mem

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)

omit w in
theorem realLayerOneCorrection_mem_pointwiseSubgroup [Fintype σ]
    (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (ha : ∀ i, a i ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ) :
    F.realLayerOneCorrection e ω hF a ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U := by
  apply (F.mem_realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U _).mpr
  exact F.realLayerOneCorrection_mem_pointwise e ω hF U a ha

end Erdos3.NilpotentLieFiltration

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem realPointwisePolynomialSubgroup_le_fast
    (hU : (F.symbolPointwiseSubalgebra e ω hF w U).map (F.quotientTopSymbolMap w) ≤
      F.reducedSquareFastDiagonalSubalgebra w W) :
    F.realPointwisePolynomialSubgroup e ω hF w U ≤ F.realFastDiagonalSubgroup w W := by
  intro g hg
  have hs := (F.mem_realPointwisePolynomialSubgroup e ω hF w U g).mp hg
  apply (F.mem_realFastDiagonalSubgroup w W g).mpr
  rw [F.adaptedReducedRealSymbolHom_coord]
  have hm : (F.quotientTopSymbolMap w).toLinearMap.baseChange ℝ
      (F.realExtendedSymbolMap w g.coord) ∈
      ((F.symbolPointwiseSubalgebra e ω hF w U).toSubmodule.map
        (F.quotientTopSymbolMap w).toLinearMap).baseChange ℝ := by
    rw [realification_map]
    exact ⟨_, hs, rfl⟩
  exact Submodule.baseChange_mono ℝ hU hm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ F.AssociatedGraded)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
  (hU : (F.symbolPointwiseSubalgebra e ω hF (fun _ : σ => 1) U).map
    (F.quotientTopSymbolMap (fun _ => 1)) ≤ F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) W)

local notation "𝓗" => ℝ ⊗[ℚ] (L ⧸ F.layer 2)
local notation "𝓖" => F.realFastDiagonalSubgroup (fun _ : σ => 1) W
local notation "𝓟" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) W)

noncomputable def realFastLayerOneCorrection (a : σ → 𝓗)
    (ha : ∀ i, a i ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ) : 𝓖 :=
  ⟨F.realLayerOneCorrection e ω hF a,
    F.realPointwisePolynomialSubgroup_le_fast e ω hF (fun _ => 1) U W hU
      (F.realLayerOneCorrection_mem_pointwiseSubgroup e ω hF U a ha)⟩

theorem realFastLayerOneCorrection_horizontal [DecidableEq σ] (a : σ → 𝓗)
    (ha : ∀ i, a i ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ) (i : σ) :
    𝓟 (F.realFastCoefficientDirectionMap W
      (F.realFastLayerOneCorrection e ω hF U W hU a ha).val (Pi.single i 1)) = a i := by
  change F.realFirstCoefficientHorizontal (fun _ => 1)
    (F.realFirstCoefficientDirectionMap (F.realLayerOneCorrection e ω hF a).coord (Pi.single i 1)) = _
  exact F.realLayerOneCorrection_horizontal_derivative e ω hF a i

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FirstCoefficientPolynomialDerivative
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem firstCoefficientGradedPolynomial_horizontal (x : F.FirstCoefficientModule w) :
    coefficients (F.firstCoefficientGradedPolynomial b ω hF w x) 0 =
      F.layerOneGradedMap b ω hF (F.firstCoefficientHorizontal w x) := by
  obtain ⟨p, rfl⟩ := F.firstCoefficientMap_surjective w x
  rw [F.firstCoefficientGradedPolynomial_map, F.adaptedShiftedGradedPolynomial_apply,
    F.shiftedGradedPolynomial_coefficient, F.firstCoefficientHorizontal_map, F.layerOneGradedMap_mk]
  simp only [map_zero, zero_add]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realFirstCoefficientGradedPolynomial_coordinate (x : F.RealFirstCoefficientModule w)
    (z : FirstCoefficientIndex w ω) :
    ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (F.realFirstCoefficientGradedPolynomial b ω hF w x) z.val.1) z.val.2 =
      (F.realFirstCoefficientBasis b ω hF w).repr x z := by
  obtain ⟨y, rfl⟩ := (F.firstCoefficientRealEquiv w).surjective x
  rw [F.firstCoefficientRealEquiv_coordinates]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a x =>
    rw [F.realFirstCoefficientGradedPolynomial_tmul, Basis.baseChange_repr_tmul,
      F.firstCoefficientGradedPolynomial_coordinate, dif_pos z.property,
      Basis.baseChange_repr_tmul]

theorem realFirstCoefficientGradedPolynomial_coordinate_of_ne (x : F.RealFirstCoefficientModule w)
    (α : σ →₀ ℕ) (i : ι) (h : Finsupp.weight w α + 1 ≠ ω i) :
    ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (F.realFirstCoefficientGradedPolynomial b ω hF w x) α) i = 0 := by
  obtain ⟨y, rfl⟩ := (F.firstCoefficientRealEquiv w).surjective x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_zero]
  | tmul a x =>
    rw [F.realFirstCoefficientGradedPolynomial_tmul, Basis.baseChange_repr_tmul,
      F.firstCoefficientGradedPolynomial_coordinate, dif_neg h, zero_smul]

theorem realFirstCoefficientGradedPolynomial_homogeneous (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientGradedPolynomial b ω hF w x ∈
      shiftedGradedPolynomialSubmodule ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w 1 := by
  intro α
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  rw [LinearMap.restrictScalars_apply, basisGradeProjection_repr]
  by_cases hi : ω i = Finsupp.weight w α + 1
  · rw [if_pos hi]
  · rw [if_neg hi, F.realFirstCoefficientGradedPolynomial_coordinate_of_ne b ω hF w x α i (Ne.symm hi)]

theorem realFirstCoefficientGradedPolynomial_bound (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (x : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientSlowBound b ω hF w T M x) :
    CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) T M
      (F.realFirstCoefficientGradedPolynomial b ω hF w x) := by
  intro α i
  by_cases hi : Finsupp.weight w α + 1 = ω i
  · rw [F.realFirstCoefficientGradedPolynomial_coordinate b ω hF w x ⟨(α, i), hi⟩]
    exact hx ⟨(α, i), hi⟩
  · rw [F.realFirstCoefficientGradedPolynomial_coordinate_of_ne b ω hF w x α i hi, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem realFirstCoefficientGradedPolynomial_grid (l : ℕ) (x : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientGrid b ω hF w l x) :
    CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) l
      (F.realFirstCoefficientGradedPolynomial b ω hF w x) := by
  classical
  obtain ⟨v, hv⟩ := hx
  intro α
  refine ⟨fun i => if h : Finsupp.weight w α + 1 = ω i then v ⟨(α, i), h⟩ else 0, ?_⟩
  funext i
  change ((if h : Finsupp.weight w α + 1 = ω i then v ⟨(α, i), h⟩ else 0 : ℤ) : ℝ) =
    (l : ℝ) * ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (F.realFirstCoefficientGradedPolynomial b ω hF w x) α) i
  by_cases hi : Finsupp.weight w α + 1 = ω i
  · rw [dif_pos hi, F.realFirstCoefficientGradedPolynomial_coordinate b ω hF w x ⟨(α, i), hi⟩]
    exact congrFun hv ⟨(α, i), hi⟩
  · rw [dif_neg hi, Int.cast_zero,
      F.realFirstCoefficientGradedPolynomial_coordinate_of_ne b ω hF w x α i hi, mul_zero]

theorem realFirstCoefficientGradedPolynomial_horizontal (x : F.RealFirstCoefficientModule w) :
    coefficients (F.realFirstCoefficientGradedPolynomial b ω hF w x) 0 =
      (F.layerOneGradedMap b ω hF).baseChange ℝ (F.realFirstCoefficientHorizontal w x) := by
  obtain ⟨y, rfl⟩ := (F.firstCoefficientRealEquiv w).surjective x
  change _ = (F.layerOneGradedMap b ω hF).baseChange ℝ
    ((F.firstCoefficientHorizontal w).baseChange ℝ ((F.firstCoefficientRealEquiv w).symm
      (F.firstCoefficientRealEquiv w y)))
  rw [LinearEquiv.symm_apply_apply]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a x =>
    rw [F.realFirstCoefficientGradedPolynomial_tmul, LinearMap.baseChange_tmul,
      LinearMap.baseChange_tmul, F.firstCoefficientGradedPolynomial_horizontal]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realAdaptedGradedPolynomialLie_apply (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realAdaptedGradedPolynomialLie b ω hF w x =
      F.realAdaptedShiftedGradedPolynomial b ω hF w 0 x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a p =>
    rw [F.realAdaptedGradedPolynomialLie_tensor, realificationLieHom_tmul,
      F.realAdaptedShiftedGradedPolynomial_tensor, LinearMap.baseChange_tmul,
      F.adaptedGradedPolynomialLie_apply]
    apply coefficients.injective
    ext α
    rw [coefficients_realificationLieEquiv_tmul, realificationRealLinearEquiv_apply,
      coefficients_realificationLinearEquiv_tmul]

theorem realAdaptedGradedPolynomialLie_symbol (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realAdaptedGradedPolynomialLie b ω hF w x =
      F.realGradedSymbolPolynomial b ω hF w
        (realificationLieHom (F.polynomialSymbolMap w) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a p =>
    rw [F.realAdaptedGradedPolynomialLie_tensor, realificationLieHom_tmul,
      realificationLieHom_tmul]
    apply coefficients.injective
    ext α
    rw [coefficients_realificationLieEquiv_tmul, F.realGradedSymbolPolynomial_coefficient_tmul]
    rw [F.adaptedGradedPolynomialLie_apply, F.adaptedShiftedGradedPolynomial_apply,
      F.shiftedGradedPolynomial_zero]

theorem realAdaptedShiftedGradedPolynomial_lie
    (x y : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
    (hy : y ∈ F.realShiftedCoefficientSubmodule w 1) :
    F.realAdaptedShiftedGradedPolynomial b ω hF w 1 ⁅x, y⁆ =
      ⁅F.realAdaptedGradedPolynomialLie b ω hF w x,
        F.realAdaptedShiftedGradedPolynomial b ω hF w 1 y⁆ := by
  change realificationLieEquiv
      ((F.adaptedShiftedGradedPolynomial b ω hF w 1).baseChange ℝ ⁅x, y⁆) =
    ⁅realificationLieEquiv (realificationLieHom (F.adaptedGradedPolynomialLie b ω hF w) x),
      realificationLieEquiv ((F.adaptedShiftedGradedPolynomial b ω hF w 1).baseChange ℝ y)⁆
  rw [realification_ideal_intertwining (F.shiftedPolynomialIdeal w 1)
    (F.adaptedGradedPolynomialLie b ω hF w) (F.adaptedShiftedGradedPolynomial b ω hF w 1)
    (F.adaptedShiftedGradedPolynomial_lie b ω hF w) x y hy, LieEquiv.map_lie]

theorem realFirstCoefficientGradedPolynomial_map (x : F.realShiftedCoefficientSubmodule w 1) :
    F.realFirstCoefficientGradedPolynomial b ω hF w (F.realFirstCoefficientMap w x) =
      F.realAdaptedShiftedGradedPolynomial b ω hF w 1 x.val := by
  obtain ⟨y, rfl⟩ := (realificationSubmoduleEquiv (F.shiftedPolynomialIdeal w 1).toSubmodule).surjective x
  rw [← F.firstCoefficientRealEquiv_map, F.realFirstCoefficientGradedPolynomial_realEquiv]
  have he : (F.firstCoefficientGradedPolynomial b ω hF w).comp (F.firstCoefficientMap w) =
      (F.adaptedShiftedGradedPolynomial b ω hF w 1).comp
        (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype := by
    apply LinearMap.ext
    intro p
    exact F.firstCoefficientGradedPolynomial_map b ω hF w p
  change realificationRealLinearEquiv
      ((F.firstCoefficientGradedPolynomial b ω hF w).baseChange ℝ
        ((F.firstCoefficientMap w).baseChange ℝ y)) =
    realificationRealLinearEquiv
      ((F.adaptedShiftedGradedPolynomial b ω hF w 1).baseChange ℝ
        ((F.shiftedPolynomialIdeal w 1).toSubmodule.subtype.baseChange ℝ y))
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, he,
    LinearMap.baseChange_comp, LinearMap.comp_apply]

theorem realAdaptedShiftedGradedPolynomial_adjoint
    (g : F.RealAdaptedPolynomialGroup w) (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
    (hx : x ∈ F.realShiftedCoefficientSubmodule w 1) :
    F.realAdaptedShiftedGradedPolynomial b ω hF w 1 (dualAdjoint g x) =
      dualAdjoint (F.realAdaptedGradedPolynomialHom b ω hF w g)
        (F.realAdaptedShiftedGradedPolynomial b ω hF w 1 x) := by
  let I : LieIdeal ℚ (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :=
    { (F.realShiftedCoefficientSubmodule w 1).restrictScalars ℚ with
      lie_mem := fun {a y} hy => F.realShiftedCoefficient_lie_mem w 1 a y hy }
  exact dualLinearLift_adjoint
    (VectorPolynomial.lowerCentralSeries_eq_bot
      F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot)
    I (F.realAdaptedGradedPolynomialLie b ω hF w)
    ((F.realAdaptedShiftedGradedPolynomial b ω hF w 1).restrictScalars ℚ)
    (F.realAdaptedShiftedGradedPolynomial_lie b ω hF w) g x hx

theorem realFirstCoefficientGradedPolynomial_adjoint
    (g : F.RealAdaptedPolynomialGroup w) (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientGradedPolynomial b ω hF w (F.realFirstCoefficientAdjoint w g x) =
      dualAdjoint (F.realAdaptedGradedPolynomialHom b ω hF w g)
        (F.realFirstCoefficientGradedPolynomial b ω hF w x) := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
    ((F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype) x
  change F.realFirstCoefficientGradedPolynomial b ω hF w
      (F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientMap w y)) =
    dualAdjoint (F.realAdaptedGradedPolynomialHom b ω hF w g)
      (F.realFirstCoefficientGradedPolynomial b ω hF w (F.realFirstCoefficientMap w y))
  rw [F.realFirstCoefficientAdjoint_map, F.realFirstCoefficientGradedPolynomial_map,
    F.realFirstCoefficientGradedPolynomial_map]
  exact F.realAdaptedShiftedGradedPolynomial_adjoint b ω hF w g y.val y.property

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realAdaptedShiftedGradedPolynomial_directionalDerivative (h : σ → ℚ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedShiftedGradedPolynomial b ω hF (fun _ : σ => 1) 1
        (F.realAdaptedDirectionalDerivative h x) =
      directionalDerivative h (F.realAdaptedGradedPolynomialLie b ω hF (fun _ : σ => 1) x) := by
  rw [F.realAdaptedGradedPolynomialLie_apply]
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a p =>
    have hd : F.realAdaptedDirectionalDerivative h (a ⊗ₜ[ℚ] p) =
        a ⊗ₜ[ℚ] F.adaptedDirectionalDerivative h p := rfl
    rw [hd, F.realAdaptedShiftedGradedPolynomial_tensor, F.realAdaptedShiftedGradedPolynomial_tensor,
      LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
    rw [realificationRealLinearEquiv_apply, coefficients_realificationLinearEquiv_tmul,
      F.adaptedShiftedGradedPolynomial_directionalDerivative b ω hF h 0]
    rw [coefficients_directionalDerivative, coefficients_directionalDerivative]
    simp only [realificationRealLinearEquiv_apply, coefficients_realificationLinearEquiv_tmul,
      TensorProduct.tmul_sum, TensorProduct.tmul_smul]

variable [DecidableEq σ]

theorem realAdaptedGradedPolynomial_firstJet (i : σ)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    dualLinearLift (F.realAdaptedGradedPolynomialLie b ω hF (fun _ : σ => 1))
        ((F.realAdaptedShiftedGradedPolynomial b ω hF (fun _ : σ => 1) 1).restrictScalars ℚ)
        (F.realAdaptedPolynomialJet (Pi.single i 1) g.coord).coord =
      (formalPolynomialJetHom i (F.realAdaptedGradedPolynomialHom b ω hF (fun _ : σ => 1) g)).coord := by
  classical
  apply dual_ext
  · rw [dualLinearLift_base, F.realAdaptedPolynomialJet_base, formalPolynomialJet_base]
    rfl
  · rw [dualLinearLift_tangent, F.realAdaptedPolynomialJet_tangent, formalPolynomialJet_tangent,
      LinearMap.restrictScalars_apply, F.realAdaptedShiftedGradedPolynomial_directionalDerivative,
      directionalDerivative_single]
    rfl

theorem realAdaptedGradedPolynomial_logDerivative (i : σ)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    F.realAdaptedShiftedGradedPolynomial b ω hF (fun _ : σ => 1) 1
        (F.realAdaptedLogDerivative (Pi.single i 1) g.coord) =
      formalLogDerivative i (F.realAdaptedGradedPolynomialHom b ω hF (fun _ : σ => 1) g) := by
  classical
  let I : LieIdeal ℚ (ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :=
    { (F.realShiftedCoefficientSubmodule (fun _ : σ => 1) 1).restrictScalars ℚ with
      lie_mem := fun {a y} hy => F.realShiftedCoefficient_lie_mem (fun _ : σ => 1) 1 a y hy }
  apply dualLinearLift_logDerivative_eq
    (VectorPolynomial.lowerCentralSeries_eq_bot
      F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot)
    I (F.realAdaptedGradedPolynomialLie b ω hF (fun _ : σ => 1))
    ((F.realAdaptedShiftedGradedPolynomial b ω hF (fun _ : σ => 1) 1).restrictScalars ℚ)
    (F.realAdaptedShiftedGradedPolynomial_lie b ω hF (fun _ : σ => 1))
    (F.realAdaptedPolynomialJet (Pi.single i 1) g.coord) _
    (formalPolynomialJetHom i (F.realAdaptedGradedPolynomialHom b ω hF (fun _ : σ => 1) g))
  · exact F.realAdaptedGradedPolynomial_firstJet b ω hF i g
  · rw [F.realAdaptedPolynomialJet_tangent]
    exact F.realAdaptedDirectionalDerivative_mem_first (Pi.single i 1) g.coord

theorem realFirstCoefficientGradedPolynomial_direction (i : σ)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    F.realFirstCoefficientGradedPolynomial b ω hF (fun _ : σ => 1)
        (F.realFirstCoefficientDirectionMap g.coord (Pi.single i 1)) =
      formalLogDerivative i (F.realAdaptedGradedPolynomialHom b ω hF (fun _ : σ => 1) g) := by
  classical
  have he : (Pi.single i (1 : ℝ) : σ → ℝ) =
      (fun j => (((Pi.single i (1 : ℚ) : σ → ℚ) j) : ℝ)) := by
    ext j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  rw [he, F.realFirstCoefficientDirectionMap_rat, F.realFirstCoefficientGradedPolynomial_map]
  exact F.realAdaptedGradedPolynomial_logDerivative b ω hF i g

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GradedUnitEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))

theorem firstCoefficientGradedPolynomial_normalized (p : F.normalizedRelativeSubmodule w) :
    F.firstCoefficientGradedPolynomial e ω hF w (F.normalizedFirstCoefficientMap w p) =
      F.shiftedGradedPolynomial e ω hF w 1 p.val.val := by
  change F.firstCoefficientGradedPolynomial e ω hF w
    (F.firstCoefficientMap w ⟨p.val, p.property.1⟩) = _
  rw [F.firstCoefficientGradedPolynomial_map, F.adaptedShiftedGradedPolynomial_apply]

theorem reducedSquareGradedSnd_coefficient
    (x : F.squareFiltration.quotientTop.PolynomialSymbol w) (α : σ →₀ ℕ) :
    F.reducedSquareGradedSndMap
        (coefficients (F.squareFiltration.quotientTop.gradedSymbolPolynomial
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w x) α) =
      coefficients (F.quotientTop.gradedSymbolPolynomial (F.quotientTopBasis e ω hF)
        (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w (F.reducedSquareSndSymbolMap w x)) α := by
  unfold reducedSquareGradedSndMap reducedSquareSndSymbolMap
  rw [F.squareFiltration.quotientTop.gradedSymbolPolynomial_filteredMap_coefficient
    F.quotientTop (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem w x α]

theorem reducedSquareSnd_homogeneousSymbolLift (α : σ →₀ ℕ)
    (x : F.squareFiltration.quotientTop.AssociatedGraded) :
    F.reducedSquareSndSymbolMap w
        (F.squareFiltration.quotientTop.homogeneousSymbolLift
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w α x) =
      F.quotientTop.homogeneousSymbolLift (F.quotientTopBasis e ω hF)
        (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w α (F.reducedSquareGradedSndMap x) := by
  exact F.squareFiltration.quotientTop.homogeneousSymbolLift_filteredMap
    F.quotientTop (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem w α x

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GradedTopCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωQ" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))
local notation "bQ" => F.quotientTop.associatedGradedBasis
  (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)

theorem quotientTopGradedMap_coordinate (x : F.AssociatedGraded) (i : QuotientTopBasisIndex s ω) :
    (bQ).repr (F.quotientTopGradedMap x) i = (F.associatedGradedBasis e ω hF).repr x i.val := by
  classical
  have he : ((bQ).coord i).comp F.quotientTopGradedMap.toLinearMap =
      (F.associatedGradedBasis e ω hF).coord i.val := by
    apply (F.associatedGradedBasis e ω hF).ext
    intro j
    change (bQ).repr (F.associatedGradedMap F.quotientTop (lieQuotientMap (F.layerIdeal (s + 1)))
      (fun _ _ hx => F.quotientLie_mem _ le_rfl hx) (F.associatedGradedBasis e ω hF j)) i =
      (F.associatedGradedBasis e ω hF).repr (F.associatedGradedBasis e ω hF j) i.val
    rw [F.associatedGradedMap_basis_repr F.quotientTop e ω hF
      (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
      (lieQuotientMap (F.layerIdeal (s + 1))) (fun _ _ hx => F.quotientLie_mem _ le_rfl hx),
      F.quotientTopBasis_repr_mk, Basis.repr_self, Basis.repr_self]
    by_cases hj : j = i.val <;> simp [hj]
  exact DFunLike.congr_fun he x

theorem quotientTopGradedSection_coordinate (x : F.quotientTop.AssociatedGraded)
    (i : QuotientTopBasisIndex s ω) :
    (F.associatedGradedBasis e ω hF).repr (F.quotientTopGradedSection e ω hF x) i.val = (bQ).repr x i := by
  classical
  have he : ((F.associatedGradedBasis e ω hF).coord i.val).comp (F.quotientTopGradedSection e ω hF) =
      (bQ).coord i := by
    apply (bQ).ext
    intro j
    change (F.associatedGradedBasis e ω hF).repr (F.quotientTopGradedSection e ω hF ((bQ) j)) i.val =
      (bQ).repr ((bQ) j) i
    rw [F.quotientTopGradedSection_basis, Basis.repr_self, Basis.repr_self]
    simp [Finsupp.single_apply, Subtype.ext_iff]
  exact DFunLike.congr_fun he x

theorem quotientTopGradedSection_coordinate_zero (x : F.quotientTop.AssociatedGraded)
    (i : ι) (hi : s + 1 ≤ ω i) :
    (F.associatedGradedBasis e ω hF).repr (F.quotientTopGradedSection e ω hF x) i = 0 := by
  classical
  have he : ((F.associatedGradedBasis e ω hF).coord i).comp (F.quotientTopGradedSection e ω hF) = 0 := by
    apply (bQ).ext
    intro j
    change (F.associatedGradedBasis e ω hF).repr (F.quotientTopGradedSection e ω hF ((bQ) j)) i = 0
    rw [F.quotientTopGradedSection_basis, Basis.repr_self]
    apply Finsupp.single_eq_of_ne
    exact fun hij => j.property (hij ▸ hi)
  exact DFunLike.congr_fun he x

theorem quotientTopGradedSection_rightInverse (x : F.quotientTop.AssociatedGraded) :
    F.quotientTopGradedMap (F.quotientTopGradedSection e ω hF x) = x := by
  apply (bQ).repr.injective
  ext i
  rw [F.quotientTopGradedMap_coordinate, F.quotientTopGradedSection_coordinate]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FullFastHorizontalSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def fullFastDiagonalGenerators
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) :
    κ ⊕ TopGradedBasisIndex s ω → F.AssociatedGraded :=
  Sum.elim (fun j => F.quotientTopGradedSection e ω hF (F.reducedSquareGradedSndMap (v j)))
    (fun i => F.associatedGradedBasis e ω hF i.val)

theorem fullFastDiagonalGenerators_card [Fintype κ] [Fintype ι] :
    Fintype.card (κ ⊕ TopGradedBasisIndex s ω) ≤ Fintype.card κ + Fintype.card ι := by
  rw [Fintype.card_sum]
  exact Nat.add_le_add_left (Fintype.card_le_of_injective Subtype.val Subtype.val_injective) _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct Matrix

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def fullFastHorizontalCoordinates [Fintype ι]
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    Submodule ℝ (LayerOneBasisIndex ω → ℝ) :=
  ((F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W)).baseChange ℝ).map
    ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun.toLinearMap

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FastCoefficientRelativeKernel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem realFirstCoefficientFastSubmodule_relative :
    F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U) =
      F.realFirstCoefficientFastSubmodule w hw U.toSubmodule := by
  unfold realFirstCoefficientFastSubmodule
  rw [F.firstCoefficientFastSubmodule_relative]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReindexedFastCoefficientSection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realFirstCoefficientHorizontal_grid (l : ℕ) (x : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientGrid e ω hF w l x) :
    ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun
      (F.realFirstCoefficientHorizontal w x) ∈ realDenominatorGrid l := by
  obtain ⟨v, hv⟩ := hx
  refine ⟨fun i => v (F.horizontalCoefficientIndex e ω hF w i), ?_⟩
  funext i
  change (v (F.horizontalCoefficientIndex e ω hF w i) : ℝ) =
    (l : ℝ) * ((F.layerOneBasis e ω hF).baseChange ℝ).repr
      (F.realFirstCoefficientHorizontal w x) i
  rw [F.realFirstCoefficientHorizontal_coordinates]
  exact congrFun hv _

theorem realFirstCoefficientHorizontal_bound (T : σ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (x : F.RealFirstCoefficientModule w) (hx : F.FirstCoefficientSlowBound e ω hF w T M x) :
    ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun
      (F.realFirstCoefficientHorizontal w x)‖ ≤ M := by
  apply (pi_norm_le_iff_of_nonneg hM).mpr
  intro i
  rw [Real.norm_eq_abs, Basis.equivFun_apply, F.realFirstCoefficientHorizontal_coordinates]
  simpa only [horizontalCoefficientIndex, monomialScale_zero, div_one] using
    hx (F.horizontalCoefficientIndex e ω hF w i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι ν L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ν] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

local notation "E" => F.RealFirstCoefficientModule w
local notation "J" => F.realFirstCoefficientFastSubmodule w hw U

noncomputable def realFastCoefficientRepresentative (b : Basis ν ℝ (E ⧸ J))
    (sectionMap : (ν → ℝ) →ₗ[ℝ] E) : (E ⧸ J) →ₗ[ℝ] E :=
  sectionMap.comp b.equivFun.toLinearMap

theorem realFastCoefficientRepresentative_mk (b : Basis ν ℝ (E ⧸ J))
    (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y) (x : E ⧸ J) :
    (J).mkQ (F.realFastCoefficientRepresentative w hw U b sectionMap x) = x := by
  change (J).mkQ (sectionMap (b.equivFun x)) = x
  rw [hsection, LinearEquiv.symm_apply_apply]

theorem realFastCoefficientRepresentative_horizontal (b : Basis ν ℝ (E ⧸ J))
    (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y) (x : E ⧸ J) :
    F.realFirstCoefficientHorizontal w (F.realFastCoefficientRepresentative w hw U b sectionMap x) =
      F.realFastCoefficientHorizontal w hw U x := by
  have h := congrArg (F.realFastCoefficientHorizontal w hw U)
    (F.realFastCoefficientRepresentative_mk w hw U b sectionMap hsection x)
  exact h

theorem realFastCoefficientRepresentative_bound
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (b : Basis ν ℝ (E ⧸ J)) (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (rows : ν → FirstCoefficientIndex w ω) (T : σ → ℝ) {C M : ℝ}
    (hbound : ∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
      F.FirstCoefficientSlowBound e ω hF w T (C * M) (sectionMap y))
    (x : E ⧸ J) (hx : ∀ i, |b.equivFun x i| ≤ M / monomialScale T (rows i).val.1) :
    F.FirstCoefficientSlowBound e ω hF w T (C * M)
      (F.realFastCoefficientRepresentative w hw U b sectionMap x) := hbound (b.equivFun x) hx

theorem realFastCoefficientRepresentative_grid
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (b : Basis ν ℝ (E ⧸ J)) (sectionMap : (ν → ℝ) →ₗ[ℝ] E) (l m : ℕ)
    (hgrid : ∀ y, y ∈ realDenominatorGrid l → F.FirstCoefficientGrid e ω hF w m (sectionMap y))
    (x : E ⧸ J) (hx : b.equivFun x ∈ realDenominatorGrid l) :
    F.FirstCoefficientGrid e ω hF w m
      (F.realFastCoefficientRepresentative w hw U b sectionMap x) := hgrid (b.equivFun x) hx

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι ν L : Type*} [Fintype ι] [Fintype ν] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

local notation "E" => F.RealFirstCoefficientModule w
local notation "J" => F.realFirstCoefficientFastSubmodule w hw U
local notation "Hq" => F.realFastCoefficientHorizontal w hw U
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))

theorem realFastCoefficientHorizontal_section_norm_bound
    (b : Basis ν ℝ (E ⧸ J)) (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (rows : ν → FirstCoefficientIndex w ω) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ M, 0 ≤ M → ∀ y : ν → ℝ,
      (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF w T (C * M) (sectionMap y))
    (x : E ⧸ J) :
    ‖cH (Hq x)‖ ≤ C * ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1) x‖ := by
  let N := basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1)
  let x' := F.realFastCoefficientRepresentative w hw U b sectionMap x
  have hcoords : ∀ i, |b.equivFun x i| ≤ ‖N x‖ / monomialScale T (rows i).val.1 :=
    (basisWeightedCoordinates_norm_le_iff b _ (fun i => monomialScale_pos T hT _)
      (norm_nonneg _) x).mp le_rfl
  have hx' : F.FirstCoefficientSlowBound e ω hF w T (C * ‖N x‖) x' :=
    F.realFastCoefficientRepresentative_bound w hw U e ω hF b sectionMap rows T
      (hbound ‖N x‖ (norm_nonneg _)) x hcoords
  have hhorizontal := F.realFastCoefficientRepresentative_horizontal w hw U b sectionMap hsection x
  calc
    ‖cH (Hq x)‖ = ‖cH (F.realFirstCoefficientHorizontal w x')‖ :=
      (congrArg (fun y => ‖cH y‖) hhorizontal).symm
    _ ≤ C * ‖N x‖ := F.realFirstCoefficientHorizontal_bound e ω hF w T
      (mul_nonneg hC (norm_nonneg _)) x' hx'

theorem realFastCoefficientHorizontal_section_grid
    (b : Basis ν ℝ (E ⧸ J)) (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (l m : ℕ)
    (hgrid : ∀ y : ν → ℝ, y ∈ realDenominatorGrid l →
      F.FirstCoefficientGrid e ω hF w m (sectionMap y))
    (x : E ⧸ J) (hx : b.equivFun x ∈ realDenominatorGrid l) :
    cH (Hq x) ∈ realDenominatorGrid m := by
  have hx' := F.realFastCoefficientRepresentative_grid w hw U e ω hF b sectionMap l m hgrid x hx
  have hhorizontal := F.realFastCoefficientRepresentative_horizontal w hw U b sectionMap hsection x
  have hg := F.realFirstCoefficientHorizontal_grid e ω hF w m _ hx'
  exact (congrArg (fun y => cH y ∈ realDenominatorGrid m) hhorizontal).mp hg

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.GradedPolynomialSymbolInverse
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

section General

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realAdaptedShiftedGradedPolynomial_coefficient (k : ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.realAdaptedShiftedGradedPolynomial e ω hF w k x) α =
      (F.gradedPieceProjection e ω hF (Finsupp.weight w α + k)).baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap w x) α) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a x =>
    rw [F.realAdaptedShiftedGradedPolynomial_tensor, LinearMap.baseChange_tmul,
      realificationRealLinearEquiv_apply, coefficients_realificationLinearEquiv_tmul,
      F.adaptedShiftedGradedPolynomial_apply, F.shiftedGradedPolynomial_coefficient,
      F.realAdaptedPolynomialMap_coefficient_tmul, LinearMap.baseChange_tmul]

theorem realAdaptedGradedPolynomialLie_coefficient
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.realAdaptedGradedPolynomialLie e ω hF w x) α =
      (F.gradedPieceProjection e ω hF (Finsupp.weight w α)).baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap w x) α) := by
  rw [F.realAdaptedGradedPolynomialLie_apply, F.realAdaptedShiftedGradedPolynomial_coefficient]
  simp only [Nat.add_zero]

theorem realAdaptedGradedPolynomialLie_graded (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realAdaptedGradedPolynomialLie e ω hF w x ∈
      gradedPolynomialSubmodule ((F.associatedGradedBasis e ω hF).baseChange ℝ) ω w := by
  rw [F.realAdaptedGradedPolynomialLie_symbol]
  exact F.realGradedSymbolPolynomial_mem_gradedPolynomialSubmodule e ω hF w _

theorem realAdaptedGradedPolynomialLie_constant (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    coefficients (F.realAdaptedGradedPolynomialLie e ω hF w x) 0 = 0 := by
  rw [F.realAdaptedGradedPolynomialLie_symbol]
  apply ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr.injective
  ext i
  have hi : Finsupp.weight w (0 : σ →₀ ℕ) ≠ ω i := by
    rw [map_zero]
    exact Nat.ne_of_lt (F.adaptedBasis_weight_pos e ω hF i)
  simpa only [map_zero, Finsupp.zero_apply] using
    F.realGradedSymbolPolynomial_coordinate_of_ne e ω hF w
      (realificationLieHom (F.polynomialSymbolMap w) x) 0 i hi

omit w in
theorem realAdaptedGradedPolynomialLie_linear
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) (i : σ) :
    coefficients (F.realAdaptedGradedPolynomialLie e ω hF (fun _ : σ => 1) x)
        (Finsupp.single i 1) =
      (F.layerOneGradedMap e ω hF).baseChange ℝ ((F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) x) (Finsupp.single i 1))) := by
  rw [F.realAdaptedGradedPolynomialLie_coefficient, F.realLayerOneGradedMap_mk]
  simp only [Finsupp.weight_single, one_smul]

omit w in
theorem realAdaptedGradedPolynomialLie_horizontal_mem
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (K : Submodule ℝ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (hK : ∀ i, (F.layerOneGradedMap e ω hF).baseChange ℝ ((F.layer 2).mkQ.baseChange ℝ
      (coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) x) (Finsupp.single i 1))) ∈ K)
    (α : σ →₀ ℕ) :
    basisGradeProjection ((F.associatedGradedBasis e ω hF).baseChange ℝ) ω 1
      (coefficients (F.realAdaptedGradedPolynomialLie e ω hF (fun _ : σ => 1) x) α) ∈ K := by
  have hgraded := F.realAdaptedGradedPolynomialLie_graded e ω hF (fun _ : σ => 1) x
  by_cases hα : Finsupp.weight (fun _ : σ => (1 : ℕ)) α = 1
  · obtain hz | ⟨i, rfl⟩ := exponent_of_weight_le_one α hα.le
    · subst α
      simp only [map_zero] at hα
      omega
    · have hg := hgraded (Finsupp.single i 1)
      simp only [Finsupp.weight_single, one_smul, LinearMap.restrictScalars_apply] at hg
      rw [hg, F.realAdaptedGradedPolynomialLie_linear]
      exact hK i
  · have hz := gradedPolynomialSubmodule_projection_homogeneous
      ((F.associatedGradedBasis e ω hF).baseChange ℝ) ω (fun _ : σ => 1) _ hgraded 1 α hα
    simp only [coefficients_map, LinearMap.restrictScalars_apply] at hz
    rw [hz]
    exact K.zero_mem

end General

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealGradedFastCoefficientKernel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

variable (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

noncomputable def firstCoefficientGradedQuotientMap :
    F.FirstCoefficientModule w →ₗ[ℚ] VectorPolynomial σ ℚ
      (F.AssociatedGraded ⧸ F.fullFastGradedRelative e ω hF W) :=
  (VectorPolynomial.map (F.fullFastGradedRelative e ω hF W).mkQ).comp
    (F.firstCoefficientGradedPolynomial e ω hF w)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem realFirstCoefficientGradedQuotient_coefficient (x : ℝ ⊗[ℚ] F.FirstCoefficientModule w)
    (α : σ →₀ ℕ) :
    coefficients (realificationLinearEquiv
      ((F.firstCoefficientGradedQuotientMap e ω hF w W).baseChange ℝ x)) α =
        (F.fullFastGradedRelative e ω hF W).mkQ.baseChange ℝ
          (coefficients (F.realFirstCoefficientGradedPolynomial e ω hF w
            (F.firstCoefficientRealEquiv w x)) α) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, coefficients_realificationLinearEquiv_tmul,
      F.realFirstCoefficientGradedPolynomial_tmul, LinearMap.baseChange_tmul]
    change a ⊗ₜ[ℚ] coefficients (VectorPolynomial.map (F.fullFastGradedRelative e ω hF W).mkQ
      (F.firstCoefficientGradedPolynomial e ω hF w x)) α = _
    rw [coefficients_map]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ExtractedInitialState
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)

include hw

theorem realFirstCoefficientGradedPolynomial_initial_remainder
    (x : F.RealFirstCoefficientModule w) (α : σ →₀ ℕ) :
    coefficients (F.realFirstCoefficientGradedPolynomial e ω hF w x -
      monomial 0 ((F.layerOneGradedMap e ω hF).baseChange ℝ
        (F.realFirstCoefficientHorizontal w x))) α ∈
      (F.associatedGradedFiltration.realLayer 2).toSubmodule := by
  classical
  rw [← F.realFirstCoefficientGradedPolynomial_horizontal]
  by_cases hα : α = 0
  · subst α
    simp only [map_sub, Finsupp.sub_apply, coefficients_monomial,
      Finsupp.single_eq_same, sub_self]
    exact Submodule.zero_mem _
  · rw [map_sub, Finsupp.sub_apply, coefficients_monomial,
      Finsupp.single_eq_of_ne hα, sub_zero]
    apply (F.associatedGradedFiltration.real_mem_layer_iff_basis_coordinates
      (F.associatedGradedBasis e ω hF) ω (F.associatedGradedFiltration_layer e ω hF) 2 _).mpr
    intro i hi
    have hpos := positive_weight_of_ne_zero w hw hα
    exact F.realFirstCoefficientGradedPolynomial_coordinate_of_ne e ω hF w x α i (by omega)

theorem realFirstCoefficientGradedPolynomial_mem_second
    (x : F.RealFirstCoefficientModule w) (hx : F.realFirstCoefficientHorizontal w x = 0)
    (α : σ →₀ ℕ) :
    coefficients (F.realFirstCoefficientGradedPolynomial e ω hF w x) α ∈
      (F.associatedGradedFiltration.realLayer 2).toSubmodule := by
  have h := F.realFirstCoefficientGradedPolynomial_initial_remainder e ω hF w hw x α
  simpa only [hx, map_zero, monomial, TensorProduct.tmul_zero, sub_zero] using h

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerAffinePullbackHom
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

namespace NativeIntegerVectorEquivalence

theorem coordinatePullback {σ τ J K : Type*} [Fintype τ] [Fintype J] [Fintype K]
    {s : ℕ} {p : ℝ} {f : J → (σ → ℤ) → ℂ} {g : K → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p f g) (a : σ → τ) :
    NativeIntegerVectorEquivalence s p (fun j x => f j (fun i => x (a i)))
      (fun k x => g k (fun i => x (a i))) :=
  E.linearPullbackHom (fun i => ⟨⟨fun x => x (a i), rfl⟩, fun _ _ => rfl⟩)

end NativeIntegerVectorEquivalence

end Erdos3

end

end OAI
end


