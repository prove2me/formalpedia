-- Prove2me | Definitions.Def_OAIE3v2B154
-- name    : OAIE3v2B154
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:29:15.704423+00:00
-- url     : https://prove2.me/theorems/059abd4a-9bc0-4d81-aeb0-8101f38c6945
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 156 of 311
-- statement:
--   Definitions bundle 156 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B141`, `OAIE3v2B143`, `OAIE3v2B144`, `OAIE3v2B145` of this split.
--
--   Modules: `Estimates/FastCoefficientImage.lean`, `Estimates/FastHorizontalFactorization.lean`, `Estimates/FirstCoefficientDerivativeBounds.lean`, `Estimates/FirstCoefficientDimension.lean`, `Estimates/ProjectedPointwiseCoefficient.lean`, `Estimates/ReducedNativeFactorization.lean`, `Estimates/ReducedProjectedComparison.lean`, `Estimates/ReducedRelativeCoefficientBounds.lean`, `Estimates/ReducedSymbolDimensions.lean`, `Estimates/ReindexedFastCoefficientSection.lean`, `Estimates/SquareSymbolRelative.lean`, `Linear/FastCoefficientRelativeKernel.lean`, `Linear/LayerOneCoefficientBasis.lean`, `Linear/RealReducedFastKernel.lean`, `Linear/ReducedProjectionBounds.lean`, `Linear/ReducedSquareFastKernel.lean`, `Polynomial/FirstCoefficientPolynomialDerivative.lean`, `Polynomial/RealReducedSquarePolynomial.lean`, `Polynomial/RealSquarePolynomialFactors.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B141
import Definitions.Def_OAIE3v2B143
import Definitions.Def_OAIE3v2B144
import Definitions.Def_OAIE3v2B145

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquareSymbolRelative
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem relativeSquareSymbol_lie_eq_zero (p q : F.normalizedRelativeSubmodule w) :
    ⁅F.relativeSquareSymbolMap w hw p, F.relativeSquareSymbolMap w hw q⁆ = 0 := by
  have hpq : ⁅p.val, q.val⁆ ∈ F.shiftedPolynomialIdeal w 2 :=
    F.shiftedPolynomialIdeal_lie_mem w (i := 1) (j := 1) p.property.1 q.property.1
  have hpq0 : coefficients ⁅p.val, q.val⁆.val 0 ∈ F.layer 2 := by
    have hh := hpq 0
    change coefficients ⁅p.val, q.val⁆.val 0 ∈ F.layer (Finsupp.weight w 0 + 2) at hh
    rw [map_zero, Nat.zero_add] at hh
    exact hh
  let r : F.normalizedRelativeSubmodule w :=
    ⟨⁅p.val, q.val⁆, F.shiftedPolynomialIdeal_antitone w (by decide : 1 ≤ 2) hpq, hpq0⟩
  have he : ⁅F.relativeSquareLift w hw p, F.relativeSquareLift w hw q⁆ =
      F.relativeSquareLift w hw r := by
    apply F.square_polynomial_ext w
    · rw [LieHom.map_lie, F.squareFstPolynomialMap_relative, F.squareFstPolynomialMap_relative,
        F.squareFstPolynomialMap_relative]
    · rw [LieHom.map_lie, F.squareSndPolynomialMap_relative, F.squareSndPolynomialMap_relative,
        F.squareSndPolynomialMap_relative, lie_zero]
  change ⁅F.squareFiltration.polynomialSymbolMap w (F.relativeSquareLift w hw p),
    F.squareFiltration.polynomialSymbolMap w (F.relativeSquareLift w hw q)⁆ = 0
  rw [← LieHom.map_lie, he]
  exact (F.relativeSquareSymbolMap_eq_zero_iff w hw r).mpr hpq

include hw in
theorem squareSndSymbolKernel_lie_eq_zero {x y : F.squareFiltration.PolynomialSymbol w}
    (hx : F.squareSndSymbolMap w x = 0) (hy : F.squareSndSymbolMap w y = 0) : ⁅x, y⁆ = 0 := by
  have hx' : x ∈ LinearMap.range (F.relativeSquareSymbolMap w hw) := by
    rw [F.relativeSquareSymbolMap_range w hw]
    exact hx
  have hy' : y ∈ LinearMap.range (F.relativeSquareSymbolMap w hw) := by
    rw [F.relativeSquareSymbolMap_range w hw]
    exact hy
  obtain ⟨p, rfl⟩ := hx'
  obtain ⟨q, rfl⟩ := hy'
  exact F.relativeSquareSymbol_lie_eq_zero w hw p q

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastCoefficientImage
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem firstCoefficientBasis_repr_map (w : σ → ℕ) (p : F.shiftedPolynomialIdeal w 1)
    (z : FirstCoefficientIndex w ω) :
    (F.firstCoefficientBasis b ω hF w).repr (F.firstCoefficientMap w p) z =
      b.repr (coefficients (p.val : VectorPolynomial σ ℚ L) z.val.1) z.val.2 := by
  rw [firstCoefficientBasis, Basis.repr_reindex_apply]
  change (supportedQuotientBasis _ _ _ _).repr
    (((F.shiftedPolynomialIdeal w 2).toSubmodule.comap
      (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype).mkQ p) _ = _
  rw [supportedQuotientBasis_repr_mk, F.shiftedMonomialBasis_repr]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem reducedSquareSndSymbolKernel_lie_eq_zero (hw : ∀ i, 0 < w i)
    {x y : F.squareFiltration.quotientTop.PolynomialSymbol w}
    (hx : F.reducedSquareSndSymbolMap w x = 0) (hy : F.reducedSquareSndSymbolMap w y = 0) :
    ⁅x, y⁆ = 0 := by
  obtain ⟨a, ha, rfl⟩ := F.reducedSquareSndSymbolKernel_lift w hx
  obtain ⟨b, hb, rfl⟩ := F.reducedSquareSndSymbolKernel_lift w hy
  rw [← LieHom.map_lie, F.squareSndSymbolKernel_lie_eq_zero w hw ha hb, map_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

noncomputable def firstCoefficientRelativeRangeEquiv :
    LinearMap.range (F.normalizedFirstCoefficientMap w) ≃ₗ[ℚ]
      LinearMap.range (F.reducedRelativeSquareSymbolMap w hw) :=
  commonKernelRangeEquiv (F.normalizedFirstCoefficientMap w) (F.reducedRelativeSquareSymbolMap w hw)
    (F.normalizedFirstCoefficientMap_ker w hw)

theorem firstCoefficientRelativeRangeEquiv_apply (p : F.normalizedRelativeSubmodule w) :
    (F.firstCoefficientRelativeRangeEquiv w hw ⟨F.normalizedFirstCoefficientMap w p, ⟨p, rfl⟩⟩ :
      F.squareFiltration.quotientTop.PolynomialSymbol w) = F.reducedRelativeSquareSymbolMap w hw p :=
  commonKernelRangeEquiv_apply _ _ _ p

noncomputable def firstCoefficientRelativeEquiv :
    LinearMap.ker (F.firstCoefficientHorizontal w) ≃ₗ[ℚ]
      (F.reducedSquareSndSymbolMap w).ker :=
  (LinearEquiv.ofEq _ _ (F.normalizedFirstCoefficientMap_range w).symm).trans
    ((F.firstCoefficientRelativeRangeEquiv w hw).trans
      (LinearEquiv.ofEq _ _ (F.reducedRelativeSquareSymbolMap_range w hw)))

theorem firstCoefficientRelativeEquiv_apply (p : F.normalizedRelativeSubmodule w)
    (hp : F.normalizedFirstCoefficientMap w p ∈ LinearMap.ker (F.firstCoefficientHorizontal w)) :
    (F.firstCoefficientRelativeEquiv w hw ⟨F.normalizedFirstCoefficientMap w p, hp⟩ :
      F.squareFiltration.quotientTop.PolynomialSymbol w) = F.reducedRelativeSquareSymbolMap w hw p :=
  F.firstCoefficientRelativeRangeEquiv_apply w hw p

noncomputable def firstCoefficientRelativeMap :
    LinearMap.ker (F.firstCoefficientHorizontal w) →ₗ[ℚ]
      F.squareFiltration.quotientTop.PolynomialSymbol w :=
  (F.reducedSquareSndSymbolMap w).ker.toSubmodule.subtype.comp
    (F.firstCoefficientRelativeEquiv w hw).toLinearMap

noncomputable def firstCoefficientFastSubmodule
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w)) :
    Submodule ℚ (F.FirstCoefficientModule w) :=
  (U.comap (F.firstCoefficientRelativeMap w hw)).map (LinearMap.ker (F.firstCoefficientHorizontal w)).subtype

theorem firstCoefficientFastSubmodule_le_horizontal_ker
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w)) :
    F.firstCoefficientFastSubmodule w hw U ≤ LinearMap.ker (F.firstCoefficientHorizontal w) := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem normalizedFirstCoefficientMap_mem_fast_iff
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (p : F.normalizedRelativeSubmodule w) :
    F.normalizedFirstCoefficientMap w p ∈ F.firstCoefficientFastSubmodule w hw U ↔
      F.reducedRelativeSquareSymbolMap w hw p ∈ U := by
  have hp : F.normalizedFirstCoefficientMap w p ∈ LinearMap.ker (F.firstCoefficientHorizontal w) := by
    rw [← F.normalizedFirstCoefficientMap_range w]
    exact ⟨p, rfl⟩
  constructor
  · rintro ⟨y, hy, he⟩
    have hy' : y = ⟨F.normalizedFirstCoefficientMap w p, hp⟩ := Subtype.ext he
    rw [hy'] at hy
    change (F.firstCoefficientRelativeEquiv w hw ⟨F.normalizedFirstCoefficientMap w p, hp⟩ :
      F.squareFiltration.quotientTop.PolynomialSymbol w) ∈ U at hy
    rwa [F.firstCoefficientRelativeEquiv_apply] at hy
  · intro h
    refine ⟨⟨F.normalizedFirstCoefficientMap w p, hp⟩, ?_, rfl⟩
    change (F.firstCoefficientRelativeEquiv w hw ⟨F.normalizedFirstCoefficientMap w p, hp⟩ :
      F.squareFiltration.quotientTop.PolynomialSymbol w) ∈ U
    rwa [F.firstCoefficientRelativeEquiv_apply]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem reducedSquareCoefficientMap_horizontal
    (x : F.squareFiltration.quotientTop.PolynomialSymbol w) :
    F.firstCoefficientHorizontal w (F.reducedSquareCoefficientMap w x) = 0 := by
  obtain ⟨p, rfl⟩ := F.squareFiltration.quotientTop.polynomialSymbolMap_surjective w x
  rw [F.reducedSquareCoefficientMap_symbol]
  exact (F.normalizedFirstCoefficientMap_range w).le ⟨F.reducedSquareDifferenceRelative w p, rfl⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem reducedSquareCoefficientMap_relativeMap
    (x : LinearMap.ker (F.firstCoefficientHorizontal w)) :
    F.reducedSquareCoefficientMap w (F.firstCoefficientRelativeMap w hw x) = x.val := by
  have hx : x.val ∈ LinearMap.range (F.normalizedFirstCoefficientMap w) :=
    (F.normalizedFirstCoefficientMap_range w).ge x.property
  obtain ⟨p, hp⟩ := hx
  have hm : F.normalizedFirstCoefficientMap w p ∈ LinearMap.ker (F.firstCoefficientHorizontal w) :=
    (F.normalizedFirstCoefficientMap_range w).le ⟨p, rfl⟩
  have he : x = ⟨F.normalizedFirstCoefficientMap w p, hm⟩ := Subtype.ext hp.symm
  rw [he]
  change F.reducedSquareCoefficientMap w
    (F.firstCoefficientRelativeEquiv w hw ⟨F.normalizedFirstCoefficientMap w p, hm⟩).val = _
  rw [F.firstCoefficientRelativeEquiv_apply, F.reducedSquareCoefficientMap_relative]

theorem firstCoefficientRelativeMap_coefficientMap
    (x : F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hx : x ∈ (F.reducedSquareSndSymbolMap w).ker) :
    F.firstCoefficientRelativeMap w hw
      ⟨F.reducedSquareCoefficientMap w x, F.reducedSquareCoefficientMap_horizontal w x⟩ = x := by
  have hx' : x ∈ LinearMap.range (F.reducedRelativeSquareSymbolMap w hw) :=
    (F.reducedRelativeSquareSymbolMap_range w hw).ge hx
  obtain ⟨p, rfl⟩ := hx'
  have hm : F.normalizedFirstCoefficientMap w p ∈ LinearMap.ker (F.firstCoefficientHorizontal w) :=
    (F.normalizedFirstCoefficientMap_range w).le ⟨p, rfl⟩
  have he : (⟨F.reducedSquareCoefficientMap w (F.reducedRelativeSquareSymbolMap w hw p),
      F.reducedSquareCoefficientMap_horizontal w _⟩ : LinearMap.ker (F.firstCoefficientHorizontal w)) =
      ⟨F.normalizedFirstCoefficientMap w p, hm⟩ :=
    Subtype.ext (F.reducedSquareCoefficientMap_relative w hw p)
  exact (congrArg (F.firstCoefficientRelativeMap w hw) he).trans
    (F.firstCoefficientRelativeEquiv_apply w hw p hm)

theorem firstCoefficientFastSubmodule_eq_image
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w)) :
    F.firstCoefficientFastSubmodule w hw U =
      (U ⊓ (F.reducedSquareSndSymbolMap w).ker.toSubmodule).map (F.reducedSquareCoefficientMap w) := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨F.firstCoefficientRelativeMap w hw x, ⟨hx, ?_⟩,
      F.reducedSquareCoefficientMap_relativeMap w hw x⟩
    exact (F.firstCoefficientRelativeEquiv w hw x).property
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨⟨F.reducedSquareCoefficientMap w x, F.reducedSquareCoefficientMap_horizontal w x⟩, ?_, rfl⟩
    change F.firstCoefficientRelativeMap w hw
      ⟨F.reducedSquareCoefficientMap w x, F.reducedSquareCoefficientMap_horizontal w x⟩ ∈ U
    rw [F.firstCoefficientRelativeMap_coefficientMap w hw x hx.2]
    exact hx.1

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FirstCoefficientDimension
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι : Type*} (w : σ → ℕ) (ω : ι → ℕ)

def firstCoefficientIndexEmbedding : FirstCoefficientIndex w ω ↪ AdaptedBasisIndex w ω where
  toFun z := ⟨z.val, (Nat.le_add_right _ 1).trans z.property.le⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : AdaptedBasisIndex w ω => z.val) h

variable [Fintype σ] [Fintype ι] (s : ℕ) (hw : ∀ i, 0 < w i) (hω : ∀ i, ω i ≤ s)

@[instance_reducible] noncomputable def firstCoefficientIndexFintype :
    Fintype (FirstCoefficientIndex w ω) := by
  letI := adaptedBasisIndexFintype w ω s hw hω
  exact Fintype.ofInjective (firstCoefficientIndexEmbedding w ω) (firstCoefficientIndexEmbedding w ω).injective

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProjectedPointwiseCoefficient
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

theorem homogeneousSymbolLift_filteredMap (α : σ →₀ ℕ) (x : F.AssociatedGraded) :
    F.filteredPolynomialSymbolMap G φ hφ w (F.homogeneousSymbolLift e ω hF w α x) =
      G.homogeneousSymbolLift f ν hG w α (F.associatedGradedMap G φ hφ x) := by
  apply G.gradedSymbolPolynomial_injective f ν hG w
  rw [F.gradedSymbolPolynomial_filteredMap G e ω hF f ν hG φ hφ w,
    F.gradedSymbolPolynomial_homogeneousSymbolLift, G.gradedSymbolPolynomial_homogeneousSymbolLift,
    VectorPolynomial.map_monomial]
  apply congrArg (monomial α)
  exact F.associatedGradedMap_gradeProjection G e ω hF f ν hG φ hφ (Finsupp.weight w α) x

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FirstCoefficientDerivativeBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

def FirstCoefficientSlowBound (w : σ → ℕ) (T : σ → ℝ) (M : ℝ)
    (x : F.RealFirstCoefficientModule w) : Prop :=
  ∀ z : FirstCoefficientIndex w ω,
    |(F.realFirstCoefficientBasis b ω hF w).repr x z| ≤ M / monomialScale T z.val.1

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def realFirstCoefficientSection :
    F.RealFirstCoefficientModule w →ₗ[ℝ] F.realShiftedCoefficientSubmodule w 1 :=
  supportedQuotientSection (F.realShiftedMonomialBasis b ω hF w 1)
    ((F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype)
    {z | Finsupp.weight w z.val.val.1 + 2 ≤ ω z.val.val.2}
    (F.realShiftedCoefficient_next_eq_span b ω hF w 1)

theorem realFirstCoefficientSection_rightInverse (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientMap w (F.realFirstCoefficientSection b ω hF w x) = x :=
  supportedQuotientSection_rightInverse _ _ _ _ x

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ReducedSquareFastKernel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem reducedSquareFastRelative_action_mem (hw : ∀ i, 0 < w i)
    {u : F.quotientTop.PolynomialSymbol w} (hu : u ∈ F.reducedSquareFastDiagonalSubalgebra w W)
    {v : F.squareFiltration.quotientTop.PolynomialSymbol w} (hv : v ∈ F.reducedSquareFastRelativeSubmodule w W) :
    ⁅F.reducedSquareDiagonalSymbolMap w u, v⁆ ∈ F.reducedSquareFastRelativeSubmodule w W := by
  obtain ⟨x, hx, hxu⟩ := hu
  change F.reducedSquareSndSymbolMap w x = u at hxu
  have hk : F.reducedSquareSndSymbolMap w (x - F.reducedSquareDiagonalSymbolMap w u) = 0 := by
    rw [map_sub, F.reducedSquareSndSymbolMap_diagonal, hxu, sub_self]
  have hbracket := F.reducedSquareSndSymbolKernel_lie_eq_zero w hw hk hv.2
  rw [sub_lie] at hbracket
  have he := sub_eq_zero.mp hbracket
  constructor
  · rw [← he]
    exact W.lie_mem hx hv.1
  · change F.reducedSquareSndSymbolMap w ⁅F.reducedSquareDiagonalSymbolMap w u, v⁆ = 0
    rw [LieHom.map_lie, F.reducedSquareSndSymbolMap_diagonal, show F.reducedSquareSndSymbolMap w v = 0 from hv.2,
      lie_zero]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

theorem exists_controlled_fast_lift {ι κ μ δ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (hL : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (hM : LieModule.lowerCentralSeries ℚ M M t = ⊥)
    (e : Basis ι ℚ L) (f : Basis μ ℚ M) (c : ι → δ) (r : μ → δ)
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    (hU : BasisBlockInvariant e c U.toSubmodule)
    (φ : L →ₗ⁅ℚ⁆ M) (hblock : ∀ i j, r i ≠ c j → f.repr (φ (e j)) i = 0)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ j i, RationalHeightLE (e.repr (v j) i) H)
    (hφ : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (ι ⊕ μ) : ℝ) ≤ p)
    (hcols : ((Fintype.card ι * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    let q := (p + 2) ^ 10
    ∃ (σ : M →ₗ[ℚ] L) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((q + 2) ^ 36) ∧ l ∣ m ∧
      (∀ g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM),
        g ∈ realificationSubgroup (hnil := hM) (U.map φ) →
          realLinearCoordinateLift (hL := hL) (hM := hM) σ g ∈ realificationSubgroup (hnil := hL) U ∧
          realificationMap (hnil := hL) (hM := hM) φ (realLinearCoordinateLift (hL := hL) (hM := hM) σ g) = g) ∧
      (∀ (W : δ → ℝ), (∀ d, 0 < W d) → ∀ (B : ℝ), 0 ≤ B →
        ∀ g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM),
          (∀ i, |(f.baseChange ℝ).equivFun g.coord i| ≤ B / W (r i)) →
            ∀ i, |(e.baseChange ℝ).equivFun (realLinearCoordinateLift (hL := hL) (hM := hM) σ g).coord i| ≤
              Real.exp ((q + 2) ^ 18) * B / W (c i)) ∧
      (∀ g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM),
        (f.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun (realLinearCoordinateLift (hL := hL) (hM := hM) σ g).coord ∈
            realDenominatorGrid m) := by
  obtain ⟨σ, m, hm, hmp, hlm, _, hsolve, hslow, hgrid⟩ :=
    exists_controlled_linear_subspace_lift e f c r U.toSubmodule v hspan hU φ.toLinearMap hblock
      hH hl hv hφ hp hrows hcols hHp hlp
  refine ⟨σ, m, hm, hmp, hlm, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨hmem, hproj⟩ := hsolve g.coord hg
    exact ⟨hmem, NilpotentLieBCHGroup.ext hproj⟩
  · intro W hW B hB g hg
    exact hslow W hW B hB g.coord hg
  · intro g hg
    exact hgrid g.coord hg

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def reducedSquareRealLinearLift
    (S : F.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
    (g : F.quotientTop.RealPolynomialSymbolGroup w) :
    F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w := ⟨S.baseChange ℝ g.coord⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem reducedSquareRealSymbolKernel_lie_eq_zero (hw : ∀ i, 0 < w i)
    {x y : ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w}
    (hx : (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ x = 0)
    (hy : (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ y = 0) :
    ⁅x, y⁆ = 0 := by
  have hx' : x ∈ (F.reducedSquareSndSymbolMap w).ker.toSubmodule.baseChange ℝ := by
    rw [F.reducedSquareRealSymbolKernel_eq]
    exact hx
  have hy' : y ∈ (F.reducedSquareSndSymbolMap w).ker.toSubmodule.baseChange ℝ := by
    rw [F.reducedSquareRealSymbolKernel_eq]
    exact hy
  have hh := lie_mem_real_baseChange (F.reducedSquareSndSymbolMap w).ker.toSubmodule
    (F.reducedSquareSndSymbolMap w).ker.toSubmodule ⊥
    (fun a ha b hb => (Submodule.mem_bot ℚ).mpr
      (F.reducedSquareSndSymbolKernel_lie_eq_zero w hw ha hb)) hx' hy'
  simpa only [Submodule.baseChange_bot, Submodule.mem_bot] using hh

theorem reducedSquareRealSymbolKernel_bch (hw : ∀ i, 0 < w i)
    {x y : ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w}
    (hx : (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ x = 0)
    (hy : (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ y = 0) :
    lieBCH s x y = x + y :=
  lieBCH_eq_add_of_lie_eq_zero
    (realification_lowerCentralSeries_eq_bot
      (F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w))
    (F.reducedSquareRealSymbolKernel_lie_eq_zero w hw hx hy)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem reducedSquareRealRelative_same_diagonal_mod_kernel (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    {g h : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w}
    (hg : g.coord ∈ realificationLieSubalgebra U) (hh : h.coord ∈ realificationLieSubalgebra U)
    (hproj : F.reducedSquareRealSymbolHom w g = F.reducedSquareRealSymbolHom w h) :
    (F.reducedSquareRealRelativePart w g).coord - (F.reducedSquareRealRelativePart w h).coord ∈
      (F.reducedSquareFastRelativeSubmodule w U).baseChange ℝ := by
  have hpair := splitRelativePart_pair_mem (F.reducedSquareRealSymbolHom w)
    (F.reducedSquareRealDiagonalHom w) (F.reducedSquareRealSymbolHom_diagonal w)
    (realificationSubgroup
      (hnil := F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w) U)
    hg hh hproj
  have hneg : (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ
      (-(F.reducedSquareRealRelativePart w h).coord) = 0 := by
    rw [map_neg, F.reducedSquareRealRelativePart_coord_kernel, neg_zero]
  have he : (F.reducedSquareRealRelativePart w g * (F.reducedSquareRealRelativePart w h)⁻¹).coord =
      (F.reducedSquareRealRelativePart w g).coord - (F.reducedSquareRealRelativePart w h).coord := by
    rw [coord_mul, coord_inv, F.reducedSquareRealSymbolKernel_bch w hw
      (F.reducedSquareRealRelativePart_coord_kernel w g) hneg, sub_eq_add_neg]
  change _ ∈ (U.toSubmodule ⊓ (F.reducedSquareSndSymbolMap w).ker.toSubmodule).baseChange ℝ
  rw [realification_inf, F.reducedSquareRealSymbolKernel_eq]
  constructor
  · have hm : (F.reducedSquareRealRelativePart w g * (F.reducedSquareRealRelativePart w h)⁻¹).coord ∈
        realificationLieSubalgebra U := hpair.1
    rwa [he] at hm
  · change (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ
      ((F.reducedSquareRealRelativePart w g).coord - (F.reducedSquareRealRelativePart w h).coord) = 0
    rw [map_sub, F.reducedSquareRealRelativePart_coord_kernel,
      F.reducedSquareRealRelativePart_coord_kernel, sub_self]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def realNormalizedRelativeAdjoint (g : F.RealAdaptedPolynomialGroup w) :
    (ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) ≃ₗ[ℝ]
      (ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :=
  realIdealAdjoint (F.normalizedRelativeIdeal w)
    (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot g

theorem realNormalizedRelativeAdjoint_inclusion (g : F.RealAdaptedPolynomialGroup w)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    (F.normalizedRelativeSubmodule w).subtype.baseChange ℝ (F.realNormalizedRelativeAdjoint w g x) =
      dualAdjoint g ((F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x) :=
  realIdealAdjoint_inclusion (F.normalizedRelativeIdeal w)
    (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot g x

theorem reducedRelativeSquareSymbolMap_lie (hw : ∀ i, 0 < w i)
    (a : F.adaptedLieSubalgebra w) (p : F.normalizedRelativeSubmodule w) :
    F.reducedRelativeSquareSymbolMap w hw
        ⟨⁅a, p.val⁆, F.normalizedRelativeSubmodule_lie_mem w a p.val p.property⟩ =
      ⁅F.reducedSquareDiagonalSymbolMap w (F.adaptedReducedSymbolMap w a),
        F.reducedRelativeSquareSymbolMap w hw p⁆ := by
  change F.reducedSquareSymbolMap w
      (F.squareFiltration.polynomialSymbolMap w
        (F.relativeSquareLift w hw ⟨⁅a, p.val⁆, _⟩)) = _
  rw [F.relativeSquareLift_lie, LieHom.map_lie, LieHom.map_lie,
    ← F.squareDiagonalSymbolMap_symbol, ← F.reducedSquareDiagonalSymbolMap_quotient]
  rfl

theorem realReducedRelativeSquareSymbolMap_adjoint (hw : ∀ i, 0 < w i)
    (g : F.RealAdaptedPolynomialGroup w) (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realReducedRelativeSquareSymbolMap w hw (F.realNormalizedRelativeAdjoint w g x) =
      dualAdjoint (F.reducedSquareRealDiagonalHom w (F.adaptedReducedRealSymbolHom w g))
        (F.realReducedRelativeSquareSymbolMap w hw x) := by
  let B := (F.reducedSquareDiagonalSymbolMap w).comp (F.adaptedReducedSymbolMap w)
  have hb : realificationMap
      (hnil := (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
      (hM := F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w) B g =
      F.reducedSquareRealDiagonalHom w (F.adaptedReducedRealSymbolHom w g) := by
    apply NilpotentLieBCHGroup.ext
    change ((F.reducedSquareDiagonalSymbolMap w).toLinearMap.comp
      (F.adaptedReducedSymbolMap w).toLinearMap).baseChange ℝ g.coord =
      (F.reducedSquareDiagonalSymbolMap w).toLinearMap.baseChange ℝ
        ((F.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ g.coord)
    rw [LinearMap.baseChange_comp, LinearMap.comp_apply]
  have he := realIdealMap_adjoint (F.normalizedRelativeIdeal w)
    (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot
    (F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
    B (F.reducedRelativeSquareSymbolMap w hw) (F.reducedRelativeSquareSymbolMap_lie w hw) g x
  rw [hb] at he
  exact he

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

noncomputable def realFirstCoefficientFastSubmodule : Submodule ℝ (F.RealFirstCoefficientModule w) :=
  ((F.firstCoefficientFastSubmodule w hw U).baseChange ℝ).map (F.firstCoefficientRealEquiv w).toLinearMap

theorem realFirstCoefficientFastSubmodule_le_horizontal_ker :
    F.realFirstCoefficientFastSubmodule w hw U ≤ LinearMap.ker (F.realFirstCoefficientHorizontal w) := by
  rintro x ⟨y, hy, rfl⟩
  change (F.firstCoefficientHorizontal w).baseChange ℝ
    ((F.firstCoefficientRealEquiv w).symm (F.firstCoefficientRealEquiv w y)) = 0
  rw [LinearEquiv.symm_apply_apply]
  have hm := Submodule.baseChange_mono ℝ (F.firstCoefficientFastSubmodule_le_horizontal_ker w hw U) hy
  rw [realification_ker] at hm
  exact hm

theorem realNormalizedFirstCoefficientMap_mem_fast_iff (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realNormalizedFirstCoefficientMap w x ∈ F.realFirstCoefficientFastSubmodule w hw U ↔
      F.realReducedRelativeSquareSymbolMap w hw x ∈ U.baseChange ℝ := by
  have hp : (F.firstCoefficientFastSubmodule w hw U).comap (F.normalizedFirstCoefficientMap w) =
      U.comap (F.reducedRelativeSquareSymbolMap w hw) := by
    ext p
    exact F.normalizedFirstCoefficientMap_mem_fast_iff w hw U p
  have hr := congrArg (fun P : Submodule ℚ (F.normalizedRelativeSubmodule w) => P.baseChange ℝ) hp
  rw [realification_comap, realification_comap] at hr
  have he : (F.normalizedFirstCoefficientMap w).baseChange ℝ x ∈
        (F.firstCoefficientFastSubmodule w hw U).baseChange ℝ ↔
      F.realReducedRelativeSquareSymbolMap w hw x ∈ U.baseChange ℝ := SetLike.ext_iff.mp hr x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyx : y = (F.normalizedFirstCoefficientMap w).baseChange ℝ x :=
      (F.firstCoefficientRealEquiv w).injective hxy
    rw [hyx] at hy
    exact he.mp hy
  · intro hx
    exact ⟨(F.normalizedFirstCoefficientMap w).baseChange ℝ x, he.mpr hx, rfl⟩

noncomputable def realFastCoefficientHorizontal :
    (F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U) →ₗ[ℝ]
      (ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :=
  (F.realFirstCoefficientFastSubmodule w hw U).liftQ (F.realFirstCoefficientHorizontal w)
    (F.realFirstCoefficientFastSubmodule_le_horizontal_ker w hw U)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ReducedProjectionBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

def reducedSquareDiagonalIndex (s : ℕ) (ω : ι → ℕ)
    (i : QuotientTopBasisIndex s ω) : ReducedSquareBasisIndex s ω :=
  ⟨Sum.inl i.val, i.property⟩

def reducedSquareDiagonalSymbolIndex (s : ℕ) (w : σ → ℕ) (ω : ι → ℕ)
    (z : QuotientTopSymbolIndex s w ω) : ReducedSquareSymbolIndex s w ω :=
  ⟨(z.val.1, reducedSquareDiagonalIndex s ω z.val.2), z.property⟩

variable (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem reducedSquareSnd_basis_repr [DecidableEq ι]
    (a : ReducedSquareBasisIndex s ω) (b : QuotientTopBasisIndex s ω) :
    (F.quotientTopBasis e ω hF).repr
      (F.reducedSquareSnd (F.reducedSquareBasis e ω hF a)) b =
      if a = reducedSquareDiagonalIndex s ω b then 1 else 0 := by
  classical
  dsimp only [reducedSquareBasis]
  rw [F.squareFiltration.quotientTopBasis_apply, F.reducedSquareSnd_mk,
    F.quotientTopBasis_repr_mk]
  rcases a with ⟨a, ha⟩
  cases a with
  | inl i =>
    change e.repr ((F.adaptedSquareBasis e ω (hF 2) (Sum.inl i)).val.2) b.val = _
    rw [F.adaptedSquareBasis_inl]
    simp [reducedSquareDiagonalIndex, Basis.repr_self, Finsupp.single_apply,
      Subtype.ext_iff]
  | inr i =>
    change e.repr ((F.adaptedSquareBasis e ω (hF 2) (Sum.inr i)).val.2) b.val = _
    rw [F.adaptedSquareBasis_inr]
    simp [reducedSquareDiagonalIndex, Subtype.ext_iff]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedSymbolDimensions
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)

include hF hw in
theorem reducedSquareSymbolIndex_finite : Finite (ReducedSquareSymbolIndex s w ω) :=
  symbolBasisIndex_finite w (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω i.val) s hw
    (F.squareFiltration.quotientTop.adaptedBasis_weight_le_step (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF))

include hF hw in
theorem reducedSquareSymbolIndex_card_le [Fintype (ReducedSquareSymbolIndex s w ω)] :
    Fintype.card (ReducedSquareSymbolIndex s w ω) ≤
      2 * (Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s) := by
  have h := symbolBasisIndex_card_le w
    (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω i.val) s hw
    (F.squareFiltration.quotientTop.adaptedBasis_weight_le_step (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF))
  have hc : Fintype.card (ReducedSquareBasisIndex s ω) ≤ 2 * Fintype.card ι :=
    (Fintype.card_subtype_le _).trans (card_squareBasis_index_le ω)
  exact h.trans (by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right ((Fintype.card σ + 1) ^ s)
      (Nat.mul_le_mul_right (s + 1) hc))

include hF hw in
theorem reduced_lift_matrix_dimensions {κ : Type*} [Fintype κ]
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hσ : (Fintype.card σ : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p) :
    2 * (Fintype.card ι : ℝ) ≤ reducedMatrixParameter s p ∧
      (Fintype.card (ReducedSquareSymbolIndex s w ω ⊕ QuotientTopSymbolIndex s w ω) : ℝ) ≤
        reducedMatrixParameter s p ∧
      ((Fintype.card (ReducedSquareSymbolIndex s w ω) * Fintype.card κ : ℕ) : ℝ) ≤
        reducedMatrixParameter s p := by
  let d := (p + (s + 2)) ^ (s + 2)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hB : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ d :=
    (Nat.cast_le.mpr (F.quotientTopSymbolIndex_card_le e ω hF w hw)).trans
      (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hS : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ 2 * d := by
    have hh := Nat.cast_le (α := ℝ).mpr (F.reducedSquareSymbolIndex_card_le e ω hF w hw)
    rw [Nat.cast_mul, Nat.cast_ofNat] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ) (by norm_num))
  have hlarge : 3 * d * (p + 1) ≤ reducedMatrixParameter s p := by
    dsimp only [reducedMatrixParameter, d]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have hnonneg : 0 ≤ 3 * d * (p + 1) := by positivity
    dsimp only [reducedMatrixParameter]
    change 2 * (Fintype.card ι : ℝ) ≤ 3 * d * (p + 1) + 2 * p + 2
    linarith
  · rw [Fintype.card_sum, Nat.cast_add]
    calc
      _ ≤ 3 * d := by linarith
      _ ≤ 3 * d * (p + 1) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (show 1 ≤ p + 1 by linarith)
          (show 0 ≤ 3 * d by positivity)
      _ ≤ _ := hlarge
  · rw [Nat.cast_mul]
    calc
      _ ≤ (2 * d) * p := mul_le_mul hS hκ (Nat.cast_nonneg _) (by positivity)
      _ ≤ (3 * d) * (p + 1) :=
        mul_le_mul (by linarith) (by linarith) hp (by positivity)
      _ ≤ _ := hlarge

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

noncomputable def layerOneBasis : Basis (LayerOneBasisIndex ω) ℚ (L ⧸ F.layer 2) :=
  supportedQuotientBasis e (F.layer 2) {i | 2 ≤ ω i} (hF 2)

theorem layerOneBasis_repr_mk (x : L) (i : LayerOneBasisIndex ω) :
    (F.layerOneBasis e ω hF).repr ((F.layer 2).mkQ x) i = e.repr x i :=
  supportedQuotientBasis_repr_mk e (F.layer 2) {i | 2 ≤ ω i} (hF 2) x i

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealReducedFastKernel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem reducedSquareRealFastRelative_action_mem (hw : ∀ i, 0 < w i)
    {u : ℝ ⊗[ℚ] F.quotientTop.PolynomialSymbol w}
    (hu : u ∈ realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w W))
    {v : ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w}
    (hv : v ∈ (F.reducedSquareFastRelativeSubmodule w W).baseChange ℝ) :
    ⁅(F.reducedSquareDiagonalSymbolMap w).toLinearMap.baseChange ℝ u, v⁆ ∈
      (F.reducedSquareFastRelativeSubmodule w W).baseChange ℝ := by
  let P := (F.reducedSquareFastDiagonalSubalgebra w W).toSubmodule
  let K := F.reducedSquareFastRelativeSubmodule w W
  let d := (F.reducedSquareDiagonalSymbolMap w).toLinearMap
  have hu' : d.baseChange ℝ u ∈ (P.map d).baseChange ℝ := by
    rw [realification_map]
    exact ⟨u, hu, rfl⟩
  have hclosed : ∀ x ∈ P.map d, ∀ y ∈ K, ⁅x, y⁆ ∈ K := by
    rintro x ⟨y, hy, rfl⟩ z hz
    exact F.reducedSquareFastRelative_action_mem w W hw hy hz
  exact lie_mem_real_baseChange (P.map d) K K hclosed hu' hv

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedRelativeCoefficientBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem reducedSquareRealFastRelative_adjoint_mem (hw : ∀ i, 0 < w i)
    (g : F.quotientTop.RealPolynomialSymbolGroup w)
    (hg : g.coord ∈ realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
    (x : ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hx : x ∈ (F.reducedSquareFastRelativeSubmodule w U).baseChange ℝ) :
    dualAdjoint (F.reducedSquareRealDiagonalHom w g) x ∈
      (F.reducedSquareFastRelativeSubmodule w U).baseChange ℝ := by
  let A := (realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U)).map
    (realificationLieHom (F.reducedSquareDiagonalSymbolMap w))
  have ha : (F.reducedSquareRealDiagonalHom w g).coord ∈ realLieSubalgebraOverRat A :=
    ⟨g.coord, hg, rfl⟩
  apply dualAdjoint_real_mem_of_invariant (realLieSubalgebraOverRat A)
    ((F.reducedSquareFastRelativeSubmodule w U).baseChange ℝ) _ _ ha _ hx
  rintro z ⟨u, hu, rfl⟩ y hy
  exact F.reducedSquareRealFastRelative_action_mem w U hw hu hy

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem realFirstCoefficientAdjoint_mul (g h : F.RealAdaptedPolynomialGroup w)
    (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientAdjoint w (g * h) x =
      F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientAdjoint w h x) := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
    ((F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype) x
  change F.realFirstCoefficientAdjoint w (g * h) (F.realFirstCoefficientMap w y) =
    F.realFirstCoefficientAdjoint w g
      (F.realFirstCoefficientAdjoint w h (F.realFirstCoefficientMap w y))
  rw [F.realFirstCoefficientAdjoint_map, F.realFirstCoefficientAdjoint_map,
    F.realFirstCoefficientAdjoint_map]
  apply congrArg (F.realFirstCoefficientMap w)
  exact Subtype.ext (dualAdjoint_mul g h y.val)

theorem realFirstCoefficientAdjoint_cancel_inv (g : F.RealAdaptedPolynomialGroup w)
    (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientAdjoint w g⁻¹ x) = x := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
    ((F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype) x
  change F.realFirstCoefficientAdjoint w g
    (F.realFirstCoefficientAdjoint w g⁻¹ (F.realFirstCoefficientMap w y)) = F.realFirstCoefficientMap w y
  rw [F.realFirstCoefficientAdjoint_map, F.realFirstCoefficientAdjoint_map]
  apply congrArg (F.realFirstCoefficientMap w)
  exact Subtype.ext (dualAdjoint_cancel_inv g y.val)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

abbrev RealFastCoefficientModule := F.RealFirstCoefficientModule w ⧸
  F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)

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

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def layerOneGradedMap : (L ⧸ F.layer 2) →ₗ[ℚ] F.AssociatedGraded :=
  (F.gradedPieceProjection e ω hF 1).comp
    (supportedQuotientSection e (F.layer 2) {i | 2 ≤ ω i} (hF 2))

theorem layerOneGradedMap_mk (x : L) :
    F.layerOneGradedMap e ω hF ((F.layer 2).mkQ x) = F.gradedPieceProjection e ω hF 1 x := by
  apply (F.associatedGradedBasis e ω hF).repr.injective
  ext i
  change (F.associatedGradedBasis e ω hF).repr
    (F.gradedPieceProjection e ω hF 1
      (supportedQuotientSection e (F.layer 2) {i | 2 ≤ ω i} (hF 2) ((F.layer 2).mkQ x))) i = _
  rw [F.gradedPieceProjection_coordinate, F.gradedPieceProjection_coordinate]
  by_cases hi : ω i = 1
  · rw [if_pos hi, if_pos hi]
    have hni : ¬2 ≤ ω i := by omega
    exact (supportedQuotientSection_coordinate e (F.layer 2) {i | 2 ≤ ω i}
      (hF 2) ((F.layer 2).mkQ x) ⟨i, hni⟩).trans
        (supportedQuotientBasis_repr_mk e (F.layer 2) {i | 2 ≤ ω i} (hF 2) x ⟨i, hni⟩)
  · rw [if_neg hi, if_neg hi]

noncomputable def layerOneGradedSubmodule (U : LieSubalgebra ℚ F.AssociatedGraded) :
    Submodule ℚ (L ⧸ F.layer 2) :=
  U.toSubmodule.comap (F.layerOneGradedMap e ω hF)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))

noncomputable def realFastCoefficientDirectionMap
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    (σ → ℝ) →ₗ[ℝ] F.RealFastCoefficientModule (fun _ => 1) (fun _ => Nat.zero_lt_one) U :=
  (F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ.comp
      (F.realFirstCoefficientDirectionMap g.coord)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem adaptedReducedRealSymbolHom_coord (g : F.RealAdaptedPolynomialGroup w) :
    (F.adaptedReducedRealSymbolHom w g).coord =
      (F.quotientTopSymbolMap w).toLinearMap.baseChange ℝ (F.realExtendedSymbolMap w g.coord) := by
  change ((F.quotientTopSymbolMap w).toLinearMap.comp
    (F.polynomialSymbolMap w).toLinearMap).baseChange ℝ g.coord = _
  rw [LinearMap.baseChange_comp]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

theorem realAdaptedCoefficientBound_inv {σ ι L : Type*}
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (w : σ → ℕ) (T : σ → ℝ) (M : ℝ) (g : F.RealAdaptedPolynomialGroup w)
    (hg : F.RealAdaptedCoefficientBound e ω hF w T M g.coord) :
    F.RealAdaptedCoefficientBound e ω hF w T M (g⁻¹).coord := by
  simpa only [RealAdaptedCoefficientBound, coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hg

theorem fastCoefficientDirection_norm_bound {σ ι κ L : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
    (b : Basis κ ℝ (F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U))
    (rows : κ → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (Cproj D : ℝ) (hCproj : 0 ≤ Cproj) (hD : 0 ≤ D)
    (hproj : ∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M x →
      ∀ j, |b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) j| ≤
          Cproj * M / monomialScale T (rows j).val.1)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hg : ∀ i, F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (D / T i)
      (F.realFirstCoefficientDirectionMap g.coord (Pi.single i 1))) (i : σ) :
    ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1)
        (F.realFastCoefficientDirectionMap U g (Pi.single i 1))‖ ≤ Cproj * D / T i := by
  apply (basisWeightedCoordinates_norm_le_iff b (fun j => monomialScale T (rows j).val.1)
    (fun j => monomialScale_pos T hT _) (div_nonneg (mul_nonneg hCproj hD) (hT i).le) _).mpr
  intro j
  have h := hproj (D / T i) (div_nonneg hD (hT i).le) _ (hg i) j
  change |b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ
      (F.realFirstCoefficientDirectionMap g.coord (Pi.single i 1))) j| ≤ _
  simpa only [mul_div_assoc] using h

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedProjectedComparison
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem quotientTopBasis_structure_height {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (a b k : QuotientTopBasisIndex s ω) :
    RationalHeightLE (lieStructureConstants (F.quotientTopBasis e ω hF) a b k) H := by
  have hspan : (F.layerIdeal (s + 1)).toSubmodule =
      Submodule.span ℚ (e '' {i | s + 1 ≤ ω i}) := hF (s + 1)
  have he : lieStructureConstants (F.quotientTopBasis e ω hF) a b k =
      lieStructureConstants e a.val b.val k.val :=
    supportedQuotientBasis_lieStructure e (F.layerIdeal (s + 1))
      {i | s + 1 ≤ ω i} hspan a b k
  rw [he]
  exact hc a.val b.val k.val

theorem reducedSquareSndSymbolMap_span (w : σ → ℕ)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hv : Submodule.span ℚ (Set.range v) = U.toSubmodule) :
    Submodule.span ℚ (Set.range (fun i => F.reducedSquareSndSymbolMap w (v i))) =
      (U.map (F.reducedSquareSndSymbolMap w)).toSubmodule := by
  change _ = U.toSubmodule.map (F.reducedSquareSndSymbolMap w).toLinearMap
  rw [← hv, Submodule.map_span, ← Set.range_comp]
  rfl

theorem reducedSquareRealSymbolHom_fast (w : σ → ℕ)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (hg : g.coord ∈ realificationLieSubalgebra U) :
    (F.reducedSquareRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) := by
  rw [realificationLieSubalgebra_map]
  exact ⟨g.coord, hg, rfl⟩

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

theorem firstCoefficientFastSubmodule_relative :
    F.firstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U) =
      F.firstCoefficientFastSubmodule w hw U.toSubmodule := by
  rw [F.firstCoefficientFastSubmodule_eq_image, F.firstCoefficientFastSubmodule_eq_image]
  simp only [reducedSquareFastRelativeSubmodule, inf_assoc, inf_idem]

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

section Bounds

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem FirstCoefficientSlowBound.mono (w : σ → ℕ) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M N : ℝ} (hMN : M ≤ N) (x : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientSlowBound e ω hF w T M x) :
    F.FirstCoefficientSlowBound e ω hF w T N x := by
  intro z
  exact (hx z).trans (div_le_div_of_nonneg_right hMN (monomialScale_pos T hT z.val.1).le)

end Bounds

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

noncomputable def adaptedGradedPolynomialLie :
    F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ F.AssociatedGraded :=
  (F.gradedSymbolPolynomialLie b ω hF w).comp (F.polynomialSymbolMap w)

theorem adaptedGradedPolynomialLie_apply (p : F.adaptedLieSubalgebra w) :
    F.adaptedGradedPolynomialLie b ω hF w p = F.adaptedShiftedGradedPolynomial b ω hF w 0 p := by
  exact (F.shiftedGradedPolynomial_zero b ω hF w p).symm

theorem adaptedShiftedGradedPolynomial_lie (p q : F.adaptedLieSubalgebra w)
    (hq : q ∈ F.shiftedPolynomialIdeal w 1) :
    F.adaptedShiftedGradedPolynomial b ω hF w 1 ⁅p, q⁆ =
      ⁅F.adaptedGradedPolynomialLie b ω hF w p, F.adaptedShiftedGradedPolynomial b ω hF w 1 q⁆ := by
  have hp : p.val ∈ F.shiftedAdaptedSubmodule w 0 := by
    intro α
    simpa only [Nat.add_zero] using p.property α
  rw [F.adaptedGradedPolynomialLie_apply]
  have hq' : q.val ∈ F.shiftedAdaptedSubmodule w 1 := hq
  rw [F.adaptedShiftedGradedPolynomial_apply, F.adaptedShiftedGradedPolynomial_apply,
    F.adaptedShiftedGradedPolynomial_apply, LieSubalgebra.coe_bracket]
  have he := F.shiftedGradedPolynomial_lie b ω hF w (i := 0) (j := 1)
    (p := p.val) (q := q.val) hp hq'
  rw [Nat.zero_add] at he
  rw [he]

theorem firstCoefficientGradedPolynomial_coordinate (x : F.FirstCoefficientModule w)
    (α : σ →₀ ℕ) (i : ι) :
    (F.associatedGradedBasis b ω hF).repr
      (coefficients (F.firstCoefficientGradedPolynomial b ω hF w x) α) i =
      if h : Finsupp.weight w α + 1 = ω i then
        (F.firstCoefficientBasis b ω hF w).repr x ⟨(α, i), h⟩ else 0 := by
  classical
  obtain ⟨p, rfl⟩ := F.firstCoefficientMap_surjective w x
  rw [F.firstCoefficientGradedPolynomial_map, F.adaptedShiftedGradedPolynomial_apply,
    F.shiftedGradedPolynomial_coefficient, F.gradedPieceProjection_coordinate]
  by_cases h : Finsupp.weight w α + 1 = ω i
  · rw [dif_pos h, if_pos h.symm, F.firstCoefficientBasis_repr_map]
  · rw [dif_neg h, if_neg (Ne.symm h)]

theorem firstCoefficientGradedPolynomial_injective :
    Function.Injective (F.firstCoefficientGradedPolynomial b ω hF w) := by
  intro x y hxy
  apply (F.firstCoefficientBasis b ω hF w).repr.injective
  ext z
  have h := congrArg (fun P => (F.associatedGradedBasis b ω hF).repr (coefficients P z.val.1) z.val.2) hxy
  simpa only [F.firstCoefficientGradedPolynomial_coordinate, dif_pos z.property] using h

theorem firstCoefficientGradedPolynomial_homogeneous (x : F.FirstCoefficientModule w) (α : σ →₀ ℕ) :
    basisGradeProjection (F.associatedGradedBasis b ω hF) ω (Finsupp.weight w α + 1)
      (coefficients (F.firstCoefficientGradedPolynomial b ω hF w x) α) =
        coefficients (F.firstCoefficientGradedPolynomial b ω hF w x) α := by
  apply (F.associatedGradedBasis b ω hF).repr.injective
  ext i
  rw [basisGradeProjection_repr]
  by_cases hi : ω i = Finsupp.weight w α + 1
  · rw [if_pos hi]
  · rw [if_neg hi, F.firstCoefficientGradedPolynomial_coordinate, dif_neg (Ne.symm hi)]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def realFirstCoefficientGradedPolynomial :
    F.RealFirstCoefficientModule w →ₗ[ℝ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  realificationRealLinearEquiv.toLinearMap.comp
    (((F.firstCoefficientGradedPolynomial b ω hF w).baseChange ℝ).comp
      (F.firstCoefficientRealEquiv w).symm.toLinearMap)

theorem realFirstCoefficientGradedPolynomial_realEquiv (x : ℝ ⊗[ℚ] F.FirstCoefficientModule w) :
    F.realFirstCoefficientGradedPolynomial b ω hF w (F.firstCoefficientRealEquiv w x) =
      realificationRealLinearEquiv ((F.firstCoefficientGradedPolynomial b ω hF w).baseChange ℝ x) := by
  simp only [realFirstCoefficientGradedPolynomial, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

theorem realFirstCoefficientGradedPolynomial_tmul (a : ℝ) (x : F.FirstCoefficientModule w)
    (α : σ →₀ ℕ) :
    coefficients (F.realFirstCoefficientGradedPolynomial b ω hF w
      (F.firstCoefficientRealEquiv w (a ⊗ₜ[ℚ] x))) α =
      a ⊗ₜ[ℚ] coefficients (F.firstCoefficientGradedPolynomial b ω hF w x) α := by
  rw [F.realFirstCoefficientGradedPolynomial_realEquiv, LinearMap.baseChange_tmul,
    realificationRealLinearEquiv_apply, coefficients_realificationLinearEquiv_tmul]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def realAdaptedShiftedGradedPolynomial (k : ℕ) :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) →ₗ[ℝ]
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  realificationRealLinearEquiv.toLinearMap.comp
    ((F.adaptedShiftedGradedPolynomial b ω hF w k).baseChange ℝ)

noncomputable def realAdaptedGradedPolynomialLie :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) →ₗ⁅ℚ⁆
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  realificationLieEquiv.toLieHom.comp
    (realLieHomToRat (realificationLieHom (F.adaptedGradedPolynomialLie b ω hF w)))

theorem realAdaptedShiftedGradedPolynomial_tensor (k : ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realAdaptedShiftedGradedPolynomial b ω hF w k x =
      realificationRealLinearEquiv ((F.adaptedShiftedGradedPolynomial b ω hF w k).baseChange ℝ x) := rfl

theorem realAdaptedGradedPolynomialLie_tensor (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realAdaptedGradedPolynomialLie b ω hF w x =
      realificationLieEquiv (realificationLieHom (F.adaptedGradedPolynomialLie b ω hF w) x) := rfl

noncomputable def realAdaptedGradedPolynomialHom :
    F.RealAdaptedPolynomialGroup w →*
      PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot :=
  NilpotentLieBCHGroup.map (F.realAdaptedGradedPolynomialLie b ω hF w)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealSquarePolynomialFactors
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem realifiedSquarePolynomial_fst
    (p : VectorPolynomial σ ℚ F.realification.squareLieSubalgebra) :
    VectorPolynomial.map ((realificationLieHom F.squareFst).toLinearMap.restrictScalars ℚ)
      (VectorPolynomial.map F.realifiedSquareEquiv.symm.toLinearMap p) =
        VectorPolynomial.map F.realification.squareFst.toLinearMap p := by
  apply coefficients.injective
  ext α
  simp only [coefficients_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  have h := F.realifiedSquareEquiv_fst (F.realifiedSquareEquiv.symm (coefficients p α))
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem realifiedSquarePolynomial_snd
    (p : VectorPolynomial σ ℚ F.realification.squareLieSubalgebra) :
    VectorPolynomial.map ((realificationLieHom F.squareSnd).toLinearMap.restrictScalars ℚ)
      (VectorPolynomial.map F.realifiedSquareEquiv.symm.toLinearMap p) =
        VectorPolynomial.map F.realification.squareSnd.toLinearMap p := by
  apply coefficients.injective
  ext α
  simp only [coefficients_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  have h := F.realifiedSquareEquiv_snd (F.realifiedSquareEquiv.symm (coefficients p α))
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem realifiedSquarePolynomial_adapted (w : σ → ℕ)
    (p : VectorPolynomial σ ℚ F.realification.squareLieSubalgebra)
    (hp : F.realification.squareFiltration.Adapted w p) :
    F.squareFiltration.realification.Adapted w
      (VectorPolynomial.map F.realifiedSquareEquiv.symm.toLinearMap p) :=
  F.realification.squareFiltration.adapted_map F.squareFiltration.realification
    F.realifiedSquareEquiv.symm.toLinearMap
    (fun j x hx => (F.realifiedSquareEquiv_symm_mem_layer j x).mpr hx) w hp

end NilpotentLieFiltration

theorem exists_bounded_realified_square_polynomial (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (h : σ → ℚ) (f : D.filtration.realification.PolynomialOrbit w),
      ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
        (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + C) ^ C)) ∧
        ∃ r : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra),
          D.filtration.squareFiltration.realification.Adapted w r ∧
          VectorPolynomial.map
            ((realificationLieHom D.filtration.squareFst).toLinearMap.restrictScalars ℚ) r =
              normalizedShiftLog s h (-ε.coord) (-γ.coord) f.log ∧
          VectorPolynomial.map
            ((realificationLieHom D.filtration.squareSnd).toLinearMap.restrictScalars ℚ) r = f.log := by
  obtain ⟨C, hC, hnorm⟩ := exists_bounded_normalized_square s
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ D p hp hD w hw h f
  obtain ⟨ε, γ, hγ, hε, r, hr, hf, hs⟩ := hnorm D p hp hD w hw h f
  refine ⟨ε, γ, hγ, hε, VectorPolynomial.map D.filtration.realifiedSquareEquiv.symm.toLinearMap r,
    D.filtration.realifiedSquarePolynomial_adapted w r hr, ?_, ?_⟩
  · rw [D.filtration.realifiedSquarePolynomial_fst]
    exact hf
  · rw [D.filtration.realifiedSquarePolynomial_snd]
    exact hs

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealReducedSquarePolynomial
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem adaptedReducedRealSymbolHom_square_projection
    (r : F.squareFiltration.RealAdaptedPolynomialGroup w) :
    F.reducedSquareRealSymbolHom w (F.squareFiltration.adaptedReducedRealSymbolHom w r) =
      F.adaptedReducedRealSymbolHom w (F.realSquareSndPolynomialHom w r) := by
  have hcomp : (F.reducedSquareSndSymbolMap w).toLinearMap.comp
      (F.squareFiltration.adaptedReducedSymbolMap w).toLinearMap =
        (F.adaptedReducedSymbolMap w).toLinearMap.comp (F.squareSndPolynomialMap w).toLinearMap := by
    apply LinearMap.ext
    intro p
    change F.reducedSquareSndSymbolMap w
        (F.reducedSquareSymbolMap w (F.squareFiltration.polynomialSymbolMap w p)) =
      F.quotientTopSymbolMap w (F.polynomialSymbolMap w (F.squareSndPolynomialMap w p))
    rw [F.reducedSquareSndSymbolMap_quotient, F.squareSndSymbolMap_symbol]
  apply NilpotentLieBCHGroup.ext
  change (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ
    ((F.squareFiltration.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ r.coord) =
      (F.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ
        ((F.squareSndPolynomialMap w).toLinearMap.baseChange ℝ r.coord)
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_comp,
    LinearMap.comp_apply]

end Erdos3.NilpotentLieFiltration

end

end OAI
end


