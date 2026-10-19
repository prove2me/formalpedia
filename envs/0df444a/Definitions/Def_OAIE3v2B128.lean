-- Prove2me | Definitions.Def_OAIE3v2B128
-- name    : OAIE3v2B128
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:43:07.391406+00:00
-- url     : https://prove2.me/theorems/e82ee7c4-91ff-454e-9c66-697b20ff5797
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 130 of 311
-- statement:
--   Definitions bundle 130 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B114`, `OAIE3v2B115` of this split.
--
--   Modules: `Estimates/ControlledComparisonModel.lean`, `Estimates/FastCoefficientImage.lean`, `Estimates/FormalInductionTerminal.lean`, `Estimates/NativeSquarefreeCoefficientBases.lean`, `Estimates/RealFirstCoefficientHorizontal.lean`, `Estimates/RealSymbolGradeEvaluation.lean`, `Estimates/RefilteredPointwiseSplitting.lean`, `Estimates/SquarefreeLayerBases.lean`, `Estimates/SquarefreeRealAction.lean`, `Estimates/WeightedTranslationBaseGrading.lean`, `Estimates/WeightedTranslationRealPureFactors.lean`, `Estimates/WeightedTwistedTranslationLipschitz.lean`, `Fourier/WeightedTranslationBufferedCentralFrequency.lean`, `Lattices/NativeIntegerAffinePullbackHom.lean`, `Lattices/NativeSquarefreeLattice.lean`, `Lattices/WeightedTranslationLattice.lean`, `Lattices/WeightedTranslationResidueLattice.lean`, `Linear/ComparisonChosenLayerBasis.lean`, `Linear/OrdinarySymbolBasisDimension.lean`, `Linear/SquareBasisGeometry.lean`, `Linear/SquareSymbolProjection.lean`, `Linear/WeightedTranslationOrderedBasis.lean`, `Nilpotent/CurrentBracketInductionStep.lean`, `Nilpotent/CyclicNiltestApproximation.lean`, `Nilpotent/FactorwiseBCHCovers.lean`, `Nilpotent/NiltestBasepointNormalization.lean`, `Nilpotent/WeightedTranslationNilmanifold.lean`, `Nilpotent/WeightedTranslationRealBCHCoordinates.lean`, `Polynomial/CurrentPolynomialDerivativeRemoval.lean`, `Polynomial/FormalPolynomialCorrectionStep.lean`, `Polynomial/MajorTranslationDegreeSymbol.lean`, `Polynomial/PolynomialTranslationIntegralAction.lean`, `Polynomial/QuantitativeOuterPolynomialProducts.lean`, `Polynomial/RelativeSquarePolynomial.lean`, `Polynomial/SimultaneousPolynomialSymbolSplitting.lean`, `Polynomial/TwistedBufferedTranslationPhase.lean`, `Polynomial/WeightedTranslationLatticePhase.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B114
import Definitions.Def_OAIE3v2B115

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FactorwiseBCHCovers
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)]
  [∀ a, LieAlgebra ℚ (M a)] {s : ℕ}

theorem mem_piBCHSubgroup (F : ∀ a, NilpotentLieFiltration (M a) s)
    (Δ : ∀ a, Subgroup (F a).Group) (g : (NilpotentLieFiltration.pi F).Group) :
    g ∈ piBCHSubgroup F Δ ↔ ∀ a, (⟨g.coord a⟩ : (F a).Group) ∈ Δ a := by
  simp only [piBCHSubgroup, Subgroup.mem_iInf, Subgroup.mem_comap]
  rfl

variable [Fintype α] {κ : α → Type*} [∀ a, Fintype (κ a)]

theorem piBCHSubgroup_coordinates (F : ∀ a, NilpotentLieFiltration (M a) s)
    (f : ∀ a, Basis (κ a) ℚ (M a)) (Δ : ∀ a, Subgroup (F a).Group)
    (x : (Σ a, κ a) → ℚ) :
    x ∈ bchSubgroupCoordinates (Pi.basis f) (piBCHSubgroup F Δ) ↔
      ∀ a, (fun i => x ⟨a, i⟩) ∈ bchSubgroupCoordinates (f a) (Δ a) := by
  change (⟨(Pi.basis f).equivFun.symm x⟩ : (NilpotentLieFiltration.pi F).Group) ∈
    piBCHSubgroup F Δ ↔ _
  rw [mem_piBCHSubgroup]
  simp only [pi_basis_equivFun_symm_apply, bchSubgroupCoordinates, Set.mem_ofPred_eq]

theorem piBCHSubgroup_inner_grid (F : ∀ a, NilpotentLieFiltration (M a) s)
    (f : ∀ a, Basis (κ a) ℚ (M a)) (Δ : ∀ a, Subgroup (F a).Group) (m : ℕ)
    (hin : ∀ a, scaledIntegerGrid m ⊆ bchSubgroupCoordinates (f a) (Δ a)) :
    scaledIntegerGrid m ⊆ bchSubgroupCoordinates (Pi.basis f) (piBCHSubgroup F Δ) := by
  rintro x ⟨z, rfl⟩
  apply (piBCHSubgroup_coordinates F f Δ _).mpr
  intro a
  exact hin a ⟨fun i => z ⟨a, i⟩, rfl⟩

theorem piBCHSubgroup_outer_grid (F : ∀ a, NilpotentLieFiltration (M a) s)
    (f : ∀ a, Basis (κ a) ℚ (M a)) (Δ : ∀ a, Subgroup (F a).Group) (m : ℕ)
    (hout : ∀ a, bchSubgroupCoordinates (f a) (Δ a) ⊆ denominatorGrid m) :
    bchSubgroupCoordinates (Pi.basis f) (piBCHSubgroup F Δ) ⊆ denominatorGrid m := by
  intro x hx
  have h := (piBCHSubgroup_coordinates F f Δ x).mp hx
  choose z hz using fun a => hout a (h a)
  exact ⟨fun i => z i.1 i.2, fun i => hz i.1 i.2⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization
namespace OAI

section

namespace Erdos3

open Module

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem bchSubgroup_outer_grid_reindex (b : Basis ι ℚ L) (e : ι ≃ κ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) {N : ℕ}
    (h : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    bchSubgroupCoordinates (b.reindex e) Γ ⊆ denominatorGrid N := by
  intro x hx
  obtain ⟨z, hz⟩ := h ((bchSubgroupCoordinates_reindex b e Γ x).mp hx)
  refine ⟨fun i => z (e.symm i), fun i => ?_⟩
  simpa only [Pi.smul_apply, Equiv.apply_symm_apply] using hz (e.symm i)

end Erdos3

end

section

open Module
open scoped BigOperators

namespace Erdos3

namespace RationalFilteredNilmanifold

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem product_inner_grid : scaledIntegerGrid (∏ i, (D i).grid) ⊆
    bchSubgroupCoordinates (productFinBasis D)
      (piBCHSubgroup (fun i => (D i).filtration) (fun i => (D i).lattice)) := by
  classical
  apply bchSubgroup_inner_grid_reindex
  apply piBCHSubgroup_inner_grid
  intro i
  exact (scaledIntegerGrid_subset_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))).trans (D i).inner_grid

theorem product_outer_grid :
    bchSubgroupCoordinates (productFinBasis D)
      (piBCHSubgroup (fun i => (D i).filtration) (fun i => (D i).lattice)) ⊆
        denominatorGrid (∏ i, (D i).grid) := by
  classical
  apply bchSubgroup_outer_grid_reindex
  apply piBCHSubgroup_outer_grid
  intro i
  exact (D i).outer_grid.trans (denominatorGrid_subset_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))

noncomputable def pi : RationalFilteredNilmanifold (∀ i, L i) s (Fintype.card (Σ i, Fin (d i))) where
  filtration := NilpotentLieFiltration.pi (fun i => (D i).filtration)
  basis := productFinBasis D
  layerBasis := productLayerFinBasis D
  lattice := piBCHSubgroup (fun i => (D i).filtration) (fun i => (D i).lattice)
  grid := ∏ i, (D i).grid
  grid_pos := Finset.prod_pos (fun i _ => (D i).grid_pos)
  inner_grid := product_inner_grid D
  outer_grid := product_outer_grid D

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CurrentBracketInductionStep
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module

variable {σ : Type*} [Fintype σ]

@[simp] theorem weightedBasis_inr_base (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}) :
    (weightedBasis w d hw (Sum.inr a)).val.base = 0 := by
  unfold weightedBasis
  erw [Basis.map_apply]
  rw [Basis.prod_apply]
  simp [weightedCoordinatesEquiv]
  rfl

@[simp] theorem weightedBasis_inr_polynomial (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}) :
    (weightedBasis w d hw (Sum.inr a)).val.polynomial = monomial a.val 1 := by
  classical
  apply MvPolynomial.ext
  intro t
  by_cases ht : Finsupp.weight w t < d
  · rw [← weightedBasis_repr_inr w d hw _ ⟨t, ht⟩]
    simp [Basis.repr_self, Finsupp.single_apply, coeff_monomial, Subtype.ext_iff]
  · have hcoeff : (weightedBasis w d hw (Sum.inr a)).val.polynomial.coeff t = 0 := by
      by_contra hn
      have hh := (weightedBasis w d hw (Sum.inr a)).property.2 (mem_support_iff.mpr hn)
      change Finsupp.weight w t + 1 ≤ d at hh
      omega
    rw [hcoeff, coeff_monomial]
    have hne : a.val ≠ t := by
      intro he
      exact ht (he ▸ a.property)
    simp [hne]

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FormalPolynomialCorrectionStep
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L]

noncomputable def gradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ) (v : σ → ℕ) :
    Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {P | ∀ α,
    (basisGradeProjection b w (Finsupp.weight v α)).restrictScalars ℚ (coefficients P α) = coefficients P α}
  zero_mem' := by intro α; simp only [map_zero, Finsupp.zero_apply]
  add_mem' := by
    intro P Q hP hQ α
    simp only [map_add, Finsupp.add_apply, hP α, hQ α]
  smul_mem' := by
    intro a P hP α
    simp only [map_smul, Finsupp.smul_apply, hP α]

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L]

noncomputable def shiftedGradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ)
    (v : σ → ℕ) (r : ℕ) : Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {P | ∀ α,
    (basisGradeProjection b w (Finsupp.weight v α + r)).restrictScalars ℚ
      (coefficients P α) = coefficients P α}
  zero_mem' := by intro α; simp only [map_zero, Finsupp.zero_apply]
  add_mem' := by
    intro P Q hP hQ α
    simp only [map_add, Finsupp.add_apply, hP α, hQ α]
  smul_mem' := by
    intro a P hP α
    simp only [map_smul, Finsupp.smul_apply, hP α]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CurrentPolynomialDerivativeRemoval
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

def PolynomialLiftSystemMod (V : Submodule ℚ L) (P : PolynomialGroup σ hnil)
    (S R : κ → VectorPolynomial σ ℚ L) : Prop :=
  ∀ k, S k - dualAdjoint P (R k) ∈ coefficientSubmodule V

def PolynomialDerivativeSystemMod (V : Submodule ℚ L) (P : PolynomialGroup σ hnil)
    (small rational extra : σ → VectorPolynomial σ ℚ L) : Prop :=
  ∀ i, formalLogDerivative i P - (small i + dualAdjoint P (rational i) + extra i) ∈ coefficientSubmodule V

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RelativeSquarePolynomial
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

noncomputable def relativeSquareSymbolMap :
    F.normalizedRelativeSubmodule w →ₗ[ℚ] F.squareFiltration.PolynomialSymbol w :=
  (F.squareFiltration.polynomialSymbolMap w).toLinearMap.comp (F.relativeSquareLift w hw)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SquareSymbolProjection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem squareSndSymbolMap_map_eq_zero_iff (r : F.squareFiltration.adaptedLieSubalgebra w) :
    F.squareSndSymbolMap w (F.squareFiltration.polynomialSymbolMap w r) = 0 ↔
      ∀ α, (coefficients r.val α).val.2 ∈ F.layer (Finsupp.weight w α + 1) := by
  change F.polynomialSymbolMap w
    (F.squareFiltration.filteredPolynomialMap F F.squareSnd (fun _ _ hx => hx.2.1) w r) = 0 ↔ _
  rw [F.polynomialSymbolMap_eq_zero_iff]
  change (∀ α, coefficients (VectorPolynomial.map F.squareSnd.toLinearMap r.val) α ∈
    F.layer (Finsupp.weight w α + 1)) ↔ _
  simp only [coefficients_map]
  rfl

variable (hw : ∀ i, 0 < w i)

theorem squareSndSymbolMap_relative (p : F.normalizedRelativeSubmodule w) :
    F.squareSndSymbolMap w (F.relativeSquareSymbolMap w hw p) = 0 := by
  apply (F.squareSndSymbolMap_map_eq_zero_iff w (F.relativeSquareLift w hw p)).mpr
  intro α
  change (coefficients (F.relativeSquarePolynomial w hw p) α).val.2 ∈ _
  rw [F.relativeSquarePolynomial_coefficient]
  exact (F.layer _).zero_mem

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SquareBasisGeometry
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem reducedSquareSndPolynomialMap_quotient (p : F.squareFiltration.adaptedLieSubalgebra w) :
    F.reducedSquareSndPolynomialMap w (F.reducedSquarePolynomialMap w p) =
      F.quotientTopPolynomialMap w (F.squareSndPolynomialMap w p) := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  change coefficients (VectorPolynomial.map F.reducedSquareSnd.toLinearMap
      (VectorPolynomial.map (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))).toLinearMap p.val)) α =
    coefficients (VectorPolynomial.map (lieQuotientMap (F.layerIdeal (s + 1))).toLinearMap
      (VectorPolynomial.map F.squareSnd.toLinearMap p.val)) α
  simp only [coefficients_map]
  rfl

theorem reducedSquareSndSymbolMap_quotient (x : F.squareFiltration.PolynomialSymbol w) :
    F.reducedSquareSndSymbolMap w (F.reducedSquareSymbolMap w x) =
      F.quotientTopSymbolMap w (F.squareSndSymbolMap w x) := by
  obtain ⟨p, rfl⟩ := F.squareFiltration.polynomialSymbolMap_surjective w x
  rw [F.reducedSquareSymbolMap_symbol, F.reducedSquareSndSymbolMap_symbol,
    F.squareSndSymbolMap_symbol, F.quotientTopSymbolMap_symbol,
    F.reducedSquareSndPolynomialMap_quotient]

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

noncomputable def firstCoefficientMap (F : NilpotentLieFiltration L s) (w : σ → ℕ) :
    (F.shiftedPolynomialIdeal w 1) →ₗ[ℚ] F.FirstCoefficientModule w :=
  ((F.shiftedPolynomialIdeal w 2).toSubmodule.comap
    (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype).mkQ

theorem firstCoefficientMap_eq_zero_iff (F : NilpotentLieFiltration L s) (w : σ → ℕ)
    (p : F.shiftedPolynomialIdeal w 1) :
    F.firstCoefficientMap w p = 0 ↔
      ∀ α, coefficients (p.val : VectorPolynomial σ ℚ L) α ∈ F.layer (Finsupp.weight w α + 2) :=
  Submodule.Quotient.mk_eq_zero _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def firstCoefficientHorizontal : F.FirstCoefficientModule w →ₗ[ℚ] L ⧸ F.layer 2 :=
  ((F.shiftedPolynomialIdeal w 2).toSubmodule.comap
    (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype).liftQ
    (((F.layer 2).mkQ.comp (F.adaptedCoefficientMap w 0)).comp
      (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype) (by
        intro p hp
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        change coefficients p.val.val 0 ∈ F.layer 2
        have h := hp 0
        change coefficients p.val.val 0 ∈ F.layer (Finsupp.weight w 0 + 2) at h
        simpa only [map_zero, Nat.zero_add] using h)

@[simp] theorem firstCoefficientHorizontal_map (p : F.shiftedPolynomialIdeal w 1) :
    F.firstCoefficientHorizontal w (F.firstCoefficientMap w p) =
      (F.layer 2).mkQ (coefficients p.val.val 0) := rfl

noncomputable def firstCoefficientConstant : L →ₗ[ℚ] F.FirstCoefficientModule w :=
  (F.firstCoefficientMap w).comp
    ((F.adaptedConstantLieHom w).toLinearMap.codRestrict
      (F.shiftedPolynomialIdeal w 1).toSubmodule (F.adaptedConstant_mem_shiftedIdeal w))

@[simp] theorem firstCoefficientHorizontal_constant (x : L) :
    F.firstCoefficientHorizontal w (F.firstCoefficientConstant w x) = (F.layer 2).mkQ x := by
  change (F.layer 2).mkQ (coefficients (monomial 0 x) 0) = _
  simp only [coefficients_monomial, Finsupp.single_eq_same]

noncomputable def firstCoefficientHorizontalSection : (L ⧸ F.layer 2) →ₗ[ℚ] F.FirstCoefficientModule w :=
  (F.layer 2).liftQ (F.firstCoefficientConstant w) (by
    intro x hx
    change F.firstCoefficientMap w ⟨F.adaptedConstant w x, F.adaptedConstant_mem_shiftedIdeal w x⟩ = 0
    apply (F.firstCoefficientMap_eq_zero_iff w _).mpr
    exact F.adaptedConstant_mem_shiftedPolynomialIdeal w 2 hx)

@[simp] theorem firstCoefficientHorizontalSection_mk (x : L) :
    F.firstCoefficientHorizontalSection w ((F.layer 2).mkQ x) = F.firstCoefficientConstant w x := rfl

noncomputable def normalizedFirstCoefficientMap :
    F.normalizedRelativeSubmodule w →ₗ[ℚ] F.FirstCoefficientModule w :=
  (F.firstCoefficientMap w).comp
    ((F.normalizedRelativeSubmodule w).subtype.codRestrict
      (F.shiftedPolynomialIdeal w 1).toSubmodule (fun p => p.property.1))

theorem normalizedFirstCoefficientMap_eq_zero_iff (p : F.normalizedRelativeSubmodule w) :
    F.normalizedFirstCoefficientMap w p = 0 ↔ p.val ∈ F.shiftedPolynomialIdeal w 2 :=
  F.firstCoefficientMap_eq_zero_iff w _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

noncomputable def reducedRelativeSquareSymbolMap :
    F.normalizedRelativeSubmodule w →ₗ[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w :=
  (F.reducedSquareSymbolMap w).toLinearMap.comp (F.relativeSquareSymbolMap w hw)

@[simp] theorem reducedRelativeSquareSymbolMap_apply (p : F.normalizedRelativeSubmodule w) :
    F.reducedRelativeSquareSymbolMap w hw p =
      F.reducedSquareSymbolMap w (F.relativeSquareSymbolMap w hw p) := rfl

@[simp] theorem reducedRelativeSquareSymbolMap_projection (p : F.normalizedRelativeSubmodule w) :
    F.reducedSquareSndSymbolMap w (F.reducedRelativeSquareSymbolMap w hw p) = 0 := by
  rw [F.reducedRelativeSquareSymbolMap_apply, F.reducedSquareSndSymbolMap_quotient,
    F.squareSndSymbolMap_relative, map_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def reducedSquareDifference :
    (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] L :=
  (F.squareFiltration.layerIdeal (s + 1)).toSubmodule.liftQ
    (F.squareFst.toLinearMap - F.squareSnd.toLinearMap) (by
      intro x hx
      change x.val.1 - x.val.2 = 0
      exact sub_eq_zero.mpr ((F.mem_squareFiltration_top x).mp hx).2)

@[simp] theorem reducedSquareDifference_mk (x : F.squareLieSubalgebra) :
    F.reducedSquareDifference (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)) x) =
      x.val.1 - x.val.2 := rfl

theorem reducedSquareDifference_mem_layer (j : ℕ)
    (x : F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1))
    (hx : x ∈ F.squareFiltration.quotientTop.layer j) :
    F.reducedSquareDifference x ∈ F.layer (j + 1) := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact hy.2.2

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem reducedSquareDifference_mem_two
    (x : F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) :
    F.reducedSquareDifference x ∈ F.layer 2 := by
  obtain ⟨y, rfl⟩ := lieQuotientMap_surjective (F.squareFiltration.layerIdeal (s + 1)) x
  rw [F.reducedSquareDifference_mk]
  exact (F.mem_squareLieSubalgebra y.val).mp y.property

noncomputable def reducedSquareDifferenceAdapted :
    F.squareFiltration.quotientTop.adaptedLieSubalgebra w →ₗ[ℚ] F.adaptedLieSubalgebra w :=
  ((VectorPolynomial.map F.reducedSquareDifference).comp
    (F.squareFiltration.quotientTop.adaptedLieSubalgebra w).incl.toLinearMap).codRestrict
      (F.adaptedLieSubalgebra w).toSubmodule (by
        intro p α
        change coefficients (VectorPolynomial.map F.reducedSquareDifference p.val) α ∈ _
        rw [coefficients_map]
        exact F.antitone (Nat.le_succ _) (F.reducedSquareDifference_mem_layer _ _ (p.property α)))

noncomputable def reducedSquareDifferenceRelative :
    F.squareFiltration.quotientTop.adaptedLieSubalgebra w →ₗ[ℚ] F.normalizedRelativeSubmodule w :=
  (F.reducedSquareDifferenceAdapted w).codRestrict (F.normalizedRelativeSubmodule w) (by
    intro p
    constructor
    · intro α
      change coefficients (VectorPolynomial.map F.reducedSquareDifference p.val) α ∈ _
      rw [coefficients_map]
      exact F.reducedSquareDifference_mem_layer _ _ (p.property α)
    · change coefficients (VectorPolynomial.map F.reducedSquareDifference p.val) 0 ∈ F.layer 2
      rw [coefficients_map]
      exact F.reducedSquareDifference_mem_two _)

theorem reducedSquareDifferenceRelative_coefficient
    (p : F.squareFiltration.quotientTop.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.reducedSquareDifferenceRelative w p).val.val α =
      F.reducedSquareDifference (coefficients p.val α) :=
  coefficients_map F.reducedSquareDifference p.val α

noncomputable def reducedSquareCoefficientMap :
    F.squareFiltration.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.FirstCoefficientModule w :=
  (F.squareFiltration.quotientTop.shiftedAdaptedIdeal w).toSubmodule.liftQ
    ((F.normalizedFirstCoefficientMap w).comp (F.reducedSquareDifferenceRelative w)) (by
      intro p hp
      apply (F.normalizedFirstCoefficientMap_eq_zero_iff w _).mpr
      intro α
      change coefficients (F.reducedSquareDifferenceRelative w p).val.val α ∈ _
      rw [F.reducedSquareDifferenceRelative_coefficient]
      exact F.reducedSquareDifference_mem_layer _ _ (hp α))

@[simp] theorem reducedSquareCoefficientMap_symbol
    (p : F.squareFiltration.quotientTop.adaptedLieSubalgebra w) :
    F.reducedSquareCoefficientMap w (F.squareFiltration.quotientTop.polynomialSymbolMap w p) =
      F.normalizedFirstCoefficientMap w (F.reducedSquareDifferenceRelative w p) := rfl

theorem reducedSquareDifferenceRelative_relative (hw : ∀ i, 0 < w i)
    (p : F.normalizedRelativeSubmodule w) :
    F.reducedSquareDifferenceRelative w
      (F.reducedSquarePolynomialMap w (F.relativeSquareLift w hw p)) = p := by
  apply Subtype.ext
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.reducedSquareDifferenceRelative_coefficient]
  change F.reducedSquareDifference
    (coefficients (VectorPolynomial.map
      (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))).toLinearMap
      (F.relativeSquarePolynomial w hw p)) α) = _
  rw [coefficients_map]
  change F.reducedSquareDifference
    (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
      (coefficients (F.relativeSquarePolynomial w hw p) α)) = _
  rw [F.reducedSquareDifference_mk, F.relativeSquarePolynomial_coefficient, sub_zero]

@[simp] theorem reducedSquareCoefficientMap_relative (hw : ∀ i, 0 < w i)
    (p : F.normalizedRelativeSubmodule w) :
    F.reducedSquareCoefficientMap w (F.reducedRelativeSquareSymbolMap w hw p) =
      F.normalizedFirstCoefficientMap w p := by
  change F.reducedSquareCoefficientMap w (F.squareFiltration.quotientTop.polynomialSymbolMap w
    (F.reducedSquarePolynomialMap w (F.relativeSquareLift w hw p))) = _
  rw [F.reducedSquareCoefficientMap_symbol, F.reducedSquareDifferenceRelative_relative]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealFirstCoefficientHorizontal
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

noncomputable def realAdaptedDirectionalDerivative :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) →ₗ[ℝ]
      (ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :=
  (F.adaptedDirectionalDerivative h).baseChange ℝ

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

noncomputable def realAdaptedPolynomialJet
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    DualGroup (F.adaptedPolynomialFiltration (fun _ : σ => 1)).realification.lowerCentralSeries_eq_bot :=
  ⟨dualConstantLie x + dualInfinitesimal (F.realAdaptedDirectionalDerivative h x)⟩

@[simp] theorem realAdaptedPolynomialJet_base
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    dualBaseLinear (F.realAdaptedPolynomialJet h x).coord = x := by
  change dualBaseLinear (dualConstantLie x + dualInfinitesimal _) = x
  simp only [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]

@[simp] theorem realAdaptedPolynomialJet_tangent
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    dualTangentLinear (F.realAdaptedPolynomialJet h x).coord = F.realAdaptedDirectionalDerivative h x := by
  change dualTangentLinear (dualConstantLie x + dualInfinitesimal _) = _
  simp only [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

omit [Fintype σ] [DecidableEq σ] in
noncomputable def realFullPolynomialLie (v : σ → ℕ) :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra v) →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  (F.realification.adaptedLieSubalgebra v).incl.comp (F.realAdaptedPolynomialTensor v)

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem realFullPolynomialLie_apply (v : σ → ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra v) :
    F.realFullPolynomialLie v x = F.realAdaptedPolynomialMap v x := rfl

omit [Fintype σ] [DecidableEq σ] in
noncomputable def realFullPolynomialHom (v : σ → ℕ) :
    F.RealAdaptedPolynomialGroup v →* PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot :=
  NilpotentLieBCHGroup.map (F.realFullPolynomialLie v)

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem realFullPolynomialHom_coord (v : σ → ℕ) (P : F.RealAdaptedPolynomialGroup v) :
    (F.realFullPolynomialHom v P).coord = F.realAdaptedPolynomialMap v P.coord := rfl

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def realShiftedCoefficientSubmodule (w : σ → ℕ) (k : ℕ) :
    Submodule ℝ (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :=
  (F.shiftedPolynomialIdeal w k).toSubmodule.baseChange ℝ

theorem realShiftedCoefficient_lie_mem (w : σ → ℕ) (k : ℕ)
    (x y : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) (hy : y ∈ F.realShiftedCoefficientSubmodule w k) :
    ⁅x, y⁆ ∈ F.realShiftedCoefficientSubmodule w k :=
  ((F.shiftedPolynomialIdeal w k).baseChange ℝ).lie_mem hy

abbrev RealFirstCoefficientModule (w : σ → ℕ) :=
  (F.realShiftedCoefficientSubmodule w 1) ⧸
    (F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype

noncomputable def realFirstCoefficientMap (w : σ → ℕ) :
    (F.realShiftedCoefficientSubmodule w 1) →ₗ[ℝ] F.RealFirstCoefficientModule w :=
  ((F.realShiftedCoefficientSubmodule w 2).comap
    (F.realShiftedCoefficientSubmodule w 1).subtype).mkQ

noncomputable def realFirstCoefficientAdjoint (w : σ → ℕ) (g : F.RealAdaptedPolynomialGroup w) :
    F.RealFirstCoefficientModule w ≃ₗ[ℝ] F.RealFirstCoefficientModule w :=
  invariantRealAdjointQuotient ⊤ (F.realShiftedCoefficientSubmodule w 1)
    (F.realShiftedCoefficientSubmodule w 2)
    (fun x _ y hy => F.realShiftedCoefficient_lie_mem w 1 x y hy)
    (fun x _ y hy => F.realShiftedCoefficient_lie_mem w 2 x y hy) g (by trivial)

@[simp] theorem realFirstCoefficientAdjoint_map (w : σ → ℕ) (g : F.RealAdaptedPolynomialGroup w)
    (x : F.realShiftedCoefficientSubmodule w 1) :
    F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientMap w x) =
      F.realFirstCoefficientMap w
        ⟨dualAdjoint g x.val, dualAdjoint_real_mem_of_invariant ⊤ _
          (fun a _ b hb => F.realShiftedCoefficient_lie_mem w 1 a b hb) g (by trivial) x.val x.property⟩ :=
  rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

def CoefficientBound (b : Basis ι ℝ L) (T : σ → ℝ) (M : ℝ)
    (P : VectorPolynomial σ ℚ L) : Prop :=
  ∀ α i, |b.repr (coefficients P α) i| ≤ M / monomialScale T α

def CoefficientGrid (b : Basis ι ℝ L) (l : ℕ) (P : VectorPolynomial σ ℚ L) : Prop :=
  ∀ α, (fun i => b.repr (coefficients P α) i) ∈ realDenominatorGrid l

theorem CoefficientBound.mono (b : Basis ι ℝ L) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M N : ℝ} {P : VectorPolynomial σ ℚ L} (h : CoefficientBound b T M P) (hMN : M ≤ N) :
    CoefficientBound b T N P := by
  intro α i
  exact (h α i).trans (div_le_div_of_nonneg_right hMN (monomialScale_pos T hT α).le)

end VectorPolynomial

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

noncomputable def adaptedFullPolynomialHom (F : NilpotentLieFiltration L s) (w : σ → ℕ) :
    (F.adaptedPolynomialFiltration w).Group →* PolynomialGroup σ F.lowerCentralSeries_eq_bot :=
  NilpotentLieBCHGroup.map (F.adaptedLieSubalgebra w).incl

@[simp] theorem adaptedFullPolynomialHom_coord (F : NilpotentLieFiltration L s) (w : σ → ℕ)
    (g : (F.adaptedPolynomialFiltration w).Group) :
    (F.adaptedFullPolynomialHom w g).coord = (g.coord : VectorPolynomial σ ℚ L) := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

section Modules

variable {σ ι κ L M : Type*} [AddCommGroup L] [Module ℚ L]
  [AddCommGroup M] [Module ℚ M]

noncomputable def sectionCorrectedPolynomial (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  p - VectorPolynomial.map ((S.baseChange ℝ).restrictScalars ℚ)
    (VectorPolynomial.map ((φ.baseChange ℝ).restrictScalars ℚ) p - q)

@[simp] theorem sectionCorrectedPolynomial_coefficients (φ : L →ₗ[ℚ] M)
    (S : M →ₗ[ℚ] L) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) (α : σ →₀ ℕ) :
    coefficients (sectionCorrectedPolynomial φ S p q) α =
      coefficients p α - S.baseChange ℝ
        (φ.baseChange ℝ (coefficients p α) - coefficients q α) := by
  simp only [sectionCorrectedPolynomial, map_sub, Finsupp.sub_apply, coefficients_map,
    LinearMap.restrictScalars_apply]

end Modules

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalInductionTerminal
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace VectorPolynomial

variable {σ κ K L : Type*} [AddCommGroup K] [Module ℝ K]
  [LieRing L] [LieAlgebra ℚ L]

noncomputable def basisPolynomialLift (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    K →ₗ[ℝ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) := b.constr ℝ S

@[simp] theorem basisPolynomialLift_basis (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k : κ) :
    basisPolynomialLift b S (b k) = S k := b.constr_basis ℝ S k

end VectorPolynomial

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype κ] {s : ℕ}

structure FormalInductionState (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L)
    (w : μ → ℕ) (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℚ L)
    (e : Basis κ ℚ K) (T : σ → ℝ) (j : ℕ) (p : ℝ) where
  P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot
  S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)
  R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)
  small : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)
  rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)
  k : σ → κ → ℝ
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp p
  constant_zero : coefficients P.coord 0 = 0
  mem_U : ∀ α, coefficients P.coord α ∈ U
  graded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
  horizontal : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K.baseChange ℝ
  lower_log : ∀ α d, 2 ≤ d → d < j →
    basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V.baseChange ℝ
  lower_bracket : ∀ d < j - 1, ∀ z α,
    ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), (1 : ℝ) ⊗ₜ[ℚ] (e z : L)⁆ ∈ V.baseChange ℝ
  lift_system : PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P S R
  derivative_system : PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P small rational
    (fun i => basisPolynomialLift (Pi.basisFun ℝ κ) S (k i))
  S_shift : ∀ z, S z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1
  R_shift : ∀ z, R z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1
  small_shift : ∀ i, small i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1
  rational_shift : ∀ i, rational i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1
  S_remainder : ∀ z α, coefficients (S z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] (e z : L))) α ∈
    V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule
  R_remainder : ∀ z α, coefficients (R z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] (e z : L))) α ∈
    V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule
  small_remainder : ∀ i α, coefficients (small i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule
  rational_remainder : ∀ i α, coefficients (rational i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule
  S_bound : ∀ z, CoefficientBound (b.baseChange ℝ) T (Real.exp p) (S z)
  R_grid : ∀ z, CoefficientGrid (b.baseChange ℝ) denominator (R z)
  small_bound : ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp p / T i) (small i)
  rational_grid : ∀ i, CoefficientGrid (b.baseChange ℝ) denominator (rational i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s j : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
  {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} {V K : Submodule ℚ L}
  {eK : Basis κ ℚ K} {T : σ → ℝ} {p q : ℝ}

noncomputable def FormalInductionState.enlarge
    (X : F.FormalInductionState b w U V K eK T j p) (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    F.FormalInductionState b w U V K eK T j q :=
  { X with
    denominator_bound := X.denominator_bound.trans (Real.exp_le_exp.mpr hpq)
    S_bound := fun z => (X.S_bound z).mono _ T hT (Real.exp_le_exp.mpr hpq)
    small_bound := fun i => (X.small_bound i).mono _ T hT
      (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hpq) (hT i).le) }

@[simp] theorem FormalInductionState.enlarge_P
    (X : F.FormalInductionState b w U V K eK T j p) (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    (X.enlarge hpq hT).P = X.P := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSquarefreeCoefficientBases
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def squarefreeCoefficientBasis (p : ℝ) (a : SquarefreeIndex (ReplicatedIndex bound)) :
    Basis (Fin (finrank ℚ
      (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a))) ℚ
      (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a) := by
  letI : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact chosenBoundedSubmoduleBasis D.basis ⌈Real.exp p⌉₊ _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeLayerBases
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module
open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)
  {κ : SquarefreeIndex ι → Type*} [∀ a, Fintype (κ a)]
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer π a))

noncomputable def squarefreeSupportedFinBasis (P : SquarefreeIndex ι → Prop) :
    Basis (Fin (finrank ℚ
      ((squarefreeSupportModule P).comap (F.squarefreeAdaptedSubalgebra π).incl.toLinearMap))) ℚ
      ((squarefreeSupportModule P).comap (F.squarefreeAdaptedSubalgebra π).incl.toLinearMap) := by
  classical
  exact (F.squarefreeSupportedBasis π b P).reindex
    (Fintype.equivFinOfCardEq (finrank_eq_card_basis (F.squarefreeSupportedBasis π b P)).symm)

noncomputable def squarefreeDegreeBasis (n : ℕ) :
    Basis (Fin (finrank ℚ (F.squarefreeDegreeLayer π n))) ℚ (F.squarefreeDegreeLayer π n) :=
  F.squarefreeSupportedFinBasis π b (fun a => n ≤ ∑ i, a.val i)

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ComparisonChosenLayerBasis
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

abbrev SquarefreeBasisIndex := Σ a : SquarefreeIndex (ReplicatedIndex bound),
  Fin (finrank ℚ (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a))

noncomputable def squarefreeBasis (p : ℝ) : Basis M.SquarefreeBasisIndex ℚ
    (M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :=
  M.filtration.squarefreeBasis _ (M.squarefreeCoefficientBasis p)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeSquarefreeLattice
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

def SquarefreeGridStable (p : ℝ) (B : ℕ) : Prop :=
  ∀ x ∈ coordinateGridModule (M.squarefreeBasis p) B,
    ∀ y ∈ coordinateGridModule (M.squarefreeBasis p) B,
      lieBCH (Fintype.card (ReplicatedIndex bound)) x y ∈ coordinateGridModule (M.squarefreeBasis p) B

noncomputable def squarefreeLattice (p : ℝ) (B : ℕ) (hstable : M.SquarefreeGridStable p B) :
    Subgroup (M.filtration.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).Group :=
  coordinateGridBCHSubgroup (M.squarefreeBasis p) B
    (M.filtration.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).lowerCentralSeries_eq_bot
    hstable

theorem squarefreeLattice_coordinates (p : ℝ) (B : ℕ) (hstable : M.SquarefreeGridStable p B) :
    bchSubgroupCoordinates (M.squarefreeBasis p) (M.squarefreeLattice p B hstable) = scaledIntegerGrid B :=
  coordinateGridBCHSubgroup_coordinates _ _ _ hstable

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeRealAction
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def squarefreeFinBasis (p : ℝ) : Basis (Fin (Fintype.card M.SquarefreeBasisIndex)) ℚ
    (M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :=
  (M.squarefreeBasis p).reindex (Fintype.equivFin M.SquarefreeBasisIndex)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def squarefreeModel (p : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.SquarefreeGridStable p B) :
    RationalFilteredNilmanifold (M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))
      (Fintype.card (ReplicatedIndex bound)) (Fintype.card M.SquarefreeBasisIndex) where
  filtration := M.filtration.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)
  basis := M.squarefreeFinBasis p
  layerBasis i := M.filtration.squarefreeDegreeBasis (fun j : ReplicatedIndex bound => j.1)
    (M.squarefreeCoefficientBasis p) (i.val + 1)
  lattice := M.squarefreeLattice p B hstable
  grid := B
  grid_pos := hB
  inner_grid := by
    apply bchSubgroup_inner_grid_reindex
    rw [M.squarefreeLattice_coordinates]
  outer_grid := by
    apply bchSubgroup_outer_grid_reindex
    rw [M.squarefreeLattice_coordinates]
    exact fun _ hx => scaledIntegerGrid_mem_denominatorGrid B B hx

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (p : ℝ) (B : ℕ) (hB : 0 < B)
  (hstable : M.SquarefreeGridStable p B)

noncomputable def squarefreeRealPermute (e : ReplicatedPermutation bound) :
    (M.squarefreeModel p B hB hstable).RealGroup →*
      (M.squarefreeModel p B hB hstable).RealGroup :=
  realificationMap
    (hnil := (M.squarefreeModel p B hB hstable).filtration.lowerCentralSeries_eq_bot)
    (hM := (M.squarefreeModel p B hB hstable).filtration.lowerCentralSeries_eq_bot)
    (M.filtration.replicatedLiePermute e).toLieHom

theorem squarefreeRealPermute_mul (e f : ReplicatedPermutation bound)
    (g : (M.squarefreeModel p B hB hstable).RealGroup) :
    M.squarefreeRealPermute p B hB hstable (e * f) g =
      M.squarefreeRealPermute p B hB hstable e (M.squarefreeRealPermute p B hB hstable f g) := by
  apply NilpotentLieBCHGroup.ext
  exact realificationLieHom_comp_apply _ _ _ (M.filtration.replicatedLiePermute_mul e f) g.coord

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
namespace OAI

section

open Module
open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem productProjection_lattice (i : ι) :
    (pi D).lattice ≤ (D i).lattice.comap (NilpotentLieBCHGroup.mapOfSteps (liePiEval i)) := by
  intro g hg
  exact (mem_piBCHSubgroup (fun i => (D i).filtration) (fun i => (D i).lattice) g).mp hg i

noncomputable def productProjectionHom (i : ι) : (pi D).RealGroup →* (D i).RealGroup :=
  NilpotentLieBCHGroup.realificationMap (hnil := (pi D).filtration.lowerCentralSeries_eq_bot)
    (hM := (D i).filtration.lowerCentralSeries_eq_bot) (liePiEval i)

noncomputable def productProjection (i : ι) : (pi D).Space → (D i).Space :=
  cosetMap (pi D).realLattice (D i).realLattice (productProjectionHom D i)
    (NilpotentLieBCHGroup.realificationMap_subgroup (liePiEval i) _ _ (productProjection_lattice D i))

@[simp] theorem productProjection_mk (i : ι) (g : (pi D).RealGroup) :
    productProjection D i (QuotientGroup.mk g) = QuotientGroup.mk (productProjectionHom D i g) := rfl

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.OrdinarySymbolBasisDimension
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [Fintype σ] [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

@[instance_reducible] noncomputable def ordinarySymbolBasisFintype :
    Fintype (SymbolBasisIndex (fun _ : σ => 1) ω) :=
  symbolBasisIndexFintype (fun _ : σ => 1) ω s (fun _ => Nat.zero_lt_one)
    (F.adaptedBasis_weight_le_step b ω hF)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolGradeEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def realSymbolGradeEvaluation (d : ℕ) (t : σ → ℝ) :
    F.RealPolynomialSymbol w →ₗ[ℚ] (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  (eval₂ t).comp ((F.realGradedSymbolPolynomial b ω hlayers w).toLinearMap.comp
    ((basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
      (fun z => ω z.val.2) d).restrictScalars ℚ))

@[simp] theorem realSymbolGradeEvaluation_apply (d : ℕ) (t : σ → ℝ)
    (x : F.RealPolynomialSymbol w) :
    F.realSymbolGradeEvaluation b ω hlayers w d t x =
      eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
        (basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
          (fun z => ω z.val.2) d x)) := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SimultaneousPolynomialSymbolSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

@[simp] theorem realPolynomialSymbolLift_log (g : F.RealPolynomialSymbolGroup w) :
    ((F.realPolynomialSymbolLift b ω hlayers w g).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) = F.realSymbolRepresentative b ω hlayers w g.coord := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefilteredPointwiseSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (U : LieSubalgebra ℚ F.AssociatedGraded)

noncomputable def realGradedRefiltrationLayer (j : ℕ) : Submodule ℝ (ℝ ⊗[ℚ] L) :=
  (F.gradedRefiltrationLayer U j).baseChange ℝ

theorem realGradedRefiltrationLayer_antitone : Antitone (F.realGradedRefiltrationLayer U) :=
  fun _ _ hij => Submodule.baseChange_mono ℝ (F.gradedRefiltrationLayer_antitone U hij)

theorem realGradedRefiltrationLayer_lie_mem {i j : ℕ} {v z : ℝ ⊗[ℚ] L}
    (hv : v ∈ F.realGradedRefiltrationLayer U i) (hz : z ∈ F.realGradedRefiltrationLayer U j) :
    ⁅v, z⁆ ∈ F.realGradedRefiltrationLayer U (i + j) :=
  lie_mem_real_baseChange _ _ _ (fun _ ha _ hb => F.gradedRefiltrationLayer_lie_mem U ha hb) hv hz

theorem realGradedRefiltrationLayer_terminal : F.realGradedRefiltrationLayer U (s + 1) = ⊥ := by
  rw [realGradedRefiltrationLayer, F.gradedRefiltrationLayer_terminal, Submodule.baseChange_bot]

noncomputable def realGradedRefiltrationSubalgebra : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
  realLieSubalgebraOverRat (realificationLieSubalgebra (F.gradedRefiltrationSubalgebra U))

noncomputable def realGradedRefiltration :
    NilpotentLieFiltration (F.realGradedRefiltrationSubalgebra U) s where
  layer j := ((F.realGradedRefiltrationLayer U j).restrictScalars ℚ).comap
    (F.realGradedRefiltrationSubalgebra U).incl.toLinearMap
  antitone := fun _ _ hij _ hv => F.realGradedRefiltrationLayer_antitone U hij hv
  one_eq_top := by
    apply top_unique
    intro v _
    exact v.property
  lie_mem := fun hv hz => F.realGradedRefiltrationLayer_lie_mem U hv hz
  terminal := by
    apply bot_unique
    intro v hv
    change v = 0
    apply Subtype.ext
    exact (Submodule.mem_bot ℝ).mp ((F.realGradedRefiltrationLayer_terminal U) ▸ hv)

@[simp] theorem mem_realGradedRefiltration_layer (j : ℕ)
    (v : F.realGradedRefiltrationSubalgebra U) :
    v ∈ (F.realGradedRefiltration U).layer j ↔
      (v : ℝ ⊗[ℚ] L) ∈ F.realGradedRefiltrationLayer U j := Iff.rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationBaseGrading
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

noncomputable def baseLinear : PolynomialTranslationLie σ →ₗ[ℚ] (σ → ℚ) where
  toFun x := x.base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def baseRange (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) :
    LieSubalgebra ℚ (PolynomialTranslationLie σ) :=
  { A.range.comap baseLinear with
    lie_mem' := by
      intro x y _ _
      change (0 : σ → ℚ) ∈ A.range
      exact Submodule.zero_mem _ }

omit [Fintype τ] in
@[simp] theorem mem_baseRange (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (x : PolynomialTranslationLie σ) : x ∈ baseRange A ↔ x.base ∈ A.range := Iff.rfl

noncomputable def baseRangeBase (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) :
    baseRange A →ₗ[ℚ] A.range where
  toFun x := ⟨x.val.base, x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def projectedBaseCoordinates (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (hA : Function.Injective A) : baseRange A →ₗ[ℚ] (τ → ℚ) :=
  (LinearEquiv.ofInjective A hA).symm.toLinearMap.comp (baseRangeBase A)

omit [Fintype τ] in
@[simp] theorem apply_projectedBaseCoordinates (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (hA : Function.Injective A) (x : baseRange A) :
    A (projectedBaseCoordinates A hA x) = x.val.base := by
  exact congrArg Subtype.val ((LinearEquiv.ofInjective A hA).apply_symm_apply
    ⟨x.val.base, x.property⟩)

noncomputable def projectedRestriction (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (hA : Function.Injective A) : baseRange A →ₗ⁅ℚ⁆ PolynomialTranslationLie τ where
  toFun x := ⟨projectedBaseCoordinates A hA x, polynomialLinearRestriction A x.val.polynomial⟩
  map_add' x y := by
    apply PolynomialTranslationLie.ext
    · exact map_add _ _ _
    · exact map_add _ _ _
  map_smul' r x := by
    apply PolynomialTranslationLie.ext
    · exact map_smul _ _ _
    · exact map_smul _ _ _
  map_lie' := by
    intro x y
    apply PolynomialTranslationLie.ext
    · apply hA
      rw [apply_projectedBaseCoordinates]
      change (0 : σ → ℚ) = A 0
      exact (map_zero A).symm
    · change polynomialLinearRestriction A (scalarDirectionalDerivative x.val.base y.val.polynomial -
        scalarDirectionalDerivative y.val.base x.val.polynomial) =
        scalarDirectionalDerivative (projectedBaseCoordinates A hA x)
          (polynomialLinearRestriction A y.val.polynomial) -
        scalarDirectionalDerivative (projectedBaseCoordinates A hA y)
          (polynomialLinearRestriction A x.val.polynomial)
      rw [map_sub, scalarDirectionalDerivative_linearRestriction,
        scalarDirectionalDerivative_linearRestriction,
        apply_projectedBaseCoordinates, apply_projectedBaseCoordinates]

@[simp] theorem projectedRestriction_base (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (hA : Function.Injective A) (x : baseRange A) :
    (projectedRestriction A hA x).base = projectedBaseCoordinates A hA x := rfl

@[simp] theorem projectedRestriction_polynomial (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (hA : Function.Injective A) (x : baseRange A) :
    (projectedRestriction A hA x).polynomial = polynomialLinearRestriction A x.val.polynomial := rfl

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.WeightedTranslationRealBCHCoordinates
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ : Type*} [Fintype σ]

theorem exponentialElement_action_eq_shear (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (x : weightedSubalgebra w d) :
    PolynomialTranslationGroup.actionMonoidHom
      (PolynomialTranslationGroup.exponentialElement x.val.base x.val.polynomial) =
      (polynomialShearExpAut (weightedShearEmbedding w d x)).val := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl i =>
      change PolynomialTranslationGroup.actionHom _ (X (Sum.inl i)) =
        (polynomialShearExpAut (weightedShearEmbedding w d x)).val (X (Sum.inl i))
      rw [PolynomialTranslationGroup.actionHom_X_inl, weightedShearExp_X_inl]
      rfl
  | inr u =>
      cases u
      change PolynomialTranslationGroup.actionHom _ (X (Sum.inr ())) =
        (polynomialShearExpAut (weightedShearEmbedding w d x)).val (X (Sum.inr ()))
      rw [PolynomialTranslationGroup.actionHom_X_inr,
        weightedShearExp_X_inr w d x (d+1) (Nat.le_succ d)]
      congr 2
      exact polynomialTranslate_exponentialCoordinate_series w hw x.val.base
        (weightedSupportDrop_le x.property.2)

noncomputable def bchTranslationHom (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) :
    (weightedFiltration w d hwd).Group →* PolynomialTranslationGroup σ where
  toFun g := PolynomialTranslationGroup.exponentialElement g.coord.val.base g.coord.val.polynomial
  map_one' := by
    apply PolynomialTranslationGroup.actionMonoidHom_injective
    change PolynomialTranslationGroup.actionMonoidHom
      (PolynomialTranslationGroup.exponentialElement (0 : weightedSubalgebra w d).val.base
        (0 : weightedSubalgebra w d).val.polynomial) = PolynomialTranslationGroup.actionMonoidHom 1
    rw [exponentialElement_action_eq_shear w d hw 0]
    change (weightedShearGroupHom w d hwd 1).val = PolynomialTranslationGroup.actionMonoidHom 1
    rw [map_one, map_one]
    rfl
  map_mul' g h := by
    apply PolynomialTranslationGroup.actionMonoidHom_injective
    rw [map_mul, exponentialElement_action_eq_shear w d hw,
      exponentialElement_action_eq_shear w d hw, exponentialElement_action_eq_shear w d hw]
    change (weightedShearGroupHom w d hwd (g*h)).val =
      (weightedShearGroupHom w d hwd g).val * (weightedShearGroupHom w d hwd h).val
    rw [map_mul]
    rfl

@[simp] theorem bchTranslationHom_apply (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).Group) :
    bchTranslationHom w d hw hwd g =
      PolynomialTranslationGroup.exponentialElement g.coord.val.base g.coord.val.polynomial := rfl

@[simp] theorem bchTranslationHom_action (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).Group) :
    PolynomialTranslationGroup.actionMonoidHom (bchTranslationHom w d hw hwd g) =
      (weightedShearGroupHom w d hwd g).val :=
  exponentialElement_action_eq_shear w d hw g.coord

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

theorem existsUnique_bchRealTranslation (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).realification.Group) :
    ∃! q : PolynomialTranslationGroupOver ℝ σ,
      PolynomialTranslationGroupOver.actionMonoidHom q = (weightedShearRealGroupHom w d hwd g).val := by
  obtain ⟨b, P, hb, hP⟩ := realShearEmbedding_shape w d g.coord
  exact existsUnique_translation_of_shear_exp (realShearEmbedding w d g.coord) b P hb hP

noncomputable def bchRealTranslationElement (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).realification.Group) :
    PolynomialTranslationGroupOver ℝ σ :=
  (existsUnique_bchRealTranslation w d hwd g).exists.choose

theorem bchRealTranslationElement_action (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).realification.Group) :
    PolynomialTranslationGroupOver.actionMonoidHom (bchRealTranslationElement w d hwd g) =
      (weightedShearRealGroupHom w d hwd g).val :=
  (existsUnique_bchRealTranslation w d hwd g).exists.choose_spec

noncomputable def bchRealTranslationHom (w : σ → ℕ) (d : ℕ) (hwd : ∀ i, w i ≤ d) :
    (weightedFiltration w d hwd).realification.Group →* PolynomialTranslationGroupOver ℝ σ where
  toFun := bchRealTranslationElement w d hwd
  map_one' := by
    apply PolynomialTranslationGroupOver.actionMonoidHom_injective
    rw [bchRealTranslationElement_action, map_one, map_one]
    rfl
  map_mul' g h := by
    apply PolynomialTranslationGroupOver.actionMonoidHom_injective
    rw [map_mul, bchRealTranslationElement_action, bchRealTranslationElement_action,
      bchRealTranslationElement_action, map_mul]
    rfl

@[simp] theorem bchRealTranslationHom_action (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).realification.Group) :
    PolynomialTranslationGroupOver.actionMonoidHom (bchRealTranslationHom w d hwd g) =
      (weightedShearRealGroupHom w d hwd g).val :=
  bchRealTranslationElement_action w d hwd g

theorem bchRealTranslationHom_injective (w : σ → ℕ) (d : ℕ) (hwd : ∀ i, w i ≤ d) :
    Function.Injective (bchRealTranslationHom w d hwd) := by
  intro g h heq
  apply weightedShearRealGroupHom_injective w d hwd
  apply Subtype.ext
  rw [← bchRealTranslationHom_action, ← bchRealTranslationHom_action, heq]

theorem bchRealTranslationHom_rational (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).Group) :
    bchRealTranslationHom w d hwd (NilpotentLieBCHGroup.realificationHom g) =
      PolynomialTranslationGroupOver.map (algebraMap ℚ ℝ)
        (PolynomialTranslationGroupOver.rationalEquiv (bchTranslationHom w d hw hwd g)) := by
  apply PolynomialTranslationGroupOver.actionMonoidHom_injective
  rw [bchRealTranslationHom_action]
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  have hrat : PolynomialTranslationGroupOver.actionMonoidHom
      (PolynomialTranslationGroupOver.rationalEquiv (bchTranslationHom w d hw hwd g)) =
      (weightedShearGroupHom w d hwd g).val := by
    rw [PolynomialTranslationGroupOver.rationalEquiv_action, bchTranslationHom_action]
  have hmap := PolynomialTranslationGroupOver.map_actionHom (algebraMap ℚ ℝ)
    (PolynomialTranslationGroupOver.rationalEquiv (bchTranslationHom w d hw hwd g)) (X i)
  have hreal := weightedShearRealGroupHom_rational w d hwd g (X i)
  simp only [MvPolynomial.map_X] at hmap hreal
  change (weightedShearRealGroupHom w d hwd
    (NilpotentLieBCHGroup.realificationHom g)).val (X i) =
    PolynomialTranslationGroupOver.actionHom _ (X i)
  rw [hreal, ← hmap]
  congr 1
  exact (congrArg (fun f : MvPolynomial (σ ⊕ Unit) ℚ ≃ₐ[ℚ]
    MvPolynomial (σ ⊕ Unit) ℚ => f (X i)) hrat).symm

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTranslationIntegralAction
namespace OAI

section

namespace Erdos3.PolynomialTranslationGroup

open _root_.MvPolynomial
variable {σ : Type*}

noncomputable def fromInteger :
    PolynomialTranslationGroupOver ℤ σ →* PolynomialTranslationGroup σ :=
  PolynomialTranslationGroupOver.rationalEquiv.symm.toMonoidHom.comp
    (PolynomialTranslationGroupOver.map (Int.castRingHom ℚ))

@[simp] theorem fromInteger_base (g : PolynomialTranslationGroupOver ℤ σ) (i : σ) :
    (fromInteger g).base i = (g.base i : ℚ) := rfl

@[simp] theorem fromInteger_polynomial (g : PolynomialTranslationGroupOver ℤ σ) :
    (fromInteger g).polynomial = MvPolynomial.map (Int.castRingHom ℚ) g.polynomial := rfl

noncomputable def integralGroup : Subgroup (PolynomialTranslationGroup σ) := fromInteger.range

theorem mem_integralGroup_iff (g : PolynomialTranslationGroup σ) :
    g ∈ integralGroup ↔ (∀ i, ∃ z : ℤ, g.base i = (z : ℚ)) ∧
      g.polynomial ∈ integerCoefficientPolynomials σ := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨fun i => ⟨h.base i, rfl⟩, ⟨h.polynomial, rfl⟩⟩
  · rintro ⟨hb, P, hP⟩
    choose b hb using hb
    refine ⟨⟨b, P⟩, ?_⟩
    apply PolynomialTranslationGroup.ext
    · exact (funext hb).symm
    · exact hP

theorem integralGroup_action_integral {g : PolynomialTranslationGroup σ}
    (hg : g ∈ integralGroup) (i : σ ⊕ Unit) :
    actionMonoidHom g (X i) ∈ integerCoefficientPolynomials (σ ⊕ Unit) := by
  obtain ⟨h, rfl⟩ := hg
  refine ⟨PolynomialTranslationGroupOver.actionHom h (X i), ?_⟩
  change MvPolynomial.map (Int.castRingHom ℚ)
    (PolynomialTranslationGroupOver.actionHom h (X i)) = _
  rw [PolynomialTranslationGroupOver.map_actionHom, MvPolynomial.map_X]
  rfl

theorem mem_integralGroup_iff_action (g : PolynomialTranslationGroup σ) :
    g ∈ integralGroup ↔
      ∀ i, actionMonoidHom g (X i) ∈ integerCoefficientPolynomials (σ ⊕ Unit) := by
  refine ⟨fun hg => integralGroup_action_integral hg, ?_⟩
  intro hg
  apply (mem_integralGroup_iff g).mpr
  have hb : ∀ i, ∃ z : ℤ, g.base i = (z : ℚ) := by
    intro i
    apply (integerCoefficientPolynomials_C_iff (σ := σ ⊕ Unit) (g.base i)).mp
    have h := (integerCoefficientPolynomials (σ ⊕ Unit)).sub_mem
      (hg (Sum.inl i)) (integerCoefficientPolynomials_X (Sum.inl i))
    change actionHom g (X (Sum.inl i)) - X (Sum.inl i) ∈ _ at h
    simpa only [actionHom_X_inl, add_sub_cancel_left] using h
  refine ⟨hb, ?_⟩
  apply (integerCoefficientPolynomials_translate_iff g.base hb g.polynomial).mp
  apply (integerCoefficientPolynomials_rename_iff Sum.inl Sum.inl_injective _).mp
  have h := (integerCoefficientPolynomials (σ ⊕ Unit)).sub_mem
    (hg (Sum.inr ())) (integerCoefficientPolynomials_X (Sum.inr ()))
  change actionHom g (X (Sum.inr ())) - X (Sum.inr ()) ∈ _ at h
  simpa only [actionHom_X_inr, add_sub_cancel_left] using h

end Erdos3.PolynomialTranslationGroup

namespace Erdos3.PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]

theorem bchTranslationHom_mem_integralGroup_iff (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).Group) :
    bchTranslationHom w d hw hwd g ∈ PolynomialTranslationGroup.integralGroup ↔
      weightedShearGroupHom w d hwd g ∈ integerWeightedLoweringSubgroup (shearWeight w d) := by
  rw [PolynomialTranslationGroup.mem_integralGroup_iff_action, bchTranslationHom_action]
  rfl

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedTranslationLattice
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ : Type*} [Fintype σ]

noncomputable def weightedTranslationLattice (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) : Subgroup (weightedFiltration w d hwd).Group :=
  (integerWeightedLoweringSubgroup (shearWeight w d)).comap (weightedShearGroupHom w d hwd)

@[simp] theorem mem_weightedTranslationLattice (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).Group) :
    g ∈ weightedTranslationLattice w d hwd ↔
      polynomialShearExpAut (weightedShearEmbedding w d g.coord) ∈
        integerWeightedLoweringSubgroup (shearWeight w d) := Iff.rfl

variable (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
  (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

theorem weightedTranslationLattice_inner_grid :
    scaledIntegerGrid d.factorial ⊆
      bchSubgroupCoordinates (weightedBasis w d hw) (weightedTranslationLattice w d hwd) := by
  intro x hx
  let X := (weightedBasis w d hw).equivFun.symm x
  have hX : (weightedBasis w d hw).equivFun X ∈ scaledIntegerGrid d.factorial := by
    simpa only [X,LinearEquiv.apply_symm_apply] using hx
  have hI := weightedBasis_scaledGrid_normalize w d hw d.factorial (Nat.factorial_pos d) X hX
  have he := polynomialShear_factorial_exp_integral d (shearWeight_le w d hwd)
    ((d.factorial : ℚ)⁻¹ • weightedShearEmbedding w d X) hI
  have hc : (d.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  rw [smul_smul,mul_inv_cancel₀ hc,one_smul] at he
  exact he

theorem weightedTranslationLattice_outer_grid :
    bchSubgroupCoordinates (weightedBasis w d hw) (weightedTranslationLattice w d hwd) ⊆
      denominatorGrid d.factorial := by
  intro x hx
  let X := (weightedBasis w d hw).equivFun.symm x
  have hE : polynomialShearExpAut (weightedShearEmbedding w d X) ∈
      integerWeightedLoweringSubgroup (shearWeight w d) := hx
  have hI (i : σ ⊕ Unit) := polynomialShear_factorial_log_integral d (shearWeight_le w d hwd)
    (polynomialShearExpAut (weightedShearEmbedding w d X)) hE i
  simp only [polynomialShearLog_exp] at hI
  have h := (weightedBasis_denominatorGrid_iff w d hw d.factorial X).mpr hI
  simpa only [X,LinearEquiv.apply_symm_apply] using h

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedTranslationOrderedBasis
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (d : ℕ)
  (hw : ∀ i, 0 < w i) [Fintype (WeightedBasisIndex w d)]

noncomputable def weightedIndexOrder :
    WeightedBasisIndex w d ≃ Fin (Fintype.card (WeightedBasisIndex w d)) :=
  let ρ := Fintype.equivFin (WeightedBasisIndex w d)
  let u := fun j => weightedBasisGrade w d (ρ.symm j)
  ρ.trans (Tuple.sort u).symm

noncomputable def weightedOrderedBasis :
    Basis (Fin (Fintype.card (WeightedBasisIndex w d))) ℚ (weightedSubalgebra w d) :=
  (weightedBasis w d hw).reindex (weightedIndexOrder w d)

noncomputable def weightedOrderedGrade (j : Fin (Fintype.card (WeightedBasisIndex w d))) : ℕ :=
  weightedBasisGrade w d ((weightedIndexOrder w d).symm j)

theorem weightedOrderedBasis_layers (hwd : ∀ i, w i ≤ d) (r : ℕ) :
    (weightedFiltration w d hwd).layer r = Submodule.span ℚ
      (weightedOrderedBasis w d hw '' {j | r ≤ weightedOrderedGrade w d j}) := by
  change (weightedFiltration w d hwd).layer r = Submodule.span ℚ
    (((weightedBasis w d hw).reindex (weightedIndexOrder w d)) ''
      {j | r ≤ weightedBasisGrade w d ((weightedIndexOrder w d).symm j)})
  rw [basis_reindex_span_weights, ← weightedFiltration_layer_eq_span w d hw hwd r]

noncomputable def weightedLayerBasis (hwd : ∀ i, w i ≤ d) (r : ℕ) :
    Basis {j : Fin (Fintype.card (WeightedBasisIndex w d)) // r ≤ weightedOrderedGrade w d j}
      ℚ ((weightedFiltration w d hwd).layer r) :=
  supportedSubmoduleBasis (weightedOrderedBasis w d hw) ((weightedFiltration w d hwd).layer r)
    {j | r ≤ weightedOrderedGrade w d j} (weightedOrderedBasis_layers w d hw hwd r)

noncomputable def weightedLayerIndexEquiv (hwd : ∀ i, w i ≤ d) (r : ℕ) :
    {j : Fin (Fintype.card (WeightedBasisIndex w d)) // r ≤ weightedOrderedGrade w d j} ≃
      Fin (finrank ℚ ((weightedFiltration w d hwd).layer r)) := by
  classical
  exact Fintype.equivFinOfCardEq (finrank_eq_card_basis (weightedLayerBasis w d hw hwd r)).symm

noncomputable def weightedLayerFinBasis (hwd : ∀ i, w i ≤ d) (r : ℕ) :
    Basis (Fin (finrank ℚ ((weightedFiltration w d hwd).layer r)))
      ℚ ((weightedFiltration w d hwd).layer r) :=
  (weightedLayerBasis w d hw hwd r).reindex (weightedLayerIndexEquiv w d hw hwd r)

@[simp] theorem weightedOrderedBasis_repr (x : weightedSubalgebra w d)
    (i : Fin (Fintype.card (WeightedBasisIndex w d))) :
    (weightedOrderedBasis w d hw).repr x i =
      (weightedBasis w d hw).repr x ((weightedIndexOrder w d).symm i) :=
  Basis.repr_reindex_apply _ _ _ _

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.WeightedTranslationNilmanifold
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module
variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

theorem weightedOrderedBasis_inner_grid :
    scaledIntegerGrid d.factorial ⊆
      bchSubgroupCoordinates (weightedOrderedBasis w d hw) (weightedTranslationLattice w d hwd) :=
  bchSubgroup_inner_grid_reindex (weightedBasis w d hw) (weightedIndexOrder w d) _
    (weightedTranslationLattice_inner_grid w d hw hwd)

theorem weightedOrderedBasis_outer_grid :
    bchSubgroupCoordinates (weightedOrderedBasis w d hw) (weightedTranslationLattice w d hwd) ⊆
      denominatorGrid d.factorial :=
  bchSubgroup_outer_grid_reindex (weightedBasis w d hw) (weightedIndexOrder w d) _
    (weightedTranslationLattice_outer_grid w d hw hwd)

noncomputable def weightedTranslationNilmanifold :
    RationalFilteredNilmanifold (weightedSubalgebra w d) d (Fintype.card (WeightedBasisIndex w d)) where
  filtration := weightedFiltration w d hwd
  basis := weightedOrderedBasis w d hw
  layerBasis i := weightedLayerFinBasis w d hw hwd (i.val+1)
  lattice := weightedTranslationLattice w d hwd
  grid := d.factorial
  grid_pos := Nat.factorial_pos d
  inner_grid := weightedOrderedBasis_inner_grid w d hw hwd
  outer_grid := weightedOrderedBasis_outer_grid w d hw hwd

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedTranslationResidueLattice
namespace OAI

section

namespace Erdos3

variable {B : Type*}

noncomputable def integerTranslationResidueSubgroup (M : ℕ) :
    Subgroup (PolynomialTranslationGroupOver ℤ B) where
  carrier := {γ | ∀ i, (γ.base i : ZMod M) = 0}
  one_mem' := by intro i; simp
  mul_mem' := by
    intro a b ha hb i
    simp only [PolynomialTranslationGroupOver.base_mul, Pi.add_apply, Int.cast_add,
      ha i, hb i, add_zero]
  inv_mem' := by
    intro a ha i
    simp only [PolynomialTranslationGroupOver.base_inv, Pi.neg_apply, Int.cast_neg,
      ha i, neg_zero]

@[simp] theorem mem_integerTranslationResidueSubgroup (M : ℕ)
    (γ : PolynomialTranslationGroupOver ℤ B) :
    γ ∈ integerTranslationResidueSubgroup M ↔ ∀ i, (γ.base i : ZMod M) = 0 := Iff.rfl

noncomputable def integerPolynomialTranslationResidueCover (M : ℕ) :
    Subgroup (PolynomialTranslationGroupOver ℝ B) :=
  (integerTranslationResidueSubgroup (B := B) M).map
    (PolynomialTranslationGroupOver.map (Int.castRingHom ℝ))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TwistedBufferedTranslationPhase
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ}

noncomputable def bufferedTranslationTerm (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ) : ℂ :=
  (Ψ.value (fun i => g.base i - (β i : ℝ)) : ℂ) *
    (Real.fourierChar (translationPhaseArgument D₀ g (fun i => (β i : ℝ))) : ℂ)

noncomputable def bufferedTranslationPhase (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) : ℂ :=
  ∑' β : Fin m → ℤ, bufferedTranslationTerm Ψ D₀ g β

theorem bufferedTranslationTerm_integer_lattice (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m))
    (γ : PolynomialTranslationGroupOver ℤ (Fin m)) (β : Fin m → ℤ) :
    bufferedTranslationTerm Ψ D₀
      (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ) (β + γ.base) =
        bufferedTranslationTerm Ψ D₀ g β := by
  unfold bufferedTranslationTerm
  have hweight : (fun i =>
      (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ).base i -
        ((β + γ.base) i : ℝ)) = (fun i => g.base i - (β i : ℝ)) := by
    funext i
    simp only [PolynomialTranslationGroupOver.base_mul, Pi.add_apply,
      PolynomialTranslationGroupOver.map_base, Int.cast_add]
    change g.base i + (γ.base i : ℝ) - ((β i : ℝ) + (γ.base i : ℝ)) = _
    ring
  rw [hweight]
  congr 1
  exact translationPhaseArgument_fourier_integer D₀ g γ.base β γ.polynomial

theorem bufferedTranslationPhase_integer_lattice (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m))
    (γ : PolynomialTranslationGroupOver ℤ (Fin m)) :
    bufferedTranslationPhase Ψ D₀
      (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ) =
        bufferedTranslationPhase Ψ D₀ g := by
  unfold bufferedTranslationPhase
  have he := (Equiv.addRight γ.base).tsum_eq (bufferedTranslationTerm Ψ D₀
    (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ))
  refine he.symm.trans (tsum_congr fun β => ?_)
  exact bufferedTranslationTerm_integer_lattice Ψ D₀ g γ β

theorem bufferedTranslationPhase_integerSubgroup (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g γ : PolynomialTranslationGroupOver ℝ (Fin m))
    (hγ : γ ∈ integerPolynomialTranslationSubgroup) :
    bufferedTranslationPhase Ψ D₀ (g * γ) = bufferedTranslationPhase Ψ D₀ g := by
  obtain ⟨γ, rfl⟩ := hγ
  exact bufferedTranslationPhase_integer_lattice Ψ D₀ g γ

noncomputable def bufferedTranslationQuotientPhase (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ) :
    (PolynomialTranslationGroupOver ℝ (Fin m) ⧸ integerPolynomialTranslationSubgroup) → ℂ :=
  Quotient.lift (bufferedTranslationPhase Ψ D₀) (fun g h hgh => by
    have hi := bufferedTranslationPhase_integerSubgroup Ψ D₀ g (g⁻¹ * h)
      (QuotientGroup.leftRel_apply.mp hgh)
    simpa only [mul_inv_cancel_left] using hi.symm)

@[simp] theorem bufferedTranslationQuotientPhase_mk (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ) (g : PolynomialTranslationGroupOver ℝ (Fin m)) :
    bufferedTranslationQuotientPhase Ψ D₀ (QuotientGroup.mk g) = bufferedTranslationPhase Ψ D₀ g := rfl

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ} (M : ℕ)

noncomputable def twistedBufferedTranslationTerm (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ) : ℂ :=
  T (fun i => g.base i - (β i : ℝ)) (fun i => (β i : ZMod M)) *
    bufferedTranslationTerm Ψ D₀ g β

noncomputable def twistedBufferedTranslationPhase (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) : ℂ :=
  ∑' β : Fin m → ℤ, twistedBufferedTranslationTerm M Ψ D₀ T g β

theorem twistedBufferedTranslationTerm_integer_lattice (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m))
    (γ : PolynomialTranslationGroupOver ℤ (Fin m))
    (hγ : γ ∈ integerTranslationResidueSubgroup M) (β : Fin m → ℤ) :
    twistedBufferedTranslationTerm M Ψ D₀ T
      (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ) (β + γ.base) =
        twistedBufferedTranslationTerm M Ψ D₀ T g β := by
  rw [twistedBufferedTranslationTerm, bufferedTranslationTerm_integer_lattice]
  have hx : (fun i =>
      (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ).base i -
        ((β + γ.base) i : ℝ)) = (fun i => g.base i - (β i : ℝ)) := by
    funext i
    simp only [PolynomialTranslationGroupOver.base_mul, Pi.add_apply,
      PolynomialTranslationGroupOver.map_base, Int.cast_add]
    change g.base i + (γ.base i : ℝ) - ((β i : ℝ) + (γ.base i : ℝ)) = _
    ring
  have hr : (fun i => ((β + γ.base) i : ZMod M)) = (fun i => (β i : ZMod M)) := by
    funext i
    simp only [Pi.add_apply, Int.cast_add, hγ i, add_zero]
  rw [hx, hr]
  rfl

theorem twistedBufferedTranslationPhase_integer_lattice (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m))
    (γ : PolynomialTranslationGroupOver ℤ (Fin m))
    (hγ : γ ∈ integerTranslationResidueSubgroup M) :
    twistedBufferedTranslationPhase M Ψ D₀ T
      (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ) =
        twistedBufferedTranslationPhase M Ψ D₀ T g := by
  unfold twistedBufferedTranslationPhase
  have he := (Equiv.addRight γ.base).tsum_eq (twistedBufferedTranslationTerm M Ψ D₀ T
    (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ))
  exact he.symm.trans (tsum_congr fun β =>
    twistedBufferedTranslationTerm_integer_lattice M Ψ D₀ T g γ hγ β)

theorem twistedBufferedTranslationPhase_residueCover (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g γ : PolynomialTranslationGroupOver ℝ (Fin m))
    (hγ : γ ∈ integerPolynomialTranslationResidueCover M) :
    twistedBufferedTranslationPhase M Ψ D₀ T (g * γ) =
      twistedBufferedTranslationPhase M Ψ D₀ T g := by
  obtain ⟨γ, hγ, rfl⟩ := hγ
  exact twistedBufferedTranslationPhase_integer_lattice M Ψ D₀ T g γ hγ

noncomputable def twistedBufferedTranslationQuotientPhase (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) :
    (PolynomialTranslationGroupOver ℝ (Fin m) ⧸ integerPolynomialTranslationResidueCover M) → ℂ :=
  Quotient.lift (twistedBufferedTranslationPhase M Ψ D₀ T) (fun g h hgh => by
    have hi := twistedBufferedTranslationPhase_residueCover M Ψ D₀ T g (g⁻¹ * h)
      (QuotientGroup.leftRel_apply.mp hgh)
    simpa only [mul_inv_cancel_left] using hi.symm)

@[simp] theorem twistedBufferedTranslationQuotientPhase_mk (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) :
    twistedBufferedTranslationQuotientPhase M Ψ D₀ T (QuotientGroup.mk g) =
      twistedBufferedTranslationPhase M Ψ D₀ T g := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTwistedTranslationLipschitz
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
  [Fintype (WeightedBasisIndex w d)]
  [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

noncomputable def translationDisplacementNN : ℝ≥0 :=
  ⟨weightedTranslationDisplacementConstant d m (Fintype.card (WeightedBasisIndex w d)),
    (weightedTranslationDisplacementConstant_pos _ _ _).le⟩

noncomputable def bufferedTranslationTermLip (Ψ : PatchKernel m) (M : ℝ≥0) : ℝ≥0 :=
  let C := translationDisplacementNN w d
  max (8 * C) ((Ψ.lip + ⟨2 * Real.pi, by positivity⟩ * (1 + M * m * d)) * C)

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationRealPureFactors
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

noncomputable def polynomialRealElement (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (P : weightedSupportLT (R := ℝ) w d) : ℝ ⊗[ℚ] weightedSubalgebra w d := by
  letI := weightedBasisIndex_finite w d hw
  exact ((weightedBasis w d hw).baseChange ℝ).equivFun.symm
    (Sum.elim (fun _ => 0) (fun a => P.val.coeff a.val))

@[simp] theorem polynomialRealElement_repr (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (P : weightedSupportLT (R := ℝ) w d) (a : WeightedBasisIndex w d) :
    ((weightedBasis w d hw).baseChange ℝ).repr (polynomialRealElement w d hw P) a =
      Sum.elim (fun _ => 0) (fun a => P.val.coeff a.val) a := by
  let := weightedBasisIndex_finite w d hw
  exact congrFun (((weightedBasis w d hw).baseChange ℝ).equivFun.apply_symm_apply _) a

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorTranslationDegreeSymbol
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

variable {U B : Type*}

noncomputable def translationBaseCoordinatePolynomial
    (w : B → ℕ) (d : ℕ) (A : B → MvPolynomial U ℝ) :
    WeightedBasisIndex w d → MvPolynomial U ℝ :=
  Sum.elim A (fun _ => 0)

noncomputable def translationPolynomialCoordinatePolynomial
    (w : B → ℕ) (d : ℕ) (P : MvPolynomial (U ⊕ B) ℝ) :
    WeightedBasisIndex w d → MvPolynomial U ℝ :=
  Sum.elim (fun _ => 0) (fun α => polynomialSlotCoefficient α.val P)

theorem translationBaseCoordinatePolynomial_adapted
    (w : B → ℕ) (d : ℕ) (A : B → MvPolynomial U ℝ)
    (hA : ∀ i, (A i).totalDegree ≤ w i) (i : WeightedBasisIndex w d) :
    translationBaseCoordinatePolynomial w d A i ∈
      weightedSupportLE (fun _ : U => 1) (weightedBasisGrade w d i) := by
  cases i with
  | inl i => exact (mem_weightedSupportLE_one_iff _ _).mpr (hA i)
  | inr α => exact Submodule.zero_mem _

theorem translationPolynomialCoordinatePolynomial_adapted
    (w : B → ℕ) (d : ℕ) (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (i : WeightedBasisIndex w d) :
    translationPolynomialCoordinatePolynomial w d P i ∈
      weightedSupportLE (fun _ : U => 1) (weightedBasisGrade w d i) := by
  cases i with
  | inl i => exact Submodule.zero_mem _
  | inr α => exact polynomialSlotCoefficient_degree (fun _ : U => 1) w hP α.val

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

noncomputable def translationBasePolynomialOrbit
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) := by
  letI := weightedBasisIndex_finite w d hw
  letI : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  exact (weightedFiltration w d hwd).realCoordinatePolynomialOrbit
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationBaseCoordinatePolynomial w d A)
    (translationBaseCoordinatePolynomial_adapted w d A hA)

noncomputable def translationPurePolynomialOrbit
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) := by
  letI := weightedBasisIndex_finite w d hw
  letI : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  exact (weightedFiltration w d hwd).realCoordinatePolynomialOrbit
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationPolynomialCoordinatePolynomial w d P)
    (translationPolynomialCoordinatePolynomial_adapted w d P hP)

@[simp] theorem translationBasePolynomialOrbit_log
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    letI := weightedBasisIndex_finite w d hw
    letI : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
    (translationBasePolynomialOrbit w d hw hwd A hA).log =
      VectorPolynomial.ofCoordinates (R := ℚ) ((weightedBasis w d hw).baseChange ℝ)
        (translationBaseCoordinatePolynomial w d A) := rfl

@[simp] theorem translationPurePolynomialOrbit_log
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    letI := weightedBasisIndex_finite w d hw
    letI : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
    (translationPurePolynomialOrbit w d hw hwd P hP).log =
      VectorPolynomial.ofCoordinates (R := ℚ) ((weightedBasis w d hw).baseChange ℝ)
        (translationPolynomialCoordinatePolynomial w d P) := rfl

@[simp] theorem translationBasePolynomialOrbit_coordinate
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (i : WeightedBasisIndex w d) :
    VectorPolynomial.coordinate (((weightedBasis w d hw).baseChange ℝ).coord i).toAddMonoidHom
      (translationBasePolynomialOrbit w d hw hwd A hA).log =
        translationBaseCoordinatePolynomial w d A i := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  exact (weightedFiltration w d hwd).realCoordinatePolynomialOrbit_coordinate
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationBaseCoordinatePolynomial w d A)
    (translationBaseCoordinatePolynomial_adapted w d A hA) i

@[simp] theorem translationPurePolynomialOrbit_coordinate
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (i : WeightedBasisIndex w d) :
    VectorPolynomial.coordinate (((weightedBasis w d hw).baseChange ℝ).coord i).toAddMonoidHom
      (translationPurePolynomialOrbit w d hw hwd P hP).log =
        translationPolynomialCoordinatePolynomial w d P i := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  exact (weightedFiltration w d hwd).realCoordinatePolynomialOrbit_coordinate
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationPolynomialCoordinatePolynomial w d P)
    (translationPolynomialCoordinatePolynomial_adapted w d P hP) i

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module VectorPolynomial
open NilpotentLieFiltration
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

noncomputable def translationPolynomialSymbolHom
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) :
    (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) →*
      (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1) :=
  ((weightedFiltration w d hwd).realPolynomialSymbolHom
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)).comp
      ((weightedFiltration w d hwd).realification.polynomialOrbitCoordinates
        (fun _ : U => 1)).toMonoidHom

@[simp] theorem translationPolynomialSymbolHom_coord
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (p : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1)) :
    (translationPolynomialSymbolHom w d hw hwd p).coord =
      (weightedFiltration w d hwd).realSymbolOfPolynomial
        (weightedBasis w d hw) (weightedBasisGrade w d)
        (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1) p.log := rfl

noncomputable def translationPolynomialSymbolLift
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (x : (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) :=
  ((weightedFiltration w d hwd).realification.polynomialOrbitCoordinates
    (fun _ : U => 1)).symm
      ((weightedFiltration w d hwd).realPolynomialSymbolLift
        (weightedBasis w d hw) (weightedBasisGrade w d)
        (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1) x)

@[simp] theorem translationPolynomialSymbolLift_log
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (x : (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (translationPolynomialSymbolLift w d hw hwd x).log =
      (weightedFiltration w d hwd).realSymbolRepresentative
        (weightedBasis w d hw) (weightedBasisGrade w d)
        (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1) x.coord := rfl

@[simp] theorem translationPolynomialSymbolHom_lift
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (x : (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1)) :
    translationPolynomialSymbolHom w d hw hwd
      (translationPolynomialSymbolLift w d hw hwd x) = x := by
  simp only [translationPolynomialSymbolHom, translationPolynomialSymbolLift,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    realPolynomialSymbolHom_lift]

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedTranslationLatticePhase
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

theorem realLattice_translation_integral
    {g : (weightedFiltration w d hwd).realification.Group}
    (hg : g ∈ (weightedTranslationNilmanifold w d hw hwd).realLattice) :
    bchRealTranslationHom w d hwd g ∈ integerPolynomialTranslationSubgroup := by
  change g ∈ (weightedTranslationLattice w d hwd).map NilpotentLieBCHGroup.realificationHom at hg
  obtain ⟨r,hr,rfl⟩ := hg
  have hi : bchTranslationHom w d hw hwd r ∈ PolynomialTranslationGroup.integralGroup :=
    (bchTranslationHom_mem_integralGroup_iff w d hw hwd r).mpr hr
  obtain ⟨z,hz⟩ := hi
  refine ⟨z,?_⟩
  rw [bchRealTranslationHom_rational w d hw hwd, ← hz]
  apply PolynomialTranslationGroupOver.ext
  · funext i
    change (z.base i : ℝ) = ((z.base i : ℚ) : ℝ)
    simp
  · change MvPolynomial.map (Int.castRingHom ℝ) z.polynomial =
      MvPolynomial.map (algebraMap ℚ ℝ) (MvPolynomial.map (Int.castRingHom ℚ) z.polynomial)
    rw [MvPolynomial.map_map]
    congr 1

noncomputable def weightedTranslationPhaseQuotientMap :
    (weightedTranslationNilmanifold w d hw hwd).Space →
      (PolynomialTranslationGroupOver ℝ σ ⧸ integerPolynomialTranslationSubgroup) :=
  Quotient.map (bchRealTranslationHom w d hwd) (by
    intro a b hab
    apply QuotientGroup.leftRel_apply.mpr
    have h := realLattice_translation_integral w d hw hwd (QuotientGroup.leftRel_apply.mp hab)
    simpa only [map_mul,map_inv] using h)

@[simp] theorem weightedTranslationPhaseQuotientMap_mk
    (g : (weightedFiltration w d hwd).realification.Group) :
    weightedTranslationPhaseQuotientMap w d hw hwd (QuotientGroup.mk g) =
      QuotientGroup.mk (bchRealTranslationHom w d hwd g) := rfl

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledComparisonModel
namespace OAI

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

def pairToPi : (L × L) →ₗ⁅ℚ⁆ (Fin 2 → L) :=
  liePiMap ![LieHom.fst ℚ L L, LieHom.snd ℚ L L]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.WeightedTranslationBufferedCentralFrequency
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

noncomputable def centralConstantPolynomial (w : σ → ℕ) (d : ℕ) (hd : 0 < d)
    (t : ℝ) : weightedSupportLT (R := ℝ) w d :=
  ⟨C t, (monomial_mem_restrictSupport ℝ).mpr (Or.inl (by simpa using hd))⟩

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerAffinePullbackHom
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

structure NativeIntegerModelFamily {σ I : Type*} (w : σ → ℕ)
    (degree : ℕ) (p : ℝ) (f : I → (σ → ℤ) → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : I → model.Niltest w
  norm : ∀ i, (test i).normBound ≤ 1
  complexity : ∀ i, (test i).ComplexityLE p
  normalized : ∀ i, model.filtration.realification.polynomialOrbitEval w 0 (test i).orbit = 1
  eval : ∀ i x, (test i).eval x = f i x

attribute [local instance] NativeIntegerModelFamily.lie NativeIntegerModelFamily.algebra
  NativeIntegerModelFamily.topology NativeIntegerModelFamily.topologicalAdd
  NativeIntegerModelFamily.continuousSMul NativeIntegerModelFamily.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeIntegerExpansion {σ : Type*} (w : σ → ℕ)
    (s : ℕ) (p : ℝ) (f : (σ → ℤ) → ℂ) where
  count : ℕ
  count_bound : (count : ℝ) ≤ Real.exp p
  L : Fin count → Type
  [lie : ∀ i, LieRing (L i)]
  [algebra : ∀ i, LieAlgebra ℚ (L i)]
  dim : Fin count → ℕ
  [topology : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
  [topologicalAdd : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [continuousSMul : ∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)]
  [hausdorff : ∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  model : ∀ i, RationalFilteredNilmanifold (L i) s (dim i)
  test : ∀ i, (model i).Niltest w
  complexity : ∀ i, (test i).ComplexityLE p
  coefficient : Fin count → ℂ
  cost : (∑ i, ‖coefficient i‖) ≤ Real.exp p
  eval : ∀ x, f x = ∑ i, coefficient i * (test i).eval x

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeIntegerModelFamily.lie NativeIntegerModelFamily.algebra
  NativeIntegerModelFamily.topology NativeIntegerModelFamily.topologicalAdd
  NativeIntegerModelFamily.continuousSMul NativeIntegerModelFamily.hausdorff

end Erdos3

end

end OAI
end


