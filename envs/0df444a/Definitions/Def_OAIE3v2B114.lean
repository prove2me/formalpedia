-- Prove2me | Definitions.Def_OAIE3v2B114
-- name    : OAIE3v2B114
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:35:00.714269+00:00
-- url     : https://prove2.me/theorems/6eec1a7c-8153-4cab-9e0e-5b158c3276e6
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 116 of 311
-- statement:
--   Definitions bundle 116 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B101`, `OAIE3v2B102` of this split.
--
--   Modules: `Estimates/FastCoefficientImage.lean`, `Estimates/FreeWeightedEvaluationBounds.lean`, `Estimates/ProductOrbitCongruence.lean`, `Estimates/ProjectedNativeCoefficient.lean`, `Estimates/ProjectedPointwiseCoefficient.lean`, `Estimates/QuotientTopSymbol.lean`, `Estimates/ReducedSquareSymbol.lean`, `Estimates/ShiftedGradedCalculus.lean`, `Estimates/SquareSymbolRelative.lean`, `Estimates/SymbolFastMembership.lean`, `Estimates/WeightedTranslationAssociatedGraded.lean`, `Fourier/FourierLawTransport.lean`, `Lattices/WeightedCubeIntegerSupport.lean`, `Lattices/WeightedSliceIntegerImage.lean`, `Linear/AssociatedGradedBasisIndependence.lean`, `Linear/DualLogarithmicDifferential.lean`, `Linear/HomogeneousGradedProjectionBounds.lean`, `Linear/RealDualRationalBounds.lean`, `Linear/RealRankHorizontalSymbol.lean`, `Linear/SquareBasisGeometry.lean`, `Linear/SquareSymbolProjection.lean`, `Nilpotent/FactorwiseBCHCovers.lean`, `Nilpotent/IdealInvariantNiltestBudget.lean`, `Nilpotent/NativeNilsequenceExpansion.lean`, `Nilpotent/NiltestAffineProjection.lean`, `Nilpotent/NiltestBasepointNormalization.lean`, `Polynomial/RelativeSquarePolynomial.lean`, `Polynomial/ShiftedGradedPolynomial.lean`, `Polynomial/SquarePolynomialCoordinates.lean`, `Polynomial/WeightedLinearPolynomialRestriction.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B101
import Definitions.Def_OAIE3v2B102

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedLinearPolynomialRestriction
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

omit [Fintype σ] in
@[simp] theorem coeff_zero_polynomialLinearRestriction
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ) :
    (polynomialLinearRestriction A P).coeff 0 = P.coeff 0 := by
  have h := eval_polynomialLinearRestriction A 0 P
  simpa only [map_zero, eval_zero, constantCoeff_eq] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuotientTopSymbol
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def quotientTopPolynomialMap : F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆
    F.quotientTop.adaptedLieSubalgebra w :=
  F.filteredPolynomialMap F.quotientTop (lieQuotientMap (F.layerIdeal (s + 1)))
    (fun _ _ hx => F.quotientLie_mem _ le_rfl hx) w

noncomputable def quotientTopSymbolMap : F.PolynomialSymbol w →ₗ⁅ℚ⁆
    F.quotientTop.PolynomialSymbol w :=
  F.filteredPolynomialSymbolMap F.quotientTop (lieQuotientMap (F.layerIdeal (s + 1)))
    (fun _ _ hx => F.quotientLie_mem _ le_rfl hx) w

@[simp] theorem quotientTopSymbolMap_symbol (p : F.adaptedLieSubalgebra w) :
    F.quotientTopSymbolMap w (F.polynomialSymbolMap w p) =
      F.quotientTop.polynomialSymbolMap w (F.quotientTopPolynomialMap w p) := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualLogarithmicDifferential
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem dualTangentLinear_lift_add (f g k : X → DualLieAlgebra L)
    (hfg : ∀ x, dualBaseLinear (f x) = dualBaseLinear (g x))
    (hfk : ∀ x, dualBaseLinear (f x) = dualBaseLinear (k x))
    (ht : ∀ x, dualTangentLinear (f x) = dualTangentLinear (g x) + dualTangentLinear (k x))
    (p : FreeLieAlgebra ℚ X) :
    dualTangentLinear (FreeLieAlgebra.lift ℚ f p) =
      dualTangentLinear (FreeLieAlgebra.lift ℚ g p) +
        dualTangentLinear (FreeLieAlgebra.lift ℚ k p) := by
  have hbr (u v : FreeLieAlgebra ℚ X)
      (hu : dualTangentLinear (FreeLieAlgebra.lift ℚ f u) =
        dualTangentLinear (FreeLieAlgebra.lift ℚ g u) + dualTangentLinear (FreeLieAlgebra.lift ℚ k u))
      (hv : dualTangentLinear (FreeLieAlgebra.lift ℚ f v) =
        dualTangentLinear (FreeLieAlgebra.lift ℚ g v) + dualTangentLinear (FreeLieAlgebra.lift ℚ k v)) :
      dualTangentLinear (FreeLieAlgebra.lift ℚ f ⁅u, v⁆) =
        dualTangentLinear (FreeLieAlgebra.lift ℚ g ⁅u, v⁆) +
          dualTangentLinear (FreeLieAlgebra.lift ℚ k ⁅u, v⁆) := by
    simp only [LieHom.map_lie, dualTangentLinear_lie, hu, hv,
      ← base_lift_congr f g hfg, ← base_lift_congr f k hfk,
      LieRing.lie_add, LieRing.add_lie]
    abel
  apply freeLie_linear_induction (fun q =>
    dualTangentLinear (FreeLieAlgebra.lift ℚ f q) =
      dualTangentLinear (FreeLieAlgebra.lift ℚ g q) +
        dualTangentLinear (FreeLieAlgebra.lift ℚ k q))
  · simp only [map_zero, add_zero]
  · intro u v hu hv
    simp only [map_add, hu, hv]
    abel
  · intro r q hq
    simp only [map_smul, hq, smul_add]
  · intro t
    induction t with
    | ih1 x => simpa only [lieTreeEval, FreeLieAlgebra.lift_of_apply] using ht x
    | ih2 u v hu hv => exact hbr _ _ hu hv

theorem dualTangentLinear_bch_add (s : ℕ) (a a₁ a₂ b b₁ b₂ : DualLieAlgebra L)
    (ha₁ : dualBaseLinear a = dualBaseLinear a₁)
    (ha₂ : dualBaseLinear a = dualBaseLinear a₂)
    (hb₁ : dualBaseLinear b = dualBaseLinear b₁)
    (hb₂ : dualBaseLinear b = dualBaseLinear b₂)
    (hat : dualTangentLinear a = dualTangentLinear a₁ + dualTangentLinear a₂)
    (hbt : dualTangentLinear b = dualTangentLinear b₁ + dualTangentLinear b₂) :
    dualTangentLinear (lieBCH s a b) =
      dualTangentLinear (lieBCH s a₁ b₁) + dualTangentLinear (lieBCH s a₂ b₂) := by
  apply dualTangentLinear_lift_add ![a, b] ![a₁, b₁] ![a₂, b₂]
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualLogDerivative_tangent_add (x y z : L) :
    dualLogDerivative (hnil := hnil) ⟨dualConstantLie x + dualInfinitesimal (y + z)⟩ =
      dualLogDerivative (hnil := hnil) ⟨dualConstantLie x + dualInfinitesimal y⟩ +
        dualLogDerivative (hnil := hnil) ⟨dualConstantLie x + dualInfinitesimal z⟩ := by
  simp only [dualLogDerivative_value_tangent]
  apply dualTangentLinear_bch_add <;>
    simp only [map_add, map_neg, dualBaseLinear_constant, dualBaseLinear_infinitesimal,
      dualTangentLinear_constant, dualTangentLinear_infinitesimal, add_zero, zero_add, neg_zero]

noncomputable def dualLogarithmicDifferential (x : L) : L →ₗ[ℚ] L :=
  (AddMonoidHom.mk'
    (fun y => dualLogDerivative (hnil := hnil) ⟨dualConstantLie x + dualInfinitesimal y⟩)
    (dualLogDerivative_tangent_add x)).toRatLinearMap

@[simp] theorem dualLogarithmicDifferential_apply (x y : L) :
    dualLogarithmicDifferential (hnil := hnil) x y =
      dualLogDerivative (hnil := hnil) ⟨dualConstantLie x + dualInfinitesimal y⟩ := rfl

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FactorwiseBCHCovers
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)]
  [∀ a, LieAlgebra ℚ (M a)] {s : ℕ}

noncomputable def piBCHSubgroup (F : ∀ a, NilpotentLieFiltration (M a) s)
    (Δ : ∀ a, Subgroup (F a).Group) : Subgroup (NilpotentLieFiltration.pi F).Group :=
  ⨅ a, (Δ a).comap (map (hM := (F a).lowerCentralSeries_eq_bot) (liePiEval a))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealDualRationalBounds
namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

@[simp] theorem realDualBasis_inl (b : Basis ι ℝ L) (i : ι) :
    realDualBasis b (Sum.inl i) = dualConstantLie (b i) := by
  simp [realDualBasis, Basis.map_apply]

@[simp] theorem realDualBasis_inr (b : Basis ι ℝ L) (i : ι) :
    realDualBasis b (Sum.inr i) = dualInfinitesimal (b i) := by
  simp [realDualBasis, Basis.map_apply]

@[simp] theorem realDualBasis_repr_inl (b : Basis ι ℝ L) (x : DualLieAlgebra L) (i : ι) :
    (realDualBasis b).repr x (Sum.inl i) = b.repr (dualBaseLinear x) i := by
  simp [realDualBasis, Basis.map_repr]

@[simp] theorem realDualBasis_repr_inr (b : Basis ι ℝ L) (x : DualLieAlgebra L) (i : ι) :
    (realDualBasis b).repr x (Sum.inr i) = b.repr (dualTangentLinear x) i := by
  simp [realDualBasis, Basis.map_repr]

end Erdos3

end

section

namespace Erdos3

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def rationalDualBasis (b : Basis ι ℚ L) : Basis (ι ⊕ ι) ℚ (DualLieAlgebra L) :=
  (b.prod b).map dualCoordinates.symm

@[simp] theorem rationalDualBasis_inl (b : Basis ι ℚ L) (i : ι) :
    rationalDualBasis b (Sum.inl i) = dualConstantLie (b i) := by
  simp [rationalDualBasis, Basis.map_apply]

@[simp] theorem rationalDualBasis_inr (b : Basis ι ℚ L) (i : ι) :
    rationalDualBasis b (Sum.inr i) = dualInfinitesimal (b i) := by
  simp [rationalDualBasis, Basis.map_apply]

@[simp] theorem rationalDualBasis_repr_inl (b : Basis ι ℚ L) (x : DualLieAlgebra L) (i : ι) :
    (rationalDualBasis b).repr x (Sum.inl i) = b.repr (dualBaseLinear x) i := by
  simp [rationalDualBasis, Basis.map_repr]

@[simp] theorem rationalDualBasis_repr_inr (b : Basis ι ℚ L) (x : DualLieAlgebra L) (i : ι) :
    (rationalDualBasis b).repr x (Sum.inr i) = b.repr (dualTangentLinear x) i := by
  simp [rationalDualBasis, Basis.map_repr]

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

theorem bchSubgroupCoordinates_reindex (b : Basis ι ℚ L) (e : ι ≃ κ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (x : κ → ℚ) :
    x ∈ bchSubgroupCoordinates (b.reindex e) Γ ↔
      (fun i => x (e i)) ∈ bchSubgroupCoordinates b Γ := by
  unfold bchSubgroupCoordinates
  simp only [Set.mem_ofPred_eq, basis_reindex_equivFun_symm]

theorem bchSubgroup_inner_grid_reindex (b : Basis ι ℚ L) (e : ι ≃ κ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) {N : ℕ}
    (h : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ) :
    scaledIntegerGrid N ⊆ bchSubgroupCoordinates (b.reindex e) Γ := by
  rintro x ⟨z, rfl⟩
  apply (bchSubgroupCoordinates_reindex b e Γ _).mpr
  exact h ⟨fun i => z (e i), rfl⟩

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L s d)

namespace Niltest

variable {D} {w : σ → ℕ}

noncomputable def evalCyclic (T : D.Niltest w) (N : ℕ) [NeZero N] (x : σ → ZMod N) : ℂ :=
  T.eval (fun i => ((x i).val : ℤ))

end Niltest
end Erdos3.RationalFilteredNilmanifold

end

section

open Module
open scoped BigOperators

namespace Erdos3

namespace NilpotentLieFiltration

variable {ι : Type*} {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}

def piLayerEquiv (F : ∀ i, NilpotentLieFiltration (L i) s) (n : ℕ) :
    (∀ i, (F i).layer n) ≃ₗ[ℚ] (pi F).layer n where
  toFun x := ⟨fun i => x i, (mem_pi_layer F n _).mpr (fun i => (x i).property)⟩
  invFun x i := ⟨x.val i, (mem_pi_layer F n _).mp x.property i⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def productFinBasis : Basis (Fin (Fintype.card (Σ i, Fin (d i)))) ℚ (∀ i, L i) :=
  (Pi.basis (fun i => (D i).basis)).reindex (Fintype.equivFin _)

noncomputable def productLayerBasis (j : Fin (s + 1)) :
    Basis (Σ i, Fin (finrank ℚ ((D i).filtration.layer (j.val + 1)))) ℚ
      ((NilpotentLieFiltration.pi (fun i => (D i).filtration)).layer (j.val + 1)) :=
  (Pi.basis (fun i => (D i).layerBasis j)).map
    (NilpotentLieFiltration.piLayerEquiv (fun i => (D i).filtration) (j.val + 1))

noncomputable def productLayerFinBasis (j : Fin (s + 1)) :
    Basis (Fin (finrank ℚ ((NilpotentLieFiltration.pi (fun i => (D i).filtration)).layer (j.val + 1)))) ℚ
      ((NilpotentLieFiltration.pi (fun i => (D i).filtration)).layer (j.val + 1)) :=
  (productLayerBasis D j).reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis (productLayerBasis D j)).symm)

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {σ K Ξ : Type*} [LieRing K] [LieAlgebra ℚ K] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
  (D : RationalFilteredNilmanifold K s d) {w : σ → ℕ}

noncomputable def cyclicOrbitPoint
    (g : D.filtration.realification.PolynomialOrbit w)
    (N : ℕ) [NeZero N] (x : σ → ZMod N) : D.Space :=
  QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w
    (fun i => ((x i).val : ℤ)) g)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AssociatedGradedBasisIndependence
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def gradedPieceProjection (j : ℕ) : L →ₗ[ℚ] F.AssociatedGraded :=
  (F.associatedGradedBasis b ω hlayers).repr.symm.toLinearMap.comp
    (b.repr.toLinearMap.comp (basisGradeProjection b ω j))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedGradedPolynomial
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def shiftedGradedPolynomial (k : ℕ) :
    VectorPolynomial σ ℚ L →ₗ[ℚ] VectorPolynomial σ ℚ F.AssociatedGraded where
  toFun p := coefficients.symm (Finsupp.onFinset (coefficients p).support
    (fun α => F.gradedPieceProjection b ω hlayers (Finsupp.weight w α + k) (coefficients p α)) (by
      intro α hα
      apply Finsupp.mem_support_iff.mpr
      intro hc
      apply hα
      rw [hc, map_zero]))
  map_add' p q := by
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    simp only [LinearEquiv.apply_symm_apply, Finsupp.onFinset_apply, map_add, Finsupp.add_apply]
  map_smul' c p := by
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    simp only [LinearEquiv.apply_symm_apply, Finsupp.onFinset_apply, map_smul, Finsupp.smul_apply,
      RingHom.id_apply]

@[simp] theorem shiftedGradedPolynomial_coefficient (k : ℕ) (p : VectorPolynomial σ ℚ L)
    (α : σ →₀ ℕ) :
    coefficients (F.shiftedGradedPolynomial b ω hlayers w k p) α =
      F.gradedPieceProjection b ω hlayers (Finsupp.weight w α + k) (coefficients p α) := by
  simp only [shiftedGradedPolynomial, LinearMap.coe_mk, AddHom.coe_mk,
    LinearEquiv.apply_symm_apply, Finsupp.onFinset_apply]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedGradedCalculus
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

abbrev FilteredFirstJet := F.adaptedLieSubalgebra w ⧸ F.shiftedPolynomialIdeal w 2

noncomputable def filteredFirstJetMap : F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.FilteredFirstJet w :=
  lieQuotientMap (F.shiftedPolynomialIdeal w 2)

theorem filteredFirstJetMap_eq_zero_iff (p : F.adaptedLieSubalgebra w) :
    F.filteredFirstJetMap w p = 0 ↔ ∀ α, coefficients p.val α ∈ F.layer (Finsupp.weight w α + 2) :=
  lieQuotientMap_eq_zero _ p

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem coefficients_pderiv (i : σ) (p : VectorPolynomial σ ℚ L) (α : σ →₀ ℕ) :
    coefficients ((MvPolynomial.pderiv i).toLinearMap.rTensor L p) α =
      (α i + 1 : ℚ) • coefficients p (α + Finsupp.single i 1) := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q x =>
    rw [LinearMap.rTensor_tmul]
    rw [coefficients_tmul, coefficients_tmul]
    change (MvPolynomial.pderiv i q).coeff α • x =
      (α i + 1 : ℚ) • (q.coeff (α + Finsupp.single i 1) • x)
    rw [MvPolynomial.coeff_pderiv, smul_smul]
    congr 1
    ring
  | add p q hp hq => simp only [map_add, Finsupp.add_apply, hp, hq, smul_add]

theorem coefficients_directionalDerivative [Fintype σ]
    (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) (α : σ →₀ ℕ) :
    coefficients (directionalDerivative h p) α =
      ∑ i, h i • ((α i + 1 : ℚ) • coefficients p (α + Finsupp.single i 1)) := by
  simp only [directionalDerivative, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
    Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply, coefficients_pderiv]

end VectorPolynomial

namespace NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem directionalDerivative_mem_shifted [Fintype σ] (h : σ → ℚ) (k : ℕ)
    {p : VectorPolynomial σ ℚ L} (hp : p ∈ F.shiftedAdaptedSubmodule (fun _ => 1) k) :
    directionalDerivative h p ∈ F.shiftedAdaptedSubmodule (fun _ => 1) (k + 1) := by
  intro α
  rw [coefficients_directionalDerivative]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  have hi := hp (α + Finsupp.single i 1)
  simpa only [map_add, Finsupp.weight_single, one_smul, Nat.add_right_comm, Nat.add_assoc] using hi

theorem directionalDerivative_mem_next [Fintype σ] (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    directionalDerivative h p.val ∈ F.shiftedAdaptedSubmodule (fun _ => 1) 1 := by
  apply F.directionalDerivative_mem_shifted h 0
  intro α
  simpa only [Nat.add_zero] using p.property α

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

noncomputable def adaptedDirectionalDerivative :
    F.adaptedLieSubalgebra (fun _ : σ => 1) →ₗ[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1) :=
  ((directionalDerivative h).comp (F.adaptedLieSubalgebra (fun _ => 1)).incl.toLinearMap).codRestrict
    (F.adaptedLieSubalgebra (fun _ => 1)).toSubmodule (by
      intro p α
      exact F.antitone (Nat.le_succ _) (F.directionalDerivative_mem_next h p α))

@[simp] theorem adaptedDirectionalDerivative_coe (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (F.adaptedDirectionalDerivative h p : VectorPolynomial σ ℚ L) = directionalDerivative h p.val := rfl

theorem adaptedDirectionalDerivative_mem_shifted (k : ℕ)
    {p : F.adaptedLieSubalgebra (fun _ : σ => 1)}
    (hp : p ∈ F.shiftedPolynomialIdeal (fun _ => 1) k) :
    F.adaptedDirectionalDerivative h p ∈ F.shiftedPolynomialIdeal (fun _ => 1) (k + 1) :=
  F.directionalDerivative_mem_shifted h k hp

noncomputable def symbolFirstDerivative :
    F.PolynomialSymbol (fun _ : σ => 1) →ₗ[ℚ] F.FilteredFirstJet (fun _ : σ => 1) :=
  (F.shiftedAdaptedIdeal (fun _ => 1)).toSubmodule.liftQ
    ((F.filteredFirstJetMap (fun _ => 1)).toLinearMap.comp (F.adaptedDirectionalDerivative h)) (by
      intro p hp
      exact (F.filteredFirstJetMap_eq_zero_iff (fun _ => 1) _).mpr
        (F.adaptedDirectionalDerivative_mem_shifted h 1 hp))

@[simp] theorem symbolFirstDerivative_map (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.symbolFirstDerivative h (F.polynomialSymbolMap (fun _ => 1) p) =
      F.filteredFirstJetMap (fun _ => 1) (F.adaptedDirectionalDerivative h p) := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

noncomputable def adaptedPolynomialJet (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    DualGroup (F.adaptedPolynomialFiltration (fun _ : σ => 1)).lowerCentralSeries_eq_bot :=
  ⟨dualConstantLie p + dualInfinitesimal (F.adaptedDirectionalDerivative h p)⟩

@[simp] theorem adaptedPolynomialJet_base (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    dualBaseLinear (F.adaptedPolynomialJet h p).coord = p := by
  change dualBaseLinear (dualConstantLie p + dualInfinitesimal (F.adaptedDirectionalDerivative h p)) = p
  rw [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]

@[simp] theorem adaptedPolynomialJet_tangent (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    dualTangentLinear (F.adaptedPolynomialJet h p).coord = F.adaptedDirectionalDerivative h p := by
  change dualTangentLinear (dualConstantLie p + dualInfinitesimal (F.adaptedDirectionalDerivative h p)) = _
  rw [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add]

@[simp] theorem adaptedPolynomialJet_baseHom (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    dualBaseHom (F.adaptedPolynomialJet h p) =
      (⟨p⟩ : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) := by
  apply NilpotentLieBCHGroup.ext
  exact F.adaptedPolynomialJet_base h p

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

theorem adaptedDirectionalDerivative_lie (p q : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.adaptedDirectionalDerivative h ⁅p, q⁆ =
      ⁅F.adaptedDirectionalDerivative h p, q⁆ + ⁅p, F.adaptedDirectionalDerivative h q⁆ := by
  apply Subtype.ext
  exact directionalDerivative_lie h p.val q.val

noncomputable def adaptedPolynomialJetLie :
    F.adaptedLieSubalgebra (fun _ : σ => 1) →ₗ⁅ℚ⁆
      DualLieAlgebra (F.adaptedLieSubalgebra (fun _ : σ => 1)) where
  toLinearMap := dualConstantLie.toLinearMap +
    dualInfinitesimal.comp (F.adaptedDirectionalDerivative h)
  map_lie' {p q} := by
    change dualConstantLie ⁅p, q⁆ + dualInfinitesimal (F.adaptedDirectionalDerivative h ⁅p, q⁆) =
      ⁅dualConstantLie p + dualInfinitesimal (F.adaptedDirectionalDerivative h p),
        dualConstantLie q + dualInfinitesimal (F.adaptedDirectionalDerivative h q)⁆
    apply dual_ext
    · simp only [map_add, dualBaseLinear_constant,
        dualBaseLinear_infinitesimal, add_zero, dualBaseLinear_lie]
    · simp only [map_add, dualTangentLinear_constant,
        dualTangentLinear_infinitesimal, zero_add, dualTangentLinear_lie,
        dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]
      rw [F.adaptedDirectionalDerivative_lie]
      exact add_comm _ _

noncomputable def adaptedPolynomialJetHom :
    (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group →*
      DualGroup (F.adaptedPolynomialFiltration (fun _ : σ => 1)).lowerCentralSeries_eq_bot :=
  NilpotentLieBCHGroup.map (F.adaptedPolynomialJetLie h)

@[simp] theorem adaptedPolynomialJetHom_apply
    (P : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    F.adaptedPolynomialJetHom h P = F.adaptedPolynomialJet h P.coord := rfl

end Erdos3.NilpotentLieFiltration

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

noncomputable def normalizedRelativeSubmodule : Submodule ℚ (F.adaptedLieSubalgebra w) :=
  (F.shiftedAdaptedIdeal w).toSubmodule ⊓ (F.layer 2).comap (F.adaptedCoefficientMap w 0)

include hw in
theorem normalizedRelative_coefficient_mem_two (p : F.normalizedRelativeSubmodule w) (α : σ →₀ ℕ) :
    coefficients p.val.val α ∈ F.layer 2 := by
  by_cases hα : α = 0
  · subst α
    exact p.property.2
  · exact F.antitone (by have := positive_weight_of_ne_zero w hw hα; omega) (p.property.1 α)

noncomputable def relativeSquarePolynomial (p : F.normalizedRelativeSubmodule w) :
    VectorPolynomial σ ℚ F.squareLieSubalgebra :=
  restrictCoefficients F.squareLieSubalgebra.toSubmodule (pair p.val.val 0) (by
    intro α
    rw [coefficients_pair, map_zero, Finsupp.zero_apply]
    apply (F.mem_squareLieSubalgebra _).mpr
    simpa only [sub_zero] using F.normalizedRelative_coefficient_mem_two w hw p α)

theorem relativeSquarePolynomial_coefficient (p : F.normalizedRelativeSubmodule w) (α : σ →₀ ℕ) :
    (coefficients (F.relativeSquarePolynomial w hw p) α : L × L) = (coefficients p.val.val α, 0) := by
  rw [relativeSquarePolynomial, coefficients_restrictCoefficients, coefficients_pair, map_zero,
    Finsupp.zero_apply]

theorem relativeSquarePolynomial_adapted (p : F.normalizedRelativeSubmodule w) :
    F.relativeSquarePolynomial w hw p ∈ F.squareFiltration.adaptedLieSubalgebra w := by
  intro α
  change (coefficients (F.relativeSquarePolynomial w hw p) α : L × L) ∈ F.squareLayer (Finsupp.weight w α)
  rw [F.relativeSquarePolynomial_coefficient]
  refine ⟨p.val.property α, (F.layer _).zero_mem, ?_⟩
  change coefficients p.val.val α - 0 ∈ F.layer (Finsupp.weight w α + 1)
  rw [sub_zero]
  exact p.property.1 α

noncomputable def relativeSquareLift :
    F.normalizedRelativeSubmodule w →ₗ[ℚ] F.squareFiltration.adaptedLieSubalgebra w where
  toFun p := ⟨F.relativeSquarePolynomial w hw p, F.relativeSquarePolynomial_adapted w hw p⟩
  map_add' p q := by
    apply Subtype.ext
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    change coefficients (F.relativeSquarePolynomial w hw (p + q)) α =
      coefficients (F.relativeSquarePolynomial w hw p + F.relativeSquarePolynomial w hw q) α
    rw [map_add, Finsupp.add_apply]
    apply Subtype.ext
    change (coefficients (F.relativeSquarePolynomial w hw (p + q)) α : L × L) =
      (coefficients (F.relativeSquarePolynomial w hw p) α : L × L) +
        (coefficients (F.relativeSquarePolynomial w hw q) α : L × L)
    rw [F.relativeSquarePolynomial_coefficient, F.relativeSquarePolynomial_coefficient,
      F.relativeSquarePolynomial_coefficient]
    change (coefficients (p.val.val + q.val.val) α, 0) = _
    simp only [map_add, Finsupp.add_apply, Prod.mk_add_mk, add_zero]
  map_smul' c p := by
    apply Subtype.ext
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    change coefficients (F.relativeSquarePolynomial w hw (c • p)) α =
      coefficients (c • F.relativeSquarePolynomial w hw p) α
    rw [map_smul, Finsupp.smul_apply]
    apply Subtype.ext
    change (coefficients (F.relativeSquarePolynomial w hw (c • p)) α : L × L) =
      c • (coefficients (F.relativeSquarePolynomial w hw p) α : L × L)
    rw [F.relativeSquarePolynomial_coefficient, F.relativeSquarePolynomial_coefficient]
    change (coefficients (c • p.val.val) α, 0) = _
    simp only [map_smul, Finsupp.smul_apply, Prod.smul_mk, smul_zero]

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

noncomputable def squareSndSymbolMap : F.squareFiltration.PolynomialSymbol w →ₗ⁅ℚ⁆ F.PolynomialSymbol w :=
  F.squareFiltration.filteredPolynomialSymbolMap F F.squareSnd (fun _ _ hx => hx.2.1) w

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SquarePolynomialCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

def squareDiagonalLie : L →ₗ⁅ℚ⁆ F.squareLieSubalgebra where
  toFun x := ⟨(x, x), (F.mem_squareLieSubalgebra _).mpr (by simp)⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
  map_lie' := Subtype.ext rfl

noncomputable def squareFstPolynomialMap :
    F.squareFiltration.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.adaptedLieSubalgebra w :=
  F.squareFiltration.filteredPolynomialMap F F.squareFst (fun _ _ hx => hx.1) w

noncomputable def squareSndPolynomialMap :
    F.squareFiltration.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.adaptedLieSubalgebra w :=
  F.squareFiltration.filteredPolynomialMap F F.squareSnd (fun _ _ hx => hx.2.1) w

noncomputable def squareDiagonalPolynomialMap :
    F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.squareFiltration.adaptedLieSubalgebra w :=
  F.filteredPolynomialMap F.squareFiltration F.squareDiagonalLie
    (fun j x hx => ⟨hx, hx, by change x - x ∈ F.layer (j + 1); simp⟩) w

theorem squareFstPolynomialMap_coefficient (r : F.squareFiltration.adaptedLieSubalgebra w)
    (α : σ →₀ ℕ) : coefficients (F.squareFstPolynomialMap w r).val α =
      (coefficients r.val α).val.1 := by
  change coefficients (VectorPolynomial.map F.squareFst.toLinearMap r.val) α = _
  rw [coefficients_map]
  rfl

theorem squareSndPolynomialMap_coefficient (r : F.squareFiltration.adaptedLieSubalgebra w)
    (α : σ →₀ ℕ) : coefficients (F.squareSndPolynomialMap w r).val α =
      (coefficients r.val α).val.2 := by
  change coefficients (VectorPolynomial.map F.squareSnd.toLinearMap r.val) α = _
  rw [coefficients_map]
  rfl

theorem squareDiagonalPolynomialMap_coefficient (p : F.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    (coefficients (F.squareDiagonalPolynomialMap w p).val α).val =
      (coefficients p.val α, coefficients p.val α) := by
  change (coefficients (VectorPolynomial.map F.squareDiagonalLie.toLinearMap p.val) α).val = _
  rw [coefficients_map]
  rfl

@[simp] theorem squareFstPolynomialMap_diagonal (p : F.adaptedLieSubalgebra w) :
    F.squareFstPolynomialMap w (F.squareDiagonalPolynomialMap w p) = p := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.squareFstPolynomialMap_coefficient, F.squareDiagonalPolynomialMap_coefficient]

@[simp] theorem squareSndPolynomialMap_diagonal (p : F.adaptedLieSubalgebra w) :
    F.squareSndPolynomialMap w (F.squareDiagonalPolynomialMap w p) = p := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.squareSndPolynomialMap_coefficient, F.squareDiagonalPolynomialMap_coefficient]

@[simp] theorem squareFstPolynomialMap_relative (hw : ∀ i, 0 < w i)
    (p : F.normalizedRelativeSubmodule w) :
    F.squareFstPolynomialMap w (F.relativeSquareLift w hw p) = p.val := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.squareFstPolynomialMap_coefficient]
  change (coefficients (F.relativeSquarePolynomial w hw p) α).val.1 = _
  rw [F.relativeSquarePolynomial_coefficient]

@[simp] theorem squareSndPolynomialMap_relative (hw : ∀ i, 0 < w i)
    (p : F.normalizedRelativeSubmodule w) :
    F.squareSndPolynomialMap w (F.relativeSquareLift w hw p) = 0 := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.squareSndPolynomialMap_coefficient]
  change (coefficients (F.relativeSquarePolynomial w hw p) α).val.2 = coefficients 0 α
  rw [F.relativeSquarePolynomial_coefficient, map_zero, Finsupp.zero_apply]

noncomputable def squareDiagonalSymbolMap :
    F.PolynomialSymbol w →ₗ⁅ℚ⁆ F.squareFiltration.PolynomialSymbol w :=
  F.filteredPolynomialSymbolMap F.squareFiltration F.squareDiagonalLie
    (fun j x hx => ⟨hx, hx, by change x - x ∈ F.layer (j + 1); simp⟩) w

@[simp] theorem squareDiagonalSymbolMap_symbol (p : F.adaptedLieSubalgebra w) :
    F.squareDiagonalSymbolMap w (F.polynomialSymbolMap w p) =
      F.squareFiltration.polynomialSymbolMap w (F.squareDiagonalPolynomialMap w p) := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedSquareSymbol
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def quotientGradedMap (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule) :
    F.AssociatedGraded →ₗ⁅ℚ⁆ (F.quotientLie I hI).AssociatedGraded :=
  F.associatedGradedMap (F.quotientLie I hI) (lieQuotientMap I)
    (fun _ _ hx => F.quotientLie_mem I hI hx)

@[simp] theorem quotientGradedMap_piece (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
    (j : ℕ) (x : F.layer j) :
    F.quotientGradedMap I hI (F.associatedGradedPieceMap j x) =
      (F.quotientLie I hI).associatedGradedPieceMap j
        ⟨lieQuotientMap I x, F.quotientLie_mem I hI x.property⟩ :=
  F.associatedGradedMap_piece _ _ _ j x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def reducedSquarePolynomialMap :
    F.squareFiltration.adaptedLieSubalgebra w →ₗ⁅ℚ⁆
      F.squareFiltration.quotientTop.adaptedLieSubalgebra w :=
  F.squareFiltration.filteredPolynomialMap F.squareFiltration.quotientTop
    (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)))
    (fun _ _ hx => F.squareFiltration.quotientLie_mem _ le_rfl hx) w

noncomputable def reducedSquareSymbolMap :
    F.squareFiltration.PolynomialSymbol w →ₗ⁅ℚ⁆ F.squareFiltration.quotientTop.PolynomialSymbol w :=
  F.squareFiltration.filteredPolynomialSymbolMap F.squareFiltration.quotientTop
    (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)))
    (fun _ _ hx => F.squareFiltration.quotientLie_mem _ le_rfl hx) w

@[simp] theorem reducedSquareSymbolMap_symbol (r : F.squareFiltration.adaptedLieSubalgebra w) :
    F.reducedSquareSymbolMap w (F.squareFiltration.polynomialSymbolMap w r) =
      F.squareFiltration.quotientTop.polynomialSymbolMap w (F.reducedSquarePolynomialMap w r) := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquareSymbolRelative
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

@[simp] theorem squareSndSymbolMap_symbol (r : F.squareFiltration.adaptedLieSubalgebra w) :
    F.squareSndSymbolMap w (F.squareFiltration.polynomialSymbolMap w r) =
      F.polynomialSymbolMap w (F.squareSndPolynomialMap w r) := rfl

@[simp] theorem squareSndSymbolMap_diagonal (x : F.PolynomialSymbol w) :
    F.squareSndSymbolMap w (F.squareDiagonalSymbolMap w x) = x := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  rw [F.squareDiagonalSymbolMap_symbol, F.squareSndSymbolMap_symbol, F.squareSndPolynomialMap_diagonal]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SquareBasisGeometry
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def squareCoordinates : F.squareLieSubalgebra ≃ₗ[ℚ] L × F.layer 2 where
  toFun x := (x.val.2, ⟨x.val.1 - x.val.2, (F.mem_squareLieSubalgebra x.val).mp x.property⟩)
  invFun x := ⟨(x.1 + x.2, x.1), (F.mem_squareLieSubalgebra _).mpr (by
    change x.1 + (x.2 : L) - x.1 ∈ F.layer 2
    rw [add_sub_cancel_left]
    exact x.2.property)⟩
  left_inv x := by apply Subtype.ext; apply Prod.ext <;> simp
  right_inv x := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext; simp
  map_add' x y := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext; dsimp; abel
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext; exact (smul_sub r _ _).symm

noncomputable def squareBasis (b : Basis ι ℚ L) (c : Basis κ ℚ (F.layer 2)) :
    Basis (ι ⊕ κ) ℚ F.squareLieSubalgebra :=
  (b.prod c).map F.squareCoordinates.symm

@[simp] theorem squareBasis_inl (b : Basis ι ℚ L) (c : Basis κ ℚ (F.layer 2)) (i : ι) :
    (F.squareBasis b c (Sum.inl i)).val = (b i, b i) := by
  simp [squareBasis, Basis.map_apply, squareCoordinates]

@[simp] theorem squareBasis_inr (b : Basis ι ℚ L) (c : Basis κ ℚ (F.layer 2)) (i : κ) :
    (F.squareBasis b c (Sum.inr i)).val = ((c i : L), 0) := by
  simp [squareBasis, Basis.map_apply, squareCoordinates]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def adaptedSquareBasis (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i})) :
    Basis (ι ⊕ {i // 2 ≤ w i}) ℚ F.squareLieSubalgebra :=
  F.squareBasis b (supportedSubmoduleBasis b (F.layer 2) {i | 2 ≤ w i} h)

@[simp] theorem adaptedSquareBasis_inl (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i})) (i : ι) :
    (F.adaptedSquareBasis b w h (Sum.inl i)).val = (b i, b i) :=
  F.squareBasis_inl b _ i

@[simp] theorem adaptedSquareBasis_inr (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i})) (i : {i // 2 ≤ w i}) :
    (F.adaptedSquareBasis b w h (Sum.inr i)).val = (b i, 0) := by
  simp only [adaptedSquareBasis, F.squareBasis_inr]
  apply Prod.ext
  · exact supportedSubmoduleBasis_coe b (F.layer 2) {i | 2 ≤ w i} h i
  · rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

variable (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def quotientTopBasis :
    Basis (QuotientTopBasisIndex s ω) ℚ (L ⧸ F.layerIdeal (s + 1)) :=
  supportedQuotientBasis e (F.layerIdeal (s + 1)).toSubmodule {i | s + 1 ≤ ω i} (hF (s + 1))

@[simp] theorem quotientTopBasis_apply (i : QuotientTopBasisIndex s ω) :
    F.quotientTopBasis e ω hF i = lieQuotientMap (F.layerIdeal (s + 1)) (e i.val) :=
  supportedQuotientBasis_apply e _ _ _ i

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def reducedSquareSnd :
    (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ⁅ℚ⁆
      (L ⧸ F.layerIdeal (s + 1)) :=
  lieQuotientDescend (F.squareFiltration.layerIdeal (s + 1))
    ((lieQuotientMap (F.layerIdeal (s + 1))).comp F.squareSnd) (by
      intro x hx
      exact (lieQuotientMap_eq_zero _ _).mpr hx.2.1)

noncomputable def reducedSquareDiagonal :
    (L ⧸ F.layerIdeal (s + 1)) →ₗ⁅ℚ⁆
      (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) :=
  lieQuotientDescend (F.layerIdeal (s + 1))
    ((lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))).comp F.squareDiagonalLie) (by
      intro x hx
      apply (lieQuotientMap_eq_zero _ _).mpr
      exact ⟨hx, hx, by change x - x ∈ F.layer (s + 1 + 1); simp⟩)

@[simp] theorem reducedSquareSnd_mk (x : F.squareLieSubalgebra) :
    F.reducedSquareSnd (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)) x) =
      lieQuotientMap (F.layerIdeal (s + 1)) (F.squareSnd x) := rfl

@[simp] theorem reducedSquareDiagonal_mk (x : L) :
    F.reducedSquareDiagonal (lieQuotientMap (F.layerIdeal (s + 1)) x) =
      lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)) (F.squareDiagonalLie x) := rfl

@[simp] theorem reducedSquareSnd_diagonal (x : L ⧸ F.layerIdeal (s + 1)) :
    F.reducedSquareSnd (F.reducedSquareDiagonal x) = x := by
  obtain ⟨a, rfl⟩ := lieQuotientMap_surjective (F.layerIdeal (s + 1)) x
  rfl

theorem reducedSquareSnd_mem (j : ℕ)
    (x : F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1))
    (hx : x ∈ F.squareFiltration.quotientTop.layer j) :
    F.reducedSquareSnd x ∈ F.quotientTop.layer j := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact F.quotientLie_mem _ le_rfl ha.2.1

theorem reducedSquareDiagonal_mem (j : ℕ) (x : L ⧸ F.layerIdeal (s + 1))
    (hx : x ∈ F.quotientTop.layer j) :
    F.reducedSquareDiagonal x ∈ F.squareFiltration.quotientTop.layer j := by
  obtain ⟨a, ha, rfl⟩ := hx
  apply F.squareFiltration.quotientLie_mem _ le_rfl
  exact ⟨ha, ha, by change a - a ∈ F.layer (j + 1); simp⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def squarePairMap : F.squareLieSubalgebra →ₗ⁅ℚ⁆ (Bool → L) :=
  liePiMap (fun i : Bool => cond i F.squareFst F.squareSnd)

@[simp] theorem squarePairMap_false (x : F.squareLieSubalgebra) : F.squarePairMap x false = x.val.2 := rfl
@[simp] theorem squarePairMap_true (x : F.squareLieSubalgebra) : F.squarePairMap x true = x.val.1 := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def reducedSquareSndPolynomialMap :
    F.squareFiltration.quotientTop.adaptedLieSubalgebra w →ₗ⁅ℚ⁆
      F.quotientTop.adaptedLieSubalgebra w :=
  F.squareFiltration.quotientTop.filteredPolynomialMap F.quotientTop
    F.reducedSquareSnd F.reducedSquareSnd_mem w

noncomputable def reducedSquareDiagonalPolynomialMap :
    F.quotientTop.adaptedLieSubalgebra w →ₗ⁅ℚ⁆
      F.squareFiltration.quotientTop.adaptedLieSubalgebra w :=
  F.quotientTop.filteredPolynomialMap F.squareFiltration.quotientTop
    F.reducedSquareDiagonal F.reducedSquareDiagonal_mem w

noncomputable def reducedSquareSndSymbolMap :
    F.squareFiltration.quotientTop.PolynomialSymbol w →ₗ⁅ℚ⁆ F.quotientTop.PolynomialSymbol w :=
  F.squareFiltration.quotientTop.filteredPolynomialSymbolMap F.quotientTop
    F.reducedSquareSnd F.reducedSquareSnd_mem w

noncomputable def reducedSquareDiagonalSymbolMap :
    F.quotientTop.PolynomialSymbol w →ₗ⁅ℚ⁆ F.squareFiltration.quotientTop.PolynomialSymbol w :=
  F.quotientTop.filteredPolynomialSymbolMap F.squareFiltration.quotientTop
    F.reducedSquareDiagonal F.reducedSquareDiagonal_mem w

@[simp] theorem reducedSquareSndSymbolMap_symbol
    (r : F.squareFiltration.quotientTop.adaptedLieSubalgebra w) :
    F.reducedSquareSndSymbolMap w (F.squareFiltration.quotientTop.polynomialSymbolMap w r) =
      F.quotientTop.polynomialSymbolMap w (F.reducedSquareSndPolynomialMap w r) := rfl

@[simp] theorem reducedSquareDiagonalSymbolMap_symbol (p : F.quotientTop.adaptedLieSubalgebra w) :
    F.reducedSquareDiagonalSymbolMap w (F.quotientTop.polynomialSymbolMap w p) =
      F.squareFiltration.quotientTop.polynomialSymbolMap w (F.reducedSquareDiagonalPolynomialMap w p) := rfl

@[simp] theorem reducedSquareSndPolynomialMap_diagonal (p : F.quotientTop.adaptedLieSubalgebra w) :
    F.reducedSquareSndPolynomialMap w (F.reducedSquareDiagonalPolynomialMap w p) = p := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  simp only [reducedSquareSndPolynomialMap, reducedSquareDiagonalPolynomialMap,
    filteredPolynomialMap_coefficient, F.reducedSquareSnd_diagonal]

@[simp] theorem reducedSquareSndSymbolMap_diagonal (x : F.quotientTop.PolynomialSymbol w) :
    F.reducedSquareSndSymbolMap w (F.reducedSquareDiagonalSymbolMap w x) = x := by
  obtain ⟨p, rfl⟩ := F.quotientTop.polynomialSymbolMap_surjective w x
  rw [F.reducedSquareDiagonalSymbolMap_symbol, F.reducedSquareSndSymbolMap_symbol,
    F.reducedSquareSndPolynomialMap_diagonal]

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

abbrev FirstCoefficientModule (F : NilpotentLieFiltration L s) (w : σ → ℕ) :=
  (F.shiftedPolynomialIdeal w 1) ⧸
    (F.shiftedPolynomialIdeal w 2).toSubmodule.comap (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeWeightedEvaluationBounds
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : X → ℕ) (f : X → L)
  (hf : ∀ x, f x ∈ F.layer (w x))

include hf in
theorem FreeNilpotentLieAlgebra.lift_weightedLayer {d : ℕ} {x : FreeNilpotentLieAlgebra X s}
    (hx : x ∈ FreeNilpotentLieAlgebra.weightedLayer X s w d) :
    FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot x ∈ F.layer d :=
  weightedLieUpperSpan_le_comap F (FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot)
    (FreeNilpotentLieAlgebra.of X s) w
    (fun i => by rw [FreeNilpotentLieAlgebra.lift_of]; exact hf i) d hx

namespace FreeWeightedNilpotentLieAlgebra

noncomputable def lift : FreeWeightedNilpotentLieAlgebra X s w →ₗ⁅ℚ⁆ L :=
  lieQuotientDescend (FreeNilpotentLieAlgebra.weightedLayerIdeal X s w (s + 1))
    (FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot)
    (fun x hx => by
      have h := FreeNilpotentLieAlgebra.lift_weightedLayer F w f hf hx
      simpa only [F.terminal, Submodule.mem_bot] using h)

@[simp] theorem lift_of (x : X) : lift F w f hf (of X s w x) = f x :=
  FreeNilpotentLieAlgebra.lift_of f F.lowerCentralSeries_eq_bot x

end FreeWeightedNilpotentLieAlgebra

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductOrbitCongruence
namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3

variable {ι : Type*} {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

theorem realProductSingle_mem_layer {s : ℕ} (F : ∀ i, NilpotentLieFiltration (L i) s)
    (i : ι) (n : ℕ) {x : ℝ ⊗[ℚ] L i} (hx : x ∈ (F i).realification.layer n) :
    realProductSingle i x ∈ (NilpotentLieFiltration.pi F).realification.layer n := by
  classical
  apply baseChange_mem_of_mapsTo ((F i).layer n) ((NilpotentLieFiltration.pi F).layer n)
    (LinearMap.single ℚ L i) _ hx
  intro a ha
  apply (NilpotentLieFiltration.mem_pi_layer F n _).mpr
  intro j
  change Pi.single i a j ∈ (F j).layer n
  by_cases hji : j = i
  · subst j
    simpa only [Pi.single_eq_same] using ha
  · rw [Pi.single_eq_of_ne hji]
    exact Submodule.zero_mem _

end Erdos3

end

section

open scoped TensorProduct BigOperators

namespace Erdos3.NilpotentLieFiltration

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
  (F : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ}

noncomputable def piRealOrbit (p : ∀ i, (F i).realification.PolynomialOrbit w) :
    (pi F).realification.PolynomialOrbit w :=
  polynomialOrbitOfLog
    (∑ i, VectorPolynomial.map ((realProductSingle i).restrictScalars ℚ) (p i).log) (by
      apply ((pi F).realification.adapted_iff_coefficients w _).mpr
      intro α
      simp only [map_sum, Finsupp.finsetSum_apply, VectorPolynomial.coefficients_map]
      apply Submodule.sum_mem
      intro i _
      exact realProductSingle_mem_layer F i _
        (((F i).realification.adapted_iff_coefficients w _).mp (p i).adapted α))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealRankHorizontalSymbol
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

@[simp] theorem realHorizontalSymbolHom_apply (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ)
    (X : F.associatedDegree.RealPolynomialSymbolGroup w) :
    Multiplicative.toAdd (F.realHorizontalSymbolHom hs w α X) =
      (F.higherHorizontalSymbolCoefficient w α).baseChange ℝ X.coord := rfl

noncomputable def realHorizontalPolynomialHom (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) :
    (F.associatedDegree.realification.adaptedPolynomialFiltration w).Group →*
      Multiplicative (ℝ ⊗[ℚ] F.HigherHorizontal (Finsupp.weight w α)) :=
  (F.realHorizontalSymbolHom hs w α).comp
    (F.associatedDegree.realPolynomialSymbolHom b ω hF w)

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProjectedNativeCoefficient
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def adaptedTranslateLinear (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ) :
    F.adaptedLieSubalgebra w →ₗ[ℚ] F.adaptedLieSubalgebra w :=
  ((VectorPolynomial.translate h).comp (F.adaptedLieSubalgebra w).incl.toLinearMap).codRestrict
    (F.adaptedLieSubalgebra w).toSubmodule (by
      intro p
      exact (F.mem_adaptedSubmodule w _).mpr
        (F.adapted_translate w hw h ((F.mem_adaptedSubmodule w _).mp p.property)))

@[simp] theorem adaptedTranslateLinear_coe (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra w) :
    (F.adaptedTranslateLinear w hw h p : VectorPolynomial σ ℚ L) = translate h p.val := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {F : NilpotentLieFiltration L s} {w : σ → ℕ}

noncomputable def PolynomialOrbit.translate (g : F.PolynomialOrbit w)
    (hw : ∀ i, 0 < w i) (h : σ → ℤ) : F.PolynomialOrbit w :=
  polynomialOrbitOfLog (VectorPolynomial.translate (fun i => (h i : ℚ)) g.log)
    (F.adapted_translate w hw _ g.adapted)

@[simp] theorem polynomialOrbitEval_translate (g : F.PolynomialOrbit w)
    (hw : ∀ i, 0 < w i) (h x : σ → ℤ) :
    F.polynomialOrbitEval w x (g.translate hw h) = F.polynomialOrbitEval w (x + h) g := by
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.eval (fun i => (x i : ℚ))
      (VectorPolynomial.translate (fun i => (h i : ℚ)) g.log) =
    VectorPolynomial.eval (fun i => ((x + h) i : ℚ)) g.log
  rw [VectorPolynomial.eval_translate]
  simp only [Pi.add_apply, Int.cast_add]

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

noncomputable def integerOrbitPoint
    (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)) (n : ℤ) : D.Space :=
  QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
    (fun _ : Unit => 1) (fun _ => n) g)

@[simp] theorem cyclicOrbitPoint_translate
    (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (h : ℤ) (N : ℕ) [NeZero N] (x : ZMod N) :
    D.cyclicOrbitPoint (g.translate (fun _ => Nat.zero_lt_one) (fun _ => h)) N
      (fun _ : Unit => x) = D.integerOrbitPoint g ((x.val : ℤ) + h) := by
  unfold cyclicOrbitPoint integerOrbitPoint
  rw [NilpotentLieFiltration.polynomialOrbitEval_translate]
  rfl

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def nativeHorizontalCoefficientHom (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.associatedDegree.realification.PolynomialOrbit w →*
      Multiplicative (ℝ ⊗[ℚ] F.HigherHorizontal (Finsupp.weight w α)) :=
  (F.realHorizontalPolynomialHom hs b ω hF w α).comp
    (F.associatedDegree.realification.polynomialOrbitCoordinates w).toMonoidHom

@[simp] theorem nativeHorizontalCoefficientHom_apply (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w) :
    Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α g) =
      (F.higherHorizontalSymbolCoefficient w α).baseChange ℝ
        (F.associatedDegree.realSymbolOfPolynomial b ω hF w g.log) := rfl

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProjectedPointwiseCoefficient
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def gradedPolynomialSymbol :
    VectorPolynomial σ ℚ F.AssociatedGraded →ₗ[ℚ] F.PolynomialSymbol w :=
  (F.polynomialSymbolBasis b ω hlayers w).repr.symm.toLinearMap.comp
    (supportedCoordinates (F.associatedGradedBasis b ω hlayers)
      {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2})

theorem gradedPolynomialSymbol_coordinate
    (p : VectorPolynomial σ ℚ F.AssociatedGraded) (z : SymbolBasisIndex w ω) :
    (F.polynomialSymbolBasis b ω hlayers w).repr (F.gradedPolynomialSymbol b ω hlayers w p) z =
      (F.associatedGradedBasis b ω hlayers).repr (coefficients p z.val.1) z.val.2 := by
  change ((F.polynomialSymbolBasis b ω hlayers w).repr
    ((F.polynomialSymbolBasis b ω hlayers w).repr.symm _)) z = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

@[simp] theorem gradedPolynomialSymbol_gradedSymbolPolynomial (x : F.PolynomialSymbol w) :
    F.gradedPolynomialSymbol b ω hlayers w (F.gradedSymbolPolynomial b ω hlayers w x) = x := by
  apply (F.polynomialSymbolBasis b ω hlayers w).repr.injective
  ext z
  rw [F.gradedPolynomialSymbol_coordinate, F.gradedSymbolPolynomial_coefficient]

noncomputable def homogeneousSymbolLift (α : σ →₀ ℕ) :
    F.AssociatedGraded →ₗ[ℚ] F.PolynomialSymbol w :=
  (F.gradedPolynomialSymbol b ω hlayers w).comp
    (coefficients.symm.toLinearMap.comp (Finsupp.lsingle α))

@[simp] theorem homogeneousSymbolLift_apply (α : σ →₀ ℕ) (v : F.AssociatedGraded) :
    F.homogeneousSymbolLift b ω hlayers w α v =
      F.gradedPolynomialSymbol b ω hlayers w (monomial α v) := by
  simp only [homogeneousSymbolLift, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Finsupp.lsingle_apply, coefficients_symm_single]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationAssociatedGraded
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def homogeneousAssociatedGradedEquiv
    (hb : BasisHomogeneousBrackets b ω) : F.AssociatedGraded ≃ₗ⁅ℚ⁆ L :=
  { (F.associatedGradedBasis b ω hF).repr.trans b.repr.symm with
    map_lie' {x y} := by
      let f := (F.associatedGradedBasis b ω hF).repr.trans b.repr.symm
      change f ⁅x, y⁆ = ⁅f x, f y⁆
      apply linear_map_lie_of_basis (F.associatedGradedBasis b ω hF) f.toLinearMap
      intro i j
      apply b.repr.injective
      ext k
      have hf (z : F.AssociatedGraded) : b.repr (f z) =
          (F.associatedGradedBasis b ω hF).repr z := b.repr.apply_symm_apply _
      have hbi (a : ι) : f (F.associatedGradedBasis b ω hF a) = b a := by
        apply b.repr.injective
        rw [hf]
        simp only [Basis.repr_self]
      change b.repr (f ⁅F.associatedGradedBasis b ω hF i, F.associatedGradedBasis b ω hF j⁆) k =
        b.repr ⁅f (F.associatedGradedBasis b ω hF i), f (F.associatedGradedBasis b ω hF j)⁆ k
      rw [hf, hbi, hbi, F.associatedGradedBasis_bracket]
      by_cases h : ω i + ω j = ω k
      · simp only [h, ite_true]
      · rw [if_neg h, hb i j k (Ne.symm h)] }

@[simp] theorem homogeneousAssociatedGradedEquiv_repr
    (hb : BasisHomogeneousBrackets b ω) (x : F.AssociatedGraded) (i : ι) :
    b.repr (F.homogeneousAssociatedGradedEquiv b ω hF hb x) i =
      (F.associatedGradedBasis b ω hF).repr x i := by
  exact congrArg (fun z : ι →₀ ℚ => z i) (b.repr.apply_symm_apply _)

@[simp] theorem homogeneousAssociatedGradedEquiv_basis
    (hb : BasisHomogeneousBrackets b ω) (i : ι) :
    F.homogeneousAssociatedGradedEquiv b ω hF hb (F.associatedGradedBasis b ω hF i) = b i := by
  apply b.repr.injective
  ext k
  rw [homogeneousAssociatedGradedEquiv_repr]
  simp only [Basis.repr_self]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.HomogeneousGradedProjectionBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module
variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

noncomputable def homogeneousGradedProjection : F.AssociatedGraded →ₗ⁅ℚ⁆ M :=
  (G.homogeneousAssociatedGradedEquiv c ν hG hc).toLieHom.comp
    (F.associatedGradedMap G φ hφ)

@[simp] theorem homogeneousGradedProjection_repr (x : F.AssociatedGraded) (j : κ) :
    c.repr (F.homogeneousGradedProjection G c ν hG hc φ hφ x) j =
      (G.associatedGradedBasis c ν hG).repr (F.associatedGradedMap G φ hφ x) j :=
  G.homogeneousAssociatedGradedEquiv_repr c ν hG hc _ j

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolFastMembership
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

@[simp] theorem adaptedWeightedDilation_coe (w : σ → ℕ) (r : ℚ)
    (p : F.adaptedLieSubalgebra w) :
    (F.adaptedWeightedDilation w r p : VectorPolynomial σ ℚ L) =
      weightedDilation w r (p : VectorPolynomial σ ℚ L) := rfl

noncomputable def realPolynomialSymbolDilation (w : σ → ℕ) (r : ℚ) :
    F.RealPolynomialSymbol w →ₗ⁅ℚ⁆ F.RealPolynomialSymbol w :=
  LieAlgebra.ExtendScalars.map (AlgHom.id ℚ ℝ) (F.polynomialSymbolDilation w r)

@[simp] theorem realPolynomialSymbolDilation_tmul (w : σ → ℕ) (r : ℚ)
    (a : ℝ) (x : F.PolynomialSymbol w) :
    F.realPolynomialSymbolDilation w r (a ⊗ₜ[ℚ] x) =
      a ⊗ₜ[ℚ] F.polynomialSymbolDilation w r x := by
  simp only [realPolynomialSymbolDilation, LieAlgebra.ExtendScalars.map_apply_tmul, AlgHom.id_apply]

@[simp] theorem realPolynomialSymbolDilation_one (w : σ → ℕ) (x : F.RealPolynomialSymbol w) :
    F.realPolynomialSymbolDilation w 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp only [F.realPolynomialSymbolDilation_tmul, F.polynomialSymbolDilation_one]
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def realPolynomialSymbolDilationHom (w : σ → ℕ) (r : ℚ) :
    F.RealPolynomialSymbolGroup w →* F.RealPolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.map (F.realPolynomialSymbolDilation w r)

@[simp] theorem realPolynomialSymbolDilationHom_coord (w : σ → ℕ) (r : ℚ)
    (g : F.RealPolynomialSymbolGroup w) :
    (F.realPolynomialSymbolDilationHom w r g).coord = F.realPolynomialSymbolDilation w r g.coord := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedCubeIntegerSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerGridCoefficient {X J : Type*} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) [NeZero M] (k : J → Fin M) : ℂ :=
  p.complexMean (fun x => rectangularGridCharacter M k (Y x))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedSliceIntegerImage
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def integerGridApproximation {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (K M : ℕ) [NeZero M]
    (S : Finset (J → Fin M)) (z : J → ℤ) : ℂ :=
  ((K : ℂ) / M) ^ Fintype.card J * ∑ k ∈ S, integerGridCoefficient p Y M k * star (rectangularGridCharacter M k z)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FourierLawTransport
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

structure IntegerFourierAxis where
  Source : Type
  Coordinate : Type
  [sourceFinite : Fintype Source]
  [coordinateFinite : Fintype Coordinate]
  scale : ℕ
  [scaleNeZero : NeZero scale]
  radius : ℕ
  period : ℕ
  [periodNeZero : NeZero period]
  scale_le_period : scale ≤ period
  law : FiniteProbabilityWeights Source
  image : (Coordinate → ℤ) → Source → Coordinate → ℤ
  countConstant : ℝ
  countExponent : ℕ
  coefficientCap : ℝ
  denominatorBound : ℝ → ℝ
  residualBound : ℝ → ℝ
  approximation : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∃ S : Finset (Coordinate → Fin period),
      (S.card : ℝ) ≤ countConstant / ε ^ countExponent ∧
      (∀ center, (∑ k, ‖integerGridCoefficient law (image center) period k‖) ≤
        coefficientCap) ∧
      (∀ k ∈ S, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ denominatorBound ε ∧
        ∃ (a : Coordinate → ℤ) (ξ : Coordinate → ℝ),
          (∀ j, |ξ j| ≤ residualBound ε) ∧
          ∀ j, ((k j).val : ℝ) / period = (a j : ℝ) / d + ξ j / scale) ∧
      ∀ center z, centeredFundamentalBox radius scale center z →
        ‖(((scale : ℝ) ^ Fintype.card Coordinate * finiteImageMass law (image center) z : ℝ) : ℂ) -
          integerGridApproximation law (image center) scale period S z‖ ≤ ε

attribute [local instance] IntegerFourierAxis.sourceFinite IntegerFourierAxis.coordinateFinite
  IntegerFourierAxis.scaleNeZero IntegerFourierAxis.periodNeZero

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeNilsequenceExpansion
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def conjugate (T : D.Niltest w) : D.Niltest w where
  orbit := T.orbit
  observable := fun x => star (T.observable x)
  normBound := T.normBound
  lipBound := T.lipBound
  norm_le x := by simpa only [norm_star] using T.norm_le x
  lipschitz := by
    let := D.metricSpace
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, ← star_sub, norm_star] using T.lipschitz.dist_le_mul x y

@[simp] theorem eval_conjugate (T : D.Niltest w) (x : σ → ℤ) :
    T.conjugate.eval x = star (T.eval x) := rfl

@[simp] theorem conjugate_complexityLE (T : D.Niltest w) (p : ℝ) :
    T.conjugate.ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeNilsequenceExpansion (s N : ℕ) [NeZero N] (p : ℝ) (f : ZMod N → ℂ) where
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
  test : ∀ i, (model i).Niltest (fun _ : Unit => 1)
  complexity : ∀ i, (test i).ComplexityLE p
  coefficient : Fin count → ℂ
  cost : (∑ i, ‖coefficient i‖) ≤ Real.exp p
  eval : ∀ x, f x = ∑ i, coefficient i * (test i).evalCyclic N (fun _ => x)

attribute [local instance] NativeNilsequenceExpansion.lie NativeNilsequenceExpansion.algebra
  NativeNilsequenceExpansion.topology NativeNilsequenceExpansion.topologicalAdd
  NativeNilsequenceExpansion.continuousSMul NativeNilsequenceExpansion.hausdorff

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

noncomputable def substitute (T : D.Niltest w) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) : D.Niltest v :=
  { T with orbit := D.filtration.realification.polynomialOrbitSubstitute f hf T.orbit }

theorem eval_substitute (T : D.Niltest w) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) (x : τ → ℤ) (y : σ → ℤ)
    (hxy : ∀ i, MvPolynomial.aeval (R := ℚ) (fun j => (x j : ℚ)) (f i) = (y i : ℚ)) :
    (T.substitute f hf).eval x = T.eval y := by
  exact congrArg (fun z : D.RealGroup => T.observable (QuotientGroup.mk z))
    (D.filtration.realification.polynomialOrbitSubstitute_eval f hf T.orbit x y hxy)

@[simp] theorem substitute_complexityLE (T : D.Niltest w) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) (p : ℝ) :
    (T.substitute f hf).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

noncomputable def affinePullback [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (A : σ → τ → ℤ) (b : σ → ℤ) : D.Niltest (fun _ : τ => 1) :=
  T.substitute (integerAffinePolynomial A b) (integerAffinePolynomial_support A b)

@[simp] theorem affinePullback_complexityLE [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (A : σ → τ → ℤ) (b : σ → ℤ) (p : ℝ) :
    (T.affinePullback A b).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

noncomputable def linearPullbackHom [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (f : σ → ((τ → ℤ) →+ ℤ)) : D.Niltest (fun _ : τ => 1) := by
  classical
  exact T.affinePullback (fun i j => f i (Pi.single j 1)) 0

@[simp] theorem linearPullbackHom_complexityLE [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (f : σ → ((τ → ℤ) →+ ℤ)) (p : ℝ) :
    (T.linearPullbackHom f).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def translate (T : D.Niltest w) (hw : ∀ i, 0 < w i) (h : σ → ℤ) : D.Niltest w :=
  { T with
    orbit := NilpotentLieFiltration.polynomialOrbitOfLog
      (VectorPolynomial.translate (fun i => (h i : ℚ)) T.orbit.log)
      (D.filtration.realification.adapted_translate w hw (fun i => (h i : ℚ)) T.orbit.adapted) }

@[simp] theorem eval_translate (T : D.Niltest w) (hw : ∀ i, 0 < w i) (h x : σ → ℤ) :
    (T.translate hw h).eval x = T.eval (x + h) := by
  apply congrArg T.observable
  apply congrArg QuotientGroup.mk
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.eval (fun i => (x i : ℚ))
      (VectorPolynomial.translate (fun i => (h i : ℚ)) T.orbit.log) =
    VectorPolynomial.eval (fun i => ((x + h) i : ℚ)) T.orbit.log
  rw [VectorPolynomial.eval_translate]
  simp only [Pi.add_apply, Int.cast_add]

@[simp] theorem translate_complexityLE (T : D.Niltest w) (hw : ∀ i, 0 < w i)
    (h : σ → ℤ) (p : ℝ) : (T.translate hw h).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {K K' L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

noncomputable def coordinateEquiv (T : D.Niltest (fun _ : K => 1)) (e : K ≃ K') :
    D.Niltest (fun _ : K' => 1) :=
  T.substitute (fun i => MvPolynomial.X (e i))
    (fun i => weightedSupportLE_X (fun _ : K' => 1) (e i))

@[simp] theorem eval_coordinateEquiv (T : D.Niltest (fun _ : K => 1)) (e : K ≃ K')
    (x : K' → ℤ) :
    (T.coordinateEquiv e).eval x = T.eval (fun i => x (e i)) := by
  exact T.eval_substitute (fun i => MvPolynomial.X (e i))
    (fun i => weightedSupportLE_X (fun _ : K' => 1) (e i))
    x (fun i => x (e i)) (fun _ => by simp)

@[simp] theorem eval_coordinateEquiv_symm (T : D.Niltest (fun _ : K => 1)) (e : K ≃ K')
    (x : K → ℤ) :
    (T.coordinateEquiv e).eval (fun j => x (e.symm j)) = T.eval x := by
  simp only [eval_coordinateEquiv, Equiv.symm_apply_apply]

@[simp] theorem coordinateEquiv_observable (T : D.Niltest (fun _ : K => 1)) (e : K ≃ K') :
    (T.coordinateEquiv e).observable = T.observable := rfl

@[simp] theorem coordinateEquiv_normBound (T : D.Niltest (fun _ : K => 1)) (e : K ≃ K') :
    (T.coordinateEquiv e).normBound = T.normBound := rfl

@[simp] theorem coordinateEquiv_lipBound (T : D.Niltest (fun _ : K => 1)) (e : K ≃ K') :
    (T.coordinateEquiv e).lipBound = T.lipBound := rfl

@[simp] theorem coordinateEquiv_complexityLE (T : D.Niltest (fun _ : K => 1))
    (e : K ≃ K') (p : ℝ) :
    (T.coordinateEquiv e).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

theorem scalarAffinePolynomial_support {σ : Type*} (r : ℚ) (shift : σ → ℚ) (i : σ) :
    scalarAffinePolynomial r shift i ∈ weightedSupportLE (fun _ : σ => 1) 1 := by
  apply Submodule.add_mem
  · exact weightedSupportLE_C _ 1 (shift i)
  · simpa only [zero_add] using
      weightedSupportLE_mul (weightedSupportLE_C (fun _ : σ => 1) 0 r)
        (weightedSupportLE_X (fun _ : σ => 1) i)

namespace RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

noncomputable def scalarAffinePullback (T : D.Niltest (fun _ : σ => 1))
    (r : ℚ) (shift : σ → ℚ) : D.Niltest (fun _ : σ => 1) :=
  T.substitute (scalarAffinePolynomial r shift) (scalarAffinePolynomial_support r shift)

@[simp] theorem scalarAffinePullback_complexityLE (T : D.Niltest (fun _ : σ => 1))
    (r : ℚ) (shift : σ → ℚ) (p : ℝ) :
    (T.scalarAffinePullback r shift).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

end OAI
end


