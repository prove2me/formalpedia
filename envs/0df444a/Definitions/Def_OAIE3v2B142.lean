-- Prove2me | Definitions.Def_OAIE3v2B142
-- name    : OAIE3v2B142
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:02:59.546774+00:00
-- url     : https://prove2.me/theorems/52bfb9c1-2e48-4aad-b6e1-46fd70a576b3
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 144 of 311
-- statement:
--   Definitions bundle 144 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B128`, `OAIE3v2B129`, `OAIE3v2B130`, `OAIE3v2B131` of this split.
--
--   Modules: `Estimates/CommonDependentWordLayers.lean`, `Estimates/NativeProductCoefficient.lean`, `Estimates/NativeSubspaceFreeModel.lean`, `Estimates/ProductiveFrozenLocalMajorFamily.lean`, `Estimates/ProjectedHorizontalFactorization.lean`, `Estimates/SquarefreeRealAction.lean`, `Fourier/AnchoredCoefficientFourierNormalization.lean`, `Geometry/ControlledGradedBaseCoordinates.lean`, `Lattices/AffineCoefficientCongruenceRemoval.lean`, `Lattices/AffineCoefficientCoverTilt.lean`, `Lattices/AffineCoefficientResidueWidths.lean`, `Lattices/DenseResidueScalarScoreNet.lean`, `Lattices/NativeIntegerAffinePullbackHom.lean`, `Lattices/NativeProperAffineRecovery.lean`, `Lattices/RelativeSliceAffineThreeFactorLaw.lean`, `Lattices/ResidueBoxSliceCoordinateDisintegration.lean`, `Lattices/ResidueBoxSliceSubtypeSites.lean`, `Linear/KernelPrincipalFiberSliceLaw.lean`, `Linear/MultiaffineTripleLayerBasis.lean`, `Linear/MultidegreeBasisConstruction.lean`, `Linear/RationalTagConstraintChartBasis.lean`, `Linear/WeightedTranslationAssociatedGradedProjection.lean`, `Nilpotent/ComparisonLayerBracket.lean`, `Nilpotent/CurrentBracketInductionStep.lean`, `Nilpotent/NiltestComplement.lean`, `Polynomial/FreeDegreeRankAdaptedBounds.lean`, `Polynomial/PositivePolynomialLayerBases.lean`, `Polynomial/QuantitativeOuterPolynomialProducts.lean`, `Polynomial/RaisedDegreeRank.lean`, `Polynomial/RealPositivePolynomialEvaluation.lean`, `Probability/CanonicalCoverLaw.lean`, `Probability/FiniteRelativeDensity.lean`, `Sampling/AllocatedDenseFiberSliceForecastGeometry.lean`, `Sampling/CoefficientUniformPerturbationSampling.lean`, `Sampling/PrecenterForecastNativeAtomDictionary.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B128
import Definitions.Def_OAIE3v2B129
import Definitions.Def_OAIE3v2B130
import Definitions.Def_OAIE3v2B131

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CurrentBracketInductionStep
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module

variable {σ : Type*} [Fintype σ]

omit [Fintype σ] in
theorem coeff_pderiv_monomial_grade (w : σ → ℕ) (d : ℕ)
    (i : σ) (a c : {a : σ →₀ ℕ | Finsupp.weight w a < d})
    (h : d - Finsupp.weight w c.val ≠ w i + (d - Finsupp.weight w a.val)) :
    (pderiv i (monomial a.val (1 : ℚ))).coeff c.val = 0 := by
  classical
  have hne : a.val ≠ c.val + Finsupp.single i 1 := by
    intro he
    have hh := congrArg (Finsupp.weight w) he
    simp only [map_add, Finsupp.weight_single, one_smul] at hh
    have ha : Finsupp.weight w a.val < d := a.property
    have hc : Finsupp.weight w c.val < d := c.property
    omega
  rw [coeff_pderiv, coeff_monomial, if_neg hne, zero_mul]

theorem weightedBasis_homogeneous_brackets (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) :
    BasisHomogeneousBrackets (weightedBasis w d hw) (weightedBasisGrade w d) := by
  classical
  intro i j k hk
  cases k with
  | inl k =>
      rw [weightedBasis_repr_inl]
      rfl
  | inr c =>
      rw [weightedBasis_repr_inr]
      change (scalarDirectionalDerivative (weightedBasis w d hw i).val.base
        (weightedBasis w d hw j).val.polynomial -
        scalarDirectionalDerivative (weightedBasis w d hw j).val.base
          (weightedBasis w d hw i).val.polynomial).coeff c.val = 0
      cases i with
      | inl i =>
          cases j with
          | inl j => simp
          | inr a =>
              simp only [weightedBasis_inl_base, weightedBasis_inr_polynomial,
                weightedBasis_inr_base, weightedBasis_inl_polynomial,
                scalarDirectionalDerivative_direction_zero, sub_zero,
                single_direction_derivative]
              exact coeff_pderiv_monomial_grade w d i a c hk
      | inr a =>
          cases j with
          | inl i =>
              simp only [weightedBasis_inl_base, weightedBasis_inr_polynomial,
                weightedBasis_inr_base, weightedBasis_inl_polynomial,
                scalarDirectionalDerivative_direction_zero, zero_sub,
                single_direction_derivative, coeff_neg, neg_eq_zero]
              exact coeff_pderiv_monomial_grade w d i a c (by
                simpa only [weightedBasisGrade_inl, weightedBasisGrade_inr, Nat.add_comm] using hk)
          | inr b => simp

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {s : ℕ}

noncomputable def positiveUnivariate (v : Fin s → V) : VectorPolynomial Unit ℚ V :=
  ∑ d, monomial (Finsupp.single () (d.val + 1)) (v d)

theorem positiveUnivariate_coefficient (v : Fin s → V) (d : Fin s) :
    coefficients (positiveUnivariate v) (Finsupp.single () (d.val + 1)) = v d := by
  classical
  simp only [positiveUnivariate, map_sum, Finsupp.finsetSum_apply, coefficients_monomial]
  rw [Finset.sum_eq_single d]
  · simp only [Finsupp.single_eq_same]
  · intro j _ hj
    apply Finsupp.single_eq_of_ne
    intro heq
    apply hj
    apply Fin.ext
    have h := congrArg (fun α : Unit →₀ ℕ => α ()) heq
    simp only [Finsupp.single_eq_same] at h
    omega
  · simp

theorem positiveUnivariate_coefficient_eq_zero (v : Fin s → V) (α : Unit →₀ ℕ)
    (hα : ∀ d : Fin s, Finsupp.single () (d.val + 1) ≠ α) :
    coefficients (positiveUnivariate v) α = 0 := by
  classical
  simp only [positiveUnivariate, map_sum, Finsupp.finsetSum_apply, coefficients_monomial]
  exact Finset.sum_eq_zero (fun d _ => Finsupp.single_eq_of_ne (hα d).symm)

theorem positiveUnivariate_coefficients_mem (v : Fin s → V) (U : (Unit →₀ ℕ) → Submodule ℚ V)
    (hv : ∀ d, v d ∈ U (Finsupp.single () (d.val + 1))) :
    ∀ α, coefficients (positiveUnivariate v) α ∈ U α := by
  intro α
  by_cases hα : ∃ d : Fin s, Finsupp.single () (d.val + 1) = α
  · obtain ⟨d, rfl⟩ := hα
    rw [positiveUnivariate_coefficient]
    exact hv d
  · rw [positiveUnivariate_coefficient_eq_zero v α (by simpa only [not_exists] using hα)]
    exact (U α).zero_mem

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FreeDegreeRankAdaptedBounds
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem quotientLie_mem (I : LieIdeal ℚ L) {t : ℕ} (ht : t ≤ s)
    (hI : F.layer s (t + 1) ≤ I.toSubmodule) {d i : ℕ} {x : L}
    (hx : x ∈ F.layer d i) :
    lieQuotientMap I x ∈ (F.quotientLie I ht hI).layer d i := ⟨x, hx, rfl⟩

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3

namespace FreeDegreeRankLieAlgebra

variable (X : Type*) (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x)

theorem mk_surjective : Function.Surjective (mk X s r w hw) := lieQuotientMap_surjective _

noncomputable def projection : FreeNilpotentLieAlgebra X s →ₗ⁅ℚ⁆ FreeDegreeRankLieAlgebra X s r w hw :=
  (mk X s r w hw).comp (FreeWeightedNilpotentLieAlgebra.mk X s w)

theorem projection_surjective : Function.Surjective (projection X s r w hw) :=
  (mk_surjective X s r w hw).comp (FreeWeightedNilpotentLieAlgebra.mk_surjective X s w)

instance finite [Fintype X] : Module.Finite ℚ (FreeDegreeRankLieAlgebra X s r w hw) :=
  Module.Finite.of_surjective (mk X s r w hw).toLinearMap (mk_surjective X s r w hw)

end FreeDegreeRankLieAlgebra

end Erdos3

end

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (G : DegreeRankLieFiltration L s r) (w : X → ℕ) (hw : ∀ x, 0 < w x)
  (f : X → L) (hf : ∀ x, f x ∈ G.layer (w x) 0)

namespace FreeDegreeRankLieAlgebra

theorem lift_projection (x : FreeNilpotentLieAlgebra X s) :
    lift G w hw f hf (projection X s r w hw x) =
      FreeNilpotentLieAlgebra.lift f G.associatedDegree.lowerCentralSeries_eq_bot x := rfl

theorem lift_mem_layer (hr : r ≤ s) {d i : ℕ} {x : FreeDegreeRankLieAlgebra X s r w hw}
    (hx : x ∈ (filtration X s r w hw hr).layer d i) : lift G w hw f hf x ∈ G.layer d i := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact FreeWeightedNilpotentLieAlgebra.lift_mem_degreeRank G w hw f hf ha

theorem hom_ext {φ ψ : FreeDegreeRankLieAlgebra X s r w hw →ₗ⁅ℚ⁆ L}
    (h : ∀ x, φ (of X s r w hw x) = ψ (of X s r w hw x)) : φ = ψ := by
  have heq : φ.comp (mk X s r w hw) = ψ.comp (mk X s r w hw) :=
    FreeWeightedNilpotentLieAlgebra.hom_ext w h
  apply LieHom.ext
  intro x
  obtain ⟨a, rfl⟩ := mk_surjective X s r w hw x
  exact LieHom.congr_fun heq a

end FreeDegreeRankLieAlgebra

end Erdos3

end

section

namespace Erdos3

namespace FreeWeightedNilpotentLieAlgebra

variable (X : Type*) [Fintype X] (s : ℕ) (w : X → ℕ)

theorem canonicalRankGenerators_span (hw : ∀ x, 0 < w x) (d k : ℕ) :
    Submodule.span ℚ (canonicalRankGenerators X s w d k : Set _) =
      (filtration X s w hw).rankLayer d k := by
  classical
  rw [(filtration X s w hw).rankLayer_eq_weighted_tree_span
    (rankAlphabetVector X s w) (rankAlphabetWeight X s w) (rankAlphabetWeight_pos X s w)
    (rankAlphabetVector_mem X s w hw) (rankAlphabet_spans_layer X s w hw)]
  simp only [canonicalRankGenerators, Finset.coe_union, Submodule.span_union]
  rw [← layer_eq_span X s w hw (d + 1),
    weightedLieTreeSpan_eq_finite_span _ _ (rankAlphabetWeight_pos X s w)]

end FreeWeightedNilpotentLieAlgebra

namespace FreeDegreeRankLieAlgebra

open Module

variable (X : Type*) [Fintype X] (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x)

noncomputable def layerGenerators (d k : ℕ) : Finset (FreeDegreeRankLieAlgebra X s r w hw) := by
  classical
  exact (FreeWeightedNilpotentLieAlgebra.canonicalRankGenerators X s w d k).image (mk X s r w hw)

theorem layer_eq_span (hr : r ≤ s) (d k : ℕ) :
    (filtration X s r w hw hr).layer d k = Submodule.span ℚ (layerGenerators X s r w hw d k : Set _) := by
  classical
  change ((FreeWeightedNilpotentLieAlgebra.filtration X s w hw).rankLayer d k).map
    (mk X s r w hw).toLinearMap = _
  rw [← FreeWeightedNilpotentLieAlgebra.canonicalRankGenerators_span X s w hw d k, Submodule.map_span]
  simp only [layerGenerators, Finset.coe_image]
  rfl

noncomputable def layerFamily (hr : r ≤ s) (d k : ℕ)
    (x : layerGenerators X s r w hw d k) : (filtration X s r w hw hr).layer d k :=
  ⟨x.val, by rw [layer_eq_span]; exact Submodule.subset_span x.property⟩

theorem layerFamily_span (hr : r ≤ s) (d k : ℕ) :
    Submodule.span ℚ (Set.range (layerFamily X s r w hw hr d k)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff _ _).mpr
  have hrange : Set.range (Subtype.val : layerGenerators X s r w hw d k →
      FreeDegreeRankLieAlgebra X s r w hw) = (layerGenerators X s r w hw d k : Set _) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [hrange]
  exact (layer_eq_span X s r w hw hr d k).symm

theorem layerGenerators_logHeight {ι : Type*} [Fintype ι]
    (b : Basis ι ℚ (FreeDegreeRankLieAlgebra X s r w hw)) {p : ℝ}
    (hp : 0 ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p)
    (hgen : ∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
      rationalLogHeight (b.repr (projection X s r w hw x) i) ≤ p)
    (d k : ℕ) (hd : d ≤ s) (x : FreeDegreeRankLieAlgebra X s r w hw)
    (hx : x ∈ layerGenerators X s r w hw d k) (j : ι) :
    rationalLogHeight (b.repr x j) ≤ (p + 3) ^ (6 * s + 2) := by
  classical
  let H := ⌈Real.exp p⌉₊
  have hv (a : FreeWeightedNilpotentLieAlgebra.RankAlphabet X s w) (i : ι) :
      RationalHeightLE (b.repr (mk X s r w hw (FreeWeightedNilpotentLieAlgebra.rankAlphabetVector X s w a)) i) H := by
    obtain ⟨z, hz, hza⟩ := Finset.mem_image.mp a.2.property
    change RationalHeightLE (b.repr (mk X s r w hw a.2.val) i) H
    rw [← hza]
    exact rationalHeightLE_ceil_exp
      (hgen z (FreeNilpotentLieAlgebra.weightedLayerGenerators_subset X s w _ hz) i)
  have hraw : RationalHeightLE (b.repr x j) (lieTreeHeight (Fintype.card ι) H s) := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact (rationalHeightLE_ceil_exp
        (hgen z (FreeNilpotentLieAlgebra.weightedLayerGenerators_subset X s w _ hz) j)).mono
          (lieTreeHeight_ge_input _ _ _)
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      rw [map_lieTreeEval]
      exact (finiteLieTrees_coordinate_height b
        (fun a => mk X s r w hw (FreeWeightedNilpotentLieAlgebra.rankAlphabetVector X s w a))
        (fun i j k => rationalHeightLE_ceil_exp (hc i j k)) hv d a (Finset.mem_filter.mp ha).1 j).mono
          (lieTreeHeight_mono _ _ hd)
  apply rationalLogHeight_le_of_height hraw
  simpa only [show p + 1 + 2 = p + 3 by ring] using
    lieTreeHeight_le_exp (Fintype.card ι) H s
      (hp.trans (le_add_of_nonneg_right zero_le_one))
      (hn.trans (le_add_of_nonneg_right zero_le_one)) (ceil_exp_le_exp_add_one hp)

end FreeDegreeRankLieAlgebra

end Erdos3

end

section

namespace Erdos3.FreeDegreeRankLieAlgebra

open Module
open scoped Matrix

variable {X ι κ L : Type*} [Fintype X] [Fintype ι] [Fintype κ] [DecidableEq κ]
  [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}

theorem lift_basis_matrix_logHeight
    (F : DegreeRankLieFiltration L s r) (w : X → ℕ) (hw : ∀ x, 0 < w x) (f : X → L)
    (hf : ∀ x, f x ∈ F.layer (w x) 0)
    (e : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s))
    (he : ∀ i, e i ∈ FreeNilpotentLieAlgebra.treeGenerators X s)
    (b : Basis κ ℚ (FreeDegreeRankLieAlgebra X s r w hw)) (t : Basis ι ℚ L)
    (S : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) κ ℚ)
    (hS : LinearMap.toMatrix e b (projection X s r w hw).toLinearMap * S = 1)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ p)
    (ht : (Fintype.card ι : ℝ) ≤ p)
    (hSH : ∀ i j, rationalLogHeight (S i j) ≤ p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants t i j k) ≤ p)
    (hg : ∀ x i, rationalLogHeight (t.repr (f x) i) ≤ p) (i : ι) (j : κ) :
    rationalLogHeight (LinearMap.toMatrix b t (lift F w hw f hf).toLinearMap i j) ≤
      ((p + 3) ^ (6 * s + 2) + p + 2) ^ 4 := by
  classical
  let R := (p + 3) ^ (6 * s + 2) + p
  have hpR : p ≤ R := le_add_of_nonneg_left (by positivity)
  have hpowR : (p + 3) ^ (6 * s + 2) ≤ R := le_add_of_nonneg_right hp
  let σ := Matrix.toLin b e S
  have hσ : projection X s r w hw (σ (b j)) = b j := basisMatrix_section e b (projection X s r w hw).toLinearMap S hS (b j)
  have hcoord (k) : e.repr (σ (b j)) k = S k j := by
    simpa only [σ, LinearMap.toMatrix_toLin] using
      (LinearMap.toMatrix_apply b e (Matrix.toLin b e S) k j).symm
  rw [LinearMap.toMatrix_apply]
  have heval : lift F w hw f hf (b j) =
      FreeNilpotentLieAlgebra.lift f F.associatedDegree.lowerCentralSeries_eq_bot (σ (b j)) := by
    calc
      _ = lift F w hw f hf (projection X s r w hw (σ (b j))) := congrArg (lift F w hw f hf) hσ.symm
      _ = _ := lift_projection F w hw f hf (σ (b j))
  change rationalLogHeight (t.repr (lift F w hw f hf (b j)) i) ≤ (R + 2) ^ 4
  rw [heval]
  apply linearMap_coordinate_logHeight e t
    (FreeNilpotentLieAlgebra.lift f F.associatedDegree.lowerCentralSeries_eq_bot).toLinearMap (hp.trans hpR)
    (by simpa only [Fintype.card_fin] using hn.trans hpR) ?_ (σ (b j)) ?_ i
  · intro u v
    have h := FreeNilpotentLieAlgebra.lift_basis_matrix_logHeight t f
      F.associatedDegree.lowerCentralSeries_eq_bot e he hp ht hc hg v u
    apply le_trans _ hpowR
    simpa only [LinearMap.toMatrix_apply] using h
  · intro k
    rw [hcoord]
    exact (hSH k j).trans hpR

end Erdos3.FreeDegreeRankLieAlgebra

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProjectedHorizontalFactorization
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration M t)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

theorem projectedHorizontal_factorization (ht : 1 ≤ t) (b : Basis ι ℚ M) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (T : σ → ℝ) (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ) (l : ℕ)
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hfactor : F.SymbolFactorizationIn b ω hF T X p l U) :
    ∃ E R : F.RealPolynomialSymbolGroup (fun _ : σ => 1),
      F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp p) E ∧
      F.SymbolRationalGrid b ω hF (fun _ => 1) l R ∧
      ∀ α : σ →₀ ℕ,
        (G.projectedHorizontalSymbolCoefficient F φ hφ (fun _ => 1) α).baseChange ℝ X.coord -
          (G.projectedHorizontalSymbolCoefficient F φ hφ (fun _ => 1) α).baseChange ℝ E.coord -
          (G.projectedHorizontalSymbolCoefficient F φ hφ (fun _ => 1) α).baseChange ℝ R.coord ∈
        (G.layerHorizontalImage (F.gradedRefiltrationLayer U) φ
          (fun d x hx => hφ d x (F.gradedRefiltrationLayer_le U d hx))
            (Finsupp.weight (fun _ => 1) α)).baseChange ℝ := by
  obtain ⟨E, P, R, hprod, hE, hR, hP⟩ := hfactor
  refine ⟨E, R, hE, hR, ?_⟩
  intro α
  let f := (G.projectedHorizontalSymbolCoefficient F φ hφ (fun _ : σ => 1) α).baseChange ℝ
  have hsum := congrArg (G.realProjectedHorizontalSymbolHom F φ hφ ht (fun _ : σ => 1) α) hprod
  rw [map_mul, map_mul] at hsum
  have hsum' := congrArg Multiplicative.toAdd hsum
  change f E.coord + f P.coord + f R.coord = f X.coord at hsum'
  have hres : f X.coord - f E.coord - f R.coord = f P.coord := by
    rw [← hsum']
    abel
  change f X.coord - f E.coord - f R.coord ∈ _
  rw [hres]
  exact G.real_projectedHorizontalSymbolCoefficient_mem F φ hφ b ω hF (fun _ => 1) U P.coord hP α

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeRealAction
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonGraph (a : σ → ℕ) (ha : a ≠ 0) :
    F.layer a →ₗ[ℚ] (L × F.SquarefreeAlgebra π) :=
  (F.layer a).subtype.prod (F.blockLayerMap π a ha)

theorem comparisonGraph_mem_degree (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a)
    (n : ℕ) (hn : n ≤ ∑ i, a i) :
    F.comparisonGraph π a ha x ∈ (F.ordinary.layer n).prod (F.squarefreeDegreeLayer π n) :=
  ⟨F.ordinary.antitone hn (F.layer_le_ordinary a x.property),
    F.squarefreeDegreeLayer_antitone π hn (F.blockLayerMap_mem_degree π a ha x)⟩

theorem comparisonGraph_lie (a b : σ → ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0)
    (x : F.layer a) (y : F.layer b) :
    ⁅F.comparisonGraph π a ha x, F.comparisonGraph π b hb y⁆ =
      F.comparisonGraph π (a + b) hab ⟨⁅x.val, y.val⁆, F.lie_mem x.property y.property⟩ :=
  Prod.ext rfl (F.blockLayerMap_lie π a b ha hb hab x y)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonGraphLayer (n : ℕ) : Submodule ℚ (L × F.SquarefreeAlgebra π) := by
  classical
  exact ⨆ a : {a : σ → ℕ // a ≠ 0},
    if n ≤ ∑ i, a.val i then LinearMap.range (F.comparisonGraph π a.val a.property) else ⊥

theorem comparisonGraph_mem_graphLayer (n : ℕ) (a : σ → ℕ) (ha : a ≠ 0)
    (hn : n ≤ ∑ i, a i) (x : F.layer a) :
    F.comparisonGraph π a ha x ∈ F.comparisonGraphLayer π n := by
  classical
  have hle : LinearMap.range (F.comparisonGraph π a ha) ≤ F.comparisonGraphLayer π n := by
    unfold comparisonGraphLayer
    apply le_iSup_of_le (⟨a, ha⟩ : {a : σ → ℕ // a ≠ 0})
    rw [if_pos hn]
  exact hle ⟨x, rfl⟩

theorem comparisonGraphLayer_induction (n : ℕ) {P : L × F.SquarefreeAlgebra π → Prop}
    {x : L × F.SquarefreeAlgebra π} (hx : x ∈ F.comparisonGraphLayer π n)
    (hgraph : ∀ (a : σ → ℕ) (ha : a ≠ 0), n ≤ ∑ i, a i →
      ∀ y : F.layer a, P (F.comparisonGraph π a ha y))
    (hzero : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) : P x := by
  classical
  refine Submodule.iSup_induction (motive := P) _ hx ?_ hzero hadd
  intro a y hy
  by_cases hn : n ≤ ∑ i, a.val i
  · rw [if_pos hn] at hy
    obtain ⟨z, rfl⟩ := hy
    exact hgraph a.val a.property hn z
  · rw [if_neg hn, Submodule.mem_bot] at hy
    simpa only [hy] using hzero

theorem comparisonGraphLayer_antitone : Antitone (F.comparisonGraphLayer π) := by
  intro n m hnm x hx
  apply F.comparisonGraphLayer_induction π m hx
  · intro a ha hm y
    exact F.comparisonGraph_mem_graphLayer π n a ha (hnm.trans hm) y
  · exact Submodule.zero_mem _
  · intro x y hx hy
    exact Submodule.add_mem _ hx hy

theorem comparisonGraphLayer_le_degree (n : ℕ) :
    F.comparisonGraphLayer π n ≤ (F.ordinary.layer n).prod (F.squarefreeDegreeLayer π n) := by
  intro x hx
  apply F.comparisonGraphLayer_induction π n hx
  · intro a ha hn y
    exact F.comparisonGraph_mem_degree π a ha y n hn
  · exact Submodule.zero_mem _
  · intro x y hx hy
    exact Submodule.add_mem _ hx hy

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonLayer (n : ℕ) : Submodule ℚ (L × F.SquarefreeAlgebra π) :=
  F.comparisonProductLayer π (n + 1) ⊔ F.comparisonGraphLayer π n

theorem comparisonLayer_antitone : Antitone (F.comparisonLayer π) := by
  intro n m h
  exact sup_le_sup (F.comparisonProductLayer_antitone π (Nat.add_le_add_right h 1))
    (F.comparisonGraphLayer_antitone π h)

theorem comparisonLayer_le_product (n : ℕ) :
    F.comparisonLayer π n ≤ F.comparisonProductLayer π n :=
  sup_le (F.comparisonProductLayer_antitone π (Nat.le_succ n)) (F.comparisonGraphLayer_le_degree π n)

theorem comparisonLayer_terminal : F.comparisonLayer π (max s (Fintype.card ι) + 1) = ⊥ := by
  apply bot_unique
  exact (F.comparisonLayer_le_product π _).trans (F.comparisonProductLayer_terminal π).le

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientResidueWidths
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_affine_coefficient_local_removal {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) {C : ℝ}
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (N stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R : ℝ} (hζ : 0 < ζ) (hN : ∀ i : Fin m, ∀ k, multiaffineBiasBudget i.val ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((stride k : ℝ) * (N k : ℝ)))
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hrowBudget : ∀ i : Fin m, ((i.val + 1).factorial : ℝ) * C ≤ R)
    (hdenom : ∀ i : Fin m, (∏ j : Fin (i.val + 1) → I,
      (multiaffineBiasBudget i.val ζ * ∏ r, (stride (j r) : ℝ))) ≤ R)
    (hcoeff : ∀ i : Fin m, (Fintype.card I : ℝ) ^ (i.val + 1) *
      (A ^ (i.val + 1) * multiaffineBiasBudget i.val ζ) ≤ R)
    {β : ℝ} (hβ : 0 ≤ β) (hpower : ∀ i : Fin m, ζ ≤ β ^ (2 ^ (i.val + 1))) :
    ∃ i : Fin m, ∃ rows : Fin (i.val + 1) → Option K → ℤ,
      (∀ a k, |(rows a k : ℝ)| ≤ 1) ∧
      ∀ base : Option K → I → ℝ,
        ‖𝔼 x : Fin (i.val + 1) → ∀ j, Fin (N j),
          layeredCoefficientCharacter
            (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
            p (rowShiftedTuple base rows
              (fun (y : ∀ j, Fin (N j)) j => (stride j : ℝ) * ((y j).val : ℝ)) x)‖ ≤ β := by
  classical
  let L := fun j => coefficientFunctional (fun d a => (frequency j d a : ℝ))
  let site : Empty → K → ℝ := Empty.elim
  have hf (i : Fin m) := homogeneous_empty_factorization_iff
    ((affineModeLift (L i)).comp (map (U i).subtype)) (i.val + 1)
    (fun s (k : Option K) => k.elim 1 (site s))
  have hbad' : ∃ i, ¬∃ M : (Empty → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P → affineModeLift (L i) (map (U i).subtype P) =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) P) := by
    obtain ⟨i, P, hP, hn⟩ := hbad
    exact ⟨i, fun h => hn ((hf i).mp h P hP)⟩
  obtain ⟨i, hi, hfactor⟩ := exists_highest_affine_subspace_nonfactor U site L hbad'
  have hn := mt (hf i).mpr hi
  simp only [not_forall, LinearMap.comp_apply] at hn
  obtain ⟨P, hP, hnP⟩ := hn
  obtain ⟨rows, hrows, hcontract, hnonzero⟩ := exists_unit_integer_mode_rows (U i)
    (affineLiftFrequency (frequency i)) (affineLiftFrequency_bound _ (hbound i))
    (by exact ⟨P, hP, by simpa only [L, affineModeLift_integerFrequency] using hnP⟩)
  have hsite : (fun (s : Empty) (k : Option K) => (((Empty.elim s : Option K → ℤ) k : ℤ) : ℝ)) =
      (fun s (k : Option K) => k.elim 1 (site s)) := Subsingleton.elim _ _
  obtain ⟨Q', hQ', test', ht, he⟩ := exists_subspace_layered_mode_reduction i U
    (fun j => affineModeLift (L j)) p hm hp (Empty.elim : Empty → Option K → ℤ)
    (by rw [hsite]; exact hfactor) 0 (by simp) Empty.elim (fun s => s.elim)
  have he' (b : Option K → I → ℝ) :
      layeredCoefficientCharacter (fun j => affineModeLift (L j)) p b =
        coefficientModeTestedPhase
          (coefficientFunctional (fun d a => ((affineLiftFrequency (frequency i) d a : ℤ) : ℝ)))
          (p i) Q' Empty.elim test' b := by
    simpa only [layeredModeTestedPhase_empty_zero, L, affineModeLift_integerFrequency] using he b
  refine ⟨i, rows, hrows, ?_⟩
  intro base
  change ‖𝔼 x : Fin (i.val + 1) → ∀ j, Fin (N j),
    layeredCoefficientCharacter (fun j => affineModeLift (L j)) p
      (rowShiftedTuple base rows
        (fun (y : ∀ j, Fin (N j)) j => (stride j : ℝ) * ((y j).val : ℝ)) x)‖ ≤ β
  simp_rw [he']
  exact inhomogeneous_coefficient_mode_local_removal (affineLiftFrequency (frequency i)) rows
    (p i) (hp i) (U i) N stride hs hζ (hN i) H hH hA hscale (hrank i)
    hcontract (hrowBudget i) hnonzero (hdenom i) (hcoeff i)
    Empty.elim (fun s => s.elim) Q' hQ' test' ht hβ (hpower i) base

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem affine_coefficient_mode_residue_removal {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) {C : ℝ}
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (N stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R : ℝ} (hζ : 0 < ζ) (hN : ∀ i : Fin m, ∀ k, multiaffineBiasBudget i.val ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((stride k : ℝ) * (N k : ℝ)))
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hrowBudget : ∀ i : Fin m, ((i.val + 1).factorial : ℝ) * C ≤ R)
    (hdenom : ∀ i : Fin m, (∏ j : Fin (i.val + 1) → I,
      (multiaffineBiasBudget i.val ζ * ∏ r, (stride (j r) : ℝ))) ≤ R)
    (hcoeff : ∀ i : Fin m, (Fintype.card I : ℝ) ^ (i.val + 1) *
      (A ^ (i.val + 1) * multiaffineBiasBudget i.val ζ) ≤ R)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V))
    (hV1 : ∀ z, 1 ≤ residueProfileWidth stride V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ z, 1 / residueProfileWidth stride V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (Option K × I) *
      ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {r β : ℝ} (hr : 0 ≤ r)
    (hmove : ∀ i : Fin m, ∀ z,
      ((i.val + 1 : ℕ) : ℝ) * ((stride z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z)
    (hβ : 0 ≤ β) (hpower : ∀ i : Fin m, ζ ≤ β ^ (2 ^ (i.val + 1))) :
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (Option K × I) *
        ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * r + β := by
  obtain ⟨i, rows, hrows, hlocal⟩ := exists_affine_coefficient_local_removal
    U frequency hbound hbad p hp hm N stride hs hζ hN
    H hH hA hscale hrank hrowBudget hdenom hcoeff hβ hpower
  have hNp k : 0 < N k := by
    exact_mod_cast (multiaffineBiasBudget_pos i.val hζ).trans_le (hN i k)
  exact residue_smooth_row_shift_transfer N stride hNp hs rows residue V hV hZ hV1
    hδ hδ1 hmesh hsmall zero_le_one hrows hr (by simpa only [mul_one] using hmove i)
    _ (fun b => (layeredCoefficientCharacter_norm _ p b).le) hlocal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

theorem affine_coefficient_residue_removal_of_widths {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R T S : ℝ} (hζ : 0 < ζ) (hT : 0 < T) (hS : 0 ≤ S)
    (hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (hH : ∀ k, 0 < H k)
    (hsize : ∀ k, (stride k : ℝ) * T * (finiteLayerBiasBudget m ζ + 1) ≤ H k)
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hR : layerRemovalRankBudget m (Fintype.card I) C 1
      (finiteLayerBiasBudget m ζ) (2 * T) S ≤ R)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V))
    (hV1 : ∀ z, 1 ≤ residueProfileWidth stride V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ z, 1 / residueProfileWidth stride V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (Option K × I) *
      ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {ρ r β : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r)
    (hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (hmove : (m : ℝ) * 1 ≤ r * ρ * T)
    (hβ : 0 ≤ β) (hpower : ∀ i : Fin m, ζ ≤ β ^ (2 ^ (i.val + 1))) :
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (Option K × I) *
        ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * r + β := by
  classical
  let B := finiteLayerBiasBudget m ζ
  let D : ℝ := 1
  have hB : 1 ≤ B := finiteLayerBiasBudget_one_le m hζ
  have hD : 0 ≤ D := zero_le_one
  have hA : 0 ≤ 2 * T := by positivity
  have hb (i : Fin m) : multiaffineBiasBudget i.val ζ ≤ B :=
    multiaffineBiasBudget_le_finite i hζ
  obtain ⟨N, hN, hscale, hshift⟩ := exists_mode_shift_lengths m hT hB hρ hr hmove H stride hs hsize V hwidth
  have hbud (i : Fin m) := layerRemovalRankBudget_bounds i (Fintype.card I) hC hD
    (zero_le_one.trans hB) hA hS
  apply affine_coefficient_mode_residue_removal U frequency hbound hbad
    p hp hm N stride hs hζ (fun i k => (hb i).trans (hN k)) H hH hA hscale hrank
    (fun i => by simpa only [D, one_pow, mul_one] using (hbud i).1.trans hR) _ _ residue V hV hZ hV1 hδ hδ1 hmesh hsmall hr _ hβ hpower
  · intro i
    have hi := tensorDenominatorBound_le (H := Fin (i.val + 1))
      (multiaffineBiasBudget_pos i.val hζ).le (fun k => (stride k : ℝ))
      (fun k => Nat.cast_nonneg _) hstride
    have hi' : (∏ j : Fin (i.val + 1) → I,
        (multiaffineBiasBudget i.val ζ * ∏ r, (stride (j r) : ℝ))) ≤
        (multiaffineBiasBudget i.val ζ * S ^ (i.val + 1)) ^ (Fintype.card I ^ (i.val + 1)) := by
      simpa only [Fintype.card_fin] using hi
    apply hi'.trans
    apply le_trans _ ((hbud i).2.1.trans hR)
    exact pow_le_pow_left₀
      (mul_nonneg (multiaffineBiasBudget_pos i.val hζ).le (pow_nonneg hS _))
      (mul_le_mul_of_nonneg_right (hb i) (pow_nonneg hS _)) _
  · intro i
    apply le_trans _ ((hbud i).2.2.trans hR)
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hb i) (pow_nonneg hA _))
      (pow_nonneg (Nat.cast_nonneg _) _)
  · intro i z
    have hi : ((i.val + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    have hs' : (m : ℝ) * ((stride z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z := by
      simpa only [mul_one] using hshift z
    exact (mul_le_mul_of_nonneg_right hi
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).trans hs'

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientCongruenceRemoval
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem affine_coefficient_residue_removal_at_error {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε)
    (hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (hsize : ∀ k, modeResidueSideThreshold m (Fintype.card (Option K × I))
      1 S ρ ε ≤ H k)
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hR : modeRemovalRankThreshold m (Fintype.card I) (Fintype.card (Option K × I))
      C 1 S ρ ε ≤ R)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hwidth : ∀ z, ρ * H z.2 ≤ V z) :
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ))‖ ≤ ε := by
  classical
  let d := Fintype.card (Option K × I)
  let D : ℝ := 1
  let T := modeRemovalShrink m d D ρ ε
  let B := finiteLayerBiasBudget m (modeRemovalBias m ε)
  have hD : 0 ≤ D := zero_le_one
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (modeRemovalShrink_one_le m d hD hρ hε)
  have hB : 1 ≤ B := finiteLayerBiasBudget_one_le m (modeRemovalBias_pos m hε)
  have hside := modeRemovalSideThreshold_bounds m d hD hS hρ hε
  have hsizeBase k : modeRemovalSideThreshold m d D S ρ ε ≤ H k :=
    (modeResidueSideThreshold_bounds m d hD hS hρ hε).1.trans (hsize k)
  have hH k : 0 < H k := hside.1.trans_le (hsizeBase k)
  have hsize' k : (stride k : ℝ) * T * (B + 1) ≤ H k := by
    calc
      _ ≤ S * T * (B + 1) := by gcongr; exact hstride k
      _ ≤ H k := hside.2.1.trans (hsizeBase k)
  have hv z : 1 ≤ residueProfileWidth stride V z ∧
      1 / residueProfileWidth stride V z ≤ modeRemovalMesh d :=
    modeResidueWidth_mesh m d hD hS hρ hε (hs z.2) (hstride z.2) (hsize z.2) (hV z) (hwidth z)
  have hmass := shiftedSmoothProductMass_lower (residueProfileCenter residue stride)
    (residueProfileWidth stride V) (residueProfileWidth_pos stride V hs hV)
    (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d) (fun z => (hv z).2) (modeRemovalMesh_small d)
  have hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V) :=
    (div_pos (Finset.prod_pos (fun z _ => residueProfileWidth_pos stride V hs hV z)) (by norm_num)).trans_le hmass
  refine ⟨hZ, ?_⟩
  have hout := affine_coefficient_residue_removal_of_widths U hC frequency hbound hbad
    p hp hm stride hs (modeRemovalBias_pos m hε) hT hS hstride H hH hsize' hrank hR
    residue V hV hZ (fun z => (hv z).1) (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d)
    (fun z => (hv z).2) (modeRemovalMesh_small d) hρ (modeRemovalRadius_pos d hε).le hwidth
    (modeRemovalShrink_move m d hρ hε) (modeRemovalBeta_pos hε).le (fun i => modeRemovalBias_le i hε)
  exact hout.trans (modeRemovalError_bound d hε)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_affine_coefficient_residue_uniform_removal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride _hs V hV hZ z).toReal : ℂ) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ))‖ ≤ ε := by
  obtain ⟨A, hA, hbudget⟩ := exists_mode_residue_threshold_exp_budget m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U C hC hCP frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR residue V hV hwidth
  obtain ⟨hside, hrankBudget⟩ := hbudget (Fintype.card I) (Fintype.card (Option K × I))
    P C 1 S ρ ε hP hn hd hC hCP zero_le_one (Real.one_le_exp hP) hS hSP hρ hρP hε hεP
  exact affine_coefficient_residue_removal_at_error U hC frequency hbound hbad
    p hp hm stride hs hS hρ hε hstride H (fun k => hside.trans (hsize k)) hrank
    (hrankBudget.trans hR) residue V hV hwidth

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_affine_coefficient_ambient_residue_removal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothPMF residue stride _hs V hV hZ z).toReal : ℂ) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (z (k, j) : ℝ))‖ ≤ ε := by
  obtain ⟨A, hA, hremove⟩ := exists_affine_coefficient_residue_uniform_removal m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U C hC hCP frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR residue V hV hwidth
  obtain ⟨hZ, hrem⟩ := hremove hP hn hd U hC hCP frequency hbound hbad p hp hm stride hs hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR residue V hV hwidth
  refine ⟨hZ, ?_⟩
  rw [residueSmoothPMF_expectation]
  exact hrem

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_affine_coefficient_congruence_removal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (z (k, j) : ℝ))‖ ≤ ε := by
  obtain ⟨A, hA, hremove⟩ := exists_affine_coefficient_ambient_residue_removal m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U C hC hCP frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR G hG V hV hwidth
  have hh (r : G) := hremove hP hn hd U hC hCP frequency hbound hbad p hp hm stride hs hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR (columnResidueRepresentative stride r.val) V hV hwidth
  choose hZ hrem using hh
  exact selectedResidueSmoothPMF_bound_of_cells stride hs G hG V hV hZ _ hrem

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AnchoredCoefficientFourierNormalization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem exists_affine_coefficient_fourier_normalization (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (∑ a, c a * layeredCoefficientCharacter
          (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
          p (fun k j => (z (k, j) : ℝ)))) -
      (∑ a, if affineCoefficientModeTrivial U (frequency a) then c a else 0)‖ ≤ ε := by
  classical
  obtain ⟨A₀, _, hremove⟩ := exists_affine_coefficient_congruence_removal m
  obtain ⟨A₁, _, hthreshold⟩ := exists_mode_residue_threshold_exp_budget m
  obtain ⟨A, hA, hbudget⟩ := exists_fourier_uniform_budget A₀ A₁
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
  let P' := 2 * P + 2
  let δ := fourierModeError B ε
  have hPP : P ≤ P' := by dsimp [P']; linarith
  have hEP : Real.exp P ≤ Real.exp P' := Real.exp_le_exp.mpr hPP
  have hδ : 0 < δ := fourierModeError_pos hB hε
  have hδP : 1 / δ ≤ Real.exp P' := fourierModeError_inv_le_exp hP hB hBP hε hεP
  obtain ⟨hb₀, hb₁⟩ := hbudget P hP
  obtain ⟨hside, _⟩ := hthreshold (Fintype.card I) (Fintype.card (Option K × I))
    P' C 1 S ρ δ (hP.trans hPP) (hn.trans hPP) (hd.trans hPP) hC (hCP.trans hEP)
    zero_le_one (Real.one_le_exp (hP.trans hPP)) hS (hSP.trans hEP) hρ (hρP.trans hEP) hδ hδP
  have hZ := selectedResidueSmoothWeight_pos_of_threshold m zero_le_one
    hS hρ hδ stride hs hstride H (fun j => hside.trans (hb₁.trans (hsize j))) G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  have hdiscard (a : F) (hbad : ¬affineCoefficientModeTrivial U (frequency a)) :
      ‖∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        ((1 : ℂ) * layeredCoefficientCharacter
          (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
          p (fun k j => (z (k, j) : ℝ)))‖ ≤ δ := by
    obtain ⟨_, hr⟩ := hremove (hP.trans hPP) (hn.trans hPP) (hd.trans hPP)
      U hC (hCP.trans hEP) (frequency a) (hbound a)
      ((not_affineCoefficientModeTrivial_iff U (frequency a)).mp hbad)
      p hp hm stride hs hS (hSP.trans hEP) hρ hδ (hρP.trans hEP) hδP hstride
      H (fun j => hb₀.trans (hsize j)) hrank (hb₀.trans hR) G hG V hV hwidth
    simpa only [one_mul] using hr
  have hproj := selectedResidueSmoothPMF_discard_error stride G V hV hZ (fun _ => 1) c
    (fun a z => layeredCoefficientCharacter
      (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
      p (fun k j => (z (k, j) : ℝ)))
    (fun a => affineCoefficientModeTrivial U (frequency a)) hcoefficients hδ.le hdiscard
  have hkeep (b : Option K → I → ℝ) :
      (∑ a, if affineCoefficientModeTrivial U (frequency a) then
        c a * layeredCoefficientCharacter
          (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ)))) p b
        else 0) = ∑ a, if affineCoefficientModeTrivial U (frequency a) then c a else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : affineCoefficientModeTrivial U (frequency a)
    · simp only [ha, ite_true, layeredCoefficientCharacter_eq_one_of_trivial U (frequency a) ha p hp hm b,
        mul_one]
    · simp only [ha, ite_false]
  simp only [one_mul, hkeep, selectedResidueSmoothPMF_const] at hproj
  exact hproj.trans (fourierModeError_cost_le hB hε)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientCoverTilt
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem exists_affine_coefficient_haar_comparison (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        coefficientTorusFourierSum U frequency c
          (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))) -
      (∫ x, coefficientTorusFourierSum U frequency c x ∂μ)‖ ≤ ε := by
  obtain ⟨A, hA, hnormalization⟩ := exists_affine_coefficient_fourier_normalization m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
  obtain ⟨hZ, hnorm⟩ := hnormalization hP hn hd U hC hCP frequency hbound c hB hBP hcoefficients
    p hp hm stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  rw [coefficientTorusFourierSum_integral]
  simpa only [coefficientTorusFourierSum, coefficientTorusCharacter_sample U _ p hp hm] using hnorm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem exists_affine_coefficient_haar_approximation (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f : CoefficientTorus (K := K) U → ℂ) (_hf : Integrable f μ)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖f x - coefficientTorusFourierSum U frequency c x‖ ≤ η),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        f (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))) -
      (∫ x, f x ∂μ)‖ ≤ 2 * η + ε := by
  obtain ⟨A, hA, hcomparison⟩ := exists_affine_coefficient_haar_comparison m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth f hf η hη happrox
  obtain ⟨hZ, hcomp⟩ := hcomparison hP hn hd U μ hC hCP frequency hbound c hB hBP hcoefficients
    p hp hm stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  let g := coefficientTorusFourierSum U frequency c
  let sample (z : Option K × I → ℤ) := affineSampleCoefficientTorus U p hm (fun k j => (z (k, j) : ℝ))
  let E (a : CoefficientTorus (K := K) U → ℂ) :=
    ∑' z, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) * a (sample z)
  have hfirst := selectedResidueSmoothPMF_approximation stride G V hV hZ
    (fun _ => 1) (fun z => f (sample z)) (fun z => g (sample z)) hη
    (fun _ _ => by simp) (fun z _ => happrox (sample z))
  simp only [one_mul] at hfirst
  have hlast := probability_integral_approximation μ g f
    (coefficientTorusFourierSum_integrable U frequency c μ) hf
    (fun x => by simpa only [norm_sub_rev] using happrox x)
  have htri := norm_sub_le_norm_sub_add_norm_sub (E f) (E g) (∫ x, f x ∂μ)
  have htri' := norm_sub_le_norm_sub_add_norm_sub (E g) (∫ x, g x ∂μ) (∫ x, f x ∂μ)
  change ‖E f - E g‖ ≤ η at hfirst
  change ‖E g - ∫ x, g x ∂μ‖ ≤ ε at hcomp
  change ‖E f - ∫ x, f x ∂μ‖ ≤ 2 * η + ε
  linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem exists_affine_coefficient_cover_haar_approximation (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp P)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f : CoefficientTorus (K := K) U → ℂ) (_hf : Integrable f μ)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖f x - coefficientTorusFourierSum U frequency c x‖ ≤ η),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        f (affineCoefficientCoverSample U p _hm q (fun k j => (z (k, j) : ℝ)))) -
      (∫ x, f x ∂μ)‖ ≤ 2 * η + ε := by
  obtain ⟨A₀, _, hcomparison⟩ := exists_affine_coefficient_haar_approximation m
  obtain ⟨A, hA, hbudget⟩ := exists_integer_cover_threshold A₀
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm q hq hqP stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth f hf η hη happrox
  have hb := hbudget P hP
  have hR0 : 0 ≤ R := (Real.exp_pos _).le.trans hR
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hscaledR : Real.exp ((P + A₀) ^ A₀) ≤ R / q := by
    apply (le_div_iff₀ hq0).mpr
    calc
      _ ≤ Real.exp P * Real.exp ((P + A₀) ^ A₀) := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hqP (Real.exp_pos ((P + A₀) ^ A₀)).le
      _ ≤ Real.exp ((P + A) ^ A) := hb.2
      _ ≤ R := hR
  obtain ⟨hZ, he⟩ := hcomparison hP hn hd U μ hC hCP frequency hbound c hB hBP hcoefficients
    (fun j => (q : ℝ)⁻¹ • p j) (fun j => (hp j).smul (q : ℝ)⁻¹)
    (fun j => coefficients_smul_mem (U j) (p j) (hm j) (q : ℝ)⁻¹)
    stride hs hS hSP hρ hε hρP hεP hstride H (fun k => hb.1.trans (hsize k))
    (fun j => (hrank j).div_nat hR0 q hq) hscaledR G hG V hV hwidth f hf hη happrox
  refine ⟨hZ, ?_⟩
  simpa only [affineCoefficientCoverSample_eq_scaled] using he

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CanonicalCoverLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

theorem exists_covered_coefficient_density {K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (SiteTorus S U)] [BorelSpace (SiteTorus S U)]
    (site : S → K → ℤ) (q : ℕ) (hq : 0 < q)
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)
    (hT : ∀ j (x : BoundedCoefficientExponent K (j.val + 1) → U j),
      matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ))
        (matrixModuleAction (fun d s => (T j d s : ℝ))
          (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)) x)) =
        (q : ℝ) • matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)) x)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Continuous D) {B : ℝ}
    (hcap : ∀ x, D x ∈ Set.Icc (0 : ℝ) B) (hmass : (∫ x, D x ∂μ) = 1) :
    let E := coefficientSiteTorusMap U site
    let π := Set.rangeFactorization E
    let C := quotientIntegerCover (coefficientIntegerLattice U) q
    let R := coefficientSiteResidual U site (fun _ => q) T
    let hR := coefficientSiteResidual_preserves_lattice U site (fun _ => q) T
    ∃ g : Set.range E → ℝ, Continuous g ∧ (∀ y, g y ∈ Set.Icc (0 : ℝ) B) ∧
      Integrable g (μ.map π) ∧ (∫ y, g y ∂μ.map π) = 1 ∧
      (∀ x, g (π x) = linearQuotientAverage (coefficientIntegerLattice U) R hR μ D (C x)) ∧
      (realDensityMeasure μ (fun x => D (C x))).map π = realDensityMeasure (μ.map π) g := by
  intro E π C R hR
  have hE : Continuous E := coefficientSiteTorusMap_continuous U site
  have hπ : Measurable π := hE.rangeFactorization.measurable
  have hC : Continuous C := quotientIntegerCover_continuous _ q
  have hCp := coefficientCover_measurePreserving U μ q hq
  have hRc := linearQuotientEndomorphism_continuous _ R hR R.continuous_of_finiteDimensional
  have hb (x) : ‖D x‖ ≤ B := by rw [Real.norm_of_nonneg (hcap x).1]; exact (hcap x).2
  let f := linearQuotientAverage (coefficientIntegerLattice U) R hR μ D
  have hfc : Continuous f := BooleanCubeKernel.coefficientResidualAverage_continuous U R hR μ D hD hb
  have hi : Integrable D μ := Integrable.of_bound hD.aestronglyMeasurable B (ae_of_all μ hb)
  have hprob := linearQuotientAverage_probability _ R hR μ hRc.measurable D hD.measurable hi
    (fun x => (hcap x).1) hmass
  have hfiber (x y : CoefficientTorus (K := K) U) (hxy : E x = E y) : f (C x) = f (C y) := by
    exact linearQuotientAverage_cover_eq_of_map_eq (Y := SiteTorus S U)
      (coefficientIntegerLattice U) R hR μ q (coefficientSiteTorusMap U site)
      (coefficientSiteResidual_cover_on_kernel U site q T) D x y hxy
  obtain ⟨g, hgc, hg⟩ := exists_continuous_image_factor E hE (fun x => f (C x)) (hfc.comp hC)
    hfiber
  let _ : IsProbabilityMeasure (μ.map π) := Measure.isProbabilityMeasure_map hπ.aemeasurable
  have hgb (y) : g y ∈ Set.Icc (0 : ℝ) B := by
    obtain ⟨x, hx⟩ := Set.rangeFactorization_surjective y
    rw [← hx, hg]
    refine ⟨hprob.1 _, ?_⟩
    have h := linearQuotientAverage_bound _ R hR μ D hb (C x)
    rwa [Real.norm_of_nonneg (hprob.1 _)] at h
  have hgi : Integrable g (μ.map π) := Integrable.of_bound hgc.aestronglyMeasurable B
    (ae_of_all _ (fun y => by rw [Real.norm_of_nonneg (hgb y).1]; exact (hgb y).2))
  have hgmass : (∫ y, g y ∂μ.map π) = 1 := by
    rw [integral_map hπ.aemeasurable hgc.aestronglyMeasurable]
    change (∫ x, g (Set.rangeFactorization E x) ∂μ) = 1
    simp_rw [hg]
    exact (coefficientCover_integral U μ q hq f hfc.aestronglyMeasurable).trans hprob.2.2
  refine ⟨g, hgc, hgb, hgi, hgmass, hg, ?_⟩
  have hLmass : (∫ x, D (C x) ∂μ) = 1 :=
    (coefficientCover_integral U μ q hq D hD.aestronglyMeasurable).trans hmass
  have hLi : Integrable (fun x => D (C x)) μ := coefficientCover_integrable U μ q hq D hi
  have he (x) : linearQuotientAverage (coefficientIntegerLattice U) R hR μ (fun x => D (C x)) x =
      g (π x) := by
    rw [hg]
    exact (linearQuotientAverage_cover _ R hR μ q hCp D x
      (BooleanCubeKernel.coefficientResidual_section_integrable U R hR μ D hD hb (C x)).aestronglyMeasurable).symm
  have hshift : haarShiftDensity μ (-⇑(linearQuotientEndomorphism (coefficientIntegerLattice U) R hR))
      (fun x => D (C x)) = fun x => g (π x) := by
    funext x
    simpa only [haarShiftDensity, densityMixture, Pi.neg_apply, sub_neg_eq_add, linearQuotientAverage] using he x
  have hlaw := haarShiftDensity_map_eq μ μ (-⇑(linearQuotientEndomorphism (coefficientIntegerLattice U) R hR))
    hRc.measurable.neg (fun x => D (C x)) (hD.comp hC).measurable hLi (fun x => (hcap _).1) hLmass π hπ
    (fun y x => by
      apply Subtype.ext
      change E (x + -linearQuotientEndomorphism _ R hR y) = E x
      rw [map_add, map_neg, coefficientSiteResidual_site_zero U site q T hT, neg_zero, add_zero])
  rw [hshift] at hlaw
  rw [← hlaw]
  exact measurePreserving_realDensity_map μ (μ.map π) π ⟨hπ, rfl⟩ g hgc.measurable hgi (fun y => (hgb y).1)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteRelativeDensity
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {Ω : Type*} [Fintype Ω]

theorem relativeDensity_nonneg (p q : FiniteProbabilityWeights Ω) (x : Ω) :
    0 ≤ p.relativeDensity q x := div_nonneg (q.nonneg x) (p.nonneg x)

theorem mean_relativeDensity (p q : FiniteProbabilityWeights Ω) (hp : ∀ x, 0 < p.weight x)
    (f : Ω → ℝ) : p.mean (fun x => p.relativeDensity q x * f x) = q.mean f := by
  unfold mean relativeDensity
  apply Finset.sum_congr rfl
  intro x _
  field_simp [(hp x).ne']

theorem relativeDensity_tail_mass (p q : FiniteProbabilityWeights Ω) (hp : ∀ x, 0 < p.weight x)
    (C : ℝ) :
    p.mean (fun x => if x ∈ Finset.univ.filter (fun y => p.relativeDensity q y ≤ C)
      then 0 else p.relativeDensity q x) =
      q.mass (Finset.univ.filter (fun x => C*p.weight x < q.weight x)) := by
  simp only [mean, mass, Finset.sum_filter, Finset.mem_filter, Finset.mem_univ, true_and]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : C*p.weight x < q.weight x
  · have hd : ¬p.relativeDensity q x ≤ C := by
      simpa only [relativeDensity, div_le_iff₀ (hp x), not_le] using hx
    simp only [hd, ite_false, hx, ite_true]
    change p.weight x * (q.weight x / p.weight x) = q.weight x
    field_simp [(hp x).ne']
  · have hd : p.relativeDensity q x ≤ C := (div_le_iff₀ (hp x)).mpr (le_of_not_gt hx)
    simp only [hd, ite_true, mul_zero, hx, ite_false]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueBoxSliceCoordinateDisintegration
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {U : Type*} {N : U → ℕ} {q : ℕ}

variable [Fintype U] [DecidableEq U]

theorem integerPoints_eq_commonStrideBox (A : ResidueBoxSlice N q) :
    A.integerPoints = commonStrideBox (fun i => (A.start i : ℤ)) q A.length := by
  classical
  rw [commonStrideBox_eq_image]
  ext x
  constructor
  · intro hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨fun i => ((j i).val : ℤ), ?_, (A.integerPoint_eq j).symm⟩
    exact (mem_integerBox _ _).mpr (fun i => ⟨by positivity, by exact_mod_cast (j i).isLt⟩)
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hz' := (mem_integerBox _ _).mp hz
    let j : ∀ i, Fin (A.length i) := fun i => ⟨(z i).toNat, by
      have hzi := hz' i
      omega⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    rw [A.integerPoint_eq]
    congr 1
    funext i
    exact Int.toNat_of_nonneg (hz' i).1

omit [Fintype U] [DecidableEq U] in
theorem progression_inside (A : ResidueBoxSlice N q) (i : U) :
    integerProgressionSupport (A.start i : ℤ) q (A.length i) ⊆
      Finset.Ico (0 : ℤ) (N i) := by
  intro y hy
  obtain ⟨j, hj0, hjlt, rfl⟩ := (mem_integerProgressionSupport_iff_parameter _ _ _ _).mp hy
  have hj : j.toNat < A.length i := by omega
  have hinside := A.inside i j.toNat hj
  have he : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj0
  apply Finset.mem_Ico.mpr
  constructor
  · positivity
  · rw [← he]
    exact_mod_cast hinside

theorem isDenseCommonStrideBox (A : ResidueBoxSlice N q) (hq : 0 < q)
    {ρ : ℝ} (hρ : 0 < ρ) (hA : ∀ i, 0 < A.length i)
    (hlength : ∀ i, ρ * N i ≤ 4 * q * A.length i) :
    IsDenseCommonStrideBox N (Real.log (4 * (q : ℝ) / ρ)) A.integerPoints := by
  refine ⟨fun i => (A.start i : ℤ), q, A.length, hq, hA,
    A.progression_inside, ?_, A.integerPoints_eq_commonStrideBox⟩
  intro i
  rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 4 * (q : ℝ) / ρ), inv_div]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 4 * (q : ℝ))).mpr
  nlinarith [hlength i]

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I]

namespace ResidueBoxSlice

variable {N : I → ℕ} {q : ℕ}

theorem length_pos_of_integerPoints_nonempty (A : ResidueBoxSlice N q)
    (hA : A.integerPoints.Nonempty) (i : I) : 0 < A.length i := by
  classical
  obtain ⟨x, hx⟩ := hA
  obtain ⟨j, _, _⟩ := Finset.mem_image.mp hx
  exact lt_of_le_of_lt (Nat.zero_le ((j i).val)) (j i).isLt

theorem length_pos_of_dense (A : ResidueBoxSlice N q) {c : ℝ}
    (hA : IsDenseCommonStrideBox N c A.integerPoints) (i : I) :
    0 < A.length i :=
  A.length_pos_of_integerPoints_nonempty hA.nonempty i

theorem length_lower_of_dense (A : ResidueBoxSlice N q) (hq : 0 < q) {c : ℝ}
    (hA : IsDenseCommonStrideBox N c A.integerPoints) (i : I) :
    Real.exp (-c) * (N i : ℝ) ≤ (A.length i : ℝ) := by
  have hlength := A.length_pos_of_dense hA
  obtain ⟨start, m, H, hm, hH, _, hdense, heq⟩ := hA
  have hcard := congrArg
    (fun s : Finset (I → ℤ) => (s.image (fun x => x i)).card) heq
  rw [A.integerPoints_eq_commonStrideBox,
    commonStrideBox_axis_card _ _ _ hq hlength,
    commonStrideBox_axis_card _ _ _ hm hH] at hcard
  rw [hcard]
  exact hdense i

end ResidueBoxSlice
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} {P N : I → ℕ} {q : ℕ}

namespace ResidueBoxSlice

def enlargeBox (S : ResidueBoxSlice P q) (N : I → ℕ)
    (hPN : ∀ i, P i ≤ N i) : ResidueBoxSlice N q where
  start := S.start
  length := S.length
  inside i j hj := (S.inside i j hj).trans_le (hPN i)

@[simp] theorem enlargeBox_start (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) : (S.enlargeBox N hPN).start = S.start := rfl

@[simp] theorem enlargeBox_length (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) : (S.enlargeBox N hPN).length = S.length := rfl

@[simp] theorem enlargeBox_integerPoint (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) (u : ∀ i, Fin (S.length i)) :
    (S.enlargeBox N hPN).integerPoint u = S.integerPoint u := rfl

variable [Fintype I] [DecidableEq I]

@[simp] theorem enlargeBox_integerPoints (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) :
    (S.enlargeBox N hPN).integerPoints = S.integerPoints := rfl

end ResidueBoxSlice

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I V : Type*} {N : I → ℕ} {q : ℕ}

def comap (A : ResidueBoxSlice N q) (e : V → I) :
    ResidueBoxSlice (fun v => N (e v)) q where
  start v := A.start (e v)
  length v := A.length (e v)
  inside v j hj := A.inside (e v) j hj

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerAffinePullbackHom
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeIntegerModelFamily.lie NativeIntegerModelFamily.algebra
  NativeIntegerModelFamily.topology NativeIntegerModelFamily.topologicalAdd
  NativeIntegerModelFamily.continuousSMul NativeIntegerModelFamily.hausdorff

namespace NativeIntegerExpansion

variable {σ : Type*} {w : σ → ℕ} {s : ℕ} {p q : ℝ} {f : (σ → ℤ) → ℂ}

noncomputable def conjugate (E : NativeIntegerExpansion w s p f) :
    NativeIntegerExpansion w s p (fun x => star (f x)) :=
  { E with
    test := fun i => (E.test i).conjugate
    complexity := E.complexity
    coefficient := fun i => star (E.coefficient i)
    cost := by simpa only [norm_star] using E.cost
    eval := by
      intro x
      have h := congrArg star (E.eval x)
      simpa only [star_sum, star_mul, mul_comm,
        RationalFilteredNilmanifold.Niltest.eval_conjugate] using h }

noncomputable def ofTest {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d : ℕ} {D : RationalFilteredNilmanifold L s d}
    (T : D.Niltest w) (hT : T.ComplexityLE p) (hf : ∀ x, f x = T.eval x) :
    NativeIntegerExpansion w s p f := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  exact {
    count := 1
    count_bound := by simpa only [Nat.cast_one] using Real.one_le_exp hp
    L := fun _ => L
    dim := fun _ => d
    model := fun _ => D
    test := fun _ => T
    complexity := fun _ => hT
    coefficient := fun _ => 1
    cost := by simpa using Real.one_le_exp hp
    eval := fun x => by simpa using hf x }

end NativeIntegerExpansion

end Erdos3

end

section

namespace Erdos3

structure NativeIntegerVectorEquivalence {σ J K : Type*} [Fintype J] [Fintype K]
    (s : ℕ) (p : ℝ) (chi : J → (σ → ℤ) → ℂ) (eta : K → (σ → ℤ) → ℂ) : Prop where
  left_dimension : (Fintype.card J : ℝ) ≤ Real.exp p
  right_dimension : (Fintype.card K : ℝ) ≤ Real.exp p
  expansion : ∀ j k, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s p
    (fun x => chi j x * star (eta k x)))

namespace NativeIntegerVectorEquivalence

variable {σ J K : Type*} [Fintype J] [Fintype K] {s : ℕ} {p q : ℝ}
  {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ}

theorem symm (E : NativeIntegerVectorEquivalence s p chi eta) :
    NativeIntegerVectorEquivalence s p eta chi where
  left_dimension := E.right_dimension
  right_dimension := E.left_dimension
  expansion k j := by
    obtain ⟨R⟩ := E.expansion j k
    have h : Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s p
        (fun x => star (chi j x * star (eta k x)))) := ⟨R.conjugate⟩
    simpa only [star_mul, star_star, mul_comm] using h

end NativeIntegerVectorEquivalence

end Erdos3

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {σ J K : Type*} [Fintype J] [Fintype K] {s : ℕ} {p : ℝ}
  {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ}
  (E : NativeIntegerVectorEquivalence s p chi eta)

noncomputable def selectedExpansion (j : J) (k : K) :
    NativeIntegerExpansion (fun _ : σ => 1) s p
      (fun x => chi j x * star (eta k x)) :=
  Classical.choice (E.expansion j k)

end Erdos3.NativeIntegerVectorEquivalence

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestComplement
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

inductive PositiveCyclicNiltest.{u} (degree N : ℕ) [NeZero N] (p : ℝ)
    (f : ZMod N → ℝ) : Prop where
  | of_test {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s dim : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s dim) (hdegree : s ≤ degree)
      (T : D.Niltest (fun _ : Unit => 1)) (hpositive : T.UnitIntervalValued)
      (hcomplexity : T.ComplexityLE p)
      (heval : ∀ x, f x = (T.evalCyclic N (fun _ => x)).re) :
      PositiveCyclicNiltest degree N p f

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

universe u

theorem CyclicNiltestUpperComparison.test_positive {degree N : ℕ} [NeZero N]
    {P R error : ℝ} {f g a : ZMod N → ℝ}
    (hcompare : CyclicNiltestUpperComparison.{u} degree N P error f g)
    (ha : PositiveCyclicNiltest.{u} degree N R a) (hRP : R ≤ P) :
    (𝔼 x, (f x - g x) * a x) ≤ error := by
  rcases ha with ⟨D, hs, T, hT, hTc, heval⟩
  simpa only [heval] using hcompare D hs T hT (hTc.mono hRP)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RaisedDegreeRank
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem realification_associatedDegree :
    F.realification.associatedDegree = F.associatedDegree.realification := rfl

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.ComparisonLayerBracket
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem comparison_deep_lie_mem {i j : ℕ} {x y : L × F.SquarefreeAlgebra π}
    (hx : x ∈ F.comparisonProductLayer π (i + 1)) (hy : y ∈ F.comparisonLayer π j) :
    ⁅x, y⁆ ∈ F.comparisonLayer π (i + j) := by
  apply (le_sup_left : F.comparisonProductLayer π (i + j + 1) ≤ F.comparisonLayer π (i + j))
  simpa only [Nat.add_right_comm i 1 j] using
    F.comparisonProductLayer_lie_mem π hx (F.comparisonLayer_le_product π j hy)

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MultiaffineTripleLayerBasis
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def additiveTripleFiltrationLayerEquiv (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    (F.additiveTripleFiltration i hi c hc).layer n ≃ₗ[ℚ] F.additiveTripleLayer i c n where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, F.additiveTripleLayer_antitone i c hn x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPositivePolynomialEvaluation
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {bound : σ → ℕ}

theorem boxedPolynomial_coefficient (f : BoxedDegreeIndex bound → L) (a : BoxedDegreeIndex bound) :
    coefficients (boxedPolynomial f) (boxedDegreeMonomial a) = f a := by
  classical
  simp [boxedPolynomial, Finsupp.single_apply, boxedDegreeMonomial_injective.eq_iff]

theorem boxedPolynomial_coefficient_outside (f : BoxedDegreeIndex bound → L) (a : σ →₀ ℕ)
    (ha : ¬(fun i => a i) ≤ bound) : coefficients (boxedPolynomial f) a = 0 := by
  classical
  have hne (b : BoxedDegreeIndex bound) : boxedDegreeMonomial b ≠ a := by
    intro h
    apply ha
    simpa only [h] using boxedDegreeMonomial_le b
  simp [boxedPolynomial, hne]

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PositivePolynomialLayerBases
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem boxedPolynomial_positive (f : ∀ a : BoxedDegreeIndex bound, F.positiveCoefficientLayer a) :
    boxedPolynomial (fun a => (f a).val) ∈ F.positivePolynomialAlgebra := by
  constructor
  · intro a
    by_cases ha : (fun i => a i) ≤ bound
    · obtain ⟨b, rfl⟩ := exists_boxedDegreeMonomial a ha
      rw [boxedPolynomial_coefficient]
      simpa only [boxedDegreeMonomial_apply] using
        ((F.mem_positiveCoefficientLayer b (f b).val).mp (f b).property).1
    · rw [boxedPolynomial_coefficient_outside _ a ha]
      exact Submodule.zero_mem _
  · obtain ⟨b, hb⟩ := exists_boxedDegreeMonomial (bound := bound) 0 (fun i => Nat.zero_le _)
    rw [← hb, boxedPolynomial_coefficient]
    exact ((F.mem_positiveCoefficientLayer b (f b).val).mp (f b).property).2 hb

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTagConstraintChartBasis
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {κ V : Type*} [AddCommGroup V] [Module ℚ V]
  (K : Submodule ℚ V) (b : Basis κ ℚ K)

noncomputable def realSubmoduleBasis : Basis κ ℝ (K.baseChange ℝ) :=
  (b.baseChange ℝ).map (realificationSubmoduleEquiv K)

theorem realSubmoduleBasis_coe (i : κ) :
    (realSubmoduleBasis K b i : ℝ ⊗[ℚ] V) = (1 : ℝ) ⊗ₜ[ℚ] (b i : V) := by
  rw [realSubmoduleBasis, Basis.map_apply, Basis.baseChange_apply, realificationSubmoduleEquiv_tmul]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {B I : Type*} [Fintype B]
  (U : Submodule ℚ (B → ℚ)) (b : Basis I ℚ U)

noncomputable def rationalCoordinateRealBasis : Basis I ℝ (realRationalCoordinateSpan U) :=
  (realSubmoduleBasis U b).map (realRationalCoordinateEquiv.submoduleMap (U.baseChange ℝ))

@[simp] theorem rationalCoordinateRealBasis_apply (i : I) (j : B) :
    (rationalCoordinateRealBasis U b i : B → ℝ) j = ((b i : B → ℚ) j : ℝ) := by
  change realRationalCoordinateEquiv (realSubmoduleBasis U b i : ℝ ⊗[ℚ] (B → ℚ)) j = _
  rw [realSubmoduleBasis_coe, realRationalCoordinateEquiv_tmul, one_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeProductCoefficient
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ) (f : Basis ι ℚ (L ⧸ F.layer d 2))

theorem realHigherHorizontalCoordinates_map (x : (F.layer d 1).baseChange ℝ) :
    F.realHigherHorizontalCoordinates d f (F.realHorizontalMap d x) =
      realRationalCoordinateEquiv ((F.ambientHorizontalCoordinates d f).baseChange ℝ x.val) := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv (F.layer d 1)).surjective x
  rw [F.realHorizontalMap_baseChange]
  simp only [realificationSubmoduleEquiv_coe]
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realHigherHorizontalCoordinates_mem (x : ℝ ⊗[ℚ] F.HigherHorizontal d) :
    F.realHigherHorizontalCoordinates d f x ∈
      realRationalCoordinateSpan ((F.layer d 1).map (F.ambientHorizontalCoordinates d f)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    obtain ⟨v, rfl⟩ := F.higherHorizontalMk_surjective d x
    exact ⟨a ⊗ₜ[ℚ] F.ambientHorizontalCoordinates d f v.val,
      Submodule.tmul_mem_baseChange_of_mem a ⟨v.val, v.property, rfl⟩, rfl⟩
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3

open Module
open scoped TensorProduct

namespace DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ)

theorem realFourLayerComponent_horizontal (k : Fin 4) (x : (F.fourHorizontalLayer d).baseChange ℝ) :
    (LinearMap.proj k).baseChange ℝ (F.realFourHorizontalMap d x) =
      F.realHorizontalMap d (F.realFourLayerComponent d k x) := by
  obtain ⟨y, rfl⟩ := (realificationSubmoduleEquiv (F.fourHorizontalLayer d)).surjective x
  rw [F.realFourHorizontalMap_baseChange]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    let u : F.layer d 1 := ⟨v.val k, (F.mem_fourHorizontalLayer d v.val).mp v.property k⟩
    have heq : F.realFourLayerComponent d k
        (realificationSubmoduleEquiv (F.fourHorizontalLayer d) (a ⊗ₜ[ℚ] v)) =
        realificationSubmoduleEquiv (F.layer d 1) (a ⊗ₜ[ℚ] u) := by
      apply Subtype.ext
      rfl
    rw [heq, F.realHorizontalMap_baseChange]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realFourLayerComponent_norm_bound {ι : Type*} [Fintype ι] (b : Basis ι ℚ L)
    (k : Fin 4) (x : (F.fourHorizontalLayer d).baseChange ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hx : ∀ j, |((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).repr x.val j| ≤ B) :
    ‖(b.baseChange ℝ).equivFun (F.realFourLayerComponent d k x).val‖ ≤ B := by
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  change |(b.baseChange ℝ).repr ((LinearMap.proj k).baseChange ℝ x.val) i| ≤ B
  rw [real_pi_projection_coordinates]
  exact hx ⟨k, i⟩

end DegreeRankLieFiltration
end Erdos3

end

section

namespace Erdos3.DegreeRankLieFiltration

open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem realHorizontalMap_ambient (d : ℕ) (x : (F.layer d 1).baseChange ℝ) :
    (F.higherHorizontalAmbient d).baseChange ℝ (F.realHorizontalMap d x) =
      (F.layer d 2).mkQ.baseChange ℝ x.val := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv (F.layer d 1)).surjective x
  rw [F.realHorizontalMap_baseChange]
  simp only [realificationSubmoduleEquiv_coe]
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => rfl
  | add v w hv hw => simp only [map_add, hv, hw]

theorem realHorizontalMap_eq (d : ℕ) (x y : (F.layer d 1).baseChange ℝ) :
    F.realHorizontalMap d x = F.realHorizontalMap d y ↔
      x.val - y.val ∈ (F.layer d 2).baseChange ℝ := by
  rw [← realification_mkQ_eq_zero_iff, map_sub, sub_eq_zero]
  constructor
  · intro h
    rw [← F.realHorizontalMap_ambient d x, ← F.realHorizontalMap_ambient d y, h]
  · intro h
    apply F.real_higherHorizontalAmbient_injective d
    rwa [F.realHorizontalMap_ambient, F.realHorizontalMap_ambient]

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentWordLayers
namespace OAI

section

namespace Erdos3.FreeDegreeRankLieAlgebra

variable (X : Type*) (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x) (marked : X → Bool)

noncomputable def markedLayer (d k l : ℕ) : Submodule ℚ (FreeDegreeRankLieAlgebra X s r w hw) :=
  markedLieSpan (of X s r w hw) w marked d k l

theorem markedLayer_lie_mem {d e k m l n : ℕ} {x y : FreeDegreeRankLieAlgebra X s r w hw}
    (hx : x ∈ markedLayer X s r w hw marked d k l)
    (hy : y ∈ markedLayer X s r w hw marked e m n) :
    ⁅x, y⁆ ∈ markedLayer X s r w hw marked (d + e) (k + m) (l + n) :=
  markedLieSpan_lie_mem _ _ _ hx hy

theorem markedLayer_zero : markedLayer X s r w hw marked 0 0 0 = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := projection_surjective X s r w hw x
  obtain ⟨z, rfl⟩ := FreeNilpotentLieAlgebra.mk_surjective X s y
  let φ := (projection X s r w hw).comp (FreeNilpotentLieAlgebra.mk X s)
  change φ z ∈ markedLayer X s r w hw marked 0 0 0
  apply freeLie_linear_induction (fun z => φ z ∈ markedLayer X s r w hw marked 0 0 0)
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro a b ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  · intro c a ha
    rw [map_smul]
    exact Submodule.smul_mem _ c ha
  · intro a
    rw [map_lieTreeEval]
    change lieTreeEval (of X s r w hw) a ∈ markedLayer X s r w hw marked 0 0 0
    exact Submodule.subset_span ⟨a, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩

noncomputable def markedLayerIdeal (d k l : ℕ) : LieIdeal ℚ (FreeDegreeRankLieAlgebra X s r w hw) :=
  { markedLayer X s r w hw marked d k l with
    lie_mem := by
      intro x y hy
      have hx : x ∈ markedLayer X s r w hw marked 0 0 0 := by
        rw [markedLayer_zero]
        trivial
      change ⁅x, y⁆ ∈ markedLayer X s r w hw marked d k l
      simpa only [Nat.zero_add] using markedLayer_lie_mem X s r w hw marked hx hy }

theorem markedLayer_le_degreeRank (hr : r ≤ s) (d k l : ℕ) :
    markedLayer X s r w hw marked d k l ≤ (filtration X s r w hw hr).layer d l :=
  markedLieSpan_le_layer (filtration X s r w hw hr) _ _ _
    (of_mem_layer X s r w hw hr) d k l

end Erdos3.FreeDegreeRankLieAlgebra

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSubspaceFreeModel
namespace OAI

section

namespace Erdos3.SubspaceFreeLift

open Module VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (S : Fin s → Submodule ℚ L)

abbrev Algebra (r : ℕ) := FreeDegreeRankLieAlgebra (Alphabet S) s r (weight S) (weight_pos S)

end Erdos3.SubspaceFreeLift

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ControlledGradedBaseCoordinates
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module

variable {σ : Type*} [fintypeSigma : Fintype σ]

noncomputable def weightedBaseLinear (w : σ → ℕ) (d : ℕ) :
    weightedSubalgebra w d →ₗ[ℚ] (σ → ℚ) :=
  baseLinear.comp (weightedSubalgebra w d).subtype

@[simp] theorem weightedBaseLinear_apply (w : σ → ℕ) (d : ℕ)
    (x : weightedSubalgebra w d) : weightedBaseLinear w d x = x.val.base := rfl

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeProperAffineRecovery
namespace OAI

section

namespace Erdos3.FreimanModel

variable {I : Type*} (q : I → ℕ) [∀ i, NeZero (q i)]

theorem exists_large_cyclicProduct_integer_lift [Fintype I]
    (A : Finset (∀ i, ZMod (q i))) (hA : A.Nonempty) :
    ∃ J : Finset (∀ i, ZMod (q i)), J.Nonempty ∧ J ⊆ A ∧
      A.card ≤ 16 ^ Fintype.card I * J.card ∧
      IsAddFreimanIso 8 (J : Set _) (J.image (cyclicProductLift q) : Set (I → ℤ))
        (cyclicProductLift q) := by
  classical
  obtain ⟨c, hJ, hsize⟩ := exists_nonempty_large_fiber A hA (cyclicProductBlock q)
  let J := A.filter fun x => cyclicProductBlock q x = c
  refine ⟨J, hJ, Finset.filter_subset _ _, ?_, ?_⟩
  · simpa only [Fintype.card_fun, Fintype.card_fin] using hsize
  · apply isAddFreimanIso_cyclicProductLift q J
    intro x hx
    exact (Finset.mem_filter.mp hx).2

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

open scoped Pointwise BigOperators
open CyclicCrootSisask

theorem exists_bounded_affine_box_of_cyclic_model {G : Type*} [AddCommGroup G] [DecidableEq G]
    {Q : ℕ} [NeZero Q] (A : Finset G) (hA : A.Nonempty) (B : Finset (ZMod Q))
    (hB : B.Nonempty) (f : G → ZMod Q) (hf : IsAddFreimanIso 8 (A : Set _) (B : Set _) f)
    {p : ℝ} (hp : 0 ≤ p) (hdensity : Real.exp (-p) * Q ≤ (B.card : ℝ)) :
    ∃ F ⊆ A, F.Nonempty ∧
      Real.exp (-(quarticBogolyubovProgressionConstant * (p + 1) ^ 8)) * A.card ≤ (F.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (Φ : (Fin r → ℤ) →+ G) (base : G),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (p + 1) ^ 4 ∧
        (∏ i, (2 * R i + 1)) ≤ Q ∧
        Set.InjOn Φ {x | ∀ i, |x i| ≤ (R i : ℤ)} ∧
        ∀ a ∈ F, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ a = base + Φ x := by
  classical
  obtain ⟨T, hrank, hT, hTsub, hTsize⟩ := exists_quartic_bogolyubov_progression B hp hdensity
  obtain ⟨L, hmap, hinj, hzero, hadd⟩ := exists_fourfold_lift_of_eight_iso A B hB f hf
  have hpair (x y z t : T.Param) (h : T.eval x + T.eval y = T.eval z + T.eval t) :
      L (T.eval x) + L (T.eval y) = L (T.eval z) + L (T.eval t) :=
    (hadd _ (hTsub (T.eval_mem_carrier x)) _ (hTsub (T.eval_mem_carrier y))
      _ (hTsub (T.eval_mem_carrier z)) _ (hTsub (T.eval_mem_carrier t))).mpr h
  let Φ := T.freimanHom L
  let S := T.coefficientBox.image Φ
  have hS : S ⊆ 2 • A - 2 • A := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, rfl⟩ := T.mem_coefficientBox.mp hx
    change T.freimanHom L (T.coeff y) ∈ _
    rw [T.freimanHom_coeff L hzero hpair]
    exact hmap (hTsub (T.eval_mem_carrier y))
  have hScard : S.card = T.carrier.card := by
    change (T.coefficientBox.image (T.freimanHom L)).card = T.carrier.card
    rw [T.image_freimanHom L hzero hpair]
    exact Finset.card_image_of_injOn (hinj.mono hTsub)
  have hbound : ((A - S).card : ℝ) ≤ (Q : ℝ) := by
    have h := card_sub_le_of_fourfold_subset A S f (hf.mono (hmn := by decide)) hS
    have h' : (A - S).card ≤ Q := by simpa only [ZMod.card] using h
    exact_mod_cast h'
  have hsize : Real.exp (-(quarticBogolyubovProgressionConstant * (p + 1) ^ 8)) * Q ≤
      (S.card : ℝ) := by rw [hScard]; exact hTsize
  obtain ⟨base, _hbase, F, hFA, hF, hFsize, hFsub⟩ := exists_dense_translate A S hA
    (Real.exp_pos _) (by exact_mod_cast NeZero.pos Q) hbound hsize
  refine ⟨F, hFA, hF, hFsize, T.rank, T.radius, Φ, base, hrank, ?_, ?_, ?_⟩
  · rw [← T.card_carrier_of_proper hT]
    simpa only [ZMod.card] using Finset.card_le_univ T.carrier
  · intro x hx y hy hxy
    exact T.freimanHom_injOn hT L (hinj.mono hTsub) hzero hpair
      (T.mem_coefficientBox_iff_abs_le.mpr hx) (T.mem_coefficientBox_iff_abs_le.mpr hy) hxy
  · intro a ha
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp (hFsub a ha)
    refine ⟨x, T.mem_coefficientBox_iff_abs_le.mp hx, ?_⟩
    rw [heq]
    abel

end Erdos3.FreimanModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MultidegreeBasisConstruction
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  (b : ∀ a, Basis (Fin (finrank ℚ (F.layer a))) ℚ (F.layer a))

theorem ordinaryLayer_eq_span_multidegree_bases (n : ℕ) :
    F.ordinary.layer n = Submodule.span ℚ
      (Set.range (fun z : Σ a : {a : σ → ℕ // n ≤ ∑ i, a i},
          Fin (finrank ℚ (F.layer a.val)) => ((b z.1.val) z.2).val)) := by
  rw [F.degree_eq]
  apply le_antisymm
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha
    rw [← span_submodule_basis (F.layer a) (b a)]
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact Submodule.subset_span ⟨⟨⟨a, ha⟩, j⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨⟨a, j⟩, rfl⟩
    have hle : F.layer a.val ≤ ⨆ (u : σ → ℕ) (_hu : n ≤ ∑ i, u i), F.layer u :=
      le_iSup_of_le a.val (le_iSup_of_le a.property le_rfl)
    exact hle ((b a.val) j).property

theorem exists_bounded_ordinaryLayer_basis {ι : Type*} [Fintype ι]
    (e : Basis ι ℚ L) {H : ℕ}
    (hb : ∀ a i j, RationalHeightLE (e.repr ((b a) i).val j) H) (n : ℕ) :
    ∃ c : Basis (Fin (finrank ℚ (F.ordinary.layer n))) ℚ (F.ordinary.layer n),
      ∀ i j, RationalHeightLE (e.repr (c i).val j) H := by
  apply exists_bounded_submodule_basis_from_spanning e (F.ordinary.layer n)
    (fun z : Σ a : {a : σ → ℕ // n ≤ ∑ i, a i},
      Fin (finrank ℚ (F.layer a.val)) => ((b z.1.val) z.2).val)
    (F.ordinaryLayer_eq_span_multidegree_bases b n).symm
  exact fun z j => hb z.1.val z.2 j

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedTranslationAssociatedGradedProjection
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open Module _root_.MvPolynomial

variable {σ L ι : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s)
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra w d)
    (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ (weightedFiltration w d hwd).layer j)

noncomputable def weightedTranslationGradedProjection :
    F.AssociatedGraded →ₗ⁅ℚ⁆ weightedSubalgebra w d :=
  F.homogeneousGradedProjection (weightedFiltration w d hwd)
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw) φ hφ

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RelativeSliceAffineThreeFactorLaw
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {q : ℕ}

def fiberParameterLength
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q) (i : X) : ℕ :=
  if hi : keep i then S.length ⟨i, hi⟩ else 1

def fiberParameterStart
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ) (i : X) : ℤ :=
  if hi : keep i then (S.start ⟨i, hi⟩ : ℤ) else fixed ⟨i, hi⟩

omit [Fintype X] [DecidableEq X] in
theorem fiberParameterLength_pos
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (i : X) : 0 < S.fiberParameterLength i := by
  unfold fiberParameterLength
  split
  · exact hlen _
  · exact Nat.zero_lt_one

omit [Fintype X] [DecidableEq X] in
theorem fiberParameterLength_of_keep
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (i : X) (hi : keep i) : S.fiberParameterLength i = S.length ⟨i, hi⟩ := by
  simp only [fiberParameterLength, dif_pos hi]

def fiberKeptParameters
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (v : ∀ i, Fin (S.fiberParameterLength i)) (k : {x // keep x}) : Fin (S.length k) :=
  ⟨(v k.val).val, by
    simpa only [fiberParameterLength, dif_pos k.property] using (v k.val).isLt⟩

def fiberAffineIntegerPoint
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ) (v : ∀ i, Fin (S.fiberParameterLength i)) : X → ℤ :=
  fun i => S.fiberParameterStart fixed i +
    (fiberParameterStride (keep := keep) (q := q) i : ℤ) * (v i).val

omit [Fintype X] [DecidableEq X] in
theorem fiberAffineIntegerPoint_eq
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ) (v : ∀ i, Fin (S.fiberParameterLength i)) :
    S.fiberAffineIntegerPoint fixed v = S.fiberIntegerPoint fixed (S.fiberKeptParameters v) := by
  funext i
  by_cases hi : keep i
  · simp only [fiberAffineIntegerPoint, fiberParameterStart, fiberParameterStride,
      fiberIntegerPoint, finiteSplitPoint, dif_pos hi, if_pos hi,
      point, fiberKeptParameters, Nat.cast_add, Nat.cast_mul]
  · simp only [fiberAffineIntegerPoint, fiberParameterStart, fiberParameterStride,
      fiberIntegerPoint, finiteSplitPoint, dif_neg hi, if_neg hi,
      Nat.cast_zero, zero_mul, add_zero]

def fiberAffinePointInBox
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (v : ∀ i, Fin (S.fiberParameterLength i)) : integerBox N :=
  ⟨S.fiberAffineIntegerPoint fixed v, by
    rw [fiberAffineIntegerPoint_eq]
    exact S.fiberIntegerPoint_mem_integerBox fixed hfixed _⟩

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {q : ℕ}

theorem fiberParameter_inside
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (i : X) (t : Fin (S.fiberParameterLength i)) :
    0 ≤ S.fiberParameterStart fixed i +
      (fiberParameterStride (keep := keep) (q := q) i : ℤ) * t.val ∧
      S.fiberParameterStart fixed i +
        (fiberParameterStride (keep := keep) (q := q) i : ℤ) * t.val < N i := by
  let zero : ∀ j, Fin (S.fiberParameterLength j) :=
    fun j => ⟨0, S.fiberParameterLength_pos hlen j⟩
  let v := Function.update zero i t
  have hv := (mem_integerBox N _).mp (S.fiberAffinePointInBox fixed hfixed v).property i
  simpa only [fiberAffinePointInBox, fiberAffineIntegerPoint, v, Function.update_self] using hv

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CoefficientUniformPerturbationSampling
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_coefficient_ambient_cover_sampling (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp P)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℂ)
    (L B : ℝ≥0) (_hf : LipschitzWith L f) (_hb : ∀ y, ‖f y‖ ≤ B)
    {η Q : ℝ} (_hη : 0 < η) (_hQ : 0 ≤ Q)
    (_hdim : (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ Q)
    (_hLQ : (L : ℝ) ≤ Real.exp Q) (_hηQ : η⁻¹ ≤ Real.exp Q)
    (_hfreqP : Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P)
    (_hcoeffP : Real.exp (2 * Q * (2 * Q + 2) ^ 4) * B ≤ Real.exp P),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        f (coefficientAmbientTorus U (affineCoefficientCoverSample U p _hm q (fun k j => (z (k, j) : ℝ))))) -
      (∫ x, f (coefficientAmbientTorus U x) ∂μ)‖ ≤ 2 * η + ε := by
  obtain ⟨A, hA, hcomparison⟩ := exists_affine_coefficient_cover_haar_approximation m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U _ _ μ _ _ p hp hm q hq hqP stride hs R S ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    f L B hf hb η Q hη hQ hdim hLQ hηQ hfreqP hcoeffP
  obtain ⟨F, inst, frequency, coeff, _, hfreq, hcoeff, happ⟩ :=
    exists_ambient_torus_fourier_approximation f L B hf hb hη hQ hdim hLQ hηQ
  let _ := inst
  have hcont : Continuous (coefficientAmbientTorus (K := K) U) := by
    apply continuous_pi
    intro a
    exact (continuous_apply a.2).comp ((subspaceAmbientTorus_continuous (U a.1.1)).comp
      ((continuous_apply a.1).comp (coefficientCoordinateTorus_continuous U)))
  have hi : Integrable (fun x => f (coefficientAmbientTorus U x)) μ :=
    Integrable.of_bound (hf.continuous.comp hcont).measurable.aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun x => hb _))
  have he (x) : ‖f (coefficientAmbientTorus U x) - coefficientTorusFourierSum U
      (fun a => coefficientSlotFrequency (fun s i => frequency a ⟨s,i⟩)) coeff x‖ ≤ η := by
    simpa only [coefficientAmbientTorus_character, coefficientTorusFourierSum] using happ (coefficientAmbientTorus U x)
  exact hcomparison hP hn hd U μ (Real.exp_nonneg _) hfreqP
    (fun a => coefficientSlotFrequency (fun s i => frequency a ⟨s,i⟩))
    (fun a => coefficientSlotFrequency_bound _ (fun s i => hfreq a ⟨s,i⟩)) coeff
    (mul_nonneg (Real.exp_nonneg _) B.coe_nonneg) hcoeffP hcoeff p hp hm q hq hqP stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    (fun x => f (coefficientAmbientTorus U x)) hi hη.le he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_coefficient_ambient_l1_sampling (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp P)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f g : (CoefficientAmbientIndex K J → UnitAddCircle) → ℂ)
    (Lf Lg Cf Cg : ℝ≥0) (_hf : LipschitzWith Lf f) (_hg : LipschitzWith Lg g)
    (_hfb : ∀ y, ‖f y‖ ≤ Cf) (_hgb : ∀ y, ‖g y‖ ≤ Cg)
    {η Q : ℝ} (_hη : 0 < η) (_hQ : 0 ≤ Q)
    (_hdim : (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ Q)
    (_hLQ : ((Lf + Lg : ℝ≥0) : ℝ) ≤ Real.exp Q) (_hηQ : η⁻¹ ≤ Real.exp Q)
    (_hfreqP : Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P)
    (_hcoeffP : Real.exp (2 * Q * (2 * Q + 2) ^ 4) * (Cf + Cg : ℝ≥0) ≤ Real.exp P)
    {E : ℝ} (_hmass : (∫ x, ‖f (coefficientAmbientTorus U x) -
      g (coefficientAmbientTorus U x)‖ ∂μ) ≤ E),
    ∃ _hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
      selectedResidueDensityMass stride G V (fun z =>
        ‖f (coefficientAmbientTorus U (affineCoefficientCoverSample U p _hm q
          (fun k j => (z (k,j) : ℝ)))) -
          g (coefficientAmbientTorus U (affineCoefficientCoverSample U p _hm q
            (fun k j => (z (k,j) : ℝ))))‖) ≤ E + 2 * η + ε := by
  obtain ⟨A, hA, hsample⟩ := exists_coefficient_ambient_cover_sampling m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U _ _ μ _ _ p hp hm q hq hqP stride hs R S ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    f g Lf Lg Cf Cg hf hg hfb hgb η Q hη hQ hdim hLQ hηQ hfreqP hcoeffP E hmass
  let error := fun z => ‖f z - g z‖
  have hl : LipschitzWith (Lf + Lg) error := by
    simpa only [one_mul, Function.comp_def, Pi.sub_apply] using
      lipschitzWith_one_norm.comp (hf.sub hg)
  have hb (z) : error z ≤ (Cf + Cg : ℝ≥0) :=
    (norm_sub_le _ _).trans (add_le_add (hfb z) (hgb z))
  have hlc : LipschitzWith (Lf + Lg) (fun z => (error z : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [Complex.isometry_ofReal.dist_eq]
    exact hl.dist_le_mul z w
  have hbc (z) : ‖(error z : ℂ)‖ ≤ (Cf + Cg : ℝ≥0) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ error z from norm_nonneg _)]
    exact hb z
  obtain ⟨hZ, he⟩ := hsample hP hn hd U μ p hp hm q hq hqP stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    (fun z => (error z : ℂ)) (Lf + Lg) (Cf + Cg) hlc hbc hη hQ hdim hLQ hηQ hfreqP hcoeffP
  refine ⟨hZ, ?_⟩
  let law := selectedResidueSmoothPMF stride G V hV hZ
  let sample := fun z : Option K × I → ℤ =>
    error (coefficientAmbientTorus U (affineCoefficientCoverSample U p hm q
      (fun k j => (z (k,j) : ℝ))))
  have hi : Integrable sample law.toMeasure :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (Cf + Cg : ℝ≥0)
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hb _))
  have he' : ‖(∫ z, (sample z : ℂ) ∂law.toMeasure) -
      ∫ x, (error (coefficientAmbientTorus U x) : ℂ) ∂μ‖ ≤ 2 * η + ε := by
    rw [PMF.integral_eq_tsum law _ hi.ofReal]
    simpa only [Complex.real_smul] using he
  rw [integral_complex_ofReal, integral_complex_ofReal, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at he'
  rw [selectedResidueDensityMass_integral stride G V hV hZ _ hi]
  have hle := (le_abs_self _).trans he'
  linarith only [hle, hmass]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueBoxSliceSubtypeSites
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {N : I → ℕ} {q : ℕ}

theorem integerPoints_subset_integerBox (A : ResidueBoxSlice N q) :
    A.integerPoints ⊆ integerBox N := by
  classical
  intro x hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  apply (mem_integerBox N _).mpr
  intro i
  change 0 ≤ ((A.point j i).val : ℤ) ∧ ((A.point j i).val : ℤ) < (N i : ℤ)
  exact ⟨Int.natCast_nonneg _, by exact_mod_cast (A.point j i).isLt⟩

noncomputable def subtypeSites (A : ResidueBoxSlice N q) : Finset ↥(integerBox N) := by
  classical
  exact Finset.univ.filter (fun x => x.val ∈ A.integerPoints)

@[simp] theorem mem_subtypeSites (A : ResidueBoxSlice N q) (x : integerBox N) :
    x ∈ A.subtypeSites ↔ x.val ∈ A.integerPoints := by
  classical
  simp only [subtypeSites, Finset.mem_filter, Finset.mem_univ, true_and]

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductiveFrozenLocalMajorFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

variable {V : Type*} (Long : V → Prop) [DecidablePred Long]

namespace ResidueBoxSlice

variable {N : V → ℕ} {q : ℕ}

def freezeShort (A : ResidueBoxSlice (fun i : {i // Long i} => N i.val) q)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i) :
    ResidueBoxSlice N q where
  start i := if hi : Long i then A.start ⟨i, hi⟩ else fixed i
  length i := if hi : Long i then A.length ⟨i, hi⟩ else 1
  inside i j hj := by
    by_cases hi : Long i
    · simpa only [dif_pos hi] using
        A.inside ⟨i, hi⟩ j (by simpa only [dif_pos hi] using hj)
    · have hj0 : j = 0 := by simpa only [dif_neg hi, Nat.lt_one_iff] using hj
      simpa only [dif_neg hi, hj0, mul_zero, add_zero] using hfixed i hi

variable [Fintype V] [DecidableEq V]

theorem freezeShort_integerPoints
    (A : ResidueBoxSlice (fun i : {i // Long i} => N i.val) q)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i) :
    (A.freezeShort Long fixed hfixed).integerPoints =
      A.integerPoints.image (frozenLongExtension Long fixed) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    let t : ∀ i : {i // Long i}, Fin (A.length i) := fun i =>
      ⟨(j i.val).val, by simpa [freezeShort, i.property] using (j i.val).isLt⟩
    refine Finset.mem_image.mpr ⟨A.integerPoint t,
      Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩, ?_⟩
    funext i
    by_cases hi : Long i
    · simp [frozenLongExtension, integerPoint, point, freezeShort, hi, t]
    · have hj0 : (j i).val = 0 := by
        have := (j i).isLt
        simpa only [freezeShort, dif_neg hi, Nat.lt_one_iff] using this
      simp [frozenLongExtension, integerPoint, point, freezeShort, hi, hj0]
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hy
    let j : ∀ i, Fin ((A.freezeShort Long fixed hfixed).length i) := fun i =>
      if hi : Long i then
        ⟨(t ⟨i, hi⟩).val, by simp only [freezeShort, dif_pos hi]; exact (t ⟨i, hi⟩).isLt⟩
      else ⟨0, by simp [freezeShort, hi]⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    funext i
    by_cases hi : Long i <;>
      simp [frozenLongExtension, integerPoint, point, freezeShort, hi, j]

theorem expect_freezeShort
    (A : ResidueBoxSlice (fun i : {i // Long i} => N i.val) q)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    {W : Type*} [AddCommMonoid W] [Module ℚ≥0 W] (f : (V → ℤ) → W) :
    (𝔼 x ∈ (A.freezeShort Long fixed hfixed).integerPoints, f x) =
      (𝔼 x ∈ A.integerPoints, f (frozenLongExtension Long fixed x)) := by
  rw [freezeShort_integerPoints]
  exact Finset.expect_image (frozenLongExtension_injective Long fixed).injOn

omit [Fintype V] [DecidableEq V] in
theorem freezeShort_commonStrideIndex
    (A : ResidueBoxSlice (fun i : {i // Long i} => N i.val) q)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i) (x : V → ℤ) :
    (fun i : {i // Long i} =>
      commonStrideIndex (fun j => ((A.freezeShort Long fixed hfixed).start j : ℤ)) q x i.val) =
    commonStrideIndex (fun i => (A.start i : ℤ)) q (fun i => x i.val) := by
  funext i
  simp [commonStrideIndex, freezeShort, i.property]

end ResidueBoxSlice

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.DenseResidueScalarScoreNet
namespace OAI

section

namespace Erdos3

namespace DenseResidueSliceNetCode

variable {X : Type*} {Q K : ℕ}

def fullParent (N : X → ℕ) : ResidueBoxSlice N 1 where
  start _ := 0
  length := N
  inside i j hj := by simpa using hj

noncomputable def realize (N : X → ℕ) (H : ℝ) (M : ℕ)
    (c : DenseResidueSliceNetCode X Q K) : Σ q, ResidueBoxSlice N q := by
  classical
  exact if h : c.Valid N H M then
    ⟨c.stride, ⟨c.start M, c.length M, h.2.1⟩⟩ else ⟨1, fullParent N⟩

def meshCode {N : X → ℕ} {q : ℕ} (S : ResidueBoxSlice N q)
    (hq : 0 < q) (hqQ : q ≤ Q) (M : ℕ) (hM : 0 < M)
    (hlen : ∀ i, 2 * M < S.length i) (hbox : ∀ i, N i ≤ K * M) :
    DenseResidueSliceNetCode X Q K :=
  ⟨⟨q, Nat.lt_succ_of_le hqQ⟩,
    (fun i => ⟨S.start i % q, (Nat.mod_lt _ hq).trans_le (Nat.le_succ_of_le hqQ)⟩),
    (fun i => ⟨S.start i / q / M + 1, Nat.lt_succ_of_le
      ((denseResidueMeshInterval_code_bound (S.start i / q) (S.length i) M K hM (hlen i)
        ((S.residueIndex_endpoint_le hq (fun j => by have := hlen j; omega) i).trans
          (hbox i))).1)⟩),
    (fun i => ⟨(S.start i / q + S.length i) / M, Nat.lt_succ_of_le
      ((denseResidueMeshInterval_code_bound (S.start i / q) (S.length i) M K hM (hlen i)
        ((S.residueIndex_endpoint_le hq (fun j => by have := hlen j; omega) i).trans
          (hbox i))).2)⟩)⟩

end DenseResidueSliceNetCode
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelPrincipalFiberSliceLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G D : Type*} [Fintype G] [DecidableEq G] [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (LG : G → ℕ) (L : PrincipalTupleIndex B h → ℕ)

namespace ResidueBoxSlice

variable {B h LG L}
variable {keep : G ⊕ PrincipalTupleIndex B h → Prop} [DecidablePred keep] {q : ℕ}
variable (S : ResidueBoxSlice (fun k : {k // keep k} => Sum.elim LG L k.val) q)
variable (hlen : ∀ k, 0 < S.length k) (fixed : {k // ¬keep k} → ℤ)
variable (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < ((Sum.elim LG L k.val : ℕ) : ℤ))
variable (hkernel : ∀ g, keep (Sum.inl g))

include hlen hfixed in
theorem fiberPrincipalParameter_inside (j : PrincipalTupleIndex B h)
    (t : Fin (S.fiberParameterLength (Sum.inr j))) :
    0 ≤ S.fiberParameterStart fixed (Sum.inr j) +
      (fiberParameterStride (keep := keep) (q := q) (Sum.inr j) : ℤ) * t.val ∧
      S.fiberParameterStart fixed (Sum.inr j) +
        (fiberParameterStride (keep := keep) (q := q) (Sum.inr j) : ℤ) * t.val < L j :=
  S.fiberParameter_inside hlen fixed hfixed (Sum.inr j) t

end ResidueBoxSlice
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedDenseFiberSliceForecastGeometry
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

theorem fiberParameter_dense_of_keep {X : Type*} {keep : X → Prop}
    [DecidablePred keep] {N : X → ℕ} {q : ℕ}
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    {density : ℝ} (hdense : ∀ k, density * (N k.val : ℝ) ≤ S.length k)
    (hq : 0 < q) (i : X) (hi : keep i) :
    density * (N i : ℝ) ≤ S.fiberParameterLength i ∧
      0 < fiberParameterStride (keep := keep) (q := q) i := by
  constructor
  · rw [fiberParameterLength_of_keep S i hi]
    exact hdense ⟨i, hi⟩
  · simpa only [fiberParameterStride, if_pos hi] using hq

theorem fiberParameter_regular_of_threshold {X Y : Type*} {keep : X → Prop}
    [DecidablePred keep] {N : X → ℕ} {q H : ℕ}
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    {density : ℝ} (hdense : ∀ k, density * (N k.val : ℝ) ≤ S.length k)
    (hq : 0 < q) (hkeep : ∀ i, H ≤ N i → keep i) (index : Y → X) :
    (∃ y, N (index y) < H) ∨
      ((∀ y, density * (N (index y) : ℝ) ≤ S.fiberParameterLength (index y)) ∧
        ∀ y, 0 < fiberParameterStride (keep := keep) (q := q) (index y)) := by
  classical
  by_cases hsmall : ∃ y, N (index y) < H
  · exact Or.inl hsmall
  · right
    have hret (y : Y) : keep (index y) :=
      hkeep (index y) (Nat.le_of_not_gt fun h => hsmall ⟨y, h⟩)
    exact ⟨fun y => (S.fiberParameter_dense_of_keep hdense hq (index y) (hret y)).1,
      fun y => (S.fiberParameter_dense_of_keep hdense hq (index y) (hret y)).2⟩

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PrecenterForecastNativeAtomDictionary
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def FiniteProbabilityWeights.sampledComplexTest
    {T X : Type*} [Fintype T] (law : FiniteProbabilityWeights T)
    (physical : T → X) (weight : T → ℂ) : (X → ℂ) →ₗ[ℂ] ℂ where
  toFun f := law.complexMean (fun t => f (physical t) * weight t)
  map_add' f g := by
    simp only [FiniteProbabilityWeights.complexMean, Pi.add_apply, add_mul,
      mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [FiniteProbabilityWeights.complexMean, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring

end Erdos3

end

end OAI
end


