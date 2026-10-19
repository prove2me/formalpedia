-- Prove2me | Definitions.Def_OAIE3v2B123
-- name    : OAIE3v2B123
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:47:43.706981+00:00
-- url     : https://prove2.me/theorems/82a0ec45-fab5-435e-aee4-269bd3462f42
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 125 of 311
-- statement:
--   Definitions bundle 125 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B101`, `OAIE3v2B102`, `OAIE3v2B104`, `OAIE3v2B105`, `OAIE3v2B106`, `OAIE3v2B107`, `OAIE3v2B108`, `OAIE3v2B109`, `OAIE3v2B110` of this split.
--
--   Modules: `Dynamics/FilteredSectionSingleDenominatorBudget.lean`, `Dynamics/TranslationMajorDetectedPotential.lean`, `Estimates/AllocatedCandidateCommonFastGeometry.lean`, `Estimates/AllocatedTrimmedVectorSite.lean`, `Estimates/BoundedQuotientFunctional.lean`, `Estimates/CoefficientSliceEmbedding.lean`, `Estimates/ControlledLinearSubspaceLift.lean`, `Estimates/CurrentLayerSplitting.lean`, `Estimates/LinearMapIntegralCover.lean`, `Estimates/OrbitBasepointNormalization.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/RationalTaggedConstraintHistory.lean`, `Estimates/RealTranslationEvaluationContinuity.lean`, `Estimates/ScalarDominatedSlack.lean`, `Estimates/SelectedImageCorrections.lean`, `Estimates/SymbolAbsorptionBounds.lean`, `Estimates/VectorAlgebraicMajorDecomposition.lean`, `Fourier/HomogeneousGradedProjectionFrequency.lean`, `Geometry/RealCoordinateFunctionals.lean`, `Geometry/RealSubspaceCoordinateRetraction.lean`, `Geometry/TranslationShearCoordinateSeries.lean`, `Lattices/ImageLatticeSubgroup.lean`, `Linear/AssociatedGradedBasisIndependence.lean`, `Linear/GradeProjectionRemainder.lean`, `Linear/LieKernelRealificationMark.lean`, `Linear/RationalTagConstraintChartBasis.lean`, `Linear/RefilteredKernelConstantBounds.lean`, `Linear/WeightedTranslationBasisHeight.lean`, `Nilpotent/BCHLatticeImageGap.lean`, `Nilpotent/BCHOuterGridChangeBasis.lean`, `Nilpotent/NiltestBasepointNormalization.lean`, `Polynomial/MajorTranslationPolynomialSymbolDegree.lean`, `Polynomial/QuantitativeOuterPolynomialProducts.lean`, `Polynomial/RealCoordinatePolynomialSymbol.lean`, `Polynomial/ScaledPolynomialDualBounds.lean`, `Polynomial/TranslationLogCoordinatePolynomials.lean`, `Polynomial/TranslationPhaseQuotient.lean`, `Polynomial/VectorPolynomialAffineSubspace.lean`, `Sampling/IntegralGridBudget.lean`, `Sampling/ScalarFunctionalCoefficientGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B101
import Definitions.Def_OAIE3v2B102
import Definitions.Def_OAIE3v2B104
import Definitions.Def_OAIE3v2B105
import Definitions.Def_OAIE3v2B106
import Definitions.Def_OAIE3v2B107
import Definitions.Def_OAIE3v2B108
import Definitions.Def_OAIE3v2B109
import Definitions.Def_OAIE3v2B110

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHLatticeImageGap
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s t : ℕ} (e : Basis ι ℝ L)
  (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (ht : LieModule.lowerCentralSeries ℚ L L t = ⊥)

theorem lipschitz_changeStep :
    letI := rightMetricSpace (hnil := hs) e
    letI := rightMetricSpace (hnil := ht) e
    LipschitzWith 1 (changeStep hs ht) := by
  apply lipschitz_mapReal_of_coordinate_bound (hnil := hs) (hM := ht)
    e e (LieHom.id : L →ₗ⁅ℝ⁆ L) (by norm_num : (0 : ℝ≥0) < 1)
  intro w
  change coordinateL2Norm (e.equivFun (e.equivFun.symm w)) ≤ 1 * coordinateL2Norm w
  rw [LinearEquiv.apply_symm_apply, one_mul]

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorAlgebraicMajorDecomposition
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialTranslationGroupOver

theorem algebraic_major_eval_on_subspace
    {B R : Type*} [CommRing R] (K : Submodule R (B → R))
    (D D₀ V : MvPolynomial B R) (A : B → R)
    (left middle right : PolynomialTranslationGroupOver R B)
    (hfactor : (⟨A, D - polynomialTranslate (-A) D₀⟩ : PolynomialTranslationGroupOver R B) =
      left * middle * right)
    (hpotential : ∀ z ∈ K, eval z middle.polynomial = eval z V - eval (z - middle.base) V)
    (hright : right.base ∈ K) (b : B → R) (hb : b ∈ K) :
    eval b D = eval (b - A) D₀ + eval (b - A + left.base) left.polynomial -
      eval (b - A + left.base) V + eval b right.polynomial + eval (b - right.base) V := by
  have hbase : A = left.base + middle.base + right.base := congrArg base hfactor
  have hpoly := congrArg (fun g : PolynomialTranslationGroupOver R B => eval b g.polynomial) hfactor
  change eval b (D - polynomialTranslate (-A) D₀) =
    eval b (polynomialTranslate (-right.base)
      (polynomialTranslate (-middle.base) left.polynomial + middle.polynomial) +
        right.polynomial) at hpoly
  simp only [map_sub, map_add, polynomialTranslate_eval_ring] at hpoly
  have hpot := hpotential (b - right.base) (K.sub_mem hb hright)
  have hx' : b - right.base - middle.base = b - A + left.base := by rw [hbase]; abel
  rw [hx'] at hpot
  have hpoly' : eval b D - eval (b - A) D₀ =
      eval (b - right.base - middle.base) left.polynomial +
        eval (b - right.base) middle.polynomial + eval b right.polynomial := by
    simpa only [majorFunctionSub, majorFunctionAdd, majorFunctionNeg,
      sub_eq_add_neg, Pi.add_apply, Pi.neg_apply] using hpoly
  rw [hx', hpot] at hpoly'
  linear_combination hpoly'

end PolynomialTranslationGroupOver

theorem algebraic_major_normalized_identity_on_subspace
    {U B : Type*} (K : Submodule ℝ (B → ℝ))
    (D : MvPolynomial (U ⊕ B) ℝ) (D₀ : MvPolynomial B ℝ)
    (A : B → MvPolynomial U ℝ) (E : MvPolynomial (U ⊕ B) ℝ)
    (e : B → MvPolynomial U ℝ) (Q : MvPolynomial (U ⊕ B) ℚ)
    (a : B → MvPolynomial U ℚ) (V : MvPolynomial B ℚ) (H : U → ℝ)
    (middle : (U → ℝ) → PolynomialTranslationGroupOver ℝ B)
    (hfactor : ∀ u, algebraicMajorSymbol D D₀ A u =
      normalizedMajorLeft E e H u * middle u * rationalMajorRight Q a u)
    (hpotential : ∀ u, ∀ z ∈ K,
      eval z (middle u).polynomial = eval₂ (algebraMap ℚ ℝ) z V -
        eval₂ (algebraMap ℚ ℝ) (z - (middle u).base) V)
    (hright : ∀ u, (fun j => eval₂ (algebraMap ℚ ℝ) u (a j)) ∈ K)
    (u : U → ℝ) (b : B → ℝ) (hb : b ∈ K) :
    eval (Sum.elim u b) D =
      eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j)))
        (majorSlowPolynomial D₀ E (map (algebraMap ℚ ℝ) V) e) +
      eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) (majorRationalPolynomial Q V a) := by
  have h := PolynomialTranslationGroupOver.algebraic_major_eval_on_subspace K
    (specializeMajorParameters (RingHom.id ℝ) D u) D₀ (map (algebraMap ℚ ℝ) V)
    (fun j => eval u (A j)) (normalizedMajorLeft E e H u) (middle u)
    (rationalMajorRight Q a u) (hfactor u)
    (by simpa only [eval_map] using hpotential u) (hright u) b hb
  rw [majorSlowPolynomial_eval, majorRationalPolynomial_eval₂]
  simp only [normalizedMajorLeft, rationalMajorRight, specializeMajorParameters_eval,
    eval₂_id, eval_map] at h ⊢
  simpa only [majorFunctionSub, majorFunctionAdd, Pi.sub_apply, Pi.add_apply, add_assoc] using h

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem specializeMajorParameters_translatedSlice {U B : Type*}
    (P0 : MvPolynomial B ℝ) (x : B → MvPolynomial U ℝ) (u : U → ℝ) :
    specializeMajorParameters (RingHom.id ℝ)
      (eval₂Hom C (fun j => X (Sum.inr j) - rename Sum.inl (x j)) P0) u =
        polynomialTranslate (fun j => -eval u (x j)) P0 := by
  apply MvPolynomial.funext
  intro b
  rw [specializeMajorParameters_eval, polynomialTranslate_eval_ring]
  change eval₂ (RingHom.id ℝ) (Sum.elim u b)
    (eval₂ C (fun j => X (Sum.inr j) - rename Sum.inl (x j)) P0) = _
  rw [← eval₂_assoc]
  simp only [eval₂_id]
  apply congrArg (fun f : B → ℝ => eval f P0)
  funext j
  rw [map_sub, eval_X, eval_rename]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPhaseQuotient
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {B U : Type*}

theorem translationPhaseArgument_majorSymbol
    (D : MvPolynomial (U ⊕ B) ℝ) (D₀ : MvPolynomial B ℝ)
    (A : B → MvPolynomial U ℝ) (u : U → ℝ) (β : B → ℝ) :
    translationPhaseArgument D₀ (algebraicMajorSymbol D D₀ A u) β =
      eval (Sum.elim u β) D := by
  simp only [translationPhaseArgument, algebraicMajorSymbol, map_sub,
    polynomialTranslate_eval_ring, specializeMajorParameters_eval]
  have he : (fun i => β i + -eval u (A i)) = β - (fun i => eval u (A i)) := by
    ext i; simp [sub_eq_add_neg]
  rw [he]
  exact sub_add_cancel _ _

theorem translationPhaseFunction_central
    (D₀ : MvPolynomial B ℝ) (g : PolynomialTranslationGroupOver ℝ B) (a : ℝ) :
    translationPhaseFunction D₀ (g * ⟨0, C a⟩) =
      translationPhaseFunction D₀ g * (Real.fourierChar a : ℂ) := by
  unfold translationPhaseFunction
  have hb : (g * (⟨0, C a⟩ : PolynomialTranslationGroupOver ℝ B)).base = g.base := by
    simp
  rw [hb]
  have ha := translationPhaseArgument_mul D₀ g
    (⟨0, C a⟩ : PolynomialTranslationGroupOver ℝ B) (fun i => (⌊g.base i + 1 / 2⌋ : ℝ))
  simp only [add_zero, eval_C] at ha
  rw [ha, Real.fourierChar.map_add_eq_mul]
  rfl

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedTranslationBasisHeight
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ : Type*} [Fintype σ]

theorem raw_lie_mem (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (x z : σ → ℚ) (P Q : MvPolynomial σ ℚ)
    (hx : (⟨x,P⟩ : PolynomialTranslationLie σ) ∈ U)
    (hz : (⟨z,Q⟩ : PolynomialTranslationLie σ) ∈ U) :
    (⟨0, scalarDirectionalDerivative x Q - scalarDirectionalDerivative z P⟩ :
      PolynomialTranslationLie σ) ∈ U :=
  U.lie_mem (x := ⟨x,P⟩) (y := ⟨z,Q⟩) hx hz

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module

variable {σ : Type*} [Fintype σ]

theorem weightedBasis_top_projection_polynomial (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d) (x : weightedSubalgebra w d) :
    (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) d x).val.polynomial =
      C (x.val.polynomial.coeff 0) := by
  classical
  let : Finsupp.NonTorsionWeight ℕ w := Finsupp.nonTorsionWeight_of ℕ w (fun i => (hw i).ne')
  apply MvPolynomial.ext
  intro a
  by_cases ha : Finsupp.weight w a < d
  · rw [weightedBasis_projection_coeff w d d hw x ⟨a, ha⟩]
    have he : d - Finsupp.weight w a = d ↔ a = 0 := by
      rw [← Finsupp.weight_eq_zero_iff_eq_zero w]
      omega
    simp only [he]
    by_cases ha0 : a = 0
    · subst a
      simp
    · simp [ha0, Ne.symm ha0]
  · have ha0 : a ≠ 0 := by
      intro h
      subst a
      simp only [map_zero] at ha
      omega
    rw [coeff_C, if_neg (Ne.symm ha0)]
    by_contra hne
    have hh := (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) d x).property.2
      (MvPolynomial.mem_support_iff.mpr hne)
    change Finsupp.weight w a + 1 ≤ d at hh
    omega

theorem weightedBasis_top_projection_val (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d) (x : weightedSubalgebra w d) :
    (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) d x).val =
      ⟨fun i => if w i = d then x.val.base i else 0, C (x.val.polynomial.coeff 0)⟩ := by
  apply PolynomialTranslationLie.ext
  · funext i
    exact weightedBasis_projection_base w d d hw x i
  · exact weightedBasis_top_projection_polynomial w d hw hd x

theorem weightedBasis_top_projection_eq (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d) (x : weightedSubalgebra w d) :
    (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) d x).val =
      topProjection w d x.val :=
  weightedBasis_top_projection_val w d hw hd x

theorem topProjection_mem_of_basisGraded (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (U : Submodule ℚ (PolynomialTranslationLie σ))
    (hU : U ≤ (weightedSubalgebra w d).toSubmodule)
    (hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (U.comap (weightedSubalgebra w d).subtype))
    {x : PolynomialTranslationLie σ} (hx : x ∈ U) : topProjection w d x ∈ U := by
  let y : weightedSubalgebra w d := ⟨x, hU hx⟩
  have hy := hgraded d y hx
  change (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) d y).val ∈ U at hy
  rw [weightedBasis_top_projection_eq w d hw hd] at hy
  exact hy

theorem weightedBasis_projection_isWeightedHomogeneous (w : σ → ℕ) (d j : ℕ)
    (hw : ∀ i, 0 < w i) (x : weightedSubalgebra w d) :
    (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).val.polynomial.IsWeightedHomogeneous w (d - j) := by
  classical
  intro a ha
  have hbound := (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).property.2
    (MvPolynomial.mem_support_iff.mpr ha)
  change Finsupp.weight w a + 1 ≤ d at hbound
  have haLT : Finsupp.weight w a < d := by omega
  rw [weightedBasis_projection_coeff w d j hw x ⟨a, haLT⟩] at ha
  have hgrade : d - Finsupp.weight w a = j := by
    by_contra hne
    simp only [hne, ↓reduceIte, ne_self_iff_false] at ha
  omega

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ]
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (x : weightedSubalgebra w d) {H : ℕ}

theorem weightedBasis_base_height
    (hall : ∀ i : WeightedBasisIndex w d,
      RationalHeightLE ((weightedBasis w d hw).repr x i) H) :
    ∀ i, RationalHeightLE (x.val.base i) H := by
  intro i
  simpa only [weightedBasis_repr_inl] using hall (Sum.inl i)

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHOuterGridChangeBasis
namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem exists_integral_grid_subgroup (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ) :
    ∃ (B : ℕ) (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)),
      0 < B ∧ l ∣ B ∧ B ≤ bchIntegralDenominatorBound s * H ^ (Fintype.card ι ^ 3) * l ∧
      Λ ≤ Γ ∧ bchSubgroupCoordinates e Λ = scaledIntegerGrid B := by
  obtain ⟨B, hB, hdiv, hbound, hstable⟩ := exists_bch_stable_integral_grid e hnil l hl hc
  let Λ := coordinateGridBCHSubgroup e B hnil hstable
  have hcoords := coordinateGridBCHSubgroup_coordinates e B hnil hstable
  refine ⟨B, Λ, hB, hdiv, hbound, ?_, hcoords⟩
  intro g hg
  apply (bchSubgroupCoordinates_repr e Γ g).mp
  apply hinner
  apply scaledIntegerGrid_subset_of_dvd hdiv
  rw [← hcoords]
  exact (bchSubgroupCoordinates_repr e Λ g).mpr hg

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ImageLatticeSubgroup
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped Matrix TensorProduct

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

theorem real_image_lattice_lift [DecidableEq ι] [DecidableEq κ]
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M) (σ : M →ₗ[ℚ] L)
    (hσ : (φ.toLinearMap.comp σ).comp φ.toLinearMap = φ.toLinearMap)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL))
    (Λ : Subgroup (NilpotentLieBCHGroup M s hM)) (l B : ℕ)
    (hΓ : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (hΛ : bchSubgroupCoordinates f Λ ⊆ scaledIntegerGrid B)
    (hdiv : l * matrixDenominator (LinearMap.toMatrix f e σ) ∣ B) :
    Λ.map realificationHom ⊓ (realificationMap (hnil := hL) (hM := hM) φ).range ≤
      (Γ.map realificationHom).map (realificationMap (hnil := hL) (hM := hM) φ) := by
  rintro g ⟨hg, himage⟩
  obtain ⟨γ, hγ, rfl⟩ := hg
  obtain ⟨x, hx⟩ := himage
  have hxcoord := congrArg NilpotentLieBCHGroup.coord hx
  change φ.toLinearMap.baseChange ℝ x.coord = (1 : ℝ) ⊗ₜ[ℚ] γ.coord at hxcoord
  have hsection := DFunLike.congr_fun (linearMap_baseChange_image_section φ.toLinearMap σ hσ) x.coord
  change φ.toLinearMap.baseChange ℝ (σ.baseChange ℝ (φ.toLinearMap.baseChange ℝ x.coord)) =
    φ.toLinearMap.baseChange ℝ x.coord at hsection
  rw [hxcoord] at hsection
  have hpre : φ (σ γ.coord) = γ.coord := by
    apply rationalLieInclusion_injective f
    change (1 : ℝ) ⊗ₜ[ℚ] φ (σ γ.coord) = (1 : ℝ) ⊗ₜ[ℚ] γ.coord
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul] at hsection
    exact hsection
  let a : NilpotentLieBCHGroup L s hL := ⟨σ γ.coord⟩
  have ha : a ∈ Γ := by
    apply (bchSubgroupCoordinates_repr e Γ a).mp
    apply hΓ
    have hy := scaledIntegerGrid_subset_of_dvd hdiv
      (hΛ ((bchSubgroupCoordinates_repr f Λ γ).mpr hγ))
    have hs := matrix_mulVec_fine_grid (LinearMap.toMatrix f e σ) l hy
    change LinearMap.toMatrix f e σ *ᵥ f.equivFun γ.coord ∈ scaledIntegerGrid l at hs
    rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply] at hs
    exact hs
  refine ⟨realificationHom a, ⟨a, ha, rfl⟩, ?_⟩
  rw [realificationMap_realificationHom]
  apply congrArg realificationHom
  exact ext hpre

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

theorem exists_image_lattice_subgroup (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (Γ : Subgroup (NilpotentLieBCHGroup L s hL))
    (Δ : Subgroup (NilpotentLieBCHGroup M s hM))
    (l m H : ℕ) (hl : 0 < l) (hm : 0 < m) (hH : 1 ≤ H)
    (hΓ : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (hΔ : scaledIntegerGrid m ⊆ bchSubgroupCoordinates f Δ)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants f i j k) H) :
    ∃ (B : ℕ) (Λ : Subgroup (NilpotentLieBCHGroup M s hM)),
      0 < B ∧ m ∣ B ∧ B ≤ bchIntegralDenominatorBound s * H ^ (Fintype.card κ ^ 3) *
        (m * (l * rationalKernelHeight (Fintype.card κ) H ^ (Fintype.card ι * Fintype.card κ))) ∧
      Λ ≤ Δ ∧ bchSubgroupCoordinates f Λ = scaledIntegerGrid B ∧
      Λ.map realificationHom ⊓ (realificationMap (hnil := hL) (hM := hM) φ).range ≤
        (Γ.map realificationHom).map (realificationMap (hnil := hL) (hM := hM) φ) := by
  classical
  obtain ⟨σ, hσ, hσH⟩ := exists_bounded_linear_image_section e f φ.toLinearMap hH hentries
  let D := matrixDenominator (LinearMap.toMatrix f e σ)
  have hD : 0 < D := matrixDenominator_pos _
  have hDb : D ≤ rationalKernelHeight (Fintype.card κ) H ^ (Fintype.card ι * Fintype.card κ) := by
    apply matrixDenominator_le
    intro i j
    rw [LinearMap.toMatrix_apply]
    exact hσH i j
  let q := m * (l * D)
  have hq : 0 < q := Nat.mul_pos hm (Nat.mul_pos hl hD)
  have hΔq : scaledIntegerGrid q ⊆ bchSubgroupCoordinates f Δ :=
    (scaledIntegerGrid_subset_of_dvd (dvd_mul_right m (l * D))).trans hΔ
  obtain ⟨B, Λ, hB, hqB, hBb, hΛ, hgrid⟩ := exists_integral_grid_subgroup f hM Δ q hq hc hΔq
  refine ⟨B, Λ, hB, (dvd_mul_right m (l * D)).trans hqB, ?_, hΛ, hgrid, ?_⟩
  · exact hBb.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left m (Nat.mul_le_mul_left l hDb)))
  · apply real_image_lattice_lift e f φ σ hσ Γ Λ l B hΓ
    · exact hgrid.le
    · exact (dvd_mul_left (l * D) m).trans hqB

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolAbsorptionBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in

theorem truncateRealGrades_mem_of_quotient_mem (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (hU : BasisGradedSubmodule (b.baseChange ℝ) w U.toSubmodule)
    (j : ℕ) (g : F.realification.Group)
    (hg : NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) g ∈
      (NilpotentLieBCHGroup.realLieSubgroup (hnil := F.realification.lowerCentralSeries_eq_bot) U).map
        (NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j))) :
    (F.truncateRealGrades b w j g).coord ∈ U := by
  obtain ⟨u, hu, heq⟩ := Subgroup.mem_map.mp hg
  have hdiff : g.coord - u.coord ∈ F.realification.layer j := by
    apply (lieQuotientMap_eq_zero (F.realification.layerIdeal j) _).mp
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg NilpotentLieBCHGroup.coord heq).symm
  have ht := (F.realGradeTruncation_eq_iff b w hlayers j g.coord u.coord).mpr hdiff
  change basisBelowProjection (b.baseChange ℝ) w j g.coord ∈ U
  rw [ht]
  exact hU.below_mem (b.baseChange ℝ) w U.toSubmodule j u.coord hu

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i})) (v : σ → ℕ)

theorem truncateRealSymbol_rational (j : ℕ) (g : F.RealPolynomialSymbolGroup v)
    (l : ℕ) (hg : F.SymbolRationalGrid b w hlayers v l g) :
    F.SymbolRationalGrid b w hlayers v l (F.truncateRealSymbol b w hlayers v j g) :=
  basisCoordinateProjection_real_grid ((F.polynomialSymbolBasis b w hlayers v).baseChange ℝ)
    {z | w z.val.2 < j} l g.coord hg

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem symbolPointwiseSubalgebra_iInf {η : Type*} (U : η → LieSubalgebra ℚ F.AssociatedGraded) :
    F.symbolPointwiseSubalgebra b ω hlayers w (⨅ j, U j) =
      ⨅ j, F.symbolPointwiseSubalgebra b ω hlayers w (U j) := by
  ext x
  rw [lieSubalgebra_mem_iInf, F.mem_symbolPointwiseSubalgebra_iff]
  simp only [F.mem_symbolPointwiseSubalgebra_iff, lieSubalgebra_mem_iInf]
  exact forall_comm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

theorem petalComparisonSpace_top_tree
    {I L M : Type*} [LieRing L] [LieAlgebra ℚ L] [AddCommGroup M] [Module ℚ M]
    {s r : ℕ} (F : DegreeRankLieFiltration L s r) (d : I → ℕ)
    (C P : I → Submodule ℚ L) (hC : ∀ i, C i ≤ F.layer (d i) 1)
    (hP : ∀ i, P i ≤ F.layer (d i) 1)
    (η : L →ₗ[ℚ] M) (a : FreeMagma I)
    (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (hinvariant : ∀ c p : I → L, (∀ i, c i ∈ C i) → (∀ i, p i ∈ P i) →
      η (lieTreeEval (c + p) a) = η (lieTreeEval c a))
    (z : I → Fin 2 → L)
    (hz : ∀ i, z i ∈ petalComparisonSpace (C i) (P i) (F.layer (d i) 2)) :
    pairDifferenceFunctional η (lieTreeEval z a) = 0 := by
  classical
  choose c hc p hp k₀ hk₀ k₁ hk₁ h₀ h₁ using
    (fun i => petalComparisonSpace_decompose (C i) (P i) (F.layer (d i) 2) (z i) (hz i))
  have hle (i : I) : F.layer (d i) 2 ≤ F.layer (d i) 1 :=
    F.lex_antitone (Or.inr ⟨rfl, by omega⟩)
  have hz₀ (i : I) : z i 0 ∈ F.layer (d i) 1 := by
    rw [h₀]
    exact (F.layer (d i) 1).add_mem ((F.layer (d i) 1).add_mem (hC i (hc i)) (hP i (hp i)))
      (hle i (hk₀ i))
  have hz₁ (i : I) : z i 1 ∈ F.layer (d i) 1 := by
    rw [h₁]
    exact (F.layer (d i) 1).add_mem (hC i (hc i)) (hle i (hk₁ i))
  have hdiff₀ (i : I) : z i 0 - (c i + p i) ∈ F.layer (d i) 2 := by
    rw [h₀]
    simpa only [add_sub_cancel_left] using hk₀ i
  have hdiff₁ (i : I) : z i 1 - c i ∈ F.layer (d i) 2 := by
    rw [h₁]
    simpa only [add_sub_cancel_left] using hk₁ i
  have heq₀ := F.top_lieTreeEval_congr (fun i => z i 0) (c + p) d hz₀
    (fun i => (F.layer (d i) 1).add_mem (hC i (hc i)) (hP i (hp i))) hdiff₀ a hd hr
  have heq₁ := F.top_lieTreeEval_congr (fun i => z i 1) c d hz₁
    (fun i => hC i (hc i)) hdiff₁ a hd hr
  change η ((liePiEval (0 : Fin 2)) (lieTreeEval z a)) -
    η ((liePiEval (1 : Fin 2)) (lieTreeEval z a)) = 0
  rw [map_lieTreeEval, map_lieTreeEval]
  change η (lieTreeEval (fun i => z i 0) a) - η (lieTreeEval (fun i => z i 1) a) = 0
  rw [heq₀, heq₁, hinvariant c p hc hp, sub_self]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScaledPolynomialDualBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem exists_constant_normalized_polynomial
    (g : (F.adaptedPolynomialFiltration w).Group) (r γ : F.Group)
    (hg : F.adaptedPolynomialConstantHom w g = r * γ) :
    ∃ q : (F.adaptedPolynomialFiltration w).Group,
      F.adaptedConstantGroupHom w r * q * F.adaptedConstantGroupHom w γ = g ∧
      coefficients (q.coord : VectorPolynomial σ ℚ L) 0 = 0 ∧
      F.polynomialSymbolHom w q = F.polynomialSymbolHom w g := by
  let c := F.adaptedConstantGroupHom w
  let q := c r⁻¹ * g * c γ⁻¹
  have hq : F.adaptedPolynomialConstantHom w q = 1 := by
    simp only [q, c, map_mul, F.adaptedPolynomialConstantHom_constant, hg]
    simp
  refine ⟨q, ?_, ?_, ?_⟩
  · simp [q, c, mul_assoc]
  · have hc := congrArg NilpotentLieBCHGroup.coord hq
    simpa only [F.adaptedPolynomialConstantHom_coord, NilpotentLieBCHGroup.coord_one] using hc
  · simp only [q, c, map_mul, F.polynomialSymbolHom_constant, one_mul, mul_one]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

theorem polynomialRationalGrid_of_dvd {l m : ℕ} (hl : 0 < l) (hlm : l ∣ m)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w l g) : F.PolynomialRationalGrid b w m g :=
  realDenominatorGrid_subset_of_dvd hl hlm hg

theorem polynomialRationalGrid_constant (l : ℕ) (c : F.realification.Group)
    (hc : (fun i => (b.baseChange ℝ).repr c.coord i) ∈ realDenominatorGrid l) :
    F.PolynomialRationalGrid b w l (F.realification.adaptedConstantGroupHom w c) := by
  classical
  obtain ⟨a, ha⟩ := hc
  refine ⟨fun z => if z.1 = 0 then a z.2 else 0, ?_⟩
  funext z
  change ((if z.1 = 0 then a z.2 else 0 : ℤ) : ℝ) =
    (l : ℝ) * (b.baseChange ℝ).repr
      (coefficients ((F.realification.adaptedConstantGroupHom w c).coord :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2
  rw [F.realification.adaptedConstantGroupHom_log, coefficients_monomial]
  by_cases h : z.1 = 0
  · simpa only [h, ite_true, Finsupp.single_eq_same, Pi.smul_apply, smul_eq_mul] using congrFun ha z.2
  · simp only [h, ite_false, Int.cast_zero, Finsupp.single_eq_of_ne h, map_zero,
      Finsupp.zero_apply, mul_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

theorem polynomialSlowBound_inv_iff (T : σ → ℝ) (M : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.PolynomialSlowBound b w T M g⁻¹ ↔ F.PolynomialSlowBound b w T M g := by
  change (∀ α i, |(b.baseChange ℝ).repr
    (coefficients (-(g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) α) i| ≤ M / monomialScale T α) ↔ _
  simp only [map_neg, Finsupp.neg_apply, abs_neg, PolynomialSlowBound]

theorem polynomialSlowBound_constant (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (c : F.realification.Group)
    (hc : ∀ i, |(b.baseChange ℝ).repr c.coord i| ≤ M) :
    F.PolynomialSlowBound b w T M (F.realification.adaptedConstantGroupHom w c) := by
  classical
  intro α i
  rw [F.realification.adaptedConstantGroupHom_log, coefficients_monomial]
  by_cases hα : α = 0
  · subst α
    simpa only [Finsupp.single_eq_same, monomialScale_zero, div_one] using hc i
  · rw [Finsupp.single_eq_of_ne hα, map_zero, Finsupp.zero_apply, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OrbitBasepointNormalization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def constantPolynomialOrbit (a : F.Group) : F.PolynomialOrbit w :=
  F.adaptedBCHToOrbit w (F.adaptedConstantGroupHom w a)

theorem polynomialOrbitEval_constant (a : F.Group) (x : σ → ℤ) :
    F.polynomialOrbitEval w x (F.constantPolynomialOrbit w a) = a := by
  apply NilpotentLieBCHGroup.ext
  change eval (fun i => (x i : ℚ)) (monomial 0 a.coord) = a.coord
  rw [eval_monomial, Finsupp.prod_zero_index, one_smul]

noncomputable def normalizePolynomialOrbit (g : F.PolynomialOrbit w) (a γ : F.Group) :
    F.PolynomialOrbit w :=
  F.constantPolynomialOrbit w a⁻¹ * g * F.constantPolynomialOrbit w γ⁻¹

theorem normalizePolynomialOrbit_eval (g : F.PolynomialOrbit w) (a γ : F.Group)
    (x : σ → ℤ) :
    F.polynomialOrbitEval w x (F.normalizePolynomialOrbit w g a γ) =
      a⁻¹ * F.polynomialOrbitEval w x g * γ⁻¹ := by
  simp only [normalizePolynomialOrbit, map_mul, polynomialOrbitEval_constant]

theorem normalizePolynomialOrbit_zero (g : F.PolynomialOrbit w) (a γ : F.Group)
    (hg : F.polynomialOrbitEval w 0 g = a * γ) :
    F.polynomialOrbitEval w 0 (F.normalizePolynomialOrbit w g a γ) = 1 := by
  rw [normalizePolynomialOrbit_eval, hg]
  simp

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d) (hD : D.filtration.layer (s + 1) = ⊥)

noncomputable def dropTop : RationalFilteredNilmanifold L s d where
  filtration := D.filtration.dropTop hD
  basis := D.basis
  layerBasis i := D.layerBasis ⟨i.val, by omega⟩
  lattice := D.lattice.map (NilpotentLieBCHGroup.changeStep D.filtration.lowerCentralSeries_eq_bot
    (D.filtration.dropTop hD).lowerCentralSeries_eq_bot).toMonoidHom
  grid := D.grid
  grid_pos := D.grid_pos
  inner_grid := by
    rw [bchSubgroupCoordinates_changeStep]
    exact D.inner_grid
  outer_grid := by
    rw [bchSubgroupCoordinates_changeStep]
    exact D.outer_grid

theorem dropTop_geometry {p : ℝ} (hp : D.GeometryComplexityLE p) :
    (D.dropTop hD).GeometryComplexityLE p :=
  ⟨hp.1, hp.2.1, hp.2.2.1, fun i j k => hp.2.2.2 ⟨i.val, by omega⟩ j k⟩

theorem dropTop_lattice_back :
    (D.dropTop hD).lattice ≤ D.lattice.comap
      (NilpotentLieBCHGroup.mapOfSteps
        (hL := (D.filtration.dropTop hD).lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L)) := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
  exact hx

end Erdos3.RationalFilteredNilmanifold

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

theorem eval_step_zero (D : RationalFilteredNilmanifold L 0 d)
    (T : D.Niltest w) (x : σ → ℤ) :
    T.eval x = T.observable (QuotientGroup.mk (1 : D.RealGroup)) := by
  unfold eval
  rw [NilpotentLieFiltration.polynomialOrbitEval_step_zero]

end Niltest
end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FilteredSectionSingleDenominatorBudget
namespace OAI

section

namespace Erdos3

theorem filtered_section_pair_denominator_le_exp {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) (l : ℕ) {H : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p)
    (hD : ∀ i j, RationalHeightLE (D i j) H)
    (hS : ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card κ) H))
    (hl : (l : ℝ) ≤ Real.exp p) :
    ((matrixDenominator S * matrixDenominator D * l : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 11) := by
  have hH7 := hH.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide : 1 ≤ 7)))
  have hK := rationalKernelHeight_le_budget (Fintype.card κ) H hp hκ hH
  have h := matrix_pair_denominator_le_exp_power D S l hp 7 (by decide) hι hκ
    (fun i j => (Nat.cast_le.mpr (hD i j).2).trans hH7)
    (fun i j => (Nat.cast_le.mpr (hS i j).2).trans hK) hl
  simpa only [Nat.mul_comm (matrixDenominator S) (matrixDenominator D)] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.IntegralGridBudget
namespace OAI

section

namespace Erdos3

open Module

theorem exists_integral_grid_subgroup_exp (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ),
      0 < l → (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      ∃ (B : ℕ) (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)),
        0 < B ∧ l ∣ B ∧ (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        Λ ≤ Γ ∧ bchSubgroupCoordinates e Λ = scaledIntegerGrid B := by
  refine ⟨bchIntegralDenominatorBound s + 5, by omega, ?_⟩
  intro ι L _ _ _ e hnil Γ l H p hl hc hinner hp hd hH hlp
  obtain ⟨B, Λ, hB, hdiv, hbound, hΛ, hcoords⟩ := exists_integral_grid_subgroup e hnil Γ l hl hc hinner
  exact ⟨B, Λ, hB, hdiv, (Nat.cast_le.mpr hbound).trans
    (integral_grid_allowance_le_exp _ _ _ _ hp hd hH hlp), hΛ, hcoords⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorTranslationPolynomialSymbolDegree
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem majorTranslationJointPolynomial_specialize
    (D : MvPolynomial (U ⊕ B) ℝ) (x : B → MvPolynomial U ℝ) (u : U → ℝ) :
    specializeMajorParameters (RingHom.id ℝ) (majorTranslationJointPolynomial D x) u =
      (algebraicMajorSymbol D (specializeMajorParameters (RingHom.id ℝ) D 0) x u).polynomial := by
  have hsub : specializeMajorParameters (RingHom.id ℝ) (majorTranslationJointPolynomial D x) u =
      specializeMajorParameters (RingHom.id ℝ) D u -
      specializeMajorParameters (RingHom.id ℝ)
        (eval₂Hom C (fun j => X (Sum.inr j) - rename Sum.inl (x j))
          (specializeMajorParameters (RingHom.id ℝ) D 0)) u := by
    simp only [majorTranslationJointPolynomial, specializeMajorParameters, map_sub]
  rw [hsub, specializeMajorParameters_translatedSlice]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealCoordinatePolynomialSymbol
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem real_adapted_coordinate_degree (e : Basis ι ℚ L) (omega : ι → ℕ)
    (hlayer : ∀ k, F.layer k = Submodule.span ℚ (e '' {j | k ≤ omega j}))
    {w : σ → ℕ} (p : F.realification.PolynomialOrbit w) (j : ι) :
    coordinate ((e.baseChange ℝ).coord j).toAddMonoidHom p.log ∈
      weightedSupportLE w (omega j) := by
  rw [mem_weightedSupportLE_iff, scalar_weightedDegree_le_iff]
  intro α hα
  rw [coeff_coordinate]
  change (e.baseChange ℝ).repr (coefficients p.log α) j = 0
  have hm := (F.realification.adapted_iff_coefficients w p.log).mp p.adapted α
  change coefficients p.log α ∈ (F.realLayer (Finsupp.weight w α)).toSubmodule at hm
  rw [F.realLayer_eq_span_basis e _ _ (hlayer _), (e.baseChange ℝ).mem_span_image] at hm
  by_contra h
  exact (not_le_of_gt hα) (hm (Finsupp.mem_support_iff.mpr h))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis (Fin d) ℚ L) (omega : Fin d → ℕ)
  (hlayer : ∀ k, F.layer k = Submodule.span ℚ (e '' {j | k ≤ omega j}))

include hlayer

theorem real_scaled_adapted_basis_mem (B : ℝ) (j : Fin d) :
    B • (e.baseChange ℝ) j ∈ F.realification.layer (omega j) := by
  change B • (e.baseChange ℝ) j ∈ (F.realLayer (omega j)).toSubmodule
  rw [F.realLayer_eq_span_basis e _ _ (hlayer _)]
  exact Submodule.smul_mem _ B (Submodule.subset_span ⟨j, by simp, rfl⟩)

noncomputable def orderedSlotFactor (B : ℝ) (i j : Fin d) :
    F.realification.PolynomialOrbit (patchVariableWeight (σ := σ) omega i) := by
  classical
  exact if h : j.val < i.val then
    polynomialOrbitOfLog
      (monomial (Finsupp.single (Sum.inr (⟨j.val, h⟩ : Fin i.val)) 1)
        (B • (e.baseChange ℝ) j)) (by
      apply (F.realification.mem_adaptedSubmodule _ _).mp
      apply F.realification.monomial_mem_adaptedSubmodule
      simpa only [Finsupp.weight_single, one_smul, patchVariableWeight,
        Sum.elim_inr, earlierSlot, Fin.eta] using
        F.real_scaled_adapted_basis_mem e omega hlayer B j)
  else 1

noncomputable def orderedSlotOrbit (B : ℝ) (a : F.realification.Group)
    (p : F.realification.PolynomialOrbit (fun _ : σ => 1)) (i : Fin d) :
    F.realification.PolynomialOrbit (patchVariableWeight (σ := σ) omega i) :=
  F.realification.constantPolynomialOrbit _ a *
    F.realification.polynomialOrbitSubstitute
      (w := fun _ : σ => 1) (v := patchVariableWeight omega i)
      (fun x => (MvPolynomial.X (Sum.inl x) : MvPolynomial (σ ⊕ Fin i.val) ℚ))
      (by
        intro x
        simpa only [patchVariableWeight, Sum.elim_inl] using
          (weightedSupportLE_X (R := ℚ) (patchVariableWeight (σ := σ) omega i) (Sum.inl x))) p *
    ((List.finRange d).map (F.orderedSlotFactor e omega hlayer B i)).prod

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (v : σ → ℕ) (P : ι → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE v (ω i))

include hlayers hP

theorem realCoordinatePolynomialOrbit_eval_coordinates (u : σ → ℝ) (i : ι) :
    (b.baseChange ℝ).repr
      (F.realification.polynomialOrbitRealEval v u
        (F.realCoordinatePolynomialOrbit b ω hlayers v P hP)).coord i =
      MvPolynomial.eval u (P i) := by
  change (b.baseChange ℝ).coord i
    (eval₂ u (F.realCoordinatePolynomialOrbit b ω hlayers v P hP).log) = _
  rw [coordinate_eval₂, realCoordinatePolynomialOrbit_coordinate]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis (Fin d) ℚ L) (omega : Fin d → ℕ)
  (hlayer : ∀ k, F.layer k = Submodule.span ℚ (e '' {j | k ≤ omega j}))

noncomputable def orderedPolynomialSlots (B : ℝ) (a : F.realification.Group)
    (p : F.realification.PolynomialOrbit (fun _ : σ => 1)) : PolynomialSlots σ d omega where
  center i := MvPolynomial.C (-1 / B) *
    coordinate ((e.baseChange ℝ).coord i).toAddMonoidHom
      (F.orderedSlotOrbit e omega hlayer B a p i).log
  degree i := by
    simpa only [zero_add] using weightedSupportLE_mul
      (weightedSupportLE_C (patchVariableWeight omega i) 0 (-1 / B))
      (F.real_adapted_coordinate_degree e omega hlayer
        (F.orderedSlotOrbit e omega hlayer B a p i) i)

noncomputable def orderedPolynomialPatch (hpos : ∀ i, 1 ≤ omega i)
    (hmax : ∀ i, omega i ≤ s) (hmono : Monotone omega) (B : ℝ)
    (a : F.realification.Group) (p : F.realification.PolynomialOrbit (fun _ : σ => 1))
    (Phi : PatchKernel d) : PolynomialPatch σ s d where
  weight := omega
  weight_pos := hpos
  weight_le := hmax
  weight_mono := hmono
  form := F.orderedPolynomialSlots e omega hlayer B a p
  kernel := Phi

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AssociatedGradedBasisIndependence
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hb : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem associatedGradedPieceMap_repr_symm (j : ℕ) (x : F.layer j) :
    b.repr.symm ((F.associatedGradedBasis b ω hb).repr (F.associatedGradedPieceMap j x)) =
      basisGradeProjection b ω j x.val := by
  apply b.repr.injective
  ext i
  rw [b.repr.apply_symm_apply, F.associatedGradedPieceMap_coordinate,
    basisGradeProjection_repr]
  simp only [eq_comm]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CurrentLayerSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem normalized_splitting_sub_sum_mem_next_layer (k : ℕ)
    (E P R E₀ R₀ : F.Group)
    (hE : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) E₀ =
      NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) E)
    (hR : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) R =
      NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) R₀) :
    (E₀⁻¹ * (E * P * R) * R₀⁻¹).coord -
      ((E₀⁻¹ * E).coord + P.coord + (R * R₀⁻¹).coord) ∈ F.layer (k + 1) := by
  have heq : E₀⁻¹ * (E * P * R) * R₀⁻¹ = (E₀⁻¹ * E) * P * (R * R₀⁻¹) := by
    simp only [mul_assoc]
  rw [heq]
  exact F.bch_triple_sub_sum_mem_next_layer k _ _ _
    (F.inv_mul_coord_mem_layer_of_quotient_eq k E₀ E hE)
    (F.mul_inv_coord_mem_layer_of_quotient_eq k R R₀ hR)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.GradeProjectionRemainder
namespace OAI

section

namespace Erdos3

open Module

namespace NilpotentLieFiltration

open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem realGradeProjection_normalized_splitting (k : ℕ)
    (E P R E₀ R₀ : F.realification.Group)
    (hE : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) E₀ =
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) E)
    (hR : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) R =
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) R₀) :
    basisGradeProjection (b.baseChange ℝ) w k (E₀⁻¹ * (E * P * R) * R₀⁻¹).coord =
      basisGradeProjection (b.baseChange ℝ) w k (E₀⁻¹ * E).coord +
        basisGradeProjection (b.baseChange ℝ) w k P.coord +
        basisGradeProjection (b.baseChange ℝ) w k (R * R₀⁻¹).coord := by
  have h := F.realGradeProjection_eq_zero_of_mem_next_layer b w hlayers k _
    (F.realification.normalized_splitting_sub_sum_mem_next_layer k E P R E₀ R₀ hE hR)
  simpa only [map_sub, map_add, sub_eq_zero] using h

include hlayers in

theorem realGradeProjection_normalized_residual_mem
    (U : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hU : BasisGradedSubmodule (b.baseChange ℝ) w U) (k : ℕ)
    (E P R E₀ R₀ : F.realification.Group) (hP : P.coord ∈ U)
    (hE : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) E₀ =
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) E)
    (hR : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) R =
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) R₀) :
    basisGradeProjection (b.baseChange ℝ) w k (E₀⁻¹ * (E * P * R) * R₀⁻¹).coord -
      basisGradeProjection (b.baseChange ℝ) w k (E₀⁻¹ * E).coord -
      basisGradeProjection (b.baseChange ℝ) w k (R * R₀⁻¹).coord ∈ U := by
  rw [F.realGradeProjection_normalized_splitting b w hlayers k E P R E₀ R₀ hE hR]
  convert hU k P.coord hP using 1
  abel

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.HomogeneousGradedProjectionFrequency
namespace OAI

section

namespace Erdos3

open Module

variable {K V W ι κ : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

theorem graded_image_frequency_zero
    (b : Basis ι K V) (ω : ι → ℕ) (c : Basis κ K W) (ν : κ → ℕ)
    (T : V →ₗ[K] W) (s : ℕ)
    (hT : ∀ x, T (basisGradeProjection b ω s x) = basisGradeProjection c ν s (T x))
    (U : Submodule K V) (hU : BasisGradedSubmodule b ω U) (η : W →ₗ[K] K)
    (hsource : ∀ x ∈ U, basisGradeProjection b ω s x = x → η (T x) = 0)
    {y : W} (hy : y ∈ U.map T) (hgrade : basisGradeProjection c ν s y = y) :
    η y = 0 := by
  obtain ⟨x, hx, rfl⟩ := hy
  have h := hsource (basisGradeProjection b ω s x) (hU s x hx)
    (basisCoordinateProjection_idempotent b {i | ω i = s} x)
  rwa [hT, hgrade] at h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledLinearSubspaceLift
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem exists_controlled_weighted_linear_splitting
    {ι κ δ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → δ) (c : κ → δ) (A : Matrix ι κ ℚ)
    (hblock : ∀ i j, r i ≠ c j → A i j = 0)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ (S : Matrix κ ι ℚ) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧ l ∣ m ∧
      (∀ i j, c i ≠ r j → S i j = 0) ∧
      ∀ (W : δ → ℝ), (∀ d, 0 < W d) → (∀ i, Real.exp (separationBudget p) ≤ W (r i)) →
      ∀ (a b : ι → ℝ) (v : κ → ℝ),
      (∀ i, |a i| ≤ Real.exp p / W (r i)) → b ∈ realDenominatorGrid l →
      (fun i j => (A i j : ℝ)) *ᵥ v = a + b →
      (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ a) = a ∧
      (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ b) = b ∧
      (∀ i, |((fun i j => (S i j : ℝ)) *ᵥ a) i| ≤
        Real.exp ((p + 2) ^ 18 + p) / W (c i)) ∧
      (fun i j => (S i j : ℝ)) *ᵥ b ∈ realDenominatorGrid m ∧
      (fun i j => (A i j : ℝ)) *ᵥ
        (v - (fun i j => (S i j : ℝ)) *ᵥ a - (fun i j => (S i j : ℝ)) *ᵥ b) = 0 := by
  obtain ⟨S, hS, hSb, hSH⟩ := exists_bounded_block_image_section r c A hblock hH hA
  refine ⟨S, matrixDenominator S * l, Nat.mul_pos (matrixDenominator_pos S) hl,
    real_image_section_denominator_bound S H l hSH hp hι hκ hHp hlp,
    ⟨matrixDenominator S, Nat.mul_comm _ _⟩, hSb, ?_⟩
  intro W hW hWmin a b v ha hb hv
  have hanorm : ‖a‖ ≤ Real.exp p / Real.exp (separationBudget p) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    apply (show ‖a i‖ ≤ Real.exp p / W (r i) by simpa only [Real.norm_eq_abs] using ha i).trans
    exact div_le_div_of_nonneg_left (Real.exp_nonneg p) (Real.exp_pos _) (hWmin i)
  have hsum : a + b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) :=
    (real_column_span_mem_iff A (a + b)).mpr ⟨v, hv⟩
  obtain ⟨haspan, hbspan⟩ := controlled_small_vector_separation A hH hl hA hp hι hκ hHp hlp a b hanorm hb hsum
  have hSa := real_matrix_image_section_apply A S hS a ((real_column_span_mem_iff A a).mp haspan)
  have hSb' := real_matrix_image_section_apply A S hS b ((real_column_span_mem_iff A b).mp hbspan)
  refine ⟨hSa, hSb', ?_, real_matrix_denominator_grid S l b hb, ?_⟩
  · intro i
    simpa only [← Real.exp_add] using
      real_image_section_weighted_bound r c S H hSb hSH hp hι hκ hHp W hW (Real.exp_nonneg p) a ha i
  · change Matrix.of (fun i j => (A i j : ℝ)) *ᵥ
      (v - Matrix.of (fun i j => (S i j : ℝ)) *ᵥ a - Matrix.of (fun i j => (S i j : ℝ)) *ᵥ b) = 0
    rw [Matrix.mulVec_sub, Matrix.mulVec_sub]
    exact (congrArg₂ (fun x y : ι → ℝ => x - y)
      (congrArg₂ (fun x y : ι → ℝ => x - y) hv hSa) hSb').trans (by abel)

end Erdos3

end

section

namespace Erdos3

open scoped Matrix NNReal

variable {η ι δ : Type*} [Fintype ι]

theorem exists_joint_weighted_corrections [Fintype η]
    (c : ι → δ) (Q : η → Matrix ι ι ℚ)
    (hblock : ∀ b i j, c i ≠ c j → Q b i j = 0)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hQ : ∀ b i j, RationalHeightLE (Q b i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hrows : (Fintype.card (Σ _ : η, ι) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (((p + 2) ^ 4 + 2) ^ 36) ∧ l ∣ m ∧
      ∀ (W : δ → ℝ), (∀ d, 0 < W d) →
      (∀ i, Real.exp (separationBudget ((p + 2) ^ 4)) ≤ W (c i)) →
      ∀ (e r : η → ι → ℝ) (v : ι → ℝ),
      (∀ b i, |e b i| ≤ Real.exp p / W (c i)) →
      (∀ b, r b ∈ realDenominatorGrid l) →
      (∀ b, (fun i j => (Q b i j : ℝ)) *ᵥ (v - e b - r b) = 0) →
      ∃ u d : ι → ℝ,
        (∀ i, |u i| ≤ Real.exp (((p + 2) ^ 4 + 2) ^ 18 + (p + 2) ^ 4) / W (c i)) ∧
        d ∈ realDenominatorGrid m ∧
        ∀ b, (fun i j => (Q b i j : ℝ)) *ᵥ (v - u - d) = 0 := by
  let A := jointMatrix Q
  let q : ℝ := (p + 2) ^ 4
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_power_budget hp (by decide : 1 ≤ 4)
  have hAh : ∀ bi j, RationalHeightLE (A bi j) H := fun bi j => hQ bi.1 bi.2 j
  have hAb : ∀ bi j, c bi.2 ≠ c j → A bi j = 0 := fun bi j h => hblock bi.1 bi.2 j h
  have hDen : ((matrixDenominator A * l : ℕ) : ℝ) ≤ Real.exp q := by
    simpa only [Nat.mul_comm] using matrixDenominator_allowance_le_exp A l H hAh hp hrows hι hHp hlp
  obtain ⟨S, m, hm, hmp, hdm, _, hsplit⟩ := exists_controlled_weighted_linear_splitting
    (fun bi : Σ _ : η, ι => c bi.2) c A hAb hH
    (Nat.mul_pos (matrixDenominator_pos A) hl) hAh hq (hrows.trans hpq) (hι.trans hpq)
    (hHp.trans (Real.exp_le_exp.mpr hpq)) hDen
  refine ⟨m, hm, hmp, dvd_trans ⟨matrixDenominator A, Nat.mul_comm _ _⟩ hdm, ?_⟩
  intro W hW hWmin e r v he hr hres
  have hfac : ((Fintype.card ι : ℝ) + 1) * ((H : ℝ) + 1) ≤ Real.exp ((p + 2) ^ 2) := by
    apply le_trans _ (coordinateLipschitzBound_le_exp (Fintype.card ι) (Fintype.card ι)
      (H : ℝ≥0) hp hι hι hHp)
    change _ ≤ ((Fintype.card ι : ℝ) + Fintype.card ι + 1) * ((H : ℝ) + 1)
    gcongr
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hcost : (p + 2) ^ 2 + p ≤ q := by
    have hp2 : p ≤ (p + 2) ^ 2 := le_power_budget hp (by decide : 1 ≤ 2)
    calc
      _ ≤ 2 * (p + 2) ^ 2 := by linarith
      _ ≤ (p + 2) ^ 2 * (p + 2) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [sq_nonneg p]
      _ = q := by dsimp [q]; ring
  have hslow : ∀ bi, |jointMatrixImages Q e bi| ≤ Real.exp q / W (c bi.2) := by
    intro bi
    have h := weighted_matrix_mulVec_bound c c (fun i j => (Q bi.1 i j : ℝ))
      (fun i j hij => by rw [hblock bi.1 i j hij, Rat.cast_zero])
      (H : ℝ≥0) (fun i j => (hQ bi.1 i j).abs_real_le) W hW (Real.exp_nonneg p) (e bi.1) (he bi.1) bi.2
    apply h.trans
    apply div_le_div_of_nonneg_right _ (hW _).le
    calc
      _ ≤ Real.exp ((p + 2) ^ 2) * Real.exp p := mul_le_mul_of_nonneg_right hfac (Real.exp_nonneg p)
      _ = Real.exp ((p + 2) ^ 2 + p) := (Real.exp_add _ _).symm
      _ ≤ Real.exp q := Real.exp_le_exp.mpr hcost
  obtain ⟨_, _, hu, hd, hker⟩ := hsplit W hW (fun bi => hWmin bi.2)
    (jointMatrixImages Q e) (jointMatrixImages Q r) v hslow (jointMatrixImages_grid Q l r hr)
    (jointMatrixImages_equation Q e r v hres)
  refine ⟨(fun i j => (S i j : ℝ)) *ᵥ jointMatrixImages Q e,
    (fun i j => (S i j : ℝ)) *ᵥ jointMatrixImages Q r, hu, hd, ?_⟩
  intro b
  funext i
  exact congrFun hker ⟨b, i⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem exists_block_subspace_corrections
    {η ι κ δ L : Type*} [Fintype η] [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L]
    (b : Basis ι ℚ L) (c : ι → δ) (U : η → Submodule ℚ L) (v : η → κ → L)
    (hspan : ∀ j, Submodule.span ℚ (Set.range (v j)) = U j)
    (hU : ∀ j, BasisBlockInvariant b c (U j))
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ j z i, RationalHeightLE (b.repr (v j z) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : ((Fintype.card ι * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hrows : (Fintype.card (Σ _ : η, ι) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    let q := (p + 2) ^ 10
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (((q + 2) ^ 4 + 2) ^ 36) ∧ l ∣ m ∧
      ∀ (W : δ → ℝ), (∀ d, 0 < W d) →
      (∀ i, Real.exp (separationBudget ((q + 2) ^ 4)) ≤ W (c i)) →
      ∀ (e r : η → ℝ ⊗[ℚ] L) (x : ℝ ⊗[ℚ] L),
      (∀ j i, |(b.baseChange ℝ).equivFun (e j) i| ≤ Real.exp p / W (c i)) →
      (∀ j, (b.baseChange ℝ).equivFun (r j) ∈ realDenominatorGrid l) →
      (∀ j, x - e j - r j ∈ (U j).baseChange ℝ) →
      ∃ u d : ℝ ⊗[ℚ] L,
        (∀ i, |(b.baseChange ℝ).equivFun u i| ≤ Real.exp (((q + 2) ^ 4 + 2) ^ 18 + (q + 2) ^ 4) / W (c i)) ∧
        (b.baseChange ℝ).equivFun d ∈ realDenominatorGrid m ∧
        ∀ j, x - u - d ∈ (U j).baseChange ℝ := by
  classical
  let H' := imageDefiningHeight (Fintype.card ι * Fintype.card κ) (Fintype.card ι) H
  let q : ℝ := (p + 2) ^ 10
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_power_budget hp (by decide : 1 ≤ 10)
  have hH' : 1 ≤ H' := by
    have hk := rationalKernelHeight_pos (Fintype.card ι) hH
    have hHpos : 0 < H := hH
    have hpos : 0 < H' := by
      dsimp [H', imageDefiningHeight]
      positivity
    exact hpos
  have hH'p : (H' : ℝ) ≤ Real.exp q := imageDefiningHeight_le_exp _ _ _ hp hcols hι hHp
  choose Q hQ hQb hQker using fun j =>
    exists_block_subspace_defining_matrix b c (U j) (v j) (hspan j) (hU j) hH (hv j)
  obtain ⟨m, hm, hmp, hlm, hsolve⟩ := exists_joint_weighted_corrections c Q hQb hH' hl hQ hq
    (hι.trans hpq) (hrows.trans hpq) hH'p (hlp.trans (Real.exp_le_exp.mpr hpq))
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro W hW hWmin e r x he hr hres
  have he' : ∀ j i, |(b.baseChange ℝ).equivFun (e j) i| ≤ Real.exp q / W (c i) := by
    intro j i
    exact (he j i).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hpq) (hW _).le)
  have hsys : ∀ j, (fun i k => (Q j i k : ℝ)) *ᵥ
      ((b.baseChange ℝ).equivFun x - (b.baseChange ℝ).equivFun (e j) - (b.baseChange ℝ).equivFun (r j)) = 0 := by
    intro j
    simpa only [map_sub] using (hQker j (x - e j - r j)).mpr (hres j)
  obtain ⟨u, d, hu, hd, hker⟩ := hsolve W hW hWmin
    (fun j => (b.baseChange ℝ).equivFun (e j)) (fun j => (b.baseChange ℝ).equivFun (r j))
    ((b.baseChange ℝ).equivFun x) he' hr hsys
  refine ⟨(b.baseChange ℝ).equivFun.symm u, (b.baseChange ℝ).equivFun.symm d, ?_, ?_, ?_⟩
  · simpa only [LinearEquiv.apply_symm_apply] using hu
  · simpa only [LinearEquiv.apply_symm_apply] using hd
  · intro j
    apply (hQker j _).mp
    simpa only [map_sub, LinearEquiv.apply_symm_apply] using hker j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealCoordinateFunctionals
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {V I J : Type*} [AddCommGroup V] [Module ℚ V]

theorem realifyCoordinateMap_norm_bound [Fintype I] [Fintype J]
    (b : Basis I ℚ V) (ℓ : V →ₗ[ℚ] (J → ℚ)) {H : ℕ}
    (hℓ : ∀ j i, RationalHeightLE (ℓ (b i) j) H) (x : ℝ ⊗[ℚ] V) :
    ‖realifyCoordinateMap ℓ x‖ ≤
      ((Fintype.card I : ℝ) + 1) * (H + 1) * ‖(b.baseChange ℝ).equivFun x‖ := by
  rw [realifyCoordinateMap_eq_matrix b ℓ x]
  exact norm_matrix_mulVec_le _ (H : ℝ≥0) (fun j i => (hℓ j i).abs_real_le) _

theorem realifyCoordinateMap_grid [Fintype I] [Fintype J]
    (b : Basis I ℚ V) (ℓ : V →ₗ[ℚ] (J → ℚ)) (l : ℕ) (x : ℝ ⊗[ℚ] V)
    (hx : (b.baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    realifyCoordinateMap ℓ x ∈
      realDenominatorGrid (matrixDenominator (coordinateFunctionalMatrix b ℓ) * l) := by
  rw [realifyCoordinateMap_eq_matrix b ℓ x]
  exact real_matrix_denominator_grid (coordinateFunctionalMatrix b ℓ) l _ hx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedQuotientFunctional
namespace OAI

section

namespace Erdos3

open Module

theorem exists_bounded_quotient_functional
    {ι κ V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]
    (U I : Submodule ℚ V) (b : Basis ι ℚ (V ⧸ I))
    (v : κ → V) (hspan : Submodule.span ℚ (Set.range v) = U)
    (η : V →ₗ[ℚ] ℚ) (hann : U ⊓ I ≤ η.ker)
    {H K : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (b.repr (I.mkQ (v i)) j) H)
    (hη : ∀ i, RationalHeightLE (η (v i)) K) :
    ∃ ξ : (V ⧸ I) →ₗ[ℚ] ℚ, (∀ x ∈ U, ξ (I.mkQ x) = η x) ∧
      ∀ i, RationalHeightLE (ξ (b i))
        ((finrank ℚ (U.map I.mkQ) + 1) *
          (rationalSolveHeight (finrank ℚ (U.map I.mkQ)) H * K) ^
            finrank ℚ (U.map I.mkQ)) := by
  obtain ⟨η₀, hη₀⟩ := exists_quotient_functional_preserving_subspace U I η hann
  have hmem (i) : v i ∈ U := hspan ▸ Submodule.subset_span (Set.mem_range_self i)
  have hproject : Submodule.span ℚ (Set.range (I.mkQ ∘ v)) = U.map I.mkQ := by
    rw [Set.range_comp, ← Submodule.map_span, hspan]
  obtain ⟨ξ, hξ, hbound⟩ := exists_bounded_functional_preserving_subspace b
    (U.map I.mkQ) (I.mkQ ∘ v) hproject η₀ hH hv
    (fun i => by simpa only [Function.comp_apply, hη₀ (v i) (hmem i)] using hη i)
  refine ⟨ξ, ?_, hbound⟩
  intro x hx
  rw [hξ (I.mkQ x) (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)]
  exact hη₀ x hx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealSubspaceCoordinateRetraction
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {ι κ L M : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [AddCommGroup L] [Module ℚ L] [AddCommGroup M] [Module ℚ M]

theorem realified_linear_coordinate_norm (b : Basis ι ℚ L) (c : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) {H : ℕ}
    (hφ : ∀ i j, RationalHeightLE (LinearMap.toMatrix b c φ i j) H)
    (x : ℝ ⊗[ℚ] L) :
    ‖(c.baseChange ℝ).equivFun (φ.baseChange ℝ x)‖ ≤
      ((Fintype.card ι : ℝ) + 1) * (H + 1) * ‖(b.baseChange ℝ).equivFun x‖ := by
  rw [rational_coordinate_map (b.baseChange ℝ) (c.baseChange ℝ) (φ.baseChange ℝ)
    (LinearMap.toMatrix b c φ) (realified_linear_coordinate_matrix b c φ)]
  exact norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hφ i j).abs_real_le) _

theorem realified_section_correction_coordinate_norm [DecidableEq κ]
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    {H K : ℕ}
    (hφ : ∀ i j, RationalHeightLE (LinearMap.toMatrix b c φ i j) H)
    (hS : ∀ i j, RationalHeightLE (LinearMap.toMatrix c b S i j) K)
    (x : ℝ ⊗[ℚ] L) (y : ℝ ⊗[ℚ] M) :
    ‖(b.baseChange ℝ).equivFun (x - S.baseChange ℝ (φ.baseChange ℝ x - y))‖ ≤
      ‖(b.baseChange ℝ).equivFun x‖ +
        (((Fintype.card κ : ℝ) + 1) * (K + 1)) *
          ((((Fintype.card ι : ℝ) + 1) * (H + 1)) *
            ‖(b.baseChange ℝ).equivFun x‖ + ‖(c.baseChange ℝ).equivFun y‖) := by
  have hp := realified_linear_coordinate_norm b c φ hφ x
  have hs := realified_linear_coordinate_norm c b S hS (φ.baseChange ℝ x - y)
  have ht := norm_sub_le ((c.baseChange ℝ).equivFun (φ.baseChange ℝ x))
    ((c.baseChange ℝ).equivFun y)
  have hc := norm_sub_le ((b.baseChange ℝ).equivFun x)
    ((b.baseChange ℝ).equivFun (S.baseChange ℝ (φ.baseChange ℝ x - y)))
  rw [← map_sub] at ht hc
  have hdiff := ht.trans (add_le_add hp (le_refl ‖(c.baseChange ℝ).equivFun y‖))
  have hcorrect := hs.trans (mul_le_mul_of_nonneg_left hdiff
    (by positivity : 0 ≤ ((Fintype.card κ : ℝ) + 1) * (K + 1)))
  exact hc.trans (add_le_add (le_refl ‖(b.baseChange ℝ).equivFun x‖) hcorrect)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

section Modules

variable {σ ι κ L M : Type*} [AddCommGroup L] [Module ℚ L]
  [AddCommGroup M] [Module ℚ M]

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem sectionCorrectedPolynomial_denominator_bounds
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    {H K l : ℕ} (hφ : ∀ i j, RationalHeightLE (LinearMap.toMatrix b c φ i j) H)
    (hS : ∀ i j, RationalHeightLE (LinearMap.toMatrix c b S i j) K) (hl : 0 < l) :
    0 < matrixDenominator (LinearMap.toMatrix c b S) *
      matrixDenominator (LinearMap.toMatrix b c φ) * l ∧
    l ∣ matrixDenominator (LinearMap.toMatrix c b S) *
      matrixDenominator (LinearMap.toMatrix b c φ) * l ∧
    matrixDenominator (LinearMap.toMatrix c b S) *
      matrixDenominator (LinearMap.toMatrix b c φ) * l ≤
      K ^ (Fintype.card ι * Fintype.card κ) *
        H ^ (Fintype.card κ * Fintype.card ι) * l := by
  exact ⟨Nat.mul_pos (Nat.mul_pos (matrixDenominator_pos _) (matrixDenominator_pos _)) hl,
    dvd_mul_left _ _,
    Nat.mul_le_mul_right l (Nat.mul_le_mul (matrixDenominator_le _ hS)
      (matrixDenominator_le _ hφ))⟩

end Modules

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarDominatedSlack
namespace OAI

section

namespace Erdos3

theorem exists_weighted_exponential_constant_fiber {Ω β : Type*} [Fintype Ω]
    (outer : FiniteProbabilityWeights Ω) (S : Finset Ω) (hS : 0 < outer.mass S)
    (f : Ω → β) (A : Set β) (hA : A.Finite) (hf : ∀ x ∈ S, f x ∈ A)
    {C : ℝ} (hcount : (A.ncard : ℝ) ≤ Real.exp C) :
    ∃ y ∈ A, ∃ T : Finset Ω, T ⊆ S ∧ T.Nonempty ∧ (∀ x ∈ T, f x = y) ∧
      Real.exp (-C) * outer.mass S ≤ outer.mass T := by
  classical
  have hSne : S.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hS
  obtain ⟨x₀, hx₀⟩ := hSne
  let : Fintype A := hA.fintype
  let default : A := ⟨f x₀, hf x₀ hx₀⟩
  let : Nonempty A := ⟨default⟩
  let code : Ω → A := fun x => if hx : x ∈ S then ⟨f x, hf x hx⟩ else default
  obtain ⟨y, hy⟩ := outer.exists_code_fiber_mass S code
  let T := S.filter (fun x => code x = y)
  have hcard : (Fintype.card A : ℝ) ≤ Real.exp C := by
    simpa only [Set.fintypeCard_eq_ncard] using hcount
  have hcardpos : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hmass : Real.exp (-C) * outer.mass S ≤ outer.mass T := by
    calc
      _ = outer.mass S / Real.exp C := by
        rw [Real.exp_neg, div_eq_mul_inv, mul_comm]
      _ ≤ outer.mass S / Fintype.card A :=
        div_le_div_of_nonneg_left hS.le hcardpos hcard
      _ ≤ outer.mass T := by
        convert hy using 1
        apply congrArg outer.mass
        ext x
        simp only [T, Finset.mem_filter]
  have hTpos : 0 < outer.mass T := (mul_pos (Real.exp_pos _) hS).trans_le hmass
  have hTne : T.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hTpos
  refine ⟨y.val, y.property, T, Finset.filter_subset _ _, hTne, ?_, hmass⟩
  intro x hx
  have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
  have he := congrArg Subtype.val (Finset.mem_filter.mp hx).2
  simpa only [code, dif_pos hxS] using he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

namespace NormalizedScalarCubeSource

variable {I : Type*} [Fintype I] [DecidableEq I] (s : NormalizedScalarCubeSource I)

noncomputable def baseLaw : FiniteProbabilityWeights (IntegerScalarCubeBox I s.length) :=
  scalarCubeResidueWeights I s.length s.modulusBound s.length_pos s.modulus s.residue
    s.modulus_pos s.modulus_le s.size

end NormalizedScalarCubeSource

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RefilteredKernelConstantBounds
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

section Linear

variable {ι κ V L : Type*} [Fintype κ] [AddCommGroup V] [Module ℚ V]
  [AddCommGroup L] [Module ℚ L]

theorem integral_basis_image_denominatorGrid
    (b : Basis ι ℚ L) (bk : Basis κ ℚ V) (f : V →ₗ[ℚ] L)
    (q : ℕ) (hentries : ∀ j, (fun i => b.repr (f (bk j)) i) ∈ denominatorGrid q)
    (r : V) (hr : ∀ j, ∃ z : ℤ, bk.repr r j = z) :
    (fun i => b.repr (f r) i) ∈ denominatorGrid q := by
  classical
  choose z hz using hr
  choose a ha using hentries
  refine ⟨fun i => ∑ j, z j * a j i, ?_⟩
  intro i
  change (q : ℚ) * b.repr (f r) i = ((∑ j, z j * a j i : ℤ) : ℚ)
  conv_lhs => rw [← bk.sum_repr r]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : (q : ℚ) * b.repr (f (bk j)) i = (a j i : ℚ) := ha j i
  rw [hz, ← hj]
  ring

theorem exists_basis_image_bounds_of_height [Fintype ι]
    (b : Basis ι ℚ L) (bk : Basis κ ℚ V) (f : V →ₗ[ℚ] L)
    (H : ℕ) (hentries : ∀ i j, RationalHeightLE (b.repr (f (bk j)) i) H) :
    ∃ q : ℕ, 0 < q ∧ q ≤ H ^ (Fintype.card ι * Fintype.card κ) ∧
      (∀ i j, |(b.repr (f (bk j)) i : ℝ)| ≤ H) ∧
      ∀ j, (fun i => b.repr (f (bk j)) i) ∈ denominatorGrid q := by
  classical
  let A : Matrix ι κ ℚ := fun i j => b.repr (f (bk j)) i
  refine ⟨matrixDenominator A, matrixDenominator_pos A,
    matrixDenominator_le A hentries, fun i j => (hentries i j).abs_real_le, ?_⟩
  intro j
  refine ⟨fun i => clearedMatrix A i j, fun i => ?_⟩
  exact (congrFun (congrFun (clearedMatrix_cast A) i) j).symm

end Linear

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.LieKernelRealificationMark
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem mem_realificationLieKernel_iff (φ : L →ₗ⁅ℚ⁆ M) (x : ℝ ⊗[ℚ] L) :
    x ∈ (LinearMap.ker φ.toLinearMap).baseChange ℝ ↔ realificationLieHom φ x = 0 := by
  rw [real_baseChange_ker]
  rfl

namespace NilpotentLieBCHGroup

variable {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

theorem coord_mem_realificationKernel_iff (φ : L →ₗ⁅ℚ⁆ M)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) :
    g.coord ∈ (LinearMap.ker φ.toLinearMap).baseChange ℝ ↔
      realificationMap (hnil := hnil) (hM := hM) φ g = 1 := by
  rw [mem_realificationLieKernel_iff]
  constructor
  · intro h
    exact ext h
  · intro h
    exact congrArg coord h

end NilpotentLieBCHGroup
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearMapIntegralCover
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped Matrix TensorProduct

theorem linearMap_mem_scaledGrid {L M ι κ : Type*}
    [AddCommGroup L] [Module ℚ L] [AddCommGroup M] [Module ℚ M]
    [Fintype ι] [Fintype κ] [DecidableEq ι] (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) {a b : ℕ}
    (hab : b * matrixDenominator (LinearMap.toMatrix e f φ) ∣ a)
    {x : L} (hx : e.equivFun x ∈ scaledIntegerGrid a) :
    f.equivFun (φ x) ∈ scaledIntegerGrid b := by
  classical
  have h := matrix_mulVec_fine_grid (LinearMap.toMatrix e f φ) b
    (scaledIntegerGrid_subset_of_dvd hab hx)
  change LinearMap.toMatrix e f φ *ᵥ e.equivFun x ∈ scaledIntegerGrid b at h
  have hmap : LinearMap.toMatrix e f φ *ᵥ e.equivFun x = f.equivFun (φ x) := by
    simpa only [Basis.equivFun_apply] using LinearMap.toMatrix_mulVec_repr e f φ x
  rwa [hmap] at h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTagConstraintChartBasis
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

variable {m : ℕ} {J : Fin m → Type*}

theorem rationalTagChartMatrix_height
    (W : ∀ j, Submodule ℚ (J j → ℚ)) (n : Fin m → ℕ)
    (b : ∀ j, Basis (Fin (n j)) ℚ (W j)) {P : ℝ} (hP : 0 ≤ P)
    (hb : ∀ j a i, rationalLogHeight ((b j a : J j → ℚ) i) ≤ P) :
    ∀ a x, rationalLogHeight (rationalTagChartMatrix W n b a x) ≤ P := by
  rintro ⟨j, a⟩ ⟨k, i⟩
  by_cases h : k = j
  · subst k
    rw [rationalTagChartMatrix_same]
    exact hb j a i
  · rw [rationalTagChartMatrix_of_ne W n b ⟨j, a⟩ ⟨k, i⟩ h]
    simpa [rationalLogHeight] using hP

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedImageCorrections
namespace OAI

section

namespace Erdos3

open scoped Matrix NNReal

theorem exists_selected_image_corrections
    {η ι κ σ : Type*} [Fintype η] [Fintype ι] [Fintype κ]
    (A : Matrix η κ ℚ) (ρ : ι → η) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hη : (Fintype.card η : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ (S : Matrix κ ι ℚ) (m : ℕ), 0 < m ∧
      (m : ℝ) ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 36) ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (a b : ι → ℝ) (x : η → ℝ),
        x ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) →
        ‖a‖ ≤ Real.exp p / monomialScale T α → b ∈ realDenominatorGrid l →
        (∀ i, x (ρ i) = a i + b i) →
        let e := (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ a)
        let q := (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ b)
        e ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ∧
        q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ∧
        (∀ i, e (ρ i) = a i) ∧ (∀ i, q (ρ i) = b i) ∧
        ‖e‖ ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α ∧
        q ∈ realDenominatorGrid m ∧
        x - e - q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ∧
        ∀ i, (x - e - q) (ρ i) = 0 := by
  let C : Matrix ι κ ℚ := fun i j => A (ρ i) j
  obtain ⟨S, m, hm, hmp, hsolve⟩ := exists_controlled_linear_splitting C hH hl
    (fun i j => hA (ρ i) j) hp hι hκ hHp hlp T hT
  have hHp' : (H : ℝ) ≤ Real.exp ((p + 2) ^ 1) :=
    hHp.trans (Real.exp_le_exp.mpr (by simp))
  have hden : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) :=
    matrixDenominator_le_exp_power A hp 1 hη hκ
      (fun i j => (Nat.cast_le.mpr (hA i j).2).trans hHp')
  have hfac : ((Fintype.card κ : ℝ) + 1) * (H + 1) ≤ Real.exp ((p + 2) ^ 3) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power (Fintype.card κ) hp hκ 1 (by decide))
    exact mul_le_mul_of_nonneg_left (add_le_add hHp' le_rfl) (by positivity)
  have hnorm (y : κ → ℝ) :
      ‖(fun i j => (A i j : ℝ)) *ᵥ y‖ ≤ Real.exp ((p + 2) ^ 3) * ‖y‖ :=
    (norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hA i j).abs_real_le) y).trans
      (mul_le_mul_of_nonneg_right hfac (norm_nonneg y))
  refine ⟨S, matrixDenominator A * m, Nat.mul_pos (matrixDenominator_pos A) hm, ?_, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul hden hmp (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  · intro α hα a b x hx ha hb hselect e q
    obtain ⟨z, hz⟩ := hx
    have hC : (fun i j => (C i j : ℝ)) *ᵥ z = a + b := by
      funext i
      exact (congrFun hz (ρ i)).trans (hselect i)
    obtain ⟨hSa, hSb, hslow, hgrid, _⟩ := hsolve α hα a b z ha hb hC
    have he : e ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) :=
      ⟨(fun i j => (S i j : ℝ)) *ᵥ a, rfl⟩
    have hq : q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) :=
      ⟨(fun i j => (S i j : ℝ)) *ᵥ b, rfl⟩
    have heq (i : ι) : e (ρ i) = a i := congrFun hSa i
    have hqq (i : ι) : q (ρ i) = b i := congrFun hSb i
    refine ⟨he, hq, heq, hqq, ?_, real_matrix_denominator_grid A m _ hgrid,
      Submodule.sub_mem _ (Submodule.sub_mem _ ⟨z, hz⟩ he) hq, ?_⟩
    · calc
        ‖e‖ ≤ Real.exp ((p + 2) ^ 3) * ‖(fun i j => (S i j : ℝ)) *ᵥ a‖ := hnorm _
        _ ≤ Real.exp ((p + 2) ^ 3) *
            (Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) :=
          mul_le_mul_of_nonneg_left hslow (Real.exp_pos _).le
        _ = _ := by
          rw [← mul_div_assoc, ← Real.exp_add]
          congr 2
          ring
    · intro i
      change x (ρ i) - e (ρ i) - q (ρ i) = 0
      rw [hselect i, heq i, hqq i]
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorDetectedPotential
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem weightedPolynomialPotential_height (w : σ → ℕ) {d H : ℕ}
    (hd : 0 < d) (P : σ → MvPolynomial σ ℚ)
    (hweight : ∀ i, w i ≤ d) (hP : ∀ i, RationalPolynomialHeightLE (P i) H) :
    RationalPolynomialHeightLE (weightedPolynomialPotential w d P)
      ((Fintype.card σ + 1) * (d * H) ^ Fintype.card σ) := by
  classical
  intro m
  rw [weightedPolynomialPotential_coeff]
  apply rationalHeightLE_sum
  intro i
  have hw : RationalHeightLE ((w i : ℚ) / d) d := by
    simpa only [Int.cast_natCast, Int.natAbs_natCast] using
      rationalHeightLE_fraction (w i : ℤ) (d : ℤ)
        (by exact_mod_cast hd.ne') (by simpa using hweight i) (by simp)
  exact hw.mul (by simpa only [mul_comm] using (hP i).mul_X i m)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCandidateCommonFastGeometry
namespace OAI

section

namespace Erdos3
open Module
open scoped Matrix

variable {ι η V : Type*} [Fintype ι] [Fintype η]
  [AddCommGroup V] [Module ℚ V]

theorem exists_submodule_quotient_presentation_exp_height
    [DecidableEq ι] (b : Basis ι ℚ V) (U : Submodule ℚ V) (v : η → V)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hHpos : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (b.repr (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card η : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ D : Matrix (Fin d) ι ℚ, ∃ T : Matrix ι (Fin d) ℚ,
        LinearMap.ker D.mulVecLin = U.map b.equivFun.toLinearMap ∧ D * T = 1 ∧
        (∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
          ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 7)) ∧
        ∀ i j, ((T i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 45) ∧
          ((T i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 45) := by
  obtain ⟨d, hd, D, T, hker, hDT, hD, hT⟩ :=
    exists_quotient_presentation_exp_height (fun i j => b.repr (v j) i)
      hHpos hv hp hrows hcols hH
  exact ⟨d, hd, D, T, hker.trans (basis_generator_matrix_range b v U hspan), hDT, hD, hT⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

theorem allocatedPhysicalRootBudget_nonneg : 0 ≤ allocatedPhysicalRootBudget B U basis S c := by
  unfold allocatedPhysicalRootBudget
  positivity

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ScalarFunctionalCoefficientGrid
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]

theorem scalarFunctionalDenominator_le (b : Basis ι ℚ V) (θ : V →ₗ[ℚ] ℚ)
    {H : ℕ} (hθ : ∀ i, RationalHeightLE (θ (b i)) H) :
    matrixDenominator (fun (_ : Unit) i => θ (b i)) ≤ H ^ Fintype.card ι := by
  simpa using matrixDenominator_le (fun (_ : Unit) i => θ (b i)) (fun _ i => hθ i)

theorem realifyFunctional_denominator_grid (b : Basis ι ℚ V) (θ : V →ₗ[ℚ] ℚ)
    (m : ℕ) (x : ℝ ⊗[ℚ] V)
    (hx : (b.baseChange ℝ).equivFun x ∈ realDenominatorGrid m) :
    ∃ z : ℤ,
      ((matrixDenominator (fun (_ : Unit) i => θ (b i)) * m : ℕ) : ℝ) *
        realifyFunctional θ x = (z : ℝ) := by
  let ℓ : V →ₗ[ℚ] (Unit → ℚ) := LinearMap.pi (fun _ => θ)
  obtain ⟨z, hz⟩ := realifyCoordinateMap_grid b ℓ m x hx
  refine ⟨z (), ?_⟩
  exact (congrFun hz ()).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealTranslationEvaluationContinuity
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module
open scoped TensorProduct

theorem continuous_weightedSupportLE_eval {σ : Type*} [Fintype σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (n : ℕ) :
    let := moduleTopology ℝ (weightedSupportLE (R := ℝ) w n)
    Continuous fun z : weightedSupportLE (R := ℝ) w n × (σ → ℝ) =>
      eval z.2 z.1.val := by
  classical
  let W := weightedSupportLE (R := ℝ) w n
  let instTopoW : TopologicalSpace W := moduleTopology ℝ W
  let instFiniteW : Module.Finite ℝ W := weightedSupportLE_moduleFinite w hw n
  let b := Module.finBasis ℝ W
  have hb : Continuous fun z : W × (σ → ℝ) =>
      ∑ i, b.repr z.1 i * eval z.2 (b i).val := by
    apply continuous_finsetSum
    intro i _
    exact ((IsModuleTopology.continuous_of_linearMap
      ((Finsupp.lapply i).comp b.repr.toLinearMap)).comp continuous_fst).mul
      ((MvPolynomial.continuous_eval (b i).val).comp continuous_snd)
  convert hb using 1
  ext z
  have h := congrArg (fun Q : W => eval z.2 Q.val) (b.sum_repr z.1)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, map_sum, smul_eval,
    smul_eq_mul] using h.symm

theorem continuous_polynomialShearExp_eval {σ X : Type*} [Fintype σ]
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℝ X] [T2Space X] [FiniteDimensional ℝ X]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (D : X →ₗ[ℝ] PolynomialShearLieAlgebra w ℝ) (P : MvPolynomial σ ℝ) :
    Continuous fun z : X × (σ → ℝ) => eval z.2 (polynomialShearExp (D z.1) P) := by
  classical
  let n := P.weightedTotalDegree w
  let W := weightedSupportLE (R := ℝ) w n
  let instFiniteW : Module.Finite ℝ W := weightedSupportLE_moduleFinite w hw n
  let instTopoW : TopologicalSpace W := moduleTopology ℝ W
  let instTopAddW : IsTopologicalAddGroup W := IsModuleTopology.topologicalAddGroup ℝ W
  let p : W := ⟨P, (mem_weightedSupportLE_iff w n P).mpr le_rfl⟩
  let L : X →ₗ[ℝ] Module.End ℝ W :=
    { toFun := fun x => polynomialShearEnd (D x) n
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro Q
        apply Subtype.ext
        change (D (x + y)).val Q.val = _
        rw [map_add]
        rfl
      map_smul' := by
        intro c x
        apply LinearMap.ext
        intro Q
        apply Subtype.ext
        change (D (c • x)).val Q.val = _
        rw [map_smul]
        rfl }
  let instModuleTopoX : IsModuleTopology ℝ X := isModuleTopologyOfFiniteDimensional
  have hL : Continuous (fun z : X × W => L z.1 z.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left L
  have hpower (k : ℕ) : Continuous fun x : X => (L x ^ k) p := by
    induction k with
    | zero => simpa only [pow_zero, Module.End.one_apply] using
        (continuous_const : Continuous fun _ : X => p)
    | succ k ih =>
      simpa only [pow_succ', Module.End.mul_apply, Function.comp_def, id_eq] using
        hL.comp (continuous_id.prodMk ih)
  have hexp : Continuous fun x : X =>
      ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹) • (L x ^ k) p := by
    apply continuous_finsetSum
    intro k _
    exact (hpower k).const_smul ((k.factorial : ℝ)⁻¹)
  have heval := (continuous_weightedSupportLE_eval w hw n).comp
    ((hexp.comp continuous_fst).prodMk continuous_snd)
  convert heval using 1
  ext z
  rw [polynomialShearExp_eq_sum (D z.1) p.property]
  simp only [Function.comp_apply, Submodule.coe_sum, Submodule.coe_smul, map_sum, smul_eval]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show ((L z.1 ^ k) p : MvPolynomial σ ℝ) =
    ((D z.1).val.toLinearMap ^ k) P from polynomialShearEnd_pow_coe _ _ _ _]
  rw [← Rat.cast_smul_eq_qsmul ℝ]
  simp only [smul_eval, Rat.cast_inv, Rat.cast_natCast]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TranslationShearCoordinateSeries
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R]

theorem polynomialShearExpAut_neg_over {ι : Type*}
    (w : ι → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d)
    (D : PolynomialShearLieAlgebra w R) :
    polynomialShearExpAut (-D) = (polynomialShearExpAut D)⁻¹ := by
  exact (polynomialShearBCHEquivOver w d hw).map_inv
    (⟨D⟩ : (polynomialShearRatFiltration (R := R) w d hw).Group)

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem translationShear_derivation_rename_eq {w : σ ⊕ Unit → ℕ}
    (D : PolynomialShearLieAlgebra w R) (b : σ → R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i)) (P : MvPolynomial σ R) :
    D.val (rename Sum.inl P) = rename Sum.inl (translationBaseDerivative b P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, rename_X, Derivation.leibniz, smul_eq_mul,
      hb, translationBaseDerivative_X, map_add, rename_C, hP]

theorem translationShear_derivation_pow_extra {w : σ ⊕ Unit → ℕ}
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) (k : ℕ) :
    (D.val.toLinearMap ^ (k + 1)) (X (Sum.inr ())) =
      rename Sum.inl (((translationBaseDerivative b).toLinearMap ^ k) P) := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
    exact translationShear_derivation_rename_eq D b hb _

variable [Algebra ℚ R]

theorem polynomialShear_neg_pow_apply {ι : Type*} {w : ι → ℕ}
    (D : PolynomialShearLieAlgebra w R) (k : ℕ) (Q : MvPolynomial ι R) :
    ((-D).val.toLinearMap ^ k) Q =
      (-1 : ℚ) ^ k • (D.val.toLinearMap ^ k) Q := by
  have h : (-D).val.toLinearMap = (-1 : ℚ) • D.val.toLinearMap := by
    change -D.val.toLinearMap = (-1 : ℚ) • D.val.toLinearMap
    exact (neg_one_smul ℚ D.val.toLinearMap).symm
  rw [h, smul_pow, LinearMap.smul_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationLogCoordinatePolynomials
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped BigOperators TensorProduct

variable {U B κ : Type*} [Fintype B] [Fintype κ]

theorem shear_sum_apply {S I : Type*} [CommRing S] {w : I → ℕ}
    (D : κ → PolynomialShearLieAlgebra w S) (P : MvPolynomial I S) :
    (∑ k, D k).val P = ∑ k, (D k).val P := by
  classical
  have h (t : Finset κ) : (∑ k ∈ t, D k).val P = ∑ k ∈ t, (D k).val P := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert k t hk ih =>
      simp only [Finset.sum_insert hk]
      change (D k).val P + (∑ k ∈ t, D k).val P = _
      rw [ih]
  exact h Finset.univ

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.VectorPolynomialAffineSubspace
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {I K R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem coefficients_residueAffine_nonzero_mem {V : Type*}
    [AddCommGroup V] [Module ℝ V] (W : Submodule ℝ V)
    (q : ℕ) (r : I → ℤ) (P : VectorPolynomial I ℝ V)
    (hP : ∀ β, β ≠ 0 → coefficients P β ∈ W)
    (α : I →₀ ℕ) (hα : α ≠ 0) :
    coefficients (residueAffine q r P) α ∈ W :=
  coefficients_substitute_nonzero_mem W _ P hP α hα

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalTaggedConstraintHistory
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]
    {X R : Type*} [CommRing R]

 theorem lowTaggedRestrict_weightedHomogeneousComponent (k n : ℕ)
    (P : MvPolynomial (X ⊕ (Σ j, J j)) R) :
    lowTaggedRestrict J k (weightedHomogeneousComponent (fullTaggedVariableWeight J) n P) =
      weightedHomogeneousComponent (lowTaggedVariableWeight J k) n (lowTaggedRestrict J k P) :=
  aeval_weightedHomogeneousComponent _ _ _ (lowTaggedRestrictionVariables_isWeightedHomogeneous J k) n P

end Erdos3.VectorPolynomial

end

end OAI
end


