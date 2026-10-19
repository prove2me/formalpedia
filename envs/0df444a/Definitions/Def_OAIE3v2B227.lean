-- Prove2me | Definitions.Def_OAIE3v2B227
-- name    : OAIE3v2B227
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:26:05.884987+00:00
-- url     : https://prove2.me/theorems/9fbc3591-9131-4af5-98dc-ba88c71607c3
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 232 of 311
-- statement:
--   Definitions bundle 232 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B198`, `OAIE3v2B207`, `OAIE3v2B208` of this split.
--
--   Modules: `Estimates/ControlledDetectedTranslationBaseBounds.lean`, `Estimates/DetectedTranslationMajorBase.lean`, `Estimates/DetectedTranslationNormalizedLogBounds.lean`, `Estimates/RationalTaggedConstraintHistory.lean`, `Estimates/TranslationMajorCorrelationDecomposition.lean`, `Estimates/TranslationMajorCorrelationIdentity.lean`, `Estimates/VectorSubspaceCorrectionRepresentatives.lean`, `Geometry/BoundedCertifiedFullChartMajorIteration.lean`, `Geometry/CertifiedFullChartBudgetedTreeBounds.lean`, `Geometry/DetectedTranslationLogCoordinates.lean`, `Geometry/DetectedTranslationUniformCoordinateBounds.lean`, `Geometry/FullChartHomogeneousCorrection.lean`, `Geometry/FullTaggedChartCoefficientRange.lean`, `Geometry/TerminalChartSlowEvaluation.lean`, `Linear/DetectedTranslationLogProjectionHeight.lean`, `Linear/NativePairSymbolProjection.lean`, `Polynomial/BufferedSampledCurrentGradePhase.lean`, `Polynomial/DetectedTranslationBasePolynomialBounds.lean`, `Polynomial/DetectedTranslationPhaseDegree.lean`, `Polynomial/OrdinaryPhasePairFunctionalBounds.lean`, `Polynomial/OrdinaryPolynomialPhaseAffineInverse.lean`, `Sampling/DetectedTranslationMajorSamplingContainment.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B198
import Definitions.Def_OAIE3v2B207
import Definitions.Def_OAIE3v2B208

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativePairSymbolProjection
namespace OAI

universe sourceLevel

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold
variable {σ L : Type} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] {e : ℕ}
    (D : RationalFilteredNilmanifold L d e)

theorem pairTranslationProjection_coordinate_logHeight {p : ℝ}
    (x : PairAlgebra (weightedSubalgebra w d) L)
    (hx : ∀ j, rationalLogHeight
      ((pi (pairModels (weightedTranslationNilmanifold w d hw hwd) D)).basis.repr x j) ≤ p)
    (i : WeightedBasisIndex w d) :
    rationalLogHeight ((weightedBasis w d hw).repr (x true) i) ≤ p := by
  have h := productProjection_coordinate_logHeight
    (pairModels (weightedTranslationNilmanifold w d hw hwd) D) x hx true
    (weightedIndexOrder w d i)
  change rationalLogHeight ((weightedOrderedBasis w d hw).repr (x true)
    (weightedIndexOrder w d i)) ≤ p at h
  have he := weightedOrderedBasis_repr w d hw (x true) (weightedIndexOrder w d i)
  have he' : (weightedOrderedBasis w d hw).repr (x true) (weightedIndexOrder w d i) =
      (weightedBasis w d hw).repr (x true) i :=
    he.trans (congrArg ((weightedBasis w d hw).repr (x true)) ((weightedIndexOrder w d).symm_apply_apply i))
  exact he' ▸ h

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module VectorPolynomial
open scoped TensorProduct

variable {L M : Type sourceLevel} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e)
    {σ ι κ : Type*} (w : σ → ℕ)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ j, (pi (pairModels D E)).filtration.layer j =
      Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hG : ∀ j, D.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))

theorem pairOrbitSymbol_first_projection
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w) :
    realificationLieHom
      ((pi (pairModels D E)).filtration.filteredPolynomialSymbolMap D.filtration
        (liePiEval (R := ℚ) true) (pairFirstProjection_filtered D E) w)
      (pairOrbitSymbol D E p q b ω hF).coord =
        D.filtration.realSymbolOfPolynomial c ν hG w p.log := by
  have h := (pi (pairModels D E)).filtration.realFilteredPolynomialSymbolMap_polynomial
    D.filtration (liePiEval (R := ℚ) true) (pairFirstProjection_filtered D E)
    b ω hF c ν hG w ⟨(pairOrbit D E p q).log, (pairOrbit D E p q).property⟩
  change realificationLieHom
      ((pi (pairModels D E)).filtration.filteredPolynomialSymbolMap D.filtration
        (liePiEval (R := ℚ) true) (pairFirstProjection_filtered D E) w)
      (pairOrbitSymbol D E p q b ω hF).coord =
    D.filtration.realSymbolOfPolynomial c ν hG w
      (VectorPolynomial.map ((realificationLieHom (liePiEval (R := ℚ)
        (M := BoolLieFamily L M) true)).toLinearMap.restrictScalars ℚ) (pairOrbit D E p q).log) at h
  refine h.trans (congrArg (D.filtration.realSymbolOfPolynomial c ν hG w) ?_)
  exact pairOrbit_first_projection_log D E w p q

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledDetectedTranslationBaseBounds
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold

variable {B L : Type} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

 theorem pairResidueTranslationProjection_coordinate_logHeight {p : ℝ}
    (x : PairAlgebra (weightedSubalgebra w d) L)
    (hx : ∀ j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr x j) ≤ p)
    (i : WeightedBasisIndex w d) :
    rationalLogHeight ((weightedBasis w d hw).repr (x true) i) ≤ p := by
  have h := productProjection_coordinate_logHeight
    (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) x hx true
    (weightedIndexOrder w d i)
  change rationalLogHeight ((weightedOrderedBasis w d hw).repr (x true)
    (weightedIndexOrder w d i)) ≤ p at h
  have he := weightedOrderedBasis_repr w d hw (x true) (weightedIndexOrder w d i)
  have he' : (weightedOrderedBasis w d hw).repr (x true) (weightedIndexOrder w d i) =
      (weightedBasis w d hw).repr (x true) i :=
    he.trans (congrArg ((weightedBasis w d hw).repr (x true)) ((weightedIndexOrder w d).symm_apply_apply i))
  exact he' ▸ h

 theorem detectedTranslationBaseFunctional_basis_logHeight
    {ι : Type*} (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hF : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (i : B) (j : ι) :
    rationalLogHeight (detectedTranslationBaseFunctional w d hw hwd M hM D i
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hF j)) ≤ p := by
  rw [detectedTranslationBaseFunctional_basis_apply w d hw hwd M hM D b ω hF i j]
  split_ifs
  · have hh := pairResidueTranslationProjection_coordinate_logHeight w d hw hwd M hM D
      (b j) (hb j) (Sum.inl i)
    exact (weightedBasis_repr_inl w d hw (b j true) i) ▸ hh
  · simpa [rationalLogHeight] using hp

 theorem detectedTranslationBaseFunctional_basis_height
    {ι : Type*} (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hF : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (i : B) (j : ι) :
    RationalHeightLE (detectedTranslationBaseFunctional w d hw hwd M hM D i
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hF j))
      ⌈Real.exp p⌉₊ :=
  rationalHeightLE_ceil_exp
    (detectedTranslationBaseFunctional_basis_logHeight w d hw hwd M hM D b ω hF hp hb i j)

theorem detectedTranslationBaseFunctional_value_logHeight
    {ι : Type*} [Fintype ι]
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hF : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (x : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (hx : ∀ j, rationalLogHeight
      (((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hF).repr x j) ≤ p)
    (i : B) :
    rationalLogHeight (detectedTranslationBaseFunctional w d hw hwd M hM D i x) ≤ (p + 2)^4 :=
  rational_functional_value_logHeight _ _ hp hι
    (detectedTranslationBaseFunctional_basis_logHeight w d hw hwd M hM D b ω hF hp hb i) x hx

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open Module VectorPolynomial _root_.MvPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

variable {U B L ι : Type} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hLayers : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationBaseFunctional_pairOrbitSymbol
    (p : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1))
    (q : D.filtration.realification.PolynomialOrbit (fun _ : U => 1)) (i : B) :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
      b ω hLayers (fun _ : U => 1) (detectedTranslationBaseFunctional w d hw hwd M hM D i)
      (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
        p q b ω hLayers) =
      weightedHomogeneousComponent (fun _ : U => 1) (w i)
        (coordinate (((weightedBasis w d hw).baseChange ℝ).coord (Sum.inl i)).toAddMonoidHom p.log) := by
  let N := pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
  let G := weightedFiltration w d hwd
  let η := (LinearMap.proj i).comp (baseLinear.comp (weightedSubalgebra w d).subtype)
  have h := N.filtration.homogeneousProjected_scalar_coordinate G b ω hLayers
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw)
    (liePiEval (R := ℚ) true)
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
    (fun _ : U => 1) η
    (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
      p q b ω hLayers).coord
  change N.filtration.scalarSymbolPolynomial b ω hLayers (fun _ : U => 1)
      (detectedTranslationBaseFunctional w d hw hwd M hM D i)
      (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
        p q b ω hLayers) = _ at h
  have hp := pairOrbitSymbol_first_projection
    (weightedTranslationResidueNilmanifold w d hw hwd M hM) D (fun _ : U => 1)
    b ω hLayers (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) p q
  change realificationLieHom
    (N.filtration.filteredPolynomialSymbolMap G (liePiEval (R := ℚ) true)
      (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
      (fun _ : U => 1))
      (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
        p q b ω hLayers).coord =
    G.realSymbolOfPolynomial (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1) p.log at hp
  rw [hp] at h
  dsimp only [η] at h
  rw [realifyTranslationBaseFunctional_eq_coord w d hw] at h
  exact h.trans (G.realSymbolRepresentative_coordinate_top
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1) p.log (Sum.inl i))

theorem detectedTranslationBaseFunctional_majorOrbitSymbol
    (F : MvPolynomial (U ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (q : D.filtration.realification.PolynomialOrbit (fun _ : U => 1)) (i : B) :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
      b ω hLayers (fun _ : U => 1) (detectedTranslationBaseFunctional w d hw hwd M hM D i)
      (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
        (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) q b ω hLayers) =
      weightedHomogeneousComponent (fun _ : U => 1) (w i) (A i) := by
  rw [detectedTranslationBaseFunctional_pairOrbitSymbol w d hw hwd M hM D b ω hLayers,
    majorTranslationPolynomialOrbit_base_coordinate w d hw hwd F hF A hA]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial

variable {B L : Type} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    {ι : Type*} [Fintype ι]
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hF : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

 theorem detectedTranslationBase_slow_coefficients
    {σ : Type*} (u : σ → ℕ) (T : σ → ℝ) (hT : ∀ a, 0 < T a)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup u)
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hF u T (Real.exp p) E) (i : B) (α : σ →₀ ℕ) :
    |((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
        b ω hF u (detectedTranslationBaseFunctional w d hw hwd M hM D i) E).coeff α| ≤
      Real.exp ((p + 3)^3) / monomialScale T α := by
  have hcoeff := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial_slow_coefficients_of_height b ω hF u
    (detectedTranslationBaseFunctional w d hw hwd M hM D i) T hT (Real.exp_pos p).le
    (detectedTranslationBaseFunctional_basis_height w d hw hwd M hM D b ω hF hp hb i) E hE α
  exact le_trans hcoeff
    (div_le_div_of_nonneg_right
      (detectedTranslationCoordinate_slow_factor_le_exp (Fintype.card ι) hp hι)
      (monomialScale_pos T hT α).le)

 theorem detectedTranslationBase_exists_common_coefficient_grid
    {σ : Type*} (u : σ → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hB : (Fintype.card B : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp p)
    (Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup u)
    (hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hF u m Q) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp ((p + 3)^3) ∧
      ∀ i, realPolynomialCoefficientGrid q
        ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
          b ω hF u (detectedTranslationBaseFunctional w d hw hwd M hM D i) Q) := by
  let F := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
  obtain ⟨q, hq, hqbound, hgrid⟩ := F.scalarSymbolPolynomial_family_exists_coefficient_grid
    b ω hF u (detectedTranslationBaseFunctional w d hw hwd M hM D)
    (detectedTranslationBaseFunctional_basis_height w d hw hwd M hM D b ω hF hp hb)
    m hm Q hQ
  exact ⟨q, hq,
    detectedTranslationCoordinate_denominator_le_exp (Fintype.card B) (Fintype.card ι) m q
      hp hB hι hmp hqbound, hgrid⟩

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DetectedTranslationBasePolynomialBounds
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial

variable {B L : Type} {σ ι : Type*} [Fintype B] [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)

include hp hι hb

 theorem detectedTranslationBasePolynomial_slow_coefficients
    (T : σ → ℝ) (hT : ∀ a, 0 < T a)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound b ω hN (fun _ => 1) T (Real.exp p) E) :
    ∀ α i, |coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN E) α i| ≤
      Real.exp ((p + 3)^3) / monomialScale T α := by
  intro α i
  rw [detectedTranslationBasePolynomial_coefficients_apply]
  exact detectedTranslationBase_slow_coefficients w d hw hwd M hM D b ω hN
    (fun _ => 1) T hT hp hι hb E hE i α

 theorem detectedTranslationBasePolynomial_exists_coefficient_grid
    (hB : (Fintype.card B : ℝ) ≤ p)
    (m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp p)
    (Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid b ω hN (fun _ => 1) m Q) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp ((p + 3)^3) ∧
      ∀ α, coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN Q) α ∈
        realDenominatorGrid q := by
  obtain ⟨q, hq, hqb, hgrid⟩ := detectedTranslationBase_exists_common_coefficient_grid
    w d hw hwd M hM D b ω hN (fun _ => 1) hp hB hι hb m hm hmp Q hQ
  refine ⟨q, hq, hqb, ?_⟩
  exact coefficients_ofCoordinates_mem_realDenominatorGrid _ q hgrid

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DetectedTranslationMajorBase
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {B L σ ι : Type} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

 theorem detectedTranslationBasePolynomial_majorOrbitSymbol
    (F : MvPolynomial (σ ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) d)
    (A : B → MvPolynomial σ ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (q : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1)) :
    detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN
      (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
        (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) q b ω hN) =
      ofCoordinates (R := ℝ) (Pi.basisFun ℝ B)
        (fun i => weightedHomogeneousComponent (fun _ : σ => 1) (w i) (A i)) := by
  apply (coordinatesEquiv (R := ℝ) (Pi.basisFun ℝ B)).injective
  funext i
  change coordinate ((Pi.basisFun ℝ B).coord i).toAddMonoidHom _ =
    coordinate ((Pi.basisFun ℝ B).coord i).toAddMonoidHom
      (ofCoordinates (R := ℝ) (Pi.basisFun ℝ B)
        (fun j => weightedHomogeneousComponent (fun _ : σ => 1) (w j) (A j)))
  rw [coordinate_ofCoordinates]
  exact (detectedTranslationBasePolynomial_coordinate w d hw hwd M hM D b ω hN _ i).trans
    (detectedTranslationBaseFunctional_majorOrbitSymbol w d hw hwd M hM D b ω hN F hF A hA q i)

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.DetectedTranslationMajorSamplingContainment
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial
open scoped Matrix

variable {B L : Type} {σ ι J : Type*} [Fintype B] [Fintype ι] [Fintype J]
    [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslation_samplingRank_le_base_span
    (hd : 1 ≤ d) {p : ℝ} (hp : 0 ≤ p)
    (hB : (Fintype.card B : ℝ) ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (W : LieSubalgebra ℚ
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (v : J → (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (hvheight : ∀ j i, rationalLogHeight
      (((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hN).repr (v j) i) ≤ p)
    (E P Q X : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hprod : E * P * Q = X)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : σ => 1) T (Real.exp p) E)
    (hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra
        b ω hN (fun _ : σ => 1) W))
    (m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp p)
    (hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : σ => 1) m Q)
    (h : ℕ) (R : ℝ) (retained : Submodule ℝ (B → ℝ))
    (hrank : HasLayerSamplingRank h T R retained
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN X))
    (hgridR : Real.exp ((p + 3)^3) ≤ R)
    (hrowR : (realSpanIntegerRowBound (Fintype.card J) (Fintype.card B)
      ⌈Real.exp ((p + 2)^4)⌉₊ : ℝ) ≤ R)
    (hcost : (Fintype.card B : ℝ) *
      (realSpanIntegerRowBound (Fintype.card J) (Fintype.card B)
        ⌈Real.exp ((p + 2)^4)⌉₊ : ℝ) * Real.exp ((p + 3)^3) ≤ R) :
    retained ≤ Submodule.span ℝ (Set.range (fun j i =>
      (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ))) := by
  let H : ℕ := ⌈Real.exp ((p + 2)^4)⌉₊
  let A : Matrix B J ℚ := fun i j => detectedTranslationBaseMap w d hw hwd M hM D (v j) i
  have hA : ∀ i j, RationalHeightLE (A i j) H := by
    intro i j
    exact rationalHeightLE_ceil_exp
      (detectedTranslationBaseFunctional_value_logHeight w d hw hwd M hM D
        b ω hN hp hι hb (v j) (hvheight j) i)
  obtain ⟨q, hq, hqbound, hgrid⟩ :=
    detectedTranslationBasePolynomial_exists_coefficient_grid w d hw hwd M hM D
      b ω hN hp hι hb hB m hm hmp Q hQ
  apply samplingRank_le_real_column_span_of_decomposition A (one_le_ceil_exp _) hA
    h T R (Real.exp ((p + 3)^3)) retained
    (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN X)
    (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN E)
    (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN P)
    (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN Q)
    q hq hT hrank
    (detectedTranslationBasePolynomial_factorization w d hw hwd M hM D b ω hN hd E P Q X hprod)
    (detectedTranslationBasePolynomial_slow_coefficients w d hw hwd M hM D b ω hN hp hι hb T hT E hE)
    (detectedTranslationBasePolynomial_fast_coefficients_mem_span w d hw hwd M hM D b ω hN W v hv P hP)
    hgrid (hqbound.trans hgridR) hrowR hcost

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslationMajorCorrelationIdentity
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ L : Type} {U ι : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M) {e : ℕ}
    (D : RationalFilteredNilmanifold L d e)

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationSymbolProjection_pairOrbitSymbol
    (p : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1))
    (q : D.filtration.realification.PolynomialOrbit (fun _ : U => 1)) :
    detectedTranslationSymbolProjection w d hw hwd M hM D
      (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D p q b ω hN) = translationPolynomialSymbolHom w d hw hwd p := by
  apply NilpotentLieBCHGroup.ext
  rw [detectedTranslationSymbolProjection_coord, translationPolynomialSymbolHom_coord]
  exact pairOrbitSymbol_first_projection (weightedTranslationResidueNilmanifold w d hw hwd M hM) D (fun _ : U => 1) b ω hN
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) p q

theorem detectedTranslationSymbolLift_pairOrbitSymbol
    (p : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1))
    (q : D.filtration.realification.PolynomialOrbit (fun _ : U => 1)) :
    detectedTranslationSymbolLift w d hw hwd M hM D (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D p q b ω hN) =
      translationPolynomialSymbolLift w d hw hwd (translationPolynomialSymbolHom w d hw hwd p) := by
  rw [detectedTranslationSymbolLift_apply,
    detectedTranslationSymbolProjection_pairOrbitSymbol w d hw hwd M hM D b ω hN]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationGroupEval_major_factorization
    (F : MvPolynomial (U ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (partner : D.filtration.realification.PolynomialOrbit (fun _ : U => 1))
    (E P Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hprod : E * P * Q = pairOrbitSymbol
      (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
      (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) partner b ω hN)
    (u : U → ℝ) :
    algebraicMajorSymbol
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d F)
      (specializeMajorParameters (RingHom.id ℝ)
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d F) 0)
      (majorTranslationTopCoordinates w A) u =
        detectedTranslationGroupEval w d hw hwd M hM D u E *
          detectedTranslationGroupEval w d hw hwd M hM D u P *
            detectedTranslationGroupEval w d hw hwd M hM D u Q := by
  rw [← majorTranslationPolynomialOrbit_degree_symbolLift_realEval w d hw hwd F hF A hA u,
    ← detectedTranslationSymbolLift_pairOrbitSymbol w d hw hwd M hM D b ω hN
      (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) partner,
    ← hprod]
  exact (detectedTranslationGroupEval w d hw hwd M hM D u).map_mul (E * P) Q |>.trans
    (congrArg (· * detectedTranslationGroupEval w d hw hwd M hM D u Q)
      ((detectedTranslationGroupEval w d hw hwd M hM D u).map_mul E P))

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationSymbolLift_base_coordinate
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) (i : B) :
    coordinate (((weightedBasis w d hw).baseChange ℝ).coord (Sum.inl i)).toAddMonoidHom
      (detectedTranslationSymbolLift w d hw hwd M hM D P).log =
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
      b ω hN (fun _ : U => 1) (detectedTranslationBaseFunctional w d hw hwd M hM D i) P := by
  rw [detectedTranslationSymbolLift_log]
  let N := pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
  let η := (LinearMap.proj i).comp (baseLinear.comp (weightedSubalgebra w d).subtype)
  have h := N.filtration.homogeneousProjected_scalar_coordinate
    (weightedFiltration w d hwd) b ω hN
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw)
    (liePiEval (R := ℚ) true)
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
    (fun _ : U => 1) η P.coord
  change N.filtration.scalarSymbolPolynomial b ω hN (fun _ : U => 1)
    (detectedTranslationBaseFunctional w d hw hwd M hM D i) P = _ at h
  dsimp only [η] at h
  rw [realifyTranslationBaseFunctional_eq_coord w d hw] at h
  convert h.symm using 1

theorem detectedTranslationGroupEval_base
    (u : U → ℝ)
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (detectedTranslationGroupEval w d hw hwd M hM D u P).base =
      eval₂ u (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN P) := by
  funext i
  change (bchRealTranslationHom w d hwd
    ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval (fun _ : U => 1) u
      (detectedTranslationSymbolLift w d hw hwd M hM D P))).base i = _
  rw [bchRealTranslationHom_base_coordinate w d hw hwd]
  change ((weightedBasis w d hw).baseChange ℝ).coord (Sum.inl i)
      (eval₂ u (detectedTranslationSymbolLift w d hw hwd M hM D P).log) =
    (LinearMap.proj i : (B → ℝ) →ₗ[ℝ] ℝ)
      (eval₂ u (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN P))
  rw [coordinate_eval₂, coordinate_eval₂,
    detectedTranslationSymbolLift_base_coordinate w d hw hwd M hM D b ω hN,
    detectedTranslationBasePolynomial_coordinate w d hw hwd M hM D b ω hN]

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DetectedTranslationLogCoordinates
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators TensorProduct

variable {U B κ : Type*} [Fintype B] [Fintype κ]

theorem nativeTranslationGroupPolynomial_specialize (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (b : Basis κ ℚ (weightedSubalgebra w d))
    (p : VectorPolynomial U ℚ (ℝ ⊗[ℚ] weightedSubalgebra w d)) (u : U → ℝ) :
    PolynomialTranslationGroupOver.map (eval u) (nativeTranslationGroupPolynomial w d b p) =
      bchRealTranslationHom w d hwd ⟨VectorPolynomial.eval₂ u p⟩ := by
  rw [nativeTranslationGroupPolynomial, translationLogGroupPolynomial_specialize,
    ← nativeTranslationLogCoordinate_eval]

theorem nativeTranslationGroupPolynomial_orbit (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (b : Basis κ ℚ (weightedSubalgebra w d))
    (v : U → ℕ) (g : (weightedFiltration w d hwd).realification.PolynomialOrbit v)
    (u : U → ℝ) :
    PolynomialTranslationGroupOver.map (eval u) (nativeTranslationGroupPolynomial w d b g.log) =
      bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval v u g) :=
  nativeTranslationGroupPolynomial_specialize w d hwd b g.log u

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct BigOperators

namespace PolynomialTranslationLie

open RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationLogCoordinate_eq_scalar
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (k : WeightedBasisIndex w d) :
    detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k =
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
        b ω hN (fun _ : U => 1) (detectedTranslationLogFunctional w d hw hwd M hM D k) E := by
  rw [detectedTranslationLogCoordinatePolynomial, detectedTranslationSymbolLift_log]
  have h := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.homogeneousProjected_scalar_coordinate
    (weightedFiltration w d hwd) b ω hN
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw)
    (liePiEval (R := ℚ) true)
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
    (fun _ : U => 1) ((weightedBasis w d hw).coord k) E.coord
  rw [realifyFunctional_basis_coord] at h
  change (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
    b ω hN (fun _ : U => 1) (detectedTranslationLogFunctional w d hw hwd M hM D k) E = _ at h
  convert h.symm using 1

theorem detectedTranslationLogFunctional_basis (k : WeightedBasisIndex w d) (i : ι) :
    detectedTranslationLogFunctional w d hw hwd M hM D k
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hN i) =
      detectedTranslationLogProjectionMatrix w d hw b ω k i := by
  exact (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.homogeneousGradedProjection_basis_repr
    (weightedFiltration w d hwd) (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (weightedBasis_homogeneous_brackets w d hw)
    (liePiEval (R := ℚ) true)
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
    b ω hN i k

theorem detectedTranslationLogCoordinate_slow_coefficients [Fintype ι]
    (T : U → ℝ) (hT : ∀ i, 0 < T i) {A H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (k : WeightedBasisIndex w d)
    (hproj : ∀ i, |(detectedTranslationLogProjectionMatrix w d hw b ω k i : ℝ)| ≤ H)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : U => 1) T A E) (α : U →₀ ℕ) :
    |(detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k).coeff α| ≤
      (Fintype.card ι : ℝ) * H * A / monomialScale T α := by
  rw [detectedTranslationLogCoordinate_eq_scalar w d hw hwd M hM D b ω hN]
  apply NilpotentLieFiltration.scalarSymbolPolynomial_slow_coefficients
    _ b ω hN _ _ T hT hA hH _ E hE α
  intro i
  simpa only [detectedTranslationLogFunctional_basis w d hw hwd M hM D b ω hN] using hproj i

theorem detectedTranslationLogCoordinate_joint_grid [Fintype ι]
    (m : ℕ)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : U => 1) m E) :
    (fun z : (U →₀ ℕ) × WeightedBasisIndex w d =>
      (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E z.2).coeff z.1)
        ∈ realDenominatorGrid (matrixDenominator (detectedTranslationLogProjectionMatrix w d hw b ω) * m) := by
  have h := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial_joint_grid
    b ω hN (fun _ : U => 1) (detectedTranslationLogFunctional w d hw hwd M hM D) m E hE
  simpa only [detectedTranslationLogFunctional_basis w d hw hwd M hM D b ω hN,
    ← detectedTranslationLogCoordinate_eq_scalar w d hw hwd M hM D b ω hN] using h

theorem detectedTranslationLogCoordinate_common_coefficient_grid [Fintype ι]
    (m : ℕ)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : U => 1) m E) (k : WeightedBasisIndex w d) :
    realPolynomialCoefficientGrid
      (matrixDenominator (detectedTranslationLogProjectionMatrix w d hw b ω) * m)
      (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k) := by
  obtain ⟨a, ha⟩ := detectedTranslationLogCoordinate_joint_grid w d hw hwd M hM D b ω hN m E hE
  refine ⟨fun α => a (α, k), ?_⟩
  funext α
  exact congrFun ha (α, k)

theorem exists_detectedTranslationLogCoordinate_common_grid [Fintype ι]
    {H : ℕ}
    (hproj : ∀ k i, RationalHeightLE (detectedTranslationLogProjectionMatrix w d hw b ω k i) H)
    (m : ℕ) (hm : 0 < m) :
    ∃ q : ℕ, 0 < q ∧
      q ≤ H ^ (Fintype.card (WeightedBasisIndex w d) * Fintype.card ι) * m ∧
      ∀ E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1),
        (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
          b ω hN (fun _ : U => 1) m E →
        ∀ k, realPolynomialCoefficientGrid q
          (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k) := by
  refine ⟨matrixDenominator (detectedTranslationLogProjectionMatrix w d hw b ω) * m,
    Nat.mul_pos (matrixDenominator_pos _) hm,
    Nat.mul_le_mul_right m (matrixDenominator_le _ hproj), ?_⟩
  intro E hE k
  exact detectedTranslationLogCoordinate_common_coefficient_grid w d hw hwd M hM D b ω hN m E hE k

end PolynomialTranslationLie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DetectedTranslationNormalizedLogBounds
namespace OAI

section

namespace Erdos3

namespace PolynomialTranslationLie

open Module VectorPolynomial RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

theorem detectedTranslationLogCoordinate_normalized_mass [Fintype U] [Fintype ι]
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (T : U → ℝ) (hT : ∀ i, 0 < T i) {A H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (k : WeightedBasisIndex w d)
    (hproj : ∀ i, |(detectedTranslationLogProjectionMatrix w d hw b ω k i : ℝ)| ≤ H)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : U => 1) T A E) :
    realPolynomialMass (scaleMvPolynomialAxes T
      (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k)) ≤
        ((Fintype.card U : ℝ) + 1) ^ d * ((Fintype.card ι : ℝ) * H * A) := by
  apply scaleMvPolynomialAxes_mass_le_of_totalDegree T hT _
    (detectedTranslationLogCoordinate_totalDegree w d hw hwd M hM D E k)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hH) hA)
  exact detectedTranslationLogCoordinate_slow_coefficients w d hw hwd M hM D b ω hN
    T hT hA hH k hproj E hE

end PolynomialTranslationLie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DetectedTranslationLogProjectionHeight
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)

theorem detectedTranslationLogProjectionMatrix_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (k : WeightedBasisIndex w d) (i : ι) :
    rationalLogHeight (detectedTranslationLogProjectionMatrix w d hw b ω k i) ≤ p := by
  unfold detectedTranslationLogProjectionMatrix
  split_ifs
  · exact pairResidueTranslationProjection_coordinate_logHeight w d hw hwd M hM D
      (b i) (hb i) k
  · simpa [rationalLogHeight] using hp

theorem detectedTranslationLogProjectionMatrix_height_of_basis {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (k : WeightedBasisIndex w d) (i : ι) :
    RationalHeightLE (detectedTranslationLogProjectionMatrix w d hw b ω k i) ⌈Real.exp p⌉₊ :=
  rationalHeightLE_ceil_exp
    (detectedTranslationLogProjectionMatrix_logHeight w d hw hwd M hM D b ω hp hb k i)

variable (hN : ∀ j,
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
      Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem exists_detectedTranslationLogCoordinate_grid_of_basis_height [Fintype ι]
    {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (m : ℕ) (hm : 0 < m) :
    ∃ q : ℕ, 0 < q ∧
      q ≤ ⌈Real.exp p⌉₊ ^ (Fintype.card (WeightedBasisIndex w d) * Fintype.card ι) * m ∧
      ∀ E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1),
        (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
          b ω hN (fun _ : U => 1) m E →
        ∀ k, realPolynomialCoefficientGrid q
          (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k) :=
  exists_detectedTranslationLogCoordinate_common_grid w d hw hwd M hM D b ω hN
    (detectedTranslationLogProjectionMatrix_height_of_basis w d hw hwd M hM D b ω hp hb) m hm

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DetectedTranslationPhaseDegree
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold

variable {B L : Type} {U : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

noncomputable def detectedTranslationGroupPolynomial
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    PolynomialTranslationGroupOver (MvPolynomial U ℝ) B :=
  nativeTranslationGroupPolynomial w d (weightedBasis w d hw)
    (detectedTranslationSymbolLift w d hw hwd M hM D E).log

noncomputable def detectedTranslationBaseCoordinatePolynomial
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (i : B) : MvPolynomial U ℝ :=
  (detectedTranslationGroupPolynomial w d hw hwd M hM D E).base i

noncomputable def detectedTranslationPhasePolynomial
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    MvPolynomial (U ⊕ B) ℝ :=
  packTranslationPolynomial
    (detectedTranslationGroupPolynomial w d hw hwd M hM D E).polynomial

theorem detectedTranslationPhasePolynomial_eq_logMixed
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    detectedTranslationPhasePolynomial w d hw hwd M hM D E =
      translationLogMixedGroupPolynomial w d (weightedBasis w d hw)
        (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E) := rfl

theorem detectedTranslationGroupPolynomial_specialize
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (u : U → ℝ) :
    PolynomialTranslationGroupOver.map (eval u)
        (detectedTranslationGroupPolynomial w d hw hwd M hM D E) =
      detectedTranslationGroupEval w d hw hwd M hM D u E :=
  nativeTranslationGroupPolynomial_orbit w d hwd (weightedBasis w d hw)
    (fun _ : U => 1) (detectedTranslationSymbolLift w d hw hwd M hM D E) u

theorem detectedTranslationBaseCoordinatePolynomial_eval
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (u : U → ℝ) (i : B) :
    eval u (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i) =
      (detectedTranslationGroupEval w d hw hwd M hM D u E).base i :=
  congrArg (fun g => g.base i)
    (detectedTranslationGroupPolynomial_specialize w d hw hwd M hM D E u)

theorem detectedTranslationBaseCoordinatePolynomial_eq_logCoordinate
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (i : B) :
    detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i =
      nativeTranslationLogCoordinate w d (weightedBasis w d hw)
        (detectedTranslationSymbolLift w d hw hwd M hM D E).log (Sum.inl i) := by
  apply MvPolynomial.funext
  intro u
  rw [detectedTranslationBaseCoordinatePolynomial_eval]
  change (bchRealTranslationHom w d hwd
    ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval (fun _ : U => 1) u
      (detectedTranslationSymbolLift w d hw hwd M hM D E))).base i = _
  rw [bchRealTranslationHom_base_coordinate w d hw hwd]
  exact VectorPolynomial.coordinate_eval₂
    (((weightedBasis w d hw).baseChange ℝ).coord (Sum.inl i)) u _

theorem detectedTranslationPhasePolynomial_eval
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (u : U → ℝ) (a : B → ℝ) :
    eval (Sum.elim u a) (detectedTranslationPhasePolynomial w d hw hwd M hM D E) =
      eval a (detectedTranslationGroupEval w d hw hwd M hM D u E).polynomial := by
  rw [detectedTranslationPhasePolynomial, packTranslationPolynomial_eval]
  exact congrArg (fun g => eval a g.polynomial)
    (detectedTranslationGroupPolynomial_specialize w d hw hwd M hM D E u)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold
variable {B L : Type} {U : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

theorem detectedTranslationPhasePolynomial_normalized_mass
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ k, realPolynomialMass (scaleMvPolynomialAxes H
      (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k)) ≤ A) :
    realPolynomialMass (scaleMvPolynomialAxes (Sum.elim H (fun _ : B => 1))
      (detectedTranslationPhasePolynomial w d hw hwd M hM D E)) ≤
      ((d : ℝ) + 1) * ((Fintype.card (WeightedBasisIndex w d) : ℝ) * A) *
        (1 + (Fintype.card B : ℝ) * d * ((Fintype.card (WeightedBasisIndex w d) : ℝ) * A)) ^ d := by
  have h := realPolynomialMass_translationLogMixedGroupPolynomial_scale w d hw hwd
    (weightedBasis w d hw) (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E) H hA (by norm_num : (0 : ℝ) ≤ 1)
    hf (weightedBasis_base_abs_le_one w d hw) (weightedBasis_polynomial_mass_le_one w d hw)
  rw [detectedTranslationPhasePolynomial_eq_logMixed]
  simpa only [mul_one] using h

theorem detectedTranslationPhasePolynomial_coefficientGrid
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    {q : ℕ} (hf : ∀ k, realPolynomialCoefficientGrid q
      (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k)) :
    realPolynomialCoefficientGrid (d.factorial * q ^ (d + 1))
      (detectedTranslationPhasePolynomial w d hw hwd M hM D E) := by
  have hbase (k : WeightedBasisIndex w d) (i : B) :
      ∃ z : ℤ, (z : ℝ) = ((1 : ℕ) : ℝ) * ((weightedBasis w d hw k).val.base i : ℝ) := by
    obtain ⟨z, hz⟩ := weightedBasis_base_integer w d hw k i
    refine ⟨z, ?_⟩
    simp only [Nat.cast_one, one_mul]
    exact_mod_cast hz
  have h := translationLogMixedGroupPolynomial_coefficientGrid_of_inputs w d hwd
    (weightedBasis w d hw) (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E)
    hf hbase (weightedBasis_polynomial_real_grid w d hw)
  rw [detectedTranslationPhasePolynomial_eq_logMixed]
  simpa only [mul_one] using h

variable {ι : Type*} [Fintype ι]
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationPhasePolynomial_mass_of_slow [Fintype U]
    (T : U → ℝ) (hT : ∀ i, 0 < T i) {A H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hproj : ∀ k i, |(detectedTranslationLogProjectionMatrix w d hw b ω k i : ℝ)| ≤ H)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : U => 1) T A E) :
    let Z := ((Fintype.card U : ℝ) + 1) ^ d * ((Fintype.card ι : ℝ) * H * A)
    realPolynomialMass (scaleMvPolynomialAxes (Sum.elim T (fun _ : B => 1))
      (detectedTranslationPhasePolynomial w d hw hwd M hM D E)) ≤
      ((d : ℝ) + 1) * ((Fintype.card (WeightedBasisIndex w d) : ℝ) * Z) *
        (1 + (Fintype.card B : ℝ) * d * ((Fintype.card (WeightedBasisIndex w d) : ℝ) * Z)) ^ d := by
  dsimp only
  apply detectedTranslationPhasePolynomial_normalized_mass w d hw hwd M hM D E T (by positivity)
  intro k
  exact detectedTranslationLogCoordinate_normalized_mass w d hw hwd M hM D b ω hN
    T hT hA hH k (hproj k) E hE

theorem detectedTranslationBaseCoordinatePolynomial_mass_of_slow [Fintype U]
    (T : U → ℝ) (hT : ∀ i, 0 < T i) {A H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hproj : ∀ k i, |(detectedTranslationLogProjectionMatrix w d hw b ω k i : ℝ)| ≤ H)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : U => 1) T A E) (i : B) :
    realPolynomialMass (scaleMvPolynomialAxes T
      (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i)) ≤
      ((Fintype.card U : ℝ) + 1) ^ d * ((Fintype.card ι : ℝ) * H * A) := by
  rw [detectedTranslationBaseCoordinatePolynomial_eq_logCoordinate]
  exact detectedTranslationLogCoordinate_normalized_mass w d hw hwd M hM D b ω hN
    T hT hA hH (Sum.inl i) (hproj (Sum.inl i)) E hE

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold
variable {B L : Type} {U : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

theorem detectedTranslationPhasePolynomial_isWeightedHomogeneous
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (detectedTranslationPhasePolynomial w d hw hwd M hM D E).IsWeightedHomogeneous
      (Sum.elim (fun _ : U => 1) w) d := by
  rw [detectedTranslationPhasePolynomial_eq_logMixed,
    translationLogMixedGroupPolynomial_eq_series w d hwd]
  have hf := detectedTranslationLogCoordinate_homogeneous w d hw hwd M hM D E
  exact translationDirectionalSeries_isWeightedHomogeneous (fun _ : U => 1) w d _
    (translationLogBasePolynomial_weightedBasis_isWeightedHomogeneous (fun _ : U => 1) w d hw _ hf)
    (pack_translationLogPhasePolynomial_weightedBasis_isWeightedHomogeneous (fun _ : U => 1) w d hw _ hf)

theorem detectedTranslationPhasePolynomial_weightedSupportLE
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    detectedTranslationPhasePolynomial w d hw hwd M hM D E ∈
      weightedSupportLE (Sum.elim (fun _ : U => 1) w) d := by
  intro α hα
  exact (detectedTranslationPhasePolynomial_isWeightedHomogeneous w d hw hwd M hM D E
    (mem_support_iff.mp hα)).le

theorem detectedTranslationPhasePolynomial_totalDegree
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (detectedTranslationPhasePolynomial w d hw hwd M hM D E).totalDegree ≤ d := by
  have hP := detectedTranslationPhasePolynomial_weightedSupportLE w d hw hwd M hM D E
  rw [totalDegree_eq]
  apply Finset.sup_le
  intro α hα
  have hweight : α.sum (fun _ n => n) ≤ Finsupp.weight (Sum.elim (fun _ : U => 1) w) α := by
    change (∑ i ∈ α.support, α i) ≤ ∑ i ∈ α.support, α i • Sum.elim (fun _ : U => 1) w i
    apply Finset.sum_le_sum
    intro i _
    cases i with
    | inl i => simp
    | inr i => simpa only [Sum.elim_inr, smul_eq_mul] using Nat.le_mul_of_pos_right (α (Sum.inr i)) (hw i)
  rw [Finsupp.card_toMultiset]
  change (α.sum fun _ n => n) ≤ d
  exact hweight.trans (hP hα)

theorem detectedTranslationPhasePolynomial_scaled_totalDegree
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) :
    (scaleMvPolynomialAxes (Sum.elim H (fun _ : B => 1))
      (detectedTranslationPhasePolynomial w d hw hwd M hM D E)).totalDegree ≤ d :=
  (scaleMvPolynomialAxes_totalDegree_le _ _).trans
    (detectedTranslationPhasePolynomial_totalDegree w d hw hwd M hM D E)

theorem detectedTranslationBaseCoordinatePolynomial_totalDegree
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) (i : B) :
    (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i).totalDegree ≤ w i := by
  rw [detectedTranslationBaseCoordinatePolynomial_eq_logCoordinate]
  have h := detectedTranslationLogCoordinate_homogeneous w d hw hwd M hM D E (Sum.inl i)
  rw [totalDegree_eq]
  apply Finset.sup_le
  intro α hα
  have hh := h (mem_support_iff.mp hα)
  rw [Finsupp.card_toMultiset]
  change (α.sum fun _ n => n) ≤ w i
  simpa only [Finsupp.weight_apply, smul_eq_mul, mul_one, weightedBasisGrade, Sum.elim_inl] using hh.le

theorem detectedTranslationBaseCoordinatePolynomial_scaled_totalDegree
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) (i : B) :
    (scaleMvPolynomialAxes H
      (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i)).totalDegree ≤ w i :=
  (scaleMvPolynomialAxes_totalDegree_le _ _).trans
    (detectedTranslationBaseCoordinatePolynomial_totalDegree w d hw hwd M hM D E i)

theorem detectedTranslationPhasePolynomial_scaled_weightedSupportLE
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) :
    scaleMvPolynomialAxes (Sum.elim H (fun _ : B => 1))
      (detectedTranslationPhasePolynomial w d hw hwd M hM D E) ∈
        weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
  scaleMvPolynomialAxes_mem_weightedSupportLE _ _ _
    (detectedTranslationPhasePolynomial_weightedSupportLE w d hw hwd M hM D E)

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DetectedTranslationUniformCoordinateBounds
namespace OAI

section

namespace Erdos3

namespace PolynomialTranslationLie
open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold
variable {B L : Type} {U ι : Type*} [Fintype B] [Fintype U] [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationGroupCoordinates_uniform_bounds
    {p : ℝ} (hp : 0 ≤ p)
    (hU : (Fintype.card U : ℝ) ≤ p) (hB : (Fintype.card B : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (T : U → ℝ) (hT : ∀ i, 0 < T i)
    (E Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : U => 1) T (Real.exp p) E)
    (m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp p)
    (hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : U => 1) m Q) :
    let C := detectedTranslationCoordinateConstant d
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      realPolynomialMass (scaleMvPolynomialAxes (Sum.elim T (fun _ : B => 1))
        (detectedTranslationPhasePolynomial w d hw hwd M hM D E)) ≤ Real.exp ((p + C) ^ C) ∧
      (∀ i, realPolynomialMass (scaleMvPolynomialAxes T
        (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i)) ≤ Real.exp ((p + C) ^ C)) ∧
      realPolynomialCoefficientGrid q (detectedTranslationPhasePolynomial w d hw hwd M hM D Q) ∧
      (∀ i, realPolynomialCoefficientGrid q
        (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D Q i)) := by
  have hκ : (Fintype.card (WeightedBasisIndex w d) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (weightedBasisIndex_card_le_pair_basis w d hw b)).trans hι
  have hproj : ∀ k i, |(detectedTranslationLogProjectionMatrix w d hw b ω k i : ℝ)| ≤ Real.exp p := by
    intro k i
    exact (rational_abs_real_le_numerator _).trans
      ((rationalLogHeight_le_iff _ p).mp
        (detectedTranslationLogProjectionMatrix_logHeight w d hw hwd M hM D b ω hp hb k i)).1
  obtain ⟨q₀, hq₀, hq₀bound, hq₀grid⟩ :=
    exists_detectedTranslationLogCoordinate_grid_of_basis_height w d hw hwd M hM D b ω hN hp hb m hm
  have hbudget := (exists_detectedTranslationPhase_budget d).choose_spec.2
    (Fintype.card U) (Fintype.card (WeightedBasisIndex w d)) (Fintype.card ι)
    (Fintype.card B) m q₀ p (Real.exp p) (Real.exp p) hp hU hκ hι hB
    (Real.exp_pos p).le le_rfl (Real.exp_pos p).le le_rfl hmp hq₀bound
  obtain ⟨hbase, hphase, hden⟩ := hbudget
  refine ⟨d.factorial * q₀ ^ (d + 1), by positivity, hden, ?_, ?_, ?_, ?_⟩
  · have h := detectedTranslationPhasePolynomial_mass_of_slow w d hw hwd M hM D b ω hN T hT
      (Real.exp_pos p).le (Real.exp_pos p).le hproj E hE
    exact h.trans (by simpa only [mul_assoc, detectedTranslationCoordinateConstant] using hphase)
  · intro i
    have h := detectedTranslationBaseCoordinatePolynomial_mass_of_slow w d hw hwd M hM D b ω hN T hT
      (Real.exp_pos p).le (Real.exp_pos p).le hproj E hE i
    exact h.trans (by simpa only [mul_assoc, detectedTranslationCoordinateConstant] using hbase)
  · exact detectedTranslationPhasePolynomial_coefficientGrid w d hw hwd M hM D Q (hq₀grid Q hQ)
  · intro i
    apply realPolynomialCoefficientGrid_mono (show q₀ ∣ d.factorial * q₀ ^ (d + 1) from
      dvd_mul_of_dvd_right (dvd_pow_self q₀ (by omega : d + 1 ≠ 0)) _)
    rw [detectedTranslationBaseCoordinatePolynomial_eq_logCoordinate]
    exact hq₀grid Q hQ (Sum.inl i)

end PolynomialTranslationLie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslationMajorCorrelationDecomposition
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold

variable {B L : Type} {U : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

noncomputable def detectedTranslationNormalizedBase
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) (i : B) : MvPolynomial U ℝ :=
  scaleMvPolynomialAxes H (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i)

noncomputable def detectedTranslationNormalizedPhase
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) : MvPolynomial (U ⊕ B) ℝ :=
  scaleMvPolynomialAxes (Sum.elim H (fun _ : B => 1))
    (detectedTranslationPhasePolynomial w d hw hwd M hM D E)

theorem detectedTranslationNormalizedBase_eval
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) (hH : ∀ i, H i ≠ 0) (u : U → ℝ) (i : B) :
    eval (fun j => u j / H j) (detectedTranslationNormalizedBase w d hw hwd M hM D E H i) =
      (detectedTranslationGroupEval w d hw hwd M hM D u E).base i := by
  rw [detectedTranslationNormalizedBase, scaleMvPolynomialAxes_eval]
  have hc : (fun j => H j * (u j / H j)) = u := by
    funext j
    exact mul_div_cancel₀ (u j) (hH j)
  rw [hc, detectedTranslationBaseCoordinatePolynomial_eval]

theorem detectedTranslationNormalizedPhase_eval
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) (hH : ∀ i, H i ≠ 0) (u : U → ℝ) (z : B → ℝ) :
    eval (Sum.elim (fun j => u j / H j) z)
      (detectedTranslationNormalizedPhase w d hw hwd M hM D E H) =
      eval z (detectedTranslationGroupEval w d hw hwd M hM D u E).polynomial := by
  rw [detectedTranslationNormalizedPhase, scaleMvPolynomialAxes_eval]
  have hc : (fun j => Sum.elim H (fun _ : B => 1) j *
      Sum.elim (fun i => u i / H i) z j) = Sum.elim u z := by
    funext j
    cases j with
    | inl i => exact mul_div_cancel₀ (u i) (hH i)
    | inr i => exact one_mul _
  rw [hc, detectedTranslationPhasePolynomial_eval]

theorem detectedTranslationGroupEval_normalized_left
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (H : U → ℝ) (hH : ∀ i, H i ≠ 0) (u : U → ℝ) :
    normalizedMajorLeft
      (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H) H u =
      detectedTranslationGroupEval w d hw hwd M hM D u E := by
  apply PolynomialTranslationGroupOver.ext
  · funext i
    exact detectedTranslationNormalizedBase_eval w d hw hwd M hM D E H hH u i
  · apply MvPolynomial.funext
    intro z
    change eval z (specializeMajorParameters (RingHom.id ℝ) _ _) = _
    rw [specializeMajorParameters_eval, eval₂_id]
    exact detectedTranslationNormalizedPhase_eval w d hw hwd M hM D E H hH u z

theorem exists_detectedTranslation_rational_right
    (Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (q : ℕ) (hq : 0 < q)
    (hphase : realPolynomialCoefficientGrid q
      (detectedTranslationPhasePolynomial w d hw hwd M hM D Q))
    (hbase : ∀ i, realPolynomialCoefficientGrid q
      (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D Q i)) :
    ∃ (Qrat : MvPolynomial (U ⊕ B) ℚ) (a : B → MvPolynomial U ℚ),
      map (algebraMap ℚ ℝ) Qrat = detectedTranslationPhasePolynomial w d hw hwd M hM D Q ∧
      (∀ i, map (algebraMap ℚ ℝ) (a i) =
        detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D Q i) ∧
      (fun α => Qrat.coeff α) ∈ denominatorGrid q ∧
      (∀ i, (fun α => (a i).coeff α) ∈ denominatorGrid q) ∧
      Qrat.totalDegree = (detectedTranslationPhasePolynomial w d hw hwd M hM D Q).totalDegree ∧
      ∀ u, rationalMajorRight Qrat a u = detectedTranslationGroupEval w d hw hwd M hM D u Q := by
  obtain ⟨Qrat, hQrat, hQgrid, hQdegree⟩ :=
    exists_rationalPolynomial_of_realCoefficientGrid _ hq hphase
  choose a ha hagrid _hadegree using fun i =>
    exists_rationalPolynomial_of_realCoefficientGrid _ hq (hbase i)
  refine ⟨Qrat, a, hQrat, ha, hQgrid, hagrid, hQdegree, ?_⟩
  intro u
  apply PolynomialTranslationGroupOver.ext
  · funext i
    change eval₂ (algebraMap ℚ ℝ) u (a i) = _
    rw [← eval_map, ha i]
    exact detectedTranslationBaseCoordinatePolynomial_eval w d hw hwd M hM D Q u i
  · apply MvPolynomial.funext
    intro z
    change eval z (specializeMajorParameters (algebraMap ℚ ℝ) Qrat u) = _
    rw [specializeMajorParameters_eval, ← eval_map, hQrat]
    exact detectedTranslationPhasePolynomial_eval w d hw hwd M hM D Q u z

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem exists_detectedTranslation_normalized_weighted_decomposition
    (hd : 0 < d)
    (F : MvPolynomial (U ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (partner : D.filtration.realification.PolynomialOrbit (fun _ : U => 1))
    (E P Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hprod : E * P * Q = pairOrbitSymbol
      (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
      (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) partner b ω hN)
    (W : LieSubalgebra ℚ (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra b ω hN (fun _ : U => 1) W))
    (V : MvPolynomial B ℚ) (H : U → ℝ) (hH : ∀ i, H i ≠ 0)
    (q : ℕ) (hq : 0 < q) (Cbase : ℝ) (hCbase : 0 ≤ Cbase)
    (hphaseGrid : realPolynomialCoefficientGrid q
      (detectedTranslationPhasePolynomial w d hw hwd M hM D Q))
    (hbaseGrid : ∀ i, realPolynomialCoefficientGrid q
      (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D Q i))
    (hVgrid : (fun α => V.coeff α) ∈ denominatorGrid q)
    (hVweight : V ∈ weightedSupportLE w d)
    (heMass : ∀ i, realPolynomialMass
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H i) ≤ Cbase) :
    let fast := W.map (weightedTranslationGradedProjection
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
        w d hw hwd (liePiEval (R := ℚ) true)
        (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D))
    let K := (fast.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))
    let Ftop := weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d F
    let F₀ := specializeMajorParameters (RingHom.id ℝ) Ftop 0
    (∀ x ∈ fast, ∀ z ∈ fast.toSubmodule.map
      (baseLinear.comp (weightedSubalgebra w d).subtype),
      eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) →
    (∀ u, (detectedTranslationGroupEval w d hw hwd M hM D u Q).base ∈ K) →
    ∃ (S : MvPolynomial (U ⊕ B) ℝ) (R : MvPolynomial (U ⊕ B) ℚ),
      (∀ u z, z ∈ K → eval (Sum.elim u z) Ftop =
        eval (Sum.elim (fun i => u i / H i)
          (fun j => z j - eval u (majorTranslationTopCoordinates w A j))) S +
        eval₂ (algebraMap ℚ ℝ) (Sum.elim u z) R) ∧
      realPolynomialMass S ≤ realPolynomialMass F₀ +
        (realPolynomialMass (detectedTranslationNormalizedPhase w d hw hwd M hM D E H) +
          realPolynomialMass (map (algebraMap ℚ ℝ) V)) * (1 + Cbase)^d ∧
      (fun α => R.coeff α) ∈ denominatorGrid (q^(d+1)) ∧
      S ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
      R ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
      S.totalDegree ≤ d ∧ R.totalDegree ≤ d := by
  intro fast K Ftop F₀ hderiv hright
  obtain ⟨Qrat, a, hQmap, hamap, hQgrid, hagrid, _hQratDegree, hQeval⟩ :=
    exists_detectedTranslation_rational_right w d hw hwd M hM D Q q hq hphaseGrid hbaseGrid
  have hfactor (u : U → ℝ) : algebraicMajorSymbol Ftop F₀
      (majorTranslationTopCoordinates w A) u =
        normalizedMajorLeft (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
          (detectedTranslationNormalizedBase w d hw hwd M hM D E H) H u *
        detectedTranslationGroupEval w d hw hwd M hM D u P * rationalMajorRight Qrat a u := by
    rw [detectedTranslationGroupEval_normalized_left w d hw hwd M hM D E H hH,
      hQeval]
    exact detectedTranslationGroupEval_major_factorization w d hw hwd M hM D b ω hN
      F hF A hA partner E P Q hprod u
  have hpotential := detectedTranslationGroupEval_fast_potential w d hw hwd M hM D b ω hN
    hd W P hP V hderiv
  have haright (u : U → ℝ) : (fun j => eval₂ (algebraMap ℚ ℝ) u (a j)) ∈ K := by
    have heq := congrArg PolynomialTranslationGroupOver.base (hQeval u)
    change (fun i => eval₂ (algebraMap ℚ ℝ) u (a i)) = _ at heq
    rw [heq]
    exact hright u
  have hFtopweight : Ftop ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d := by
    intro α hα
    exact ((weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      (mem_support_iff.mp hα)).le
  have hF₀weight : F₀ ∈ weightedSupportLE w d :=
    specializeMajorParameters_zero_weightedSupportLE w hFtopweight
  have hEweight : detectedTranslationNormalizedPhase w d hw hwd M hM D E H ∈
      weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
    detectedTranslationPhasePolynomial_scaled_weightedSupportLE w d hw hwd M hM D E H
  have heweight (i : B) : detectedTranslationNormalizedBase w d hw hwd M hM D E H i ∈
      weightedSupportLE (fun _ : U => 1) (w i) :=
    (mem_weightedSupportLE_one_iff _ _).mpr
      (detectedTranslationBaseCoordinatePolynomial_scaled_totalDegree w d hw hwd M hM D E H i)
  have hQweight : Qrat ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d := by
    apply weightedSupportLE_of_map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective
    rw [hQmap]
    exact detectedTranslationPhasePolynomial_weightedSupportLE w d hw hwd M hM D Q
  have haweight (i : B) : a i ∈ weightedSupportLE (fun _ : U => 1) (w i) := by
    apply weightedSupportLE_of_map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective
    rw [hamap i]
    exact (mem_weightedSupportLE_one_iff _ _).mpr
      (detectedTranslationBaseCoordinatePolynomial_totalDegree w d hw hwd M hM D Q i)
  have hVrealweight : map (algebraMap ℚ ℝ) V ∈ weightedSupportLE w d := by
    intro α hα
    exact hVweight (support_map_subset (algebraMap ℚ ℝ) V hα)
  have hVdegree : V.totalDegree ≤ d := weightedSupportLE_totalDegree_le_of_pos hw hVweight
  have hVrealDegree : (map (algebraMap ℚ ℝ) V).totalDegree ≤ d :=
    weightedSupportLE_totalDegree_le_of_pos hw hVrealweight
  have hEdegree : (detectedTranslationNormalizedPhase w d hw hwd M hM D E H).totalDegree ≤ d :=
    detectedTranslationPhasePolynomial_scaled_totalDegree w d hw hwd M hM D E H
  have hSweight := majorSlowPolynomial_weightedSupportLE (fun _ : U => 1) w F₀
    (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
    (map (algebraMap ℚ ℝ) V)
    (detectedTranslationNormalizedBase w d hw hwd M hM D E H)
    hF₀weight hEweight hVrealweight heweight
  have hRweight := majorRationalPolynomial_weightedSupportLE (fun _ : U => 1) w
    Qrat V a hQweight hVweight haweight
  have hpos (i : U ⊕ B) : 0 < Sum.elim (fun _ : U => 1) w i := by
    cases i with
    | inl i => exact Nat.zero_lt_one
    | inr i => exact hw i
  refine ⟨majorSlowPolynomial F₀
      (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
      (map (algebraMap ℚ ℝ) V)
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H),
    majorRationalPolynomial Qrat V a, ?_, ?_, ?_, hSweight, hRweight,
    weightedSupportLE_totalDegree_le_of_pos hpos hSweight,
    weightedSupportLE_totalDegree_le_of_pos hpos hRweight⟩
  · exact algebraic_major_normalized_identity_on_subspace K Ftop F₀
      (majorTranslationTopCoordinates w A)
      (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H) Qrat a V H
      (fun u => detectedTranslationGroupEval w d hw hwd M hM D u P)
      hfactor hpotential haright
  · exact algebraic_major_normalized_slow_mass F₀
      (detectedTranslationNormalizedPhase w d hw hwd M hM D E H) V
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H)
      hCbase heMass hEdegree hVrealDegree
  · exact majorRationalPolynomial_denominatorGrid Qrat V a q d hVdegree hQgrid hVgrid hagrid

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPhasePairFunctionalBounds
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

open Module PolynomialTranslationLie RationalFilteredNilmanifold

variable {L : Type} [LieRing L] [LieAlgebra ℚ L] {e : ℕ}

theorem pairScalarFunctional_basis_logHeight
    (s : ℕ) (hs : 0 < s) (D : RationalFilteredNilmanifold L s e)
    {ι : Type*} (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra weight s) L))
    (ω : ι → ℕ)
    (hF : ∀ j, (pi (pairModels (nilmanifold s) D)).filtration.layer j =
      Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (nilmanifold s) D)).basis.repr (b i) j) ≤ p) (i : ι) :
    rationalLogHeight (pairScalarFunctional s D
      ((pi (pairModels (nilmanifold s) D)).filtration.associatedGradedBasis b ω hF i)) ≤ p := by
  let := weightedBasisIndex_finite weight s weight_pos
  let : Fintype (WeightedBasisIndex weight s) := Fintype.ofFinite _
  let a : {a : Fin 0 →₀ ℕ | Finsupp.weight weight a < s} :=
    ⟨0, by change Finsupp.weight weight 0 < s; simpa only [map_zero] using hs⟩
  let N := (pi (pairModels (nilmanifold s) D)).filtration
  let φ : PairAlgebra (weightedSubalgebra weight s) L →ₗ⁅ℚ⁆ weightedSubalgebra weight s :=
    liePiEval (R := ℚ) (M := BoolLieFamily (weightedSubalgebra weight s) L) true
  change rationalLogHeight ((weightedBasis weight s weight_pos).repr
    (N.homogeneousGradedProjection (weightedFiltration weight s (weight_le s))
      (weightedBasis weight s weight_pos) (weightedBasisGrade weight s)
      (weightedFiltration_layer_eq_span weight s weight_pos (weight_le s))
      (weightedBasis_homogeneous_brackets weight s weight_pos) φ
      (projection_filtered N φ) (N.associatedGradedBasis b ω hF i)) (Sum.inr a)) ≤ p
  rw [N.homogeneousGradedProjection_basis_repr (weightedFiltration weight s (weight_le s))
    (weightedBasis weight s weight_pos) (weightedBasisGrade weight s)
    (weightedFiltration_layer_eq_span weight s weight_pos (weight_le s))
    (weightedBasis_homogeneous_brackets weight s weight_pos) φ (projection_filtered N φ)
    b ω hF i (Sum.inr a)]
  split_ifs
  · exact pairTranslationProjection_coordinate_logHeight weight s weight_pos
      (weight_le s) D (b i) (hb i) (Sum.inr a)
  · simpa [rationalLogHeight] using hp

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPolynomialPhaseAffineInverse
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

open _root_.MvPolynomial Module PolynomialTranslationLie RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

theorem pairOrbitSymbol_scalar_top {U ι L : Type} [LieRing L] [LieAlgebra ℚ L]
    (s : ℕ) (hs : 0 < s) {e : ℕ} (D : RationalFilteredNilmanifold L s e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra weight s) L)) (ω : ι → ℕ)
    (hF : ∀ j, (pi (pairModels (nilmanifold s) D)).filtration.layer j =
      Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s)
    (q : D.filtration.realification.PolynomialOrbit (fun _ : U => 1)) :
    (pi (pairModels (nilmanifold s) D)).filtration.scalarSymbolPolynomial b ω hF
      (fun _ : U => 1)
      ((constantCoefficient s).comp
        (gradedProjection (pi (pairModels (nilmanifold s) D)).filtration
          (liePiEval (R := ℚ)
            (M := BoolLieFamily (weightedSubalgebra weight s) L) true)).toLinearMap)
      (pairOrbitSymbol (nilmanifold s) D (orbit s hs P hP) q b ω hF) =
        homogeneousComponent s P := by
  let N := pi (pairModels (nilmanifold s) D)
  let c := weightedBasis weight s weight_pos
  let ν := weightedBasisGrade weight s
  have hG : ∀ j, (weightedFiltration weight s (weight_le s)).layer j =
      Submodule.span ℚ (c '' {i | j ≤ ν i}) :=
    weightedFiltration_layer_eq_span weight s weight_pos (weight_le s)
  let φ : PairAlgebra (weightedSubalgebra weight s) L →ₗ⁅ℚ⁆ weightedSubalgebra weight s :=
    liePiEval (R := ℚ) (M := BoolLieFamily (weightedSubalgebra weight s) L) true
  have hfirst := pairOrbitSymbol_first_projection (nilmanifold s) D (fun _ : U => 1)
    b ω hF c ν hG (orbit s hs P hP) q
  have hphase : coordinate (realifyFunctional (constantCoefficient s)).toAddMonoidHom
      ((weightedFiltration weight s (weight_le s)).realSymbolRepresentative c ν hG (fun _ : U => 1)
        ((weightedFiltration weight s (weight_le s)).realSymbolOfPolynomial c ν hG (fun _ : U => 1)
          (orbit s hs P hP).log)) = homogeneousComponent s P := by
    have hh := orbit_symbol_constantCoefficient s hs (weightedFiltration weight s (weight_le s)) hG P hP
    simpa only [c, ν] using hh
  have hresult := N.filtration.homogeneousProjected_scalar_identity
    (weightedFiltration weight s (weight_le s)) b ω hF c ν hG
    (weightedBasis_homogeneous_brackets weight s weight_pos) φ
    (projection_filtered N.filtration φ) (fun _ : U => 1)
    (constantCoefficient s)
    (pairOrbitSymbol (nilmanifold s) D (orbit s hs P hP) q b ω hF).coord
    ((weightedFiltration weight s (weight_le s)).realSymbolOfPolynomial c ν hG (fun _ : U => 1)
      (orbit s hs P hP).log) (homogeneousComponent s P) hfirst hphase
  simpa only [N, c, ν, φ,
    NilpotentLieFiltration.scalarSymbolPolynomial, gradedProjection] using hresult

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalTaggedConstraintHistory
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]
    {X R S V : Type*} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V]

theorem lowTaggedVectorExtend_restrict (k : ℕ)
    (P : VectorPolynomial (X ⊕ (Σ j, J j)) R V)
    (hP : DegreeLE (fullTaggedVariableWeight J) k P) :
    lowTaggedVectorExtend J k (lowTaggedVectorRestrict J k P) = P := by
  classical
  rw [← sum_monomial_coefficients P]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro α hα
  have hαk : Finsupp.weight (fullTaggedVariableWeight J) α ≤ k :=
    (degreeLE_iff _ _ P).mp hP α hα
  rw [monomial, lowTaggedVectorRestrict_tmul, lowTaggedVectorExtend_tmul]
  rw [rename_lowTaggedRestrict J k]
  exact weightedSupportLE_mono hαk
    (weightedSupportLE_monomial (fullTaggedVariableWeight J) α (1 : R))

theorem lowTaggedVectorRestrict_weightedHomogeneousPart (k n : ℕ)
    (P : VectorPolynomial (X ⊕ (Σ j, J j)) R V) :
    lowTaggedVectorRestrict J k (weightedHomogeneousPart (fullTaggedVariableWeight J) n P) =
      weightedHomogeneousPart (lowTaggedVariableWeight J k) n (lowTaggedVectorRestrict J k P) := by
  induction P using TensorProduct.induction_on with
  | zero => simp
  | tmul P v =>
    rw [weightedHomogeneousPart_tmul, lowTaggedVectorRestrict_tmul,
      lowTaggedVectorRestrict_tmul, weightedHomogeneousPart_tmul,
      lowTaggedRestrict_weightedHomogeneousComponent]
  | add P Q hP hQ => simp only [map_add, hP, hQ]

theorem lowTaggedVectorRestrict_homogeneous (k : ℕ)
    (P : VectorPolynomial (X ⊕ (Σ j, J j)) R V)
    (hP : ∀ α, Finsupp.weight (fullTaggedVariableWeight J) α ≠ k → coefficients P α = 0)
    (α : (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) →₀ ℕ)
    (hα : Finsupp.weight (lowTaggedVariableWeight J k) α ≠ k) :
    coefficients (lowTaggedVectorRestrict J k P) α = 0 := by
  have h := lowTaggedVectorRestrict_weightedHomogeneousPart J k k P
  rw [weightedHomogeneousPart_eq_self hP] at h
  rw [h]
  exact weightedHomogeneousPart_homogeneous _ _ _ _ hα

section Evaluation

variable [Algebra R S] [Module S V] [IsScalarTower R S V]

theorem lowTaggedVectorExtend_eval₂ (k : ℕ)
    (P : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V)
    (x : X ⊕ (Σ j, J j) → S) :
    eval₂ x (lowTaggedVectorExtend J k P) =
      eval₂ (x ∘ lowTaggedVariableEmbedding J k) P := by
  induction P using TensorProduct.induction_on with
  | zero => simp
  | tmul P v =>
    rw [lowTaggedVectorExtend_tmul, eval₂_tmul, eval₂_tmul, MvPolynomial.aeval_rename]
  | add P Q hP hQ => simp only [map_add, hP, hQ]

theorem lowTaggedVectorRestrict_eval₂ (k : ℕ)
    (P : VectorPolynomial (X ⊕ (Σ j, J j)) R V)
    (hP : DegreeLE (fullTaggedVariableWeight J) k P)
    (x : X ⊕ (Σ j, J j) → S) :
    eval₂ x P = eval₂ (x ∘ lowTaggedVariableEmbedding J k) (lowTaggedVectorRestrict J k P) := by
  rw [← lowTaggedVectorExtend_eval₂, lowTaggedVectorExtend_restrict J k P hP]

end Evaluation

theorem lowTaggedVectorRestrict_eval_real [Algebra R ℝ] [Module ℝ V] [IsScalarTower R ℝ V]
    (k : ℕ) (P : VectorPolynomial (X ⊕ (Σ j, J j)) R V)
    (hP : DegreeLE (fullTaggedVariableWeight J) k P)
    (u : X → ℝ) (z : ∀ j, J j → ℝ) :
    eval₂ (Sum.elim u (fun a : Σ j, J j => z a.1 a.2)) P =
      eval₂ (Sum.elim u (lowTaggedCoordinates J k z)) (lowTaggedVectorRestrict J k P) := by
  rw [lowTaggedVectorRestrict_eval₂ J k P hP, lowTaggedVariableEmbedding_eval_coordinates]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]
    {X R S V : Type*} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V]

theorem coordinate_lowTaggedVectorExtend (k : ℕ) (f : V →+ S)
    (P : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V) :
    coordinate f (lowTaggedVectorExtend J k P) =
      MvPolynomial.rename (lowTaggedVariableEmbedding J k) (coordinate f P) := by
  classical
  rw [← sum_monomial_coefficients P]
  simp only [Finsupp.sum, map_sum, coordinate_sum, lowTaggedVectorExtend_monomial,
    coordinate_monomial, MvPolynomial.rename_monomial]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]
  {X R V η : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem lowTaggedVectorExtend_coordinate_coefficient_bound (k : ℕ)
    (f : η → V →+ ℝ)
    (P : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ j α, |f j (coefficients P α)| ≤ C) :
    ∀ α j, |f j (coefficients (lowTaggedVectorExtend J k P) α)| ≤ C := by
  intro α j
  rw [← coeff_coordinate, coordinate_lowTaggedVectorExtend]
  exact abs_coeff_rename_le (lowTaggedVariableEmbedding J k) (coordinate (f j) P)
    C hC (fun β => by simpa only [coeff_coordinate] using hP j β) α

theorem lowTaggedVectorExtend_coordinate_grid (k : ℕ)
    (f : η → V →+ ℝ)
    (P : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V)
    (q : ℕ) (hP : ∀ j, realPolynomialCoefficientGrid q (coordinate (f j) P)) :
    ∀ j, realPolynomialCoefficientGrid q (coordinate (f j) (lowTaggedVectorExtend J k P)) := by
  intro j
  rw [coordinate_lowTaggedVectorExtend]
  exact realPolynomialCoefficientGrid_rename (lowTaggedVariableEmbedding J k) (hP j)

theorem lowTaggedVectorExtend_coefficients_grid (k : ℕ)
    (f : η → V →+ ℝ)
    (P : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V)
    (q : ℕ) (hP : ∀ j, realPolynomialCoefficientGrid q (coordinate (f j) P)) :
    ∀ α, (fun j => f j (coefficients (lowTaggedVectorExtend J k P) α)) ∈
      realDenominatorGrid q := by
  intro α
  have hj : ∀ j, ∃ z : ℤ, (z : ℝ) =
      (q : ℝ) * f j (coefficients (lowTaggedVectorExtend J k P) α) := by
    intro j
    obtain ⟨z, hz⟩ := lowTaggedVectorExtend_coordinate_grid J k f P q hP j
    exact ⟨z α, by simpa only [coeff_coordinate, Pi.smul_apply, smul_eq_mul] using congrFun hz α⟩
  choose z hz using hj
  exact ⟨z, funext hz⟩

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {X κ : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem fullTaggedGradedBaseIntersection_rat_dilation (k : ℕ)
    (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
    (K : κ → Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J k)) → ℝ))
    (hK : ∀ i, BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J k) (K i))
    (hK₀ : ∀ t ∈ K₀, ∀ r : ℚ,
      (fun i => (r : ℝ) ^ fullTaggedVariableWeight J i * t i) ∈ K₀)
    (t : X ⊕ (Σ j, J j) → ℝ) (ht : t ∈ fullTaggedGradedBaseIntersection J k K₀ K)
    (r : ℚ) :
    (fun i => (r : ℝ) ^ fullTaggedVariableWeight J i * t i) ∈
      fullTaggedGradedBaseIntersection J k K₀ K := by
  refine ⟨hK₀ t ht.1 r, ?_⟩
  intro i
  change (fun b => (r : ℝ) ^ fullTaggedVariableWeight J
    (lowTaggedVariableEmbedding J k (Sum.inr b)) *
      t (lowTaggedVariableEmbedding J k (Sum.inr b))) ∈ K i
  simpa only [lowTaggedVariableEmbedding_weight, lowTaggedVariableWeight, Sum.elim_inr] using
    (hK i).coordinate_dilation_mem (lowTaggedWeight J k) (K i) (r : ℝ)
      (fun b => t (lowTaggedVariableEmbedding J k (Sum.inr b))) (ht.2 i)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module RationalFilteredNilmanifold PolynomialTranslationLie

variable {m : ℕ} (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)

noncomputable def majorPhaseRationalTagConstraint {η : Type*} {count : ℕ}
    (gen : η → Fin count → weightedSubalgebra (lowTaggedWeight J k) k)
    (a : η × {j : Fin m // j.val + 1 ≤ k}) : RationalTagConstraint J where
  tag := a.2.val
  count := count
  generators := majorPhaseTaggedGenerators J k (gen a.1) a.2.val a.2.property

noncomputable def majorPhaseRationalTagConstraints {η : Type*} [Fintype η] {count : ℕ}
    (gen : η → Fin count → weightedSubalgebra (lowTaggedWeight J k) k) :
    List (RationalTagConstraint J) := by
  classical
  exact (Finset.univ : Finset (η × {j : Fin m // j.val + 1 ≤ k})).toList.map
    (majorPhaseRationalTagConstraint J k gen)

theorem majorPhaseRationalTagConstraints_length {η : Type*} [Fintype η] {count : ℕ}
    (gen : η → Fin count → weightedSubalgebra (lowTaggedWeight J k) k) :
    (majorPhaseRationalTagConstraints J k gen).length ≤ Fintype.card η * m := by
  classical
  have htag : Fintype.card {j : Fin m // j.val + 1 ≤ k} ≤ m := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun j : Fin m => j.val + 1 ≤ k)
  simpa only [majorPhaseRationalTagConstraints, List.length_map, Finset.length_toList,
    Finset.card_univ, Fintype.card_prod] using Nat.mul_le_mul_left (Fintype.card η) htag

theorem majorPhaseRationalTagConstraints_budget {η : Type*} [Fintype η] {count : ℕ}
    (gen : η → Fin count → weightedSubalgebra (lowTaggedWeight J k) k) (B : ℝ)
    (hcount : ∀ _a : η, (count : ℝ) ≤ B)
    (hheight : ∀ a i j, rationalLogHeight
      ((weightedBasis (lowTaggedWeight J k) k (lowTaggedWeight_pos J k)).repr (gen a i) j) ≤ B) :
    ∀ c ∈ majorPhaseRationalTagConstraints J k gen, c.BudgetLE B := by
  classical
  intro c hc
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
  refine ⟨hcount a.1, ?_⟩
  exact majorPhaseTaggedGenerators_logHeight J k (gen a.1) (hheight a.1) a.2.val a.2.property

theorem majorPhaseRationalTagConstraints_set_eq
    {X η : Type*} [Fintype η] {count : ℕ}
    (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J k) k))
    (gen : η → Fin count → weightedSubalgebra (lowTaggedWeight J k) k)
    (hspan : ∀ a, Submodule.span ℚ (Set.range (gen a)) = (detectedfast a).toSubmodule)
    (hgraded : ∀ a, BasisGradedSubmodule
      (weightedBasis (lowTaggedWeight J k) k (lowTaggedWeight_pos J k))
      (weightedBasisGrade (lowTaggedWeight J k) k) (detectedfast a).toSubmodule)
    (K₀ : Set (X ⊕ (Σ j, J j) → ℝ)) :
    fullTaggedGradedBaseIntersection J k K₀
      (fun a => majorPhaseDetectedRealBase J k (detectedfast a)) =
      K₀ ∩ {t | ∀ c ∈ majorPhaseRationalTagConstraints J k gen, c.member t} := by
  classical
  ext t
  change (t ∈ K₀ ∧ ∀ a,
      lowTaggedCoordinates J k (fun j i => t (Sum.inr ⟨j, i⟩)) ∈
        majorPhaseDetectedRealBase J k (detectedfast a)) ↔
    t ∈ K₀ ∧ ∀ c ∈ majorPhaseRationalTagConstraints J k gen, c.member t
  constructor
  · rintro ⟨ht, hmem⟩
    refine ⟨ht, ?_⟩
    intro c hc
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
    exact (majorPhaseTaggedGenerators_mem_iff J k (detectedfast a.1) (gen a.1)
      (hspan a.1) (hgraded a.1) (fun j i => t (Sum.inr ⟨j, i⟩))).mp
      (hmem a.1) a.2.val a.2.property
  · rintro ⟨ht, hmem⟩
    refine ⟨ht, ?_⟩
    intro a
    apply (majorPhaseTaggedGenerators_mem_iff J k (detectedfast a) (gen a)
      (hspan a) (hgraded a) (fun j i => t (Sum.inr ⟨j, i⟩))).mpr
    intro j hj
    apply hmem (majorPhaseRationalTagConstraint J k gen (a, ⟨j, hj⟩))
    exact List.mem_map.mpr ⟨(a, ⟨j, hj⟩), Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩

theorem majorPhase_rationalTaggedConstraintCertificate
    {X η : Type*} [Fintype η] {count : ℕ}
    (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J k) k))
    (gen : η → Fin count → weightedSubalgebra (lowTaggedWeight J k) k)
    (K₀ : Set (X ⊕ (Σ j, J j) → ℝ)) (B : ℝ)
    (hgen : ∀ a, (count : ℝ) ≤ B ∧
      Submodule.span ℚ (Set.range (gen a)) = (detectedfast a).toSubmodule ∧
      BasisGradedSubmodule (weightedBasis (lowTaggedWeight J k) k (lowTaggedWeight_pos J k))
        (weightedBasisGrade (lowTaggedWeight J k) k) (detectedfast a).toSubmodule ∧
      ∀ i j, rationalLogHeight
        ((weightedBasis (lowTaggedWeight J k) k (lowTaggedWeight_pos J k)).repr (gen a i) j) ≤ B) :
    RationalTaggedConstraintCertificate J K₀
      (fullTaggedGradedBaseIntersection J k K₀
        (fun a => majorPhaseDetectedRealBase J k (detectedfast a))) B (Fintype.card η * m) := by
  refine ⟨majorPhaseRationalTagConstraints J k gen,
    majorPhaseRationalTagConstraints_length J k gen,
    majorPhaseRationalTagConstraints_budget J k gen B (fun a => (hgen a).1)
      (fun a => (hgen a).2.2.2), ?_⟩
  exact majorPhaseRationalTagConstraints_set_eq J k detectedfast gen
    (fun a => (hgen a).2.1) (fun a => (hgen a).2.2.1) K₀

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FullTaggedChartCoefficientRange
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem majorTranslationTopCoordinates_lowTagged_eq (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (i : Fin (Fintype.card (LowTaggedIndex J k))) :
    majorTranslationTopCoordinates (lowTaggedWeight J k)
        (fun i => lowTaggedPolynomial J k poly i - C (c i)) i =
      fullTaggedMajorTopCoordinates J poly (lowTaggedIndex J k i) := by
  have hc : homogeneousComponent (lowTaggedWeight J k i)
      (C (c i) : MvPolynomial X ℝ) = 0 := by
    apply homogeneousComponent_eq_zero
    simpa using lowTaggedWeight_pos J k i
  change homogeneousComponent (lowTaggedWeight J k i)
      (lowTaggedPolynomial J k poly i - C (c i)) =
    homogeneousComponent (lowTaggedWeight J k i) (lowTaggedPolynomial J k poly i)
  rw [map_sub, hc, sub_zero]

theorem lowTaggedMajorChart_rename (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ) (H : X → ℝ)
    (i : X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) :
    rename (lowTaggedVariableEmbedding J k)
      (normalizedRealPolynomialChart H
        (majorTranslationTopCoordinates (lowTaggedWeight J k)
          (fun i => lowTaggedPolynomial J k poly i - C (c i))) i) =
      normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly)
        (lowTaggedVariableEmbedding J k i) := by
  cases i with
  | inl i => simp only [normalizedRealPolynomialChart_inl, lowTaggedVariableEmbedding_inl,
      map_mul, rename_C, rename_X]
  | inr i =>
    simp only [normalizedRealPolynomialChart_inr, lowTaggedVariableEmbedding_inr,
      map_sub, rename_X, rename_rename, majorTranslationTopCoordinates_lowTagged_eq]
    rfl

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]

theorem lowTaggedVectorExtend_majorChart (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ) (H : X → ℝ)
    (slow : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ V) :
    lowTaggedVectorExtend J k
        (realChartSubstitute (normalizedRealPolynomialChart H
          (majorTranslationTopCoordinates (lowTaggedWeight J k)
            (fun i => lowTaggedPolynomial J k poly i - C (c i)))) slow) =
      realChartSubstitute (normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly))
        (lowTaggedVectorExtend J k slow) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro x
  rw [map_sub, lowTaggedVectorExtend_eval₂, eval₂_realChartSubstitute,
    eval₂_realChartSubstitute, lowTaggedVectorExtend_eval₂]
  apply sub_eq_zero.mpr
  apply congrArg (fun t => eval₂ t slow)
  funext i
  change MvPolynomial.eval (x ∘ lowTaggedVariableEmbedding J k) _ =
    MvPolynomial.eval x _
  rw [← MvPolynomial.eval_rename, lowTaggedMajorChart_rename]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem fullTaggedMajorTopCoordinates_coefficients_mem_tag
    {m : ℕ} {X : Type*} (J : Fin m → Type*)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
    (α : X →₀ ℕ) (j : Fin m) :
    (fun i => (fullTaggedMajorTopCoordinates J poly ⟨j, i⟩).coeff α) ∈ U j := by
  classical
  by_cases hα : α.degree = j.val + 1
  · have hne : α ≠ 0 := by
      intro hz
      simp [hz] at hα
    have heq : (fun i => (fullTaggedMajorTopCoordinates J poly ⟨j, i⟩).coeff α) =
        coefficients (poly j) α := by
      funext i
      rw [fullTaggedMajorTopCoordinates, MvPolynomial.coeff_homogeneousComponent,
        if_pos hα, coeff_coordinate]
      rfl
    rw [heq]
    exact hcoeff j α hne
  · have heq : (fun i => (fullTaggedMajorTopCoordinates J poly ⟨j, i⟩).coeff α) = 0 := by
      funext i
      rw [fullTaggedMajorTopCoordinates, MvPolynomial.coeff_homogeneousComponent, if_neg hα]
      rfl
    rw [heq]
    exact (U j).zero_mem

theorem fullTaggedMajorTopCoordinates_coefficients_mem
    {m : ℕ} {X : Type*} (J : Fin m → Type*)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
    (K : Submodule ℝ ((Σ j, J j) → ℝ))
    (hU : ∀ x, (∀ j, (fun i => x ⟨j, i⟩) ∈ U j) → x ∈ K)
    (α : X →₀ ℕ) :
    (fun a => (fullTaggedMajorTopCoordinates J poly a).coeff α) ∈ K := by
  apply hU
  exact fun j => fullTaggedMajorTopCoordinates_coefficients_mem_tag J poly U hcoeff α j

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorSubspaceCorrectionRepresentatives
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module
open scoped BigOperators

variable {U B I η α V : Type*} [Fintype U] [Fintype B] [Fintype I] [Fintype η]
  [AddCommGroup V] [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]

omit [Fintype U] [Fintype B] [Fintype η] [IsScalarTower ℚ ℝ V] in
theorem coordinate_grid_of_vector_grid (basis : Basis η ℝ V)
    (q : ℕ) (P : VectorPolynomial (U ⊕ B) ℚ V)
    (h : ∀ ex, (fun i => basis.coord i (coefficients P ex)) ∈ realDenominatorGrid q)
    (i : η) : realPolynomialCoefficientGrid q (coordinate (basis.coord i).toAddMonoidHom P) := by
  classical
  choose z hz using h
  refine ⟨fun ex => z ex i, funext fun ex => ?_⟩
  simpa only [coeff_coordinate, LinearMap.toAddMonoidHom_coe, Pi.smul_apply, smul_eq_mul]
    using congrFun (hz ex) i

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FullChartHomogeneousCorrection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}

namespace FullChartFiniteHistory

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)]
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (Bphase : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)
local notation "State" => FullChartFiniteHistory F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase

noncomputable def outer {n : ℕ} (H : State n) :
    F.RealPolynomialSymbolGroup wt × F.RealPolynomialSymbolGroup wt :=
  F.restrictedMajorOuterFactors b ω hF wt fast lift
    (fun j => realChartSubstitute chart (H.slow j)) H.rat n

variable {F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase}

theorem invariant_outer {n : ℕ} (H : State n) :
    ∀ t ∈ H.K, ∀ j ≤ n,
      F.realSymbolGradeEvaluation b ω hF wt j t
        (H.outer.1⁻¹ * Z * H.outer.2⁻¹).coord ∈ fast.baseChange ℝ := by
  dsimp only [outer]
  have h := H.invariant
  dsimp only at h
  with_reducible exact h

end FullChartFiniteHistory
end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X M : Type} [LieRing M] [LieAlgebra ℚ M]
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (budget : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "quotientReal" => ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

omit [Fintype η] in

theorem fullChart_grade_quotient_of_low_value
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (K : η → Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J k)) → ℝ))
    (slow rat : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ quotientReal)
    (hvalue : ∀ (u : X → ℝ) (z : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ),
      (∀ i, z ∈ K i) →
      eval₂ (Sum.elim u z) (lowTaggedVectorRestrict J k
        (F.realSymbolGradeQuotientPolynomial b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord)) =
        eval₂ (Sum.elim u z) (realChartSubstitute
          (normalizedRealPolynomialChart (fun i => (N i : ℝ))
            (majorTranslationTopCoordinates (lowTaggedWeight J k)
              (fun i => lowTaggedPolynomial J k poly i - MvPolynomial.C (c i)))) slow) +
          eval₂ (Sum.elim u z) rat) :
    ∀ t ∈ fullTaggedGradedBaseIntersection J k K₀ K,
      fast.mkQ.baseChange ℝ
        (F.realSymbolGradeEvaluation b ω hF wt k t (left⁻¹ * Z * right⁻¹).coord) =
        eval₂ t (realChartSubstitute chart (lowTaggedVectorExtend J k slow)) +
          eval₂ t (lowTaggedVectorExtend J k rat) := by
  let P := F.realSymbolGradeQuotientPolynomial b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord
  let lowchart := normalizedRealPolynomialChart (fun i => (N i : ℝ))
    (majorTranslationTopCoordinates (lowTaggedWeight J k)
      (fun i => lowTaggedPolynomial J k poly i - MvPolynomial.C (c i)))
  have hP : DegreeLE wt k P := by
    rw [degreeLE_iff]
    intro α hα
    by_contra hle
    have hz := F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF wt fast k
      (left⁻¹ * Z * right⁻¹).coord α (ne_of_gt (Nat.lt_of_not_ge hle))
    exact Finsupp.mem_support_iff.mp hα hz
  have hquotLow : ∀ t ∈ fullTaggedGradedBaseIntersection J k K₀ K,
      fast.mkQ.baseChange ℝ
        (F.realSymbolGradeEvaluation b ω hF wt k t (left⁻¹ * Z * right⁻¹).coord) =
        eval₂ t (lowTaggedVectorExtend J k (realChartSubstitute lowchart slow)) +
          eval₂ t (lowTaggedVectorExtend J k rat) := by
    intro t ht
    have h := hvalue (fun i => t (Sum.inl i))
      (fun b => t (lowTaggedVariableEmbedding J k (Sum.inr b))) ht.2
    have hsplit : Sum.elim (fun i => t (Sum.inl i))
        (fun b => t (lowTaggedVariableEmbedding J k (Sum.inr b))) =
        t ∘ lowTaggedVariableEmbedding J k := by
      funext i
      cases i <;> rfl
    rw [hsplit] at h
    rw [← F.realSymbolGradeQuotientPolynomial_eval,
      lowTaggedVectorRestrict_eval₂ J k _ hP, lowTaggedVectorExtend_eval₂,
      lowTaggedVectorExtend_eval₂]
    with_reducible exact h
  intro t ht
  have h := hquotLow t ht
  dsimp only [lowchart] at h
  simp only [lowTaggedVectorExtend_majorChart J k poly c (fun i => (N i : ℝ)) slow] at h
  with_reducible exact h

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoundedCertifiedFullChartMajorIteration
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}

namespace CertifiedFullChartFiniteHistory

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)]
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (Bphase : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase

variable {F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase}

theorem invariant_outer {n : ℕ} (H : State n) :
    ∀ t ∈ H.K, ∀ j ≤ n,
      F.realSymbolGradeEvaluation b ω hF wt j t
        (H.outer.1⁻¹ * Z * H.outer.2⁻¹).coord ∈ fast.baseChange ℝ := by
  dsimp only [outer]
  have h := H.invariant
  dsimp only at h
  with_reducible exact h

end CertifiedFullChartFiniteHistory
end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TerminalChartSlowEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem FullChartAdmissibleStageCorrection.mono_budget
    {m : ℕ} {X : Type} {ι L η : Type*}
    [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
    {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
    {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
    {J : Fin m → Type} [∀ j, Fintype (J j)] {k : ℕ}
    {fast : Submodule ℚ F.AssociatedGraded}
    {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
    {lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded}
    {Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    {K₀ : Set (X ⊕ (Σ j, J j) → ℝ)}
    {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
    {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ}
    {budget budget' : ℝ} {q : ℕ} {K' : Set (X ⊕ (Σ j, J j) → ℝ)}
    {pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
      VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
    (h : FullChartAdmissibleStageCorrection F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget q K' pair)
    (hle : budget ≤ budget') :
    FullChartAdmissibleStageCorrection F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget' q K' pair := by
  obtain ⟨hShom, hRhom, hSdeg, hRdeg, hq, hqbound, hsub, hdilation, hretain,
    hslow, hgrid, hnext, horigin, hcertificate, hidentity⟩ := h
  refine ⟨hShom, hRhom, hSdeg, hRdeg, hq, ?_, hsub, hdilation, hretain,
    ?_, hgrid, hnext, horigin, hcertificate.monoB hle, hidentity⟩
  · exact hqbound.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg (Fintype.card η))))
  · exact fun α i => (hslow α i).trans (Real.exp_le_exp.mpr hle)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeQuotientPolynomial realSymbolGradeEvaluation restrictedMajorCorrection

variable {m : ℕ} {X : Type}
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (budget : ℝ)

theorem certified_basis_envelope {p : ℝ} (hp : 0 ≤ p) {a : ℕ} (ha : 254 ≤ a) :
    Real.exp (((p + 2) ^ 2 + 2) ^ 63) ≤ Real.exp ((p + a) ^ a) ∧
      Real.exp ((p + 2) ^ 254) ≤ Real.exp ((p + a) ^ a) := by
  have hbase : 1 ≤ p + 2 := by linarith
  have hshift : p + 2 ≤ p + a := by
    have : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 2 ≤ a by omega)
    linarith
  have hpow (n : ℕ) (hn : n ≤ a) : (p + 2) ^ n ≤ (p + a) ^ a :=
    (pow_le_pow_right₀ hbase hn).trans (pow_le_pow_left₀ (by positivity) hshift a)
  refine ⟨Real.exp_le_exp.mpr ?_, Real.exp_le_exp.mpr (hpow 254 ha)⟩
  exact (show ((p + 2) ^ 2 + 2) ^ 63 ≤ (p + 2) ^ 252 by
    simpa using shifted_power_budget_le hp 2 63).trans (hpow 252 (by omega))

theorem vector_correction_cover_on_set
    {A B V α : Type*} [AddCommGroup V] [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]
    (Kbase : Submodule ℝ (B → ℝ)) (K : Set (A ⊕ B → ℝ))
    (hset : K = {t | (fun z => t (Sum.inr z)) ∈ Kbase})
    (f₁ f₂ f₃ : α → VectorPolynomial (A ⊕ B) ℚ V)
    (admissible : α → Prop) {count : ℕ} (candidate : Fin count → α)
    (hcover : ∀ a, admissible a → ∃ j, ∀ (u : A → ℝ) (v : B → ℝ), v ∈ Kbase →
      eval₂ (Sum.elim u v) (f₁ (candidate j)) = eval₂ (Sum.elim u v) (f₁ a) ∧
      eval₂ (Sum.elim u v) (f₂ (candidate j)) = eval₂ (Sum.elim u v) (f₂ a) ∧
      eval₂ (Sum.elim u v) (f₃ (candidate j)) = eval₂ (Sum.elim u v) (f₃ a)) :
    ∀ a, admissible a → ∃ j, ∀ t ∈ K,
      eval₂ t (f₁ (candidate j)) = eval₂ t (f₁ a) ∧
      eval₂ t (f₂ (candidate j)) = eval₂ t (f₂ a) ∧
      eval₂ t (f₃ (candidate j)) = eval₂ t (f₃ a) := by
  intro a ha
  obtain ⟨j, hj⟩ := hcover a ha
  refine ⟨j, ?_⟩
  intro t ht
  have ht' : (fun z => t (Sum.inr z)) ∈ Kbase := by
    rw [hset] at ht
    exact ht
  have h := hj (fun i => t (Sum.inl i)) (fun z => t (Sum.inr z)) ht'
  have heq : Sum.elim (fun i => t (Sum.inl i)) (fun z => t (Sum.inr z)) = t := by
    funext i
    cases i <;> rfl
  simpa only [heq] using h

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartBudgetedTreeBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeQuotientPolynomial realSymbolGradeEvaluation restrictedMajorCorrection
  

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (budget : ℝ)

theorem stage_branch_numeric {p budget : ℝ} {r a : ℕ}
    (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p) (hb : budget ≤ p) (ha : 254 ≤ a) :
    (r : ℝ) * budget ≤ (p + a) ^ a ∧ budget ≤ (p + a) ^ a := by
  have ha2 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 2 ≤ a by omega)
  have hbase : 1 ≤ p + a := by linarith
  have hshift : p ≤ p + a := le_add_of_nonneg_right (Nat.cast_nonneg a)
  have hpower : p ^ 2 ≤ (p + a) ^ a :=
    (pow_le_pow_left₀ hp hshift 2).trans (pow_le_pow_right₀ hbase (by omega))
  have hprod : (r : ℝ) * budget ≤ p * p :=
    (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg r)).trans
      (mul_le_mul_of_nonneg_right hr hp)
  refine ⟨hprod.trans (by simpa only [pow_two] using hpower), ?_⟩
  exact hb.trans (hshift.trans (by simpa only [pow_one] using
    (pow_le_pow_right₀ hbase (show 1 ≤ a by omega))))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BufferedSampledCurrentGradePhase
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} {X : Type} (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)

noncomputable def majorPhaseNearestLift (u : X → ℤ) :
    Fin (Fintype.card (LowTaggedIndex J k)) → ℤ :=
  nearestIntegerLift (fun i => MvPolynomial.eval (fun x => (u x : ℝ))
    (lowTaggedPolynomial J k poly i) - c i)

end VectorPolynomial
end Erdos3

end

end OAI
end


