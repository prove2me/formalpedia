-- Prove2me | Definitions.Def_PhilipponMultiplicity_SourceStatements
-- name    : PhilipponMultiplicity_SourceStatements
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-23T20:33:18.69454+00:00
-- url     : https://prove2.me/theorems/d29dfd9d-0153-42e4-997f-9d793a576256
-- title:
--   Full-paper statements — 26 concrete propositions
-- statement:
--   The literal universally closed types of all 13 numbered results, both addenda, and eleven supporting/correction targets. These definitions contain no proofs or theorem imports. The completion goal is their conjunction; none is an arbitrary proposition parameter.
--
--   Compiled, admission-free definition bundle. Theorems asserting its substantive properties remain open targets in the full-paper goal.
-- source:
--   Philippon 1986, §§2–5; 1987 corrections/addenda. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Corollaries
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Differential
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_SectionFive
import Definitions.Def_PhilipponMultiplicity_SectionFour
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Definitions.Def_PhilipponMultiplicity_Support

set_option autoImplicit false
set_option maxRecDepth 4096
open scoped BigOperators Topology
open Filter
namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport
namespace SourceStatements
universe u

/-- The literal universally closed type of `theorem_2_1`. -/
def theorem_2_1 : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K),
    ∃ c : EmbeddedCommutativeGroup K → ℕ,
      (∀ E, 1 ≤ c E) ∧
      ∀ (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
        (sample : Finset G.Point), 0 ∈ sample →
      ∀ (T : ℕ) (D : G.FactorIndex → ℕ) (P : G.CoordinateRing),
        P ≠ 0 → IsMultihomogeneousOfDegree G P D →
        (∀ g ∈ sumset sample G.dimension,
          ((G.dimension * T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P g) →
        ∃ H : AlgebraicSubgroup G,
          H.IsConnected ∧
          HasIncompleteDefinition G H.carrier (fun i => c (G.factor i) * D i) ∧
          (∃ g : G.Point, H.carrier ⊆ translate g (zeroLocusOnGroup G P)) ∧
          ((Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℝ) *
              (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D ≤
            hilbertDegreeForm G Set.univ (fun i => c (G.factor i) * D i))

/-- The literal universally closed type of `corollary_2_2`. -/
def corollary_2_2 : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K),
    ∃ c : ℝ, 0 < c ∧
      ∀ (A : AnalyticSubgroup G), A.dimension = 1 →
      ∀ (sample : Finset G.Point), 0 ∈ sample →
      ∀ (T : ℕ) (D : G.FactorIndex → ℕ) (P : G.CoordinateRing),
        (∀ i, 1 ≤ D i) →
        P ≠ 0 → IsMultihomogeneousOfDegree G P D →
        (∀ g ∈ sumset sample G.dimension,
          ((G.dimension * T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P g) →
        (∀ H : AlgebraicSubgroup G, H.IsConnected → ¬ A.carrier ⊆ H.carrier →
          ∃ r : SourceMixedCodimensionIndex G H,
            c * r.degreeMonomial D ≤
              ((T + 1 : ℕ) : ℝ) * (cosetCount sample H.carrier : ℝ) *
                (mixedDegree G H.carrier r.complementIndex : ℝ)) →
        ∃ g : G.Point, translate g A.carrier ⊆ zeroLocusOnGroup G P

/-- The literal universally closed type of `corollary_2_3`. -/
def corollary_2_3 : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hdisjoint : HasDisjointFactors G),
    ∃ c : ℝ, 0 < c ∧
      ∀ (A : AnalyticSubgroup G) (l : ℕ) (γ : Fin l → G.Point)
        (S : ℝ), 0 ≤ S →
      ∀ (T : ℕ) (D : G.FactorIndex → ℕ) (P : G.CoordinateRing),
        P ≠ 0 → IsMultihomogeneousOfDegree G P D →
        (∀ g ∈ samplingGrid γ ((G.dimension : ℝ) * S),
          ((G.dimension * T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P g) →
        (∀ r : G.FactorIndex → ℕ, (∀ i, r i ≤ (G.factor i).dimension) →
          c * (∏ i, (D i : ℝ) ^ r i) ≤
            ((T + 1 : ℕ) : ℝ) ^ analyticCodimensionMinimum A r *
              S ^ samplingRankMinimum A γ r) →
        ∃ g : G.Point, translate g A.carrier ⊆ zeroLocusOnGroup G P

/-- The literal universally closed type of `lemma_3_1_positive_equation_degrees`. -/
def lemma_3_1_positive_equation_degrees : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hNontrivial : IsNontrivialIdeal M I) (ha : 0 < idealDimension M I)
    (D : M.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i)
    (P : M.CoordinateRing) (hP : M.IsHomogeneous P D)
    (hRegular : IsRegular (Ideal.Quotient.mk I P)),
    (∀ d : M.FactorIndex → ℕ, (∀ i, 1 ≤ d i) →
      idealDegreeValue M (I ⊔ Ideal.span {P}) d = hypersurfaceCoefficientSum M I D d) ∧
    idealDegreeValue M (I ⊔ Ideal.span {P}) D = idealDegreeValue M I D

/-- The literal universally closed type of `lemma_3_2`. -/
def lemma_3_2 : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hNontrivial : IsNontrivialIdeal M I)
    (d : M.FactorIndex → ℕ) (hd : ∀ i, 1 ≤ d i),
    idealDegreeValue M I d = topComponentLengthSum M I d

/-- The literal universally closed type of `proposition_3_3`. -/
def proposition_3_3 : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (M : MultiProjectiveSpace K)
    (I₀ : Ideal M.CoordinateRing) (hI₀ : IsMultihomogeneousIdeal M I₀)
    (m : ℕ) (P : Fin m → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D),
    let I := I₀ ⊔ Ideal.span (Set.range P)
    (componentHilbertSum M I.radical (⊤ : MaximalOpenLocus M) D ≤
      componentHilbertSum M I₀.radical (⊤ : MaximalOpenLocus M) D) ∧
    (∀ U : MaximalOpenLocus M, IsLocallyCohenMacaulayOn M I₀ U →
      componentHilbertSum M I U D ≤ componentHilbertSum M I₀ U D)

/-- The literal universally closed type of `lemma_3_4`. -/
def lemma_3_4 : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (M : MultiProjectiveSpace K)
    (V : ∀ i : M.FactorIndex, ProjectiveSubvariety K (M.ambientDimension i))
    (d : M.FactorIndex → ℕ) (hd : ∀ i, 1 ≤ d i),
    locusDegreeValue M (productCarrier M V) d =
      ((locusDimension M (productCarrier M V)).factorial : ℚ) /
        (∏ i, ((V i).dimension.factorial : ℚ)) *
        (∏ i, (V i).degree) * ∏ i, (d i : ℚ) ^ (V i).dimension

/-- The literal universally closed type of `proposition_4_3`. -/
def proposition_4_3 : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (g g' : G.Point) (k k' : ℕ) (I : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I)
    (atlas atlas' : TranslationAtlas A g),
    (retainedPolynomialOperatorIdeal atlas k I =
      retainedPolynomialOperatorIdeal atlas' k I) ∧
    (∀ other : TranslationAtlas A g', ∀ combined : TranslationAtlas A (g + g'),
      retainedPolynomialOperatorIdeal atlas k
        (retainedPolynomialOperatorIdeal other k' I) =
      retainedPolynomialOperatorIdeal combined (k + k') I)

/-- The literal universally closed type of `proposition_4_4`. -/
def proposition_4_4 : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (g h : G.Point) (k : ℕ) (I : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) (atlas : TranslationAtlas A g),
    (∀ Q ∈ retainedPolynomialOperatorIdeal atlas k I,
      G.ambient.eval Q (G.embedding h) = 0) ↔
    (∀ Q ∈ I, (k : WithTop ℕ) < vanishingOrder A Q (g + h))

/-- The literal universally closed type of `lemma_4_5`. -/
def lemma_4_5 : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (c : G.FactorIndex → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hbound : TranslationDegreeBound G c)
    (g : G.Point) (V : GroupSubvariety G),
    varietyDimension G V.carrier = varietyDimension G (translate g V.carrier) ∧
    ∀ D : G.FactorIndex → ℕ, (∀ i, 1 ≤ D i) →
      hilbertDegreeForm G V.carrier D ≤
        hilbertDegreeForm G (translate g V.carrier) (fun i => c i * D i)

/-- The literal universally closed type of `lemma_4_6`. -/
def lemma_4_6 : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (H : AlgebraicSubgroup G) (hH : H.IsConnected) (g : G.Point)
    (directions : Fin (analyticCodimension A H.carrier) → Fin A.parameterDimension)
    (htransverse : IsTransverseCoordinateFamily A H directions)
    (chart : TranslationChart A (0 : G.Point))
    (hmeets : (translate g H.carrier ∩ chart.domain).Nonempty),
    ∃ Q : Fin (analyticCodimension A H.carrier) → G.CoordinateRing,
      (∀ j, Q j ∈ G.vanishingIdeal (translate g H.carrier)) ∧
      (∀ i j,
        polynomialOperator chart 1 (fun _ => directions i) (Q j) ∉
          G.vanishingIdeal (translate g H.carrier) ↔ i = j)

/-- The literal universally closed type of `proposition_4_7`. -/
def proposition_4_7 : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (H : AlgebraicSubgroup G) (hH : H.IsConnected) (g : G.Point)
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (T : ℕ)
    (hcomponent : IncompletelyDefines G I (translate g H.carrier))
    (hprolongation : IncompletelyDefines G (differentialIdeal A 0 T I)
      (translate g H.carrier)),
    IncompletelyDefinesWithMultiplicityAtLeast G I (translate g H.carrier)
      (Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier))

/-- The literal universally closed type of `lemma_5_1`. -/
def lemma_5_1 : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (C : SectionFiveConstruction G A),
    (∀ g ∈ C.samplingSet,
      differentialIdeal A g C.contactParameter C.chosenIdeal ≤ C.componentPrime) ∧
    (let H := C.stabilizer.identityComponent
      let s := analyticCodimension A H
      (Nat.choose (C.contactParameter + s) s : ℝ) *
          (cosetCount C.samplingSet H : ℝ) * hilbertDegreeForm G H C.degrees ≤
        hilbertDegreeForm G Set.univ C.scaledDegrees) ∧
    (IncompletelyDefines G
      (⨆ v : {x : G.Point // x ∈ C.component}, translatedIdeal G v.1 C.chosenIdeal)
      C.stabilizer.carrier)

/-- The literal universally closed type of `addendum_strengthened_vanishing`. -/
def addendum_strengthened_vanishing : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K),
    ∃ c : EmbeddedCommutativeGroup K → ℕ,
      (∀ E, 1 ≤ c E) ∧
      ∀ (G : EmbeddedGroupProduct K), 0 < G.dimension →
      ∀ (A : AnalyticSubgroup G)
        (sample : Finset G.Point), 0 ∈ sample →
      ∀ (T : ℕ) (D : G.FactorIndex → ℕ) (P : G.CoordinateRing),
        P ≠ 0 → IsMultihomogeneousOfDegree G P D →
        (∀ g ∈ sumset sample G.dimension,
          ((G.dimension * T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P g) →
        ∃ H : AlgebraicSubgroup G,
          H.IsConnected ∧
          HasIncompleteDefinition G H.carrier (fun i => c (G.factor i) * D i) ∧
          (∀ g ∈ sample, translate g H.carrier ⊆ zeroLocusOnGroup G P) ∧
          ((Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℝ) *
              (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D ≤
            hilbertDegreeForm G Set.univ (fun i => c (G.factor i) * D i))

/-- The literal universally closed type of `addendum_converse`. -/
def addendum_converse : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hn : 0 < G.dimension) (A : AnalyticSubgroup G)
    (sample : Finset G.Point) (hsample : 0 ∈ sample) (T : ℕ) (D : G.FactorIndex → ℕ)
    (hD : ∀ i, hilbertDegreeForm G Set.univ (fun _ => 1) ≤ (D i : ℝ))
    (H : AlgebraicSubgroup G)
    (hbound :
      (Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℝ) *
          (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D ≤
        (1 / ((4 : ℝ) ^ G.dimension * (G.dimension.factorial : ℝ))) *
          hilbertDegreeForm G Set.univ D),
    ∃ P : G.CoordinateRing,
      P ≠ 0 ∧ IsMultihomogeneousOfDegree G P D ∧
      (∀ g ∈ sample, ∀ h ∈ H.carrier,
        ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h)) ∧
      (∃ x : G.Point, x ∉ zeroLocusOnGroup G P)

/-- The literal universally closed type of `section_three_foundations`. -/
def section_three_foundations : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (M : MultiProjectiveSpace K),
    -- The actual Hilbert polynomial, its support, coefficients, and dimension.
    (∀ I : Ideal M.CoordinateRing, IsMultihomogeneousIdeal M I →
      (∃ P, Hilbert.IsHilbertPolynomial K M.factorCount M.ambientDimension I P) ∧
      (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I = 0 ↔
        ¬ IsNontrivialIdeal M I) ∧
      (IsNontrivialIdeal M I →
        ringKrullDim (M.CoordinateRing ⧸ relevantRadicalCore M I) =
          ((idealDimension M I + M.factorCount : ℕ) : WithBot ℕ∞)) ∧
      (∀ α : M.FactorIndex → ℕ, ∃ n : ℕ, idealMixedDegree M I α = (n : ℚ)) ∧
      (∀ α : M.FactorIndex → ℕ, (∃ i, M.ambientDimension i < α i) →
        idealMixedDegree M I α = 0) ∧
      (∀ d : M.FactorIndex → ℕ, idealDegreeValue M I d = degreeCoefficientSum M I d) ∧
      Nonempty (PrimaryDecomposition M I)) ∧
    -- Equal-dimensional Hilbert-degree monotonicity following Lemma 3.2.
    (∀ I J : Ideal M.CoordinateRing,
      IsMultihomogeneousIdeal M I → IsMultihomogeneousIdeal M J →
      IsNontrivialIdeal M I → IsNontrivialIdeal M J → I ≤ J →
      idealDimension M I = idealDimension M J →
      ∀ d : M.FactorIndex → ℕ, (∀ i, 1 ≤ d i) →
        idealDegreeValue M J d ≤ idealDegreeValue M I d) ∧
    -- Associated primes of a genuine minimal primary decomposition.
    (∀ I : Ideal M.CoordinateRing, ∀ D : PrimaryDecomposition M I,
      associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) =
        Set.range (fun i => (D.component i).radical)) ∧
    -- Fact A, using the actual canonical isolated primary components.
    (∀ J J' : Ideal M.CoordinateRing,
      IsMultihomogeneousIdeal M J → IsMultihomogeneousIdeal M J' →
      IsNontrivialIdeal M J → IsNontrivialIdeal M J' → J ≤ J' →
      ∀ b : ℕ, (dimensionAtLeast M J (b + 1)).radical =
          (dimensionAtLeast M J' (b + 1)).radical →
        dimensionSlice M J b ≤ dimensionSlice M J' b) ∧
    -- Facts B and C: the canonical partition of the isolated components.
    (∀ J I : Ideal M.CoordinateRing, J ≤ I →
      (∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I),
        ∃ p ∈ J.minimalPrimes, p ≤ q) ∧
      (∀ p ∈ J.minimalPrimes,
        p ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → ¬ I ≤ p) ∧
      (∀ P ∈ I,
        (J ⊔ Ideal.span {P}).radical =
          (discardedPart M J I ⊔ Ideal.span {P}).radical ⊓ (retainedPart M J I).radical ∧
        ∀ q ∈ J.minimalPrimes,
          q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
          q ∈ (J ⊔ Ideal.span {P}).minimalPrimes)) ∧
    -- Fact D, slightly stronger: retain all isolated components, even irrelevant ones.
    (∀ I : Ideal M.CoordinateRing, ∀ D : PrimaryDecomposition M I,
      ∃ Q ∈ D.embeddedIntersection,
        IsRegular (Ideal.Quotient.mk D.isolatedIntersection Q)) ∧
    -- Fact E: embedded supports avoid the Cohen–Macaulay locus; prime avoidance.
    (∀ I : Ideal M.CoordinateRing, ∀ D : PrimaryDecomposition M I,
      ∀ U : MaximalOpenLocus M, IsLocallyCohenMacaulayOn M I U →
      (∀ i : Fin D.count, D.IsEmbedded i →
        ¬ Hilbert.MeetsOpen K M.factorCount M.ambientDimension (D.component i).radical U) ∧
      (∀ L : Ideal M.CoordinateRing,
        (∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ L),
          Hilbert.MeetsOpen K M.factorCount M.ambientDimension q U) →
        (∀ i : Fin D.count, D.IsEmbedded i →
          ∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ L),
            ¬ (D.component i).radical ≤ q) ∧
        ∃ Q ∈ D.embeddedIntersection, IsRegular (Ideal.Quotient.mk L Q)))

/-- The literal universally closed type of `mixed_degree_geometry`. -/
def mixed_degree_geometry : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (M : MultiProjectiveSpace K) (V : Set M.Point)
    (hV : @IsLocallyClosed _ M.zariskiTopology V)
    (hirr : @IsIrreducible _ M.zariskiTopology V)
    (α : M.FactorIndex → ℕ) (hα : ∀ i, α i ≤ M.ambientDimension i)
    (hsum : ∑ i, α i = locusDimension M V),
    (∀ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
      (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) →
      (linearSlice M V L).Finite →
      ((linearSlice M V L).ncard : ℚ) ≤ idealMixedDegree M (M.vanishingIdeal V) α) ∧
    (∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
      (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
      (linearSlice M V L).Finite ∧
      ((linearSlice M V L).ncard : ℚ) = idealMixedDegree M (M.vanishingIdeal V) α)

/-- The literal universally closed type of `section_three_counterexample`. -/
def section_three_counterexample : Prop :=
  let M := BezoutBoundary.ambient
    let I₀ := BezoutBoundary.initialIdeal
    let I := BezoutBoundary.sectionIdeal
    let Q₁ := BezoutBoundary.firstComponent
    let Q₂ := BezoutBoundary.secondComponent
    let g := BezoutBoundary.nonradicalWitness
    IsMultihomogeneousIdeal M I₀ ∧ IsNontrivialIdeal M I₀ ∧
    M.IsHomogeneous BezoutBoundary.firstEquation (fun _ => 1) ∧
    M.IsHomogeneous BezoutBoundary.secondEquation (fun _ => 1) ∧
    g ∉ I₀ ∧ g ^ 2 ∈ I₀ ∧ g ∈ I₀.radical ∧ I₀.radical ≠ I₀ ∧ ¬ I₀.IsPrime ∧
    idealDimension M I₀ = 2 ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension I₀ =
      BezoutBoundary.expectedInitialHilbertPolynomial ∧
    idealDegreeValue M I₀ (fun _ => 1) = 4 ∧
    I = BezoutBoundary.reducedSectionGenerators ∧ I = Q₁ ⊓ Q₂ ∧
    Q₁.IsPrimary ∧ Q₂.IsPrimary ∧ Q₁.radical ≠ Q₂.radical ∧
    I.minimalPrimes = {Q₁.radical, Q₂.radical} ∧
    Hilbert.IsRelevant ℂ M.factorCount M.ambientDimension Q₁.radical ∧
    Hilbert.IsRelevant ℂ M.factorCount M.ambientDimension Q₂.radical ∧
    idealDimension M Q₁ = 0 ∧ idealDimension M Q₂ = 0 ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension Q₁ = 4 ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension Q₂ = 2 ∧
    idealDegreeValue M Q₁ (fun _ => 1) = 4 ∧
    idealDegreeValue M Q₂ (fun _ => 1) = 2 ∧
    componentHilbertSum M I (⊤ : MaximalOpenLocus M) (fun _ => 1) = 6 ∧
    componentHilbertSum M I₀ (⊤ : MaximalOpenLocus M) (fun _ => 1) = 4 ∧
    componentHilbertSum M I₀ (⊤ : MaximalOpenLocus M) (fun _ => 1) <
      componentHilbertSum M I (⊤ : MaximalOpenLocus M) (fun _ => 1) ∧
    ¬ IsLocallyCohenMacaulayOn M I₀ (⊤ : MaximalOpenLocus M)

/-- The literal universally closed type of `lemma_3_1_zero_degree_counterexample`. -/
def lemma_3_1_zero_degree_counterexample : Prop :=
  let M := ZeroDegreeBoundary.ambient
    let I := ZeroDegreeBoundary.ideal
    let P := ZeroDegreeBoundary.polynomial
    let D := ZeroDegreeBoundary.equationDegrees
    let J := I ⊔ Ideal.span {P}
    I = Ideal.span {ZeroDegreeBoundary.secondCoordinate 1} ⊓
      Ideal.span {ZeroDegreeBoundary.firstCoordinate 1, ZeroDegreeBoundary.firstCoordinate 2} ∧
    IsMultihomogeneousIdeal M I ∧ IsNontrivialIdeal M I ∧
    M.IsHomogeneous P D ∧ IsRegular (Ideal.Quotient.mk I P) ∧
    idealDimension M I = 2 ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension I =
      ZeroDegreeBoundary.expectedHilbertPolynomial ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension J = 1 ∧
    (∀ d : M.FactorIndex → ℕ, idealDegreeValue M I d = (d (0 : Fin 2) : ℚ) ^ 2) ∧
    (∀ d : M.FactorIndex → ℕ, idealDegreeValue M J d = 1) ∧
    hypersurfaceCoefficientSum M I D (fun _ => 1) = 0 ∧
    idealDegreeValue M J (fun _ => 1) ≠ hypersurfaceCoefficientSum M I D (fun _ => 1) ∧
    idealDegreeValue M J D ≠ idealDegreeValue M I D

/-- The literal universally closed type of `translation_operator_foundations`. -/
def translation_operator_foundations : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K),
    (∃ c : EmbeddedCommutativeGroup K → ℕ, (∀ E, 1 ≤ c E) ∧
      ∀ (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point),
        ∃ atlas : TranslationAtlas A g, atlas.IsBoundedBy (fun i => c (G.factor i))) ∧
    (∀ (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point)
        (chart : TranslationChart A g) (order : ℕ)
        (directions : Fin order → Fin A.parameterDimension),
      (∀ (P Q : G.CoordinateRing) (a : K),
        polynomialOperator chart order directions (P + Q) =
          polynomialOperator chart order directions P + polynomialOperator chart order directions Q ∧
        polynomialOperator chart order directions (MvPolynomial.C a * P) =
          MvPolynomial.C a * polynomialOperator chart order directions P) ∧
      (∀ (P : G.CoordinateRing) (D : G.FactorIndex → ℕ),
        G.ambient.IsHomogeneous P D →
        G.ambient.IsHomogeneous (polynomialOperator chart order directions P)
          (fun i => chart.degree i * D i))) ∧
    (∀ (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point)
        (chart : TranslationChart A g) (directions : Fin 0 → Fin A.parameterDimension),
      ∃ f : G.CoordinateRing →ₐ[K] G.CoordinateRing,
        ∀ P, f P = polynomialOperator chart 0 directions P) ∧
    (∀ (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point)
        (atlas : TranslationAtlas A g) (T : ℕ)
        (I J : Ideal G.CoordinateRing),
      IsMultihomogeneousIdeal G.ambient I → IsMultihomogeneousIdeal G.ambient J →
      (retainedPolynomialOperatorIdeal atlas T I = differentialIdeal A g T I) ∧
      (I ≤ J → retainedPolynomialOperatorIdeal atlas T I ≤
        retainedPolynomialOperatorIdeal atlas T J) ∧
      (retainedPolynomialOperatorIdeal atlas T (I ⊔ J) =
        retainOnGroup G (retainedPolynomialOperatorIdeal atlas T I ⊔
          retainedPolynomialOperatorIdeal atlas T J))) ∧
    (∀ (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point)
        (atlas : TranslationAtlas A g) (T : ℕ),
      retainedPolynomialOperatorIdeal atlas T (G.vanishingIdeal Set.univ) =
        G.vanishingIdeal Set.univ)

/-- The literal universally closed type of `translation_geometry_remarks`. -/
def translation_geometry_remarks : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K),
    (∀ (G : EmbeddedGroupProduct K) (V : GroupSubvariety G) (g : G.Point),
      translatedIdeal G g (G.vanishingIdeal V.carrier) =
        G.vanishingIdeal (translate (-g) V.carrier)) ∧
    (∀ (G : EmbeddedGroupProduct K), @_root_.IsConnected _ G.zariskiTopology Set.univ →
      TranslationsExtendToClosure G →
      ∀ (V : GroupSubvariety G) (g : G.Point) (D : G.FactorIndex → ℕ),
        (∀ i, 1 ≤ D i) →
        hilbertDegreeForm G V.carrier D = hilbertDegreeForm G (translate g V.carrier) D) ∧
    (∀ E : EmbeddedCommutativeGroup K,
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        ∀ (A : AnalyticSubgroup (singleGroupProduct F)) (g : (singleGroupProduct F).Point),
          ∃ atlas : TranslationAtlas A g, atlas.IsBoundedBy (fun _ => 2))

/-- The literal universally closed type of `analytic_contact_invariance`. -/
def analytic_contact_invariance : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G),
    (∀ (g : G.Point) (P : G.CoordinateRing) (D : G.FactorIndex → ℕ),
      IsMultihomogeneousOfDegree G P D →
      ∀ f : A.ParameterSpace → G.ambient.Variable → K,
        (∀ v, AnalyticAt K (fun z => f z v) 0) →
        (∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∃ hz : z ∈ A.domain,
          ∀ i : G.FactorIndex, ∃ h : (fun j => f z ⟨i, j⟩) ≠ 0,
            Projectivization.mk K (fun j => f z ⟨i, j⟩) h =
              G.embedding (g + A.map ⟨z, hz⟩) i) →
        vanishingOrder A P g = sInf ((fun n : ℕ => (n : WithTop ℕ)) ''
          {n | iteratedFDeriv K n (fun z => MvPolynomial.eval (f z) P) 0 ≠ 0})) ∧
    (∀ H : AlgebraicSubgroup G,
      analyticCodimension A H.carrier ≤ A.dimension ∧
      (analyticCodimension A H.carrier = 0 ↔ A.carrier ⊆ H.carrier) ∧
      ∃ directions : Fin (analyticCodimension A H.carrier) → Fin A.parameterDimension,
        IsTransverseCoordinateFamily A H directions)

/-- The literal universally closed type of `corollary_counting_estimates`. -/
def corollary_counting_estimates : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K),
    (∀ (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G) (T : ℕ),
      (((T + 1 : ℕ) : ℝ) ^ analyticCodimension A H.carrier) /
          (Nat.factorial (analyticCodimension A H.carrier) : ℝ) ≤
        (Nat.choose (T + analyticCodimension A H.carrier)
          (analyticCodimension A H.carrier) : ℝ)) ∧
    (∀ (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G),
      ¬ A.carrier ⊆ H.carrier →
      ∀ (m : ℕ) (γ : Fin m → G.Point) (S : ℝ), 0 ≤ S →
        S ^ samplingQuotientRank γ H ≤
          (((fun x => translate x H.carrier) '' samplingGrid γ S).ncard : ℝ)) ∧
    (∀ (H : AlgebraicSubgroup G) (r : SourceMixedCodimensionIndex G H)
        (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
      (mixedDegree G H.carrier r.complementIndex : ℝ) *
        (Nat.factorial (varietyDimension G H.carrier) : ℝ) /
        (∏ i, (Nat.factorial (r.complementIndex i) : ℝ)) *
        (∏ i, (D i : ℝ) ^ r.complementIndex i) ≤ hilbertDegreeForm G H.carrier D) ∧
    (HasDisjointFactors G → ∃ c : ℝ, 0 < c ∧
      ∀ (H : AlgebraicSubgroup G) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
        0 < hilbertDegreeForm G H.carrier D ∧
        hilbertDegreeForm G Set.univ D / hilbertDegreeForm G H.carrier D ≤
          c * ∏ i, (D i : ℝ) ^ factorCodimension G H i)

/-- The literal universally closed type of `section_five_construction`. -/
def section_five_construction : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G),
    (∀ I : SectionFiveInput G A, ∃ C : SectionFiveConstruction G A,
      C.toSectionFiveInput = I) ∧
    (∀ H : AlgebraicSubgroup G, ∃ H₀ : AlgebraicSubgroup G,
      H₀.carrier = H.identityComponent ∧ H₀.IsConnected ∧
      @IsIrreducible _ G.zariskiTopology H₀.carrier ∧
      ∃ representatives : Finset G.Point,
        (∀ x ∈ representatives, x ∈ H.carrier) ∧
        H.carrier = ⋃ x ∈ representatives, translate x H₀.carrier ∧
        (representatives : Set G.Point).Pairwise (fun x y => Disjoint
          (translate x H₀.carrier) (translate y H₀.carrier))) ∧
    (∀ H : AlgebraicSubgroup G, H.IsConnected →
      @IsIrreducible _ G.zariskiTopology H.carrier) ∧
    (∀ V : GroupSubvariety G,
      @IsClosed _ G.zariskiTopology (setStabilizer G V.carrier : Set G.Point))

/-- The literal universally closed type of `masser_wustholz_recovery`. -/
def masser_wustholz_recovery : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (E : EmbeddedCommutativeGroup K)
    (hn : 0 < (singleGroupProduct E).dimension)
    (hconnected : @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (htranslation : MWTranslationBound (singleGroupProduct E) a)
    (hclosure : ∃ equations : Finset (singleGroupProduct E).CoordinateRing,
      (∀ P ∈ equations, (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => b)) ∧
      groupProjectiveClosure (singleGroupProduct E) =
        {x | ∀ P ∈ equations, (singleGroupProduct E).ambient.eval P x = 0})
    (m D : ℕ) (hm : 1 ≤ m) (hD : 1 ≤ D)
    (γ : Fin m → (singleGroupProduct E).Point) (θ : ℝ)
    (hθ : ((singleGroupProduct E).dimension : ℝ) / m ≤ θ)
    (P : (singleGroupProduct E).CoordinateRing)
    (hP : (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => D)),
    let G := singleGroupProduct E
    let c : ℝ := 1 / ((a : ℝ) ^ G.dimension * (b : ℝ) ^ (E.ambientDimension - G.dimension))
    (∀ x ∈ samplingGrid γ ((G.dimension : ℝ) * ((D : ℝ) / c) ^ θ),
      G.ambient.eval P (G.embedding x) = 0) →
    (∃ x : G.Point, G.ambient.eval P (G.embedding x) ≠ 0) →
    ∃ k r : ℕ, 1 ≤ k ∧ k ≤ m ∧ 1 ≤ r ∧ r ≤ G.dimension ∧
      (m : ℝ) < (k : ℝ) + (r : ℝ) / θ ∧
      ∃ Z : Submodule ℤ (Fin m → ℤ), k ≤ Module.finrank ℤ Z ∧
      ∃ H : AlgebraicSubgroup G, varietyDimension G H.carrier ≤ G.dimension - r ∧
        (∀ σ ∈ Z, integerCombination γ σ ∈ H.carrier) ∧
        (∃ σ : Fin k → Z,
          LinearIndependent ℤ (fun j => (σ j).val) ∧
          ∀ j : Fin k, ∀ i : Fin m,
            |((σ j).val i : ℝ)| ≤ ((D : ℝ) / c) ^ ((r : ℝ) / ((m : ℝ) - j.val))) ∧
        ∃ S : GroupSubvariety G, H.carrier ⊆ S.carrier ∧
          varietyDimension G S.carrier ≤ G.dimension - r ∧
          DefinedByEquations G S.carrier ((D : ℝ) / c)

/-- The literal universally closed type of `source_boundary_counterexamples`. -/
def source_boundary_counterexamples : Prop :=
  (∃ (G : EmbeddedGroupProduct ℂ) (A : AnalyticSubgroup G)
        (H : AlgebraicSubgroup G),
      Subsingleton G.Point ∧ G.dimension = 0 ∧ H.carrier = Set.univ ∧
      A.carrier = {0} ∧ analyticCodimension A H.carrier = 0 ∧
      hilbertDegreeForm G Set.univ (fun _ => 1) = 1 ∧
      hilbertDegreeForm G H.carrier (fun _ => 1) = 1 ∧
      (Nat.choose (0 + analyticCodimension A H.carrier)
          (analyticCodimension A H.carrier) : ℝ) *
        (cosetCount {0} H.carrier : ℝ) * hilbertDegreeForm G H.carrier (fun _ => 1) ≤
        (1 / ((4 : ℝ) ^ G.dimension * (G.dimension.factorial : ℝ))) *
          hilbertDegreeForm G Set.univ (fun _ => 1) ∧
      ¬ ∃ P : G.CoordinateRing,
        (∀ h ∈ H.carrier, (1 : WithTop ℕ) ≤ vanishingOrder A P h) ∧
        (∃ x : G.Point, x ∉ zeroLocusOnGroup G P)) ∧
    (∃ (G : EmbeddedGroupProduct ℂ) (A : AnalyticSubgroup G)
        (sample : Finset G.Point) (P : G.CoordinateRing),
      G.dimension = 0 ∧ sample.card = 2 ∧ 0 ∈ sample ∧ A.carrier = {0} ∧
      P ≠ 0 ∧ IsMultihomogeneousOfDegree G P (fun _ => 1) ∧
      (∀ g ∈ sumset sample G.dimension, vanishingOrder A P g = ⊤) ∧
      ¬ ∃ H : AlgebraicSubgroup G,
        ∀ g ∈ sample, translate g H.carrier ⊆ zeroLocusOnGroup G P) ∧
    (∃ (G : EmbeddedGroupProduct ℂ) (A : AnalyticSubgroup G)
        (P : G.CoordinateRing),
      G.factorCount = 2 ∧ (∀ i, (G.factor i).dimension = 1) ∧
      A.dimension = 1 ∧ P ≠ 0 ∧
      IsMultihomogeneousOfDegree G P (fun i => if i.val = 0 then 1 else 0) ∧
      vanishingOrder A P 0 = 1 ∧
      (∀ c : ℝ, 0 < c → ∀ H : AlgebraicSubgroup G,
        H.IsConnected → ¬ A.carrier ⊆ H.carrier →
        ∃ r : SourceMixedCodimensionIndex G H,
          c * r.degreeMonomial (fun i => if i.val = 0 then 1 else 0) ≤
            (cosetCount {0} H.carrier : ℝ) *
              (mixedDegree G H.carrier r.complementIndex : ℝ)) ∧
      ¬ ∃ g : G.Point, translate g A.carrier ⊆ zeroLocusOnGroup G P)

end SourceStatements
end PhilipponMultiplicity


