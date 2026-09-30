-- Prove2me | Definitions.Def_PhilipponMultiplicity_SectionFive
-- name    : PhilipponMultiplicity_SectionFive
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-23T20:22:55.158186+00:00
-- url     : https://prove2.me/theorems/bd16ec21-5d65-4796-8867-24481b68da5a
-- title:
--   The concrete section-five ideal chain and selected component
-- statement:
--   Source input polynomial and contact data, genuine bounded translation atlases, the explicit chain I₀ = I(G), I₁ = (I(G),P) and later operator-generated ideals; selection of a common minimal prime of maximal dimension at a stable index; its actual zero locus and set stabilizer. The stabilizer closedness is setup data. Construction existence and all three Lemma 5.1 conclusions remain theorem obligations.
--
--   Compiled, admission-free definition bundle. Theorems asserting its substantive properties remain open targets in the full-paper goal.
-- source:
--   Philippon 1986, §§2–5; 1987 corrections/addenda. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_Operators
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Differential

/-!
Concrete data selected in section five: a polynomial, bounded polynomial
translation atlases, the resulting ideal chain, and a common component of
maximal dimension. Existence of these selections and closedness of the
stabilizer are separate geometric obligations. None of the three conclusions
of Lemma 5.1 is a field of these structures.
-/

set_option autoImplicit false
open scoped BigOperators Pointwise
noncomputable section

namespace PhilipponMultiplicity

universe u
variable {K : Type u} [NontriviallyNormedField K]

def idealZeroLocusOnGroup (G : EmbeddedGroupProduct K)
    (I : Ideal G.CoordinateRing) : Set G.Point :=
  {x | ∀ P ∈ I, G.ambient.eval P (G.embedding x) = 0}

/-- Stabilizer of an actual subset under translation. -/
def setStabilizer (G : EmbeddedGroupProduct K) (V : Set G.Point) : AddSubgroup G.Point :=
  AddAction.stabilizer G.Point V

/-- The input from Theorem 2.1 together with the actual bounded coordinate
presentations used to construct its ideals. -/
structure SectionFiveInput (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) where
  samplingSet : Finset G.Point
  zero_mem : 0 ∈ samplingSet
  contactParameter : ℕ
  degrees : G.FactorIndex → ℕ
  polynomial : G.CoordinateRing
  polynomial_ne_zero : polynomial ≠ 0
  polynomial_homogeneous : IsMultihomogeneousOfDegree G polynomial degrees
  contact : ∀ g ∈ sumset samplingSet G.dimension,
    ((G.dimension * contactParameter + 1 : ℕ) : WithTop ℕ) ≤
      vanishingOrder A polynomial g
  coordinateBounds : G.FactorIndex → ℕ
  coordinateBounds_pos : ∀ i, 1 ≤ coordinateBounds i
  atlas : ∀ g : G.Point, TranslationAtlas A g
  atlas_bound : ∀ g : G.Point, (atlas g).IsBoundedBy coordinateBounds

def SectionFiveInput.scaledDegrees {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}
    (C : SectionFiveInput G A) : G.FactorIndex → ℕ :=
  fun i => C.coordinateBounds i * C.degrees i

/-- The source sets I₀ = I(G) and I₁ = (I(G), P) explicitly. For r ≥ 2
use its displayed polynomial-operator generators, without assuming that
raw chart substitutions at order zero equal P as an unretained ideal. -/
def SectionFiveInput.idealChain {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}
    (C : SectionFiveInput G A) : ℕ → Ideal G.CoordinateRing
  | 0 => G.vanishingIdeal Set.univ
  | 1 => G.vanishingIdeal Set.univ ⊔ Ideal.span {C.polynomial}
  | r + 2 => G.vanishingIdeal Set.univ ⊔ Ideal.span
      {Q | ∃ g ∈ sumset C.samplingSet (r + 1),
        ∃ a : (C.atlas g).Index, ∃ order : ℕ,
          order ≤ (r + 1) * C.contactParameter ∧
            ∃ directions : Fin order → Fin A.parameterDimension,
              Q = polynomialOperator ((C.atlas g).chart a) order directions C.polynomial}

/-- The common component selected on p. 380. The dimension equality and
maximal-component selection describe the source's setup, not the counting,
differential-containment, or incomplete-definition conclusions. -/
structure SectionFiveConstruction (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    extends SectionFiveInput G A where
  index : ℕ
  index_le : index ≤ G.dimension
  dimension_stable :
    varietyDimension G (idealZeroLocusOnGroup G (toSectionFiveInput.idealChain index)) =
      varietyDimension G (idealZeroLocusOnGroup G (toSectionFiveInput.idealChain (index + 1)))
  selectedPrime : PrimeSpectrum G.CoordinateRing
  minimal_at_index : selectedPrime.asIdeal ∈ (toSectionFiveInput.idealChain index).minimalPrimes
  minimal_at_next : selectedPrime.asIdeal ∈ (toSectionFiveInput.idealChain (index + 1)).minimalPrimes
  meets_group : ComponentMeetsGroup G selectedPrime.asIdeal
  maximal_dimension :
    varietyDimension G (idealZeroLocusOnGroup G selectedPrime.asIdeal) =
      varietyDimension G (idealZeroLocusOnGroup G (toSectionFiveInput.idealChain index))
  stabilizer_closed : @IsClosed _ G.zariskiTopology
    (setStabilizer G (idealZeroLocusOnGroup G selectedPrime.asIdeal) : Set G.Point)

def SectionFiveConstruction.chosenIdeal {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}
    (C : SectionFiveConstruction G A) : Ideal G.CoordinateRing :=
  C.toSectionFiveInput.idealChain C.index

def SectionFiveConstruction.componentPrime {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}
    (C : SectionFiveConstruction G A) : Ideal G.CoordinateRing :=
  C.selectedPrime.asIdeal

def SectionFiveConstruction.component {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}
    (C : SectionFiveConstruction G A) : Set G.Point :=
  idealZeroLocusOnGroup G C.componentPrime

def SectionFiveConstruction.stabilizer {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}
    (C : SectionFiveConstruction G A) : AlgebraicSubgroup G where
  toAddSubgroup := setStabilizer G C.component
  isClosed := C.stabilizer_closed

end PhilipponMultiplicity


