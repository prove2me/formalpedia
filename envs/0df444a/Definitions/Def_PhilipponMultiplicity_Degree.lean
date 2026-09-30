-- Prove2me | Definitions.Def_PhilipponMultiplicity_Degree
-- name    : PhilipponMultiplicity_Degree
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-23T20:18:00.314275+00:00
-- url     : https://prove2.me/theorems/82b475ff-e64c-4fe9-81d7-6ba21b4bd404
-- title:
--   Geometric Hilbert forms and incomplete definitions
-- statement:
--   Hilbert forms and dimensions derived from actual vanishing ideals; mixed degrees; source incomplete-definition predicates using actual minimal primes and localized quotient lengths, including the corrected lower-bound convention. Comparison with the source geometric definitions remains a proof obligation.
--
--   Compiled, admission-free definition bundle. Theorems asserting its substantive properties remain open targets in the full-paper goal.
-- source:
--   Philippon 1986, §§2–5; 1987 corrections/addenda. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_Hilbert

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity

universe u
variable {K : Type u} [Field K]

def IsMultihomogeneousIdeal (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing) : Prop :=
  Hilbert.IsHomogeneousIdeal K M.factorCount M.ambientDimension I

def IsMultihomogeneousOfDegreeAtMost (M : MultiProjectiveSpace K)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) : Prop :=
  Hilbert.IsHomogeneousOfDegreeAtMost K M.factorCount M.ambientDimension P D

abbrev MaximalOpenLocus (M : MultiProjectiveSpace K) :=
  TopologicalSpace.Opens (MaximalSpectrum M.CoordinateRing)

def componentHilbertSum (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing)
    (U : MaximalOpenLocus M) (D : M.FactorIndex → ℕ) : ℚ :=
  Hilbert.componentSum K M.factorCount M.ambientDimension I U D

def IsLocallyCohenMacaulayOn (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (U : MaximalOpenLocus M) : Prop :=
  Hilbert.IsLocallyCohenMacaulayOn K M.factorCount M.ambientDimension I U

def hilbertDegreeForm (G : EmbeddedGroupProduct K) (V : Set G.Point)
    (D : G.FactorIndex → ℕ) : ℝ :=
  (Hilbert.degreeValue K G.factorCount G.ambient.ambientDimension (G.vanishingIdeal V) D : ℝ)

def varietyDimension (G : EmbeddedGroupProduct K) (V : Set G.Point) : ℕ :=
  (Hilbert.hilbertPolynomial K G.factorCount G.ambient.ambientDimension
    (G.vanishingIdeal V)).totalDegree

def EmbeddedCommutativeGroup.dimension (E : EmbeddedCommutativeGroup K) : ℕ :=
  (Hilbert.hilbertPolynomial K 1 (fun _ => E.ambientDimension)
    ((projectiveSpace K E.ambientDimension).vanishingIdeal
      ((fun x => fun _ => x) '' E.carrier))).totalDegree

def EmbeddedGroupProduct.dimension (G : EmbeddedGroupProduct K) : ℕ :=
  ∑ i, (G.factor i).dimension

def mixedDegree (G : EmbeddedGroupProduct K) (V : Set G.Point)
    (a : G.FactorIndex → ℕ) : ℝ :=
  if ∑ i, a i = varietyDimension G V then
    (((Hilbert.hilbertPolynomial K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal V)).coeff (Finsupp.equivFunOnFinite.symm a) : ℚ) : ℝ) *
      ∏ i, ((a i).factorial : ℝ)
  else 0

/-- A component meets G when its equations vanish at some genuine group point. -/
def ComponentMeetsGroup (G : EmbeddedGroupProduct K) (q : Ideal G.CoordinateRing) : Prop :=
  ∃ x : G.Point, ∀ P ∈ q, G.ambient.eval P (G.embedding x) = 0

/-- Source Definition 3.5(1), expressed through the actual minimal primes. -/
def IncompletelyDefines (G : EmbeddedGroupProduct K) (I : Ideal G.CoordinateRing)
    (V : Set G.Point) : Prop :=
  (V = {x | ∀ P ∈ G.vanishingIdeal V, G.ambient.eval P (G.embedding x) = 0}) ∧
  ∀ q ∈ (G.vanishingIdeal V).minimalPrimes,
    ComponentMeetsGroup G q → q ∈ (G.vanishingIdeal Set.univ ⊔ I).minimalPrimes

/-- Source Definition 3.5(3), with the corrected lower bound on local lengths. -/
def IncompletelyDefinesWithMultiplicityAtLeast (G : EmbeddedGroupProduct K)
    (I : Ideal G.CoordinateRing) (V : Set G.Point) (ell : ℕ) : Prop :=
  IncompletelyDefines G I V ∧
  ∀ q : PrimeSpectrum G.CoordinateRing,
    q.asIdeal ∈ (G.vanishingIdeal V).minimalPrimes → ComponentMeetsGroup G q.asIdeal →
    (ell : ℕ∞) ≤ Hilbert.localLength K G.factorCount G.ambient.ambientDimension
      (G.vanishingIdeal Set.univ ⊔ I) q

/-- Source Definition 3.5(2), retaining equations modulo the group ideal. -/
def HasIncompleteDefinition (G : EmbeddedGroupProduct K) (V : Set G.Point)
    (D : G.FactorIndex → ℕ) : Prop :=
  ∃ I : Ideal G.CoordinateRing,
    IsMultihomogeneousIdeal G.ambient I ∧
    Hilbert.HasEquationsOfDegreeAtMost K G.factorCount G.ambient.ambientDimension
      (G.vanishingIdeal Set.univ) I D ∧ IncompletelyDefines G I V

end PhilipponMultiplicity


