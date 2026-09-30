-- Prove2me | Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
-- name    : PhilipponMultiplicity_SectionThreeSupport
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-23T20:30:42.253335+00:00
-- url     : https://prove2.me/theorems/46d941ce-7f8a-4e00-aaa1-46e5cd0e1fbb
-- title:
--   Section 3 — primary decompositions and the printed counterexample
-- statement:
--   Actual finite minimal primary decompositions, dimension slices, relevance and component selections; fixed coordinate ideals and nilpotent witness from the printed counterexample. The witness-square identity and membership are proved without admissions.
--
--   Compiled, admission-free definition bundle. Theorems asserting its substantive properties remain open targets in the full-paper goal.
-- source:
--   Philippon 1986, §§2–5; 1987 corrections/addenda. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionThree

/-! Actual primary components and concrete algebra used in section three.
No degree estimates or conclusions of Facts A–E are fields of these data. -/

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.SectionThreeSupport

open SectionThree
universe u
variable {K : Type u} [Field K]

/-- The reduced cone supported on the relevant minimal primes. Removing
irrelevant components is necessary before comparing affine and projective
dimensions in a multigraded coordinate ring. -/
def relevantRadicalCore (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing) :
    Ideal M.CoordinateRing := by
  classical
  exact ⨅ q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension I,
    if Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal then
      q.1.asIdeal else ⊤

/-- The literal expansion from equation (*) on p. 362. -/
def degreeCoefficientSum (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing)
    (d : M.FactorIndex → ℕ) : ℚ :=
  ∑ α : BoundedMultiIndex M,
    idealMixedDegree M I (fun i => (α i).val) * (idealDimension M I).factorial /
      (∏ i, ((α i).val.factorial : ℚ)) * ∏ i, (d i : ℚ) ^ (α i).val

/-- A genuine finite minimal homogeneous primary decomposition. The
intersection, primary properties, irredundancy, and distinct radicals are
the standard definition of such a decomposition, not a multiplicity bound. -/
structure PrimaryDecomposition (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing) where
  count : ℕ
  component : Fin count → Ideal M.CoordinateRing
  primary : ∀ i, (component i).IsPrimary
  homogeneous : ∀ i, IsMultihomogeneousIdeal M (component i)
  intersection_eq : I = ⨅ i, component i
  irredundant : ∀ i : Fin count, (⨅ j : {j : Fin count // j ≠ i}, component j.1) ≠ I
  radicals_injective : Function.Injective (fun i => (component i).radical)

def PrimaryDecomposition.IsIsolated {M : MultiProjectiveSpace K}
    {I : Ideal M.CoordinateRing} (D : PrimaryDecomposition M I) (i : Fin D.count) : Prop :=
  (D.component i).radical ∈ I.minimalPrimes

def PrimaryDecomposition.IsEmbedded {M : MultiProjectiveSpace K}
    {I : Ideal M.CoordinateRing} (D : PrimaryDecomposition M I) (i : Fin D.count) : Prop :=
  ¬ D.IsIsolated i

def PrimaryDecomposition.isolatedIntersection {M : MultiProjectiveSpace K}
    {I : Ideal M.CoordinateRing} (D : PrimaryDecomposition M I) : Ideal M.CoordinateRing := by
  classical
  exact ⨅ i, if D.IsIsolated i then D.component i else ⊤

def PrimaryDecomposition.embeddedIntersection {M : MultiProjectiveSpace K}
    {I : Ideal M.CoordinateRing} (D : PrimaryDecomposition M I) : Ideal M.CoordinateRing := by
  classical
  exact ⨅ i, if D.IsEmbedded i then D.component i else ⊤

/-- Source J(b): isolated, relevant primary components of dimension b. -/
def dimensionSlice (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing) (b : ℕ) :
    Ideal M.CoordinateRing := by
  classical
  exact ⨅ q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension I,
    if Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
        idealDimension M q.1.asIdeal = b then
      Hilbert.primaryComponent K M.factorCount M.ambientDimension I q.1 else ⊤

/-- Source J(≥b), with the empty intersection equal to the whole ring. -/
def dimensionAtLeast (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing) (b : ℕ) :
    Ideal M.CoordinateRing := by
  classical
  exact ⨅ q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension I,
    if Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
        b ≤ idealDimension M q.1.asIdeal then
      Hilbert.primaryComponent K M.factorCount M.ambientDimension I q.1 else ⊤

/-- Source N₁: isolated components of J whose primes are not associated to I. -/
def discardedPart (M : MultiProjectiveSpace K) (J I : Ideal M.CoordinateRing) :
    Ideal M.CoordinateRing := by
  classical
  exact ⨅ q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J,
    if q.1.asIdeal ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) then
      Hilbert.primaryComponent K M.factorCount M.ambientDimension J q.1 else ⊤

/-- Source N₂: the complementary isolated components of J. -/
def retainedPart (M : MultiProjectiveSpace K) (J I : Ideal M.CoordinateRing) :
    Ideal M.CoordinateRing := by
  classical
  exact ⨅ q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J,
    if q.1.asIdeal ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) then
      Hilbert.primaryComponent K M.factorCount M.ambientDimension J q.1 else ⊤

namespace BezoutBoundary

def ambient : MultiProjectiveSpace ℂ := projectiveSpace ℂ 4

def X (j : Fin 5) : ambient.CoordinateRing :=
  MvPolynomial.X ⟨(0 : Fin 1), j⟩

def firstGenerator : ambient.CoordinateRing := X 1 ^ 2 * X 3 - X 2 ^ 2 * X 0
def secondGenerator : ambient.CoordinateRing := X 1 * X 4 - X 2 * X 3
def thirdGenerator : ambient.CoordinateRing := X 3 ^ 3 - X 4 ^ 2 * X 0

/-- The three generators printed on p. 370, without the false primality claim. -/
def initialIdeal : Ideal ambient.CoordinateRing :=
  Ideal.span {firstGenerator, secondGenerator, thirdGenerator}

def firstEquation : ambient.CoordinateRing := X 3
def secondEquation : ambient.CoordinateRing := X 1 - X 4

def sectionIdeal : Ideal ambient.CoordinateRing :=
  initialIdeal ⊔ Ideal.span {firstEquation, secondEquation}

def reducedSectionGenerators : Ideal ambient.CoordinateRing :=
  Ideal.span {X 1 ^ 2, X 2 ^ 2 * X 0, X 3, X 1 - X 4}

def firstComponent : Ideal ambient.CoordinateRing :=
  Ideal.span {X 1 ^ 2, X 2 ^ 2, X 3, X 1 - X 4}

def secondComponent : Ideal ambient.CoordinateRing :=
  Ideal.span {X 0, X 1 ^ 2, X 3, X 1 - X 4}

/-- This explicit cubic is outside the printed ideal, but its square is in it. -/
def nonradicalWitness : ambient.CoordinateRing :=
  X 1 * X 3 ^ 2 - X 2 * X 4 * X 0

theorem witness_sq_identity : nonradicalWitness ^ 2 =
    firstGenerator * thirdGenerator + X 0 * X 3 * secondGenerator ^ 2 := by
  dsimp [nonradicalWitness, firstGenerator, secondGenerator, thirdGenerator]
  ring

theorem witness_sq_mem_initialIdeal : nonradicalWitness ^ 2 ∈ initialIdeal := by
  have hf2 : secondGenerator ∈ initialIdeal := by
    apply Ideal.subset_span
    simp
  have hf3 : thirdGenerator ∈ initialIdeal := by
    apply Ideal.subset_span
    simp
  have hs : secondGenerator ^ 2 ∈ initialIdeal := by
    simpa [pow_two] using initialIdeal.mul_mem_left secondGenerator hf2
  rw [witness_sq_identity]
  exact initialIdeal.add_mem (initialIdeal.mul_mem_left firstGenerator hf3)
    (initialIdeal.mul_mem_left (X 0 * X 3) hs)

/-- Candidate to be identified with the actual eventual Hilbert polynomial. -/
def expectedInitialHilbertPolynomial : MvPolynomial (Fin 1) ℚ :=
  2 * MvPolynomial.X 0 ^ 2 + 3 * MvPolynomial.X 0 + 1

end BezoutBoundary

end PhilipponMultiplicity.SectionThreeSupport


