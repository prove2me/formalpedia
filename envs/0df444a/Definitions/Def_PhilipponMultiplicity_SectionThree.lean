-- Prove2me | Definitions.Def_PhilipponMultiplicity_SectionThree
-- name    : PhilipponMultiplicity_SectionThree
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-23T20:21:33.510537+00:00
-- url     : https://prove2.me/theorems/660781ec-5a6e-4851-a24e-7c1f3f8101a4
-- title:
--   Section 3 — degree sums, products and zero-degree example
-- statement:
--   Actual coefficient and primary-length sums, projective subvarieties and their products, plus the fixed coordinate ideal for the zero-degree counterexample.
--
--   Compiled, admission-free definition bundle. Theorems asserting its substantive properties remain open targets in the full-paper goal.
-- source:
--   Philippon 1986, §§2–5; 1987 corrections/addenda. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_Degree

/-!
Concrete notation for Philippon's Lemmas 3.1, 3.2 and 3.4.
All coefficients and degrees are extracted from the actual quotient Hilbert
polynomial. Component multiplicities are actual localized module lengths.
No Hilbert-polynomial existence, degree formula, or multiplicity conclusion
is supplied as data.
-/

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.SectionThree

universe u
variable {K : Type u} [Field K]

/-- Source nontriviality: not all projective primary components are irrelevant.
The radical criterion is independent of a choice of primary decomposition. -/
def IsNontrivialIdeal (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing) : Prop :=
  ¬ Hilbert.irrelevantIdeal K M.factorCount M.ambientDimension ≤ I.radical

/-- The dimension extracted from the actual eventual Hilbert polynomial.
Identifying this with geometric dimension is a separate foundation theorem. -/
def idealDimension (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing) : ℕ :=
  (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I).totalDegree

def idealDegreeValue (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing)
    (d : M.FactorIndex → ℕ) : ℚ :=
  Hilbert.degreeValue K M.factorCount M.ambientDimension I d

/-- The source coefficient c_α: the top Hilbert-polynomial coefficient times
the product of the individual factorials. It is not multiplied by a!. -/
def idealMixedDegree (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing)
    (α : M.FactorIndex → ℕ) : ℚ :=
  if ∑ i, α i = idealDimension M I then
    (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I).coeff
      (Finsupp.equivFunOnFinite.symm α) * ∏ i, ((α i).factorial : ℚ)
  else 0

/-- The bounded multi-indices in source equation (*) on p. 362. -/
abbrev BoundedMultiIndex (M : MultiProjectiveSpace K) :=
  ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)

/-- The explicit right side of Lemma 3.1, including the normalization
(a−1)! / (α₁!⋯αₚ!). The theorem uses dᵢ ≥ 1. -/
def hypersurfaceCoefficientSum (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing)
    (D d : M.FactorIndex → ℕ) : ℚ := by
  classical
  let a := idealDimension M I
  exact ∑ α : BoundedMultiIndex M,
    if ∑ i, (α i).val = a then
      (idealMixedDegree M I (fun i => (α i).val) *
        ∑ i, ((α i).val : ℚ) * (D i : ℚ) / (d i : ℚ)) *
        ((a - 1).factorial : ℚ) / (∏ i, ((α i).val.factorial : ℚ)) *
        ∏ i, (d i : ℚ) ^ (α i).val
    else 0

/-- The top-dimensional part of the associativity sum in Lemma 3.2.
At a minimal prime the local length is finite by `Hilbert.localLength_ne_top`,
so `toNat` here records its actual natural-number value. -/
def topComponentLengthSum (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing)
    (d : M.FactorIndex → ℕ) : ℚ := by
  classical
  letI := Fintype.ofFinite
    (Hilbert.MinimalComponent K M.factorCount M.ambientDimension I)
  exact ∑ q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension I,
    if Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
        idealDimension M q.1.asIdeal = idealDimension M I then
      ((Hilbert.localLength K M.factorCount M.ambientDimension I q.1).toNat : ℚ) *
        idealDegreeValue M q.1.asIdeal d
    else 0

/-- An actual locally closed projective subset, not necessarily irreducible.
Its degree is defined through its projective closure's vanishing ideal.
The empty subset is allowed, with degree zero under the existing convention. -/
structure ProjectiveSubvariety (K : Type u) [Field K] (N : ℕ) where
  carrier : Set (Projectivization K (Fin (N + 1) → K))
  locallyClosed : @IsLocallyClosed _
    (TopologicalSpace.induced (fun x _ => x) (projectiveSpace K N).zariskiTopology)
    carrier

def ProjectiveSubvariety.carrierInSingleFactor {N : ℕ}
    (V : ProjectiveSubvariety K N) : Set (projectiveSpace K N).Point :=
  (fun x => fun _ => x) '' V.carrier

def ProjectiveSubvariety.dimension {N : ℕ} (V : ProjectiveSubvariety K N) : ℕ :=
  idealDimension (projectiveSpace K N)
    ((projectiveSpace K N).vanishingIdeal V.carrierInSingleFactor)

/-- The ordinary projective degree: the single-variable degree form at 1. -/
def ProjectiveSubvariety.degree {N : ℕ} (V : ProjectiveSubvariety K N) : ℚ :=
  idealDegreeValue (projectiveSpace K N)
    ((projectiveSpace K N).vanishingIdeal V.carrierInSingleFactor) (fun _ => 1)

def productCarrier (M : MultiProjectiveSpace K)
    (V : ∀ i : M.FactorIndex, ProjectiveSubvariety K (M.ambientDimension i)) :
    Set M.Point :=
  {x | ∀ i, x i ∈ (V i).carrier}

def locusDimension (M : MultiProjectiveSpace K) (V : Set M.Point) : ℕ :=
  idealDimension M (M.vanishingIdeal V)

def locusDegreeValue (M : MultiProjectiveSpace K) (V : Set M.Point)
    (d : M.FactorIndex → ℕ) : ℚ :=
  idealDegreeValue M (M.vanishingIdeal V) d

namespace ZeroDegreeBoundary

/-- The concrete ambient product P² × P¹ over the complex numbers. -/
def ambient : MultiProjectiveSpace ℂ :=
  ⟨2, by decide, fun i => if i = 0 then 2 else 1⟩

def firstCoordinate (j : Fin 3) : ambient.CoordinateRing :=
  MvPolynomial.X ⟨(0 : Fin 2), ⟨j.val, by simpa [ambient] using j.isLt⟩⟩

def secondCoordinate (j : Fin 2) : ambient.CoordinateRing :=
  MvPolynomial.X ⟨(1 : Fin 2), ⟨j.val, by simpa [ambient] using j.isLt⟩⟩

/-- I=(Y₁X₁,Y₁X₂), the ideal of the union of a surface and a curve. -/
def ideal : Ideal ambient.CoordinateRing :=
  Ideal.span {secondCoordinate 1 * firstCoordinate 1,
    secondCoordinate 1 * firstCoordinate 2}

/-- The equation Y₀ misses the surface and cuts the curve in one point. -/
def polynomial : ambient.CoordinateRing := secondCoordinate 0

def equationDegrees : ambient.FactorIndex → ℕ := fun i => if i.val = 0 then 0 else 1

/-- The actual Hilbert polynomial to be proved for this explicit ideal:
binomial(d₁+2,2)+d₂. This is a candidate polynomial, not an assumed value. -/
def expectedHilbertPolynomial : MvPolynomial (Fin 2) ℚ :=
  MvPolynomial.C (1 / 2) * MvPolynomial.X 0 ^ 2 +
    MvPolynomial.C (3 / 2) * MvPolynomial.X 0 + 1 + MvPolynomial.X 1

end ZeroDegreeBoundary

end PhilipponMultiplicity.SectionThree


