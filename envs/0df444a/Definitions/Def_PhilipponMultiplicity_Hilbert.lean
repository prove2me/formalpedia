-- Prove2me | Definitions.Def_PhilipponMultiplicity_Hilbert
-- name    : PhilipponMultiplicity_Hilbert
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-23T20:16:22.455104+00:00
-- url     : https://prove2.me/theorems/2d4cbb6b-bd9a-451a-baa1-33162c004892
-- title:
--   Multigraded Hilbert data and local lengths
-- statement:
--   Actual multigraded quotient pieces and their dimensions; a canonically chosen eventual rational Hilbert polynomial, defaulting to zero when no such polynomial exists; its factorial-normalized highest part; localized quotient lengths; minimal primary components and their degree sums; localized Cohen–Macaulayness via regular sequences. Uniqueness and local primary-component API lemmas are proved. Existence of Hilbert polynomials and their geometric dimension interpretation are required separate theorem dependencies.
--
--   Compiled, admission-free definition bundle. Theorems asserting its substantive properties remain open targets in the full-paper goal.
-- source:
--   Philippon 1986, §§2–5; 1987 corrections/addenda. https://numdam.org/articles/10.24033/bsmf.2060/

import Mathlib

/-!
# Concrete algebra behind Philippon's multigraded degree forms

The Hilbert function below is the dimension of an actual homogeneous piece of
an actual polynomial-ring quotient.  The polynomial is chosen from its
eventual-agreement predicate; it is zero if there is no such polynomial.
Existence of the eventual polynomial is a separate foundational theorem,
not an assumption or a numeric field in the data.  No multiplicity estimate
is assumed by these definitions.

The sum over isolated components uses their canonical localized contractions.
It therefore retains scheme-theoretic multiplicities.  Identifying their
degree forms with generic lengths times prime degree forms is Philippon's
Lemma 3.2 and is not built into the definition as an assumption.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace PhilipponMultiplicity.Hilbert

universe u

variable (K : Type u) [Field K] (p : ℕ) (N : Fin p → ℕ)

/-- The homogeneous coordinates of a product of `p` projective spaces. -/
abbrev CoordinateRing :=
  MvPolynomial (Sigma fun i : Fin p => Fin (N i + 1)) K

/-- Every variable in block `i` has multidegree the `i`th unit vector. -/
def blockWeight (x : Sigma fun i : Fin p => Fin (N i + 1)) : Fin p → ℕ :=
  Pi.single x.1 1

/-- Polynomials of a fixed block multidegree. -/
def degreePiece (d : Fin p → ℕ) : Submodule K (CoordinateRing K p N) :=
  MvPolynomial.weightedHomogeneousSubmodule K (blockWeight p N) d

/-- Closure under the actual multihomogeneous component projections. -/
def IsHomogeneousIdeal (I : Ideal (CoordinateRing K p N)) : Prop :=
  ∀ f ∈ I, ∀ d : Fin p → ℕ,
    MvPolynomial.weightedHomogeneousComponent (blockWeight p N) d f ∈ I

/-- Exact multihomogeneity; the zero polynomial is allowed. -/
def IsHomogeneousOfDegree (f : CoordinateRing K p N) (d : Fin p → ℕ) : Prop :=
  f.IsWeightedHomogeneous (blockWeight p N) d

/-- A homogeneous equation whose block degrees are bounded coordinatewise. -/
def IsHomogeneousOfDegreeAtMost (f : CoordinateRing K p N) (D : Fin p → ℕ) : Prop :=
  ∃ d : Fin p → ℕ, (∀ i, d i ≤ D i) ∧ IsHomogeneousOfDegree K p N f d

/-- The image of a homogeneous piece in the polynomial-ring quotient. -/
def quotientPiece (I : Ideal (CoordinateRing K p N)) (d : Fin p → ℕ) :
    Submodule K ((CoordinateRing K p N) ⧸ I) :=
  (degreePiece K p N d).map (Ideal.Quotient.mkₐ K I).toLinearMap

/-- The genuine multigraded quotient Hilbert function. -/
def hilbertFunction (I : Ideal (CoordinateRing K p N)) (d : Fin p → ℕ) : ℕ :=
  Module.finrank K (quotientPiece K p N I d)

/-- Eventual agreement in every sufficiently large block degree. -/
def IsHilbertPolynomial (I : Ideal (CoordinateRing K p N))
    (P : MvPolynomial (Fin p) ℚ) : Prop :=
  ∃ d₀ : Fin p → ℕ, ∀ d : Fin p → ℕ, (∀ i, d₀ i ≤ d i) →
    MvPolynomial.eval (fun i => (d i : ℚ)) P = (hilbertFunction K p N I d : ℚ)

/-- The eventual quotient Hilbert polynomial, with explicit zero fallback.
The separate existence theorem is required before using its specification. -/
def hilbertPolynomial (I : Ideal (CoordinateRing K p N)) : MvPolynomial (Fin p) ℚ := by
  classical
  exact if h : ∃ P, IsHilbertPolynomial K p N I P then Classical.choose h else 0

theorem hilbertPolynomial_spec (I : Ideal (CoordinateRing K p N))
    (h : ∃ P, IsHilbertPolynomial K p N I P) :
    IsHilbertPolynomial K p N I (hilbertPolynomial K p N I) := by
  rw [hilbertPolynomial, dif_pos h]
  exact Classical.choose_spec h

theorem hilbertPolynomial_eq_zero_of_not_exists (I : Ideal (CoordinateRing K p N))
    (h : ¬ ∃ P, IsHilbertPolynomial K p N I P) :
    hilbertPolynomial K p N I = 0 := by
  rw [hilbertPolynomial, dif_neg h]

/-- Eventual agreement determines at most one rational polynomial. -/
theorem IsHilbertPolynomial.unique (I : Ideal (CoordinateRing K p N))
    {P Q : MvPolynomial (Fin p) ℚ}
    (hP : IsHilbertPolynomial K p N I P) (hQ : IsHilbertPolynomial K p N I Q) : P = Q := by
  classical
  obtain ⟨a, ha⟩ := hP
  obtain ⟨b, hb⟩ := hQ
  let s : Fin p → Set ℚ := fun i =>
    (fun n : ℕ => (n : ℚ)) '' Set.Ici (max (a i) (b i))
  have hs (i : Fin p) : (s i).Infinite :=
    (Set.Ici_infinite (max (a i) (b i))).image
      (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℚ))).injOn
  apply MvPolynomial.funext_set s hs
  intro x hx
  have hx' (i : Fin p) : ∃ d : ℕ, max (a i) (b i) ≤ d ∧ (d : ℚ) = x i :=
    hx i (Set.mem_univ i)
  choose d hd heq using hx'
  have hx_eq : (fun i => (d i : ℚ)) = x := funext heq
  rw [← hx_eq, ha d (fun i => (le_max_left _ _).trans (hd i)),
    hb d (fun i => (le_max_right _ _).trans (hd i))]

theorem hilbertPolynomial_eq_of_isHilbertPolynomial
    (I : Ideal (CoordinateRing K p N)) {P : MvPolynomial (Fin p) ℚ}
    (hP : IsHilbertPolynomial K p N I P) : hilbertPolynomial K p N I = P :=
  IsHilbertPolynomial.unique K p N I
    (hilbertPolynomial_spec K p N I ⟨P, hP⟩) hP

/-- Philippon's normalization: factorial of the polynomial degree times its
top total-homogeneous part.  The degree form of the zero polynomial is zero. -/
def degreeForm (I : Ideal (CoordinateRing K p N)) : MvPolynomial (Fin p) ℚ :=
  let P := hilbertPolynomial K p N I
  (P.totalDegree.factorial : ℚ) • MvPolynomial.homogeneousComponent P.totalDegree P

/-- Evaluation of the actual degree form at arbitrary natural block degrees,
including zero degrees. -/
def degreeValue (I : Ideal (CoordinateRing K p N)) (D : Fin p → ℕ) : ℚ :=
  MvPolynomial.eval (fun i => (D i : ℚ)) (degreeForm K p N I)

/-- The ideal generated by all coordinates in one projective block. -/
def blockIdeal (i : Fin p) : Ideal (CoordinateRing K p N) :=
  Ideal.span (Set.range fun j : Fin (N i + 1) =>
    (MvPolynomial.X ⟨i, j⟩ : CoordinateRing K p N))

/-- The multiprojective irrelevant ideal, the intersection of the block ideals. -/
def irrelevantIdeal : Ideal (CoordinateRing K p N) :=
  ⨅ i, blockIdeal K p N i

/-- A prime is relevant precisely when its multiprojective support is nonempty. -/
def IsRelevant (q : Ideal (CoordinateRing K p N)) : Prop :=
  ¬ irrelevantIdeal K p N ≤ q

/-- The canonical component obtained by extension to the localization and
contraction. It is primary when the prime is minimal over `I`. -/
def primaryComponent (I : Ideal (CoordinateRing K p N))
    (q : PrimeSpectrum (CoordinateRing K p N)) : Ideal (CoordinateRing K p N) :=
  (I.map (algebraMap (CoordinateRing K p N) (Localization.AtPrime q.asIdeal))).under
    (CoordinateRing K p N)

/-- Scheme-theoretic generic length, without truncation or an arbitrary input. -/
def localLength (I : Ideal (CoordinateRing K p N))
    (q : PrimeSpectrum (CoordinateRing K p N)) : ℕ∞ :=
  Module.length (Localization.AtPrime q.asIdeal)
    ((Localization.AtPrime q.asIdeal) ⧸
      I.map (algebraMap (CoordinateRing K p N) (Localization.AtPrime q.asIdeal)))

private theorem localized_radical_eq_maximal
    (I : Ideal (CoordinateRing K p N)) (q : PrimeSpectrum (CoordinateRing K p N))
    (hq : q.asIdeal ∈ I.minimalPrimes) :
    (I.map (algebraMap (CoordinateRing K p N) (Localization.AtPrime q.asIdeal))).radical =
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) := by
  rw [IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (Localization.AtPrime q.asIdeal) q.asIdeal I hq,
    IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal (Localization.AtPrime q.asIdeal)]

/-- The canonical component at a minimal prime is genuinely primary. -/
theorem primaryComponent_isPrimary
    (I : Ideal (CoordinateRing K p N)) (q : PrimeSpectrum (CoordinateRing K p N))
    (hq : q.asIdeal ∈ I.minimalPrimes) :
    (primaryComponent K p N I q).IsPrimary := by
  have hrad := localized_radical_eq_maximal K p N I q hq
  have hprimary :
      (I.map (algebraMap (CoordinateRing K p N) (Localization.AtPrime q.asIdeal))).IsPrimary :=
    Ideal.isPrimary_of_isMaximal_radical (hrad ▸ inferInstance)
  exact hprimary.comap (algebraMap (CoordinateRing K p N) (Localization.AtPrime q.asIdeal))

theorem primaryComponent_radical
    (I : Ideal (CoordinateRing K p N)) (q : PrimeSpectrum (CoordinateRing K p N))
    (hq : q.asIdeal ∈ I.minimalPrimes) :
    (primaryComponent K p N I q).radical = q.asIdeal := by
  change ((I.map (algebraMap (CoordinateRing K p N) (Localization.AtPrime q.asIdeal))).comap
    (algebraMap (CoordinateRing K p N) (Localization.AtPrime q.asIdeal))).radical = q.asIdeal
  rw [← Ideal.comap_radical, localized_radical_eq_maximal K p N I q hq]
  exact IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q.asIdeal) q.asIdeal

/-- The generic local length of an isolated component is finite. -/
theorem localLength_ne_top
    (I : Ideal (CoordinateRing K p N)) (q : PrimeSpectrum (CoordinateRing K p N))
    (hq : q.asIdeal ∈ I.minimalPrimes) : localLength K p N I q ≠ ⊤ := by
  let A := Localization.AtPrime q.asIdeal
  let J := I.map (algebraMap (CoordinateRing K p N) A)
  have hrad : J.radical = IsLocalRing.maximalIdeal A :=
    localized_radical_eq_maximal K p N I q hq
  have hprimary : J.IsPrimary := Ideal.isPrimary_of_isMaximal_radical (hrad ▸ inferInstance)
  have hdim : Ring.KrullDimLE 0 (A ⧸ J) := by
    apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
    intro Q hQ
    rw [Ideal.minimalPrimes_eq_subsingleton hprimary, Set.mem_singleton_iff] at hQ
    rw [hQ, hrad]
    infer_instance
  letI : IsArtinianRing (A ⧸ J) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero (R := A ⧸ J)
  letI : IsArtinian A (A ⧸ J) :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := J))
  exact Module.length_ne_top

/-- Minimal primes index the isolated primary components. -/
abbrev MinimalComponent (I : Ideal (CoordinateRing K p N)) :=
  {q : PrimeSpectrum (CoordinateRing K p N) // q.asIdeal ∈ I.minimalPrimes}

instance minimalComponent_finite (I : Ideal (CoordinateRing K p N)) :
    Finite (MinimalComponent K p N I) := by
  letI : Finite I.minimalPrimes :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing (CoordinateRing K p N) I).to_subtype
  exact Finite.of_injective
    (fun q : MinimalComponent K p N I => (⟨q.1.asIdeal, q.2⟩ : I.minimalPrimes))
    (by intro a b h; apply Subtype.ext; apply PrimeSpectrum.ext; exact congrArg Subtype.val h)

/-- A component contributes on `U` exactly when its prime lies in a maximal
ideal from the specified open set. -/
def MeetsOpen (q : Ideal (CoordinateRing K p N))
    (U : TopologicalSpace.Opens (MaximalSpectrum (CoordinateRing K p N))) : Prop :=
  ∃ m : MaximalSpectrum (CoordinateRing K p N), m ∈ U ∧ q ≤ m.asIdeal

/-- Cohen--Macaulayness of the actual localized quotient at a maximal ideal.
For a nonzero local Noetherian ring this is the usual regular-sequence
characterization: a sequence of nonunits is regular and has length equal
to the Krull dimension. The zero ring is included so points outside the
closed locus satisfy the condition, as in Philippon's convention. -/
def IsCohenMacaulayAt (I : Ideal (CoordinateRing K p N))
    (m : MaximalSpectrum (CoordinateRing K p N)) : Prop :=
  let A := Localization.AtPrime m.asIdeal
  let B := A ⧸ I.map (algebraMap (CoordinateRing K p N) A)
  Subsingleton B ∨ ∃ rs : List B,
    (∀ r ∈ rs, ¬ IsUnit r) ∧ RingTheory.Sequence.IsRegular B rs ∧
    (rs.length : WithBot ℕ∞) = ringKrullDim B

/-- Philippon's "perfect at every point of U" condition, applied to genuine
localized quotient rings. -/
def IsLocallyCohenMacaulayOn (I : Ideal (CoordinateRing K p N))
    (U : TopologicalSpace.Opens (MaximalSpectrum (CoordinateRing K p N))) : Prop :=
  ∀ m : MaximalSpectrum (CoordinateRing K p N), m ∈ U → IsCohenMacaulayAt K p N I m

/-- Philippon's `S_U H`: sum the degree forms of the relevant isolated primary
components meeting `U`. No arbitrary component list or length is supplied. -/
def componentSum (I : Ideal (CoordinateRing K p N))
    (U : TopologicalSpace.Opens (MaximalSpectrum (CoordinateRing K p N)))
    (D : Fin p → ℕ) : ℚ := by
  classical
  letI := Fintype.ofFinite (MinimalComponent K p N I)
  exact ∑ q : MinimalComponent K p N I,
    if IsRelevant K p N q.1.asIdeal ∧ MeetsOpen K p N q.1.asIdeal U then
      degreeValue K p N (primaryComponent K p N I q.1) D
    else 0

/-- Finitely many genuinely homogeneous equations, with bounded block degrees,
generate the ideal modulo the ambient defining ideal. -/
def HasEquationsOfDegreeAtMost (ambient J : Ideal (CoordinateRing K p N))
    (D : Fin p → ℕ) : Prop :=
  ∃ s : Finset (CoordinateRing K p N),
    (∀ f ∈ s, IsHomogeneousOfDegreeAtMost K p N f D) ∧
    ambient ⊔ J = ambient ⊔ Ideal.span (s : Set (CoordinateRing K p N))

/-- Ideal-theoretic incomplete definition on the ambient open locus: each
component of `V` meeting that locus is an isolated component of the equations.
When `V` represents its projective closure and every component meets the
ambient locus, this is Definition 3.5(1). -/
def IsIncompletelyDefinedOn (ambient J V : Ideal (CoordinateRing K p N))
    (U : TopologicalSpace.Opens (MaximalSpectrum (CoordinateRing K p N))) : Prop :=
  ∀ q ∈ V.minimalPrimes,
    IsRelevant K p N q → MeetsOpen K p N q U →
    q ∈ (ambient ⊔ J).minimalPrimes

/-- The multiplicity clause of Definition 3.5(3), using actual localized
quotient lengths at the component primes. -/
def IsIncompletelyDefinedWithMultiplicityOn
    (ambient J V : Ideal (CoordinateRing K p N))
    (U : TopologicalSpace.Opens (MaximalSpectrum (CoordinateRing K p N)))
    (ell : ℕ) : Prop :=
  IsIncompletelyDefinedOn K p N ambient J V U ∧
  ∀ q : MinimalComponent K p N V,
    IsRelevant K p N q.1.asIdeal → MeetsOpen K p N q.1.asIdeal U →
    (ell : ℕ∞) ≤ localLength K p N (ambient ⊔ J) q.1

end PhilipponMultiplicity.Hilbert


