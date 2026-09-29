-- Prove2me | Definitions.Def_KN_HorizontalPadicLAux
-- name    : KN_HorizontalPadicLAux
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-25T10:40:20.638429+00:00
-- url     : https://prove2.me/theorems/718d133c-e6ff-48c1-a7c4-86acff0d3160
-- title:
--   Auxiliary definitions for horizontal p-adic L-functions
-- statement:
--   Reusable auxiliary definitions for the Kriz–Nordentoft horizontal p-adic L-function construction: finite horizontal quotient groups and their group rings, compatible horizontal measures, finite-order horizontal characters and evaluation, prime-relative natural density, the fixed-order eigenform nonvanishing count, and newness of an eigenform. This bundle deliberately excludes the superseded sparse horizontal prime-system formulation.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, Sections 2.1 and 5.

import Definitions.Def_KN_HorizontalPadicL
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- The finite horizontal group `∏_{n ∈ A} ℤ / p^(m n) ℤ`, written
multiplicatively so that its finitely supported functions form a group ring. -/
abbrev HorizontalFiniteGroup (p : ℕ) (m : ℕ → ℕ) (A : Finset ℕ) :=
  ∀ i : {n : ℕ // n ∈ A}, Multiplicative (ZMod (p ^ m i.1))

/-- The group ring of a finite horizontal quotient. -/
abbrev HorizontalGroupRing (R : Type*) [CommRing R]
    (p : ℕ) (m : ℕ → ℕ) (A : Finset ℕ) :=
  HorizontalFiniteGroup p m A →₀ R

/-- Restriction from the coordinates in `B` to those in `A`. -/
def restrictHorizontalCoordinates {p : ℕ} {m : ℕ → ℕ} {A B : Finset ℕ}
    (hAB : A ⊆ B) (x : HorizontalFiniteGroup p m B) : HorizontalFiniteGroup p m A :=
  fun i => x ⟨i.1, hAB i.2⟩

/-- Pushforward of finite group rings under coordinate restriction. -/
def horizontalGroupRingProjection (R : Type*) [CommRing R]
    {p : ℕ} {m : ℕ → ℕ} {A B : Finset ℕ} (hAB : A ⊆ B) :
    HorizontalGroupRing R p m B →+ HorizontalGroupRing R p m A :=
  Finsupp.mapDomain.addMonoidHom (M := R)
    (restrictHorizontalCoordinates (p := p) (m := m) hAB)

/-- An element of the horizontal Iwasawa algebra, represented as a compatible family
of group-ring elements on all finite sets of coordinates. -/
structure HorizontalMeasure (R : Type*) [CommRing R] (p : ℕ) (m : ℕ → ℕ) where
  finiteLevel : ∀ A : Finset ℕ, HorizontalGroupRing R p m A
  compatible : ∀ (A B : Finset ℕ) (hAB : A ⊆ B),
    horizontalGroupRingProjection R hAB (finiteLevel B) = finiteLevel A

/-- A horizontal measure is nonzero if one of its finite-level projections is nonzero. -/
def HorizontalMeasure.Nonzero {R : Type*} [CommRing R] {p : ℕ} {m : ℕ → ℕ}
    (ν : HorizontalMeasure R p m) : Prop :=
  ∃ A : Finset ℕ, ν.finiteLevel A ≠ 0

/-- A finite-order character of a finite quotient of the horizontal profinite group. -/
structure HorizontalCharacter (p : ℕ) [Fact p.Prime] (m : ℕ → ℕ) where
  support : Finset ℕ
  toMonoidHom : HorizontalFiniteGroup p m support →* ℂ_[p]

/-- Evaluation of a horizontal measure whose coefficient ring is a subring of `ℂ_p`
at a finite-order character. -/
def HorizontalMeasure.eval {p : ℕ} [Fact p.Prime] {m : ℕ → ℕ}
    {R : Subring ℂ_[p]} (ν : HorizontalMeasure R p m)
    (χ : HorizontalCharacter p m) : ℂ_[p] :=
  (ν.finiteLevel χ.support).sum fun g a =>
    (a : ℂ_[p]) * χ.toMonoidHom g

/-- A set of natural numbers has prime-relative natural density `δ` if the proportion
of rational primes below `X` which lie in the set tends to `δ`. -/
def HasPrimeNaturalDensity (A : Set ℕ) (δ : ℝ) : Prop := by
  classical
  exact Filter.Tendsto
    (fun X : ℕ =>
      (((Finset.range X).filter fun ℓ => ℓ.Prime ∧ ℓ ∈ A).card : ℝ) /
        (((Finset.range X).filter Nat.Prime).card : ℝ))
    Filter.atTop (nhds δ)

/-- Primitive exact-order twists of an eigenform whose central critical value is nonzero. -/
def eigenformNonvanishingCount {N k : ℕ} (ι : MTT.Qbar →+* ℂ)
    (f : MTT.Eigenform N k ι) (d : ℕ) (X : ℝ) : ℕ :=
  Set.ncard {χ : DirichletCharacterWithLevel |
    χ.2.IsPrimitive ∧ orderOf χ.2 = d ∧ (χ.2.conductor : ℝ) ≤ X ∧
    Nat.Coprime N χ.1.1 ∧
    @MTT.criticalLValue ι f.form χ.1.1 ⟨Nat.ne_of_gt χ.1.2⟩ χ.2
      (k / 2 - 1) ≠ 0}

/-- A normalized eigenform of trivial nebentypus is new at level `N` if its q-expansion
does not occur as a cusp form for `Γ₀(M)` at any smaller positive level `M`. -/
def IsNewEigenform {N k : ℕ} {ι : MTT.Qbar →+* ℂ}
    (f : MTT.Eigenform N k ι) : Prop :=
  ∀ (M : ℕ) (hM : 0 < M), M < N →
    ¬ ∃ g : CuspFormAtLevel M hM,
      ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 g).coeff n = ι (f.coeff n)

end HorizontalPadicL


