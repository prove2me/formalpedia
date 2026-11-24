-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
-- name    : GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:57.997986+00:00
-- url     : https://prove2.me/theorems/3bf562df-6876-4857-b6e1-5e44f8b75901
-- title:
--   Levi Form Gb Pot One
-- statement:
--   Definitions and structural lemmas for Levi Form Gb Pot One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/LeviFormGbPotOne.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo
open scoped ENNReal ComplexOrder
def topDens {D : ℕ} (ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : ℝ :=
  maDensity (fun _ : Fin D => fun y => ψ y / 2) z
def DetMono.Hyp {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  A'.PosSemidef ∧ (A - A').PosSemidef
def DetMono.Statement : Prop :=
  ∀ (n : ℕ) (A A' : Matrix (Fin n) (Fin n) ℂ), DetMono.Hyp A A' → A'.det.re ≤ A.det.re
def MACompact.Hyp {D : ℕ} (Ω : Set (Fin D → ℂ)) (φ v : (Fin D → ℂ) → ℝ) : Prop :=
  IsOpen Ω ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ Ω ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v Ω ∧
    HasCompactSupport v ∧ tsupport v ⊆ Ω
def MACompact.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Set (Fin D → ℂ)) (φ v : (Fin D → ℂ) → ℝ), MACompact.Hyp Ω φ v →
    ∫ z in Ω, (topDens (φ + v) z - topDens φ z) = 0
def MAComparison.Hyp {D : ℕ} (Ω : Set (Fin D → ℂ)) (φ a b : (Fin D → ℂ) → ℝ) : Prop :=
  IsOpen Ω ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ Ω ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a Ω ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b Ω ∧
    (∀ z ∈ Ω, ∀ w, 0 ≤ leviForm (φ + a) z w) ∧ (∀ z ∈ Ω, ∀ w, 0 ≤ leviForm (φ + b) z w) ∧
    ∀ k : ℝ, IsCompact {z | z ∈ Ω ∧ -k ≤ b z - a z}
def MAComparison.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Set (Fin D → ℂ)) (φ a b : (Fin D → ℂ) → ℝ), MAComparison.Hyp Ω φ a b →
    ∫⁻ z in Ω, ENNReal.ofReal (topDens (φ + b) z) ≤ ∫⁻ z in Ω, ENNReal.ofReal (topDens (φ + a) z)
def CoverMass.Hyp {D : ℕ} (M Z : Set (Fin D → ℂ)) (z : (Fin D → ℂ) → (Fin D → ℂ)) (δ : ℕ) :
    Prop :=
  IsOpen M ∧ volume Z = 0 ∧ DifferentiableOn ℂ z M ∧ Set.MapsTo z M Zᶜ ∧
    IsCoveringMapOn (fun x : M => z x) Zᶜ ∧ ∀ w ∉ Z, Set.ncard {x | x ∈ M ∧ z x = w} = δ
def CoverMass.Statement : Prop :=
  ∀ (D : ℕ) (M Z : Set (Fin D → ℂ)) (z : (Fin D → ℂ) → (Fin D → ℂ)) (δ : ℕ),
    CoverMass.Hyp M Z z δ →
      ∫⁻ x in M, ENNReal.ofReal (topDens (fun y => Real.log (1 + ∑ i, ‖z y i‖ ^ 2)) x) = δ
def LocBddRatio {A : Type*} [CommRing A] [Algebra ℂ A] (p q : A) : Prop :=
  ∀ x : A →ₐ[ℂ] ℂ, ∃ (s : Finset A) (ε : ℝ), 0 < ε ∧ ∃ M : ℝ, ∀ y : A →ₐ[ℂ] ℂ,
    (∀ a ∈ s, ‖y a - x a‖ < ε) → y q ≠ 0 → ‖y p‖ ≤ M * ‖y q‖
def RiemannExt.Hyp (A : Type*) [CommRing A] [Algebra ℂ A] (p q : A) : Prop :=
  Algebra.FiniteType ℂ A ∧ IsDomain A ∧ IsIntegrallyClosed A ∧ q ≠ 0 ∧ LocBddRatio p q
def RiemannExt.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra ℂ A] (p q : A), RiemannExt.Hyp A p q → ∃ r : A, p = q * r
def IntegralAtPoints {A : Type*} [CommRing A] (h a : A) (N : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] (y : A →+* K), (∀ b, ‖y b‖ ≤ 1) → y h ≠ 0 → ‖y a‖ ≤ ‖(N : K)‖
def Normality.Hyp (A : Type*) [CommRing A] (h a : A) (N : ℕ) : Prop :=
  Algebra.FiniteType ℤ A ∧ IsDomain A ∧ IsIntegrallyClosed A ∧ (∀ m : ℤ, m ≠ 0 → (m : A) ≠ 0) ∧
    h ≠ 0 ∧ 0 < N ∧ IntegralAtPoints h a N
def Normality.Statement : Prop :=
  ∀ (A : Type) [CommRing A] (h a : A) (N : ℕ), Normality.Hyp A h a N → ∃ b : A, a = N * b
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB


