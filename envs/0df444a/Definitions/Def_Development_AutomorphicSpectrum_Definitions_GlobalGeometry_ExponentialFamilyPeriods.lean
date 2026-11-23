-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExponentialFamilyPeriods
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExponentialFamilyPeriods
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:20.657276+00:00
-- url     : https://prove2.me/theorems/893dc95a-cfd6-499d-a0c5-ad998918238f
-- title:
--   Exponential Family Periods
-- statement:
--   Definitions and structural lemmas for Exponential Family Periods, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExponentialFamilyPeriods.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_LieModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Filter Topology
def IsHolPts {R : Type} [CommRing R] {n : ℕ} (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) : Prop :=
  IsOpen B ∧ ∀ r : R, DifferentiableOn ℂ (fun b => ψ b r) B
structure FamExp {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] {g n : ℕ}
    (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) where

  ex : ∀ b : Fin n → ℂ, (Fin g → ℂ) → (Over.mk (spMap (ψ b)) ⟶ G)
  add : ∀ b ∈ B, ∀ z w, ex b (z + w) = ex b z * ex b w
  hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (ex bz.1 bz.2).left)
  diff : ∀ b ∈ B, ∀ a : Fin g, IsDerivAt0 (fun z => (ex b z).left) (Pi.single a 1)
    (spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left)
  log : ∀ b₀ ∈ B, ∃ (V : G.left.Opens) (N : ℕ) (f : Fin N → Γ(G.left, V))
    (L : (Fin n → ℂ) × (Fin N → ℂ) → (Fin g → ℂ)), ⊤ ≤ (ex b₀ 0).left ⁻¹ᵁ V ∧
    AnalyticAt ℂ L (b₀, fun j => valAt' (ex b₀ 0).left V (f j)) ∧
    (∀ᶠ bz : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0),
      L (bz.1, fun j => valAt' (ex bz.1 bz.2).left V (f j)) = bz.2) ∧
    ∀ᶠ p : (Fin n → ℂ) × (Fin N → ℂ) in 𝓝 (b₀, fun j => valAt' (ex b₀ 0).left V (f j)),
      ∀ x : Over.mk (spMap (ψ p.1)) ⟶ G, ⊤ ≤ x.left ⁻¹ᵁ V → (∀ j, valAt' x.left V (f j) = p.2 j) →
        x = ex p.1 (L p)
def FamExp.per {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ}
    {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}
    (e : FamExp G M B ψ) (b : Fin n → ℂ) : Set (Fin g → ℂ) := {z | e.ex b z = 1}
end GlobalTheory.CompanionTheory.Ar.Flat


