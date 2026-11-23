-- Prove2me | Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Geometry__GagaSections_c8ce35651d051f04
-- name    : P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Geometry__GagaSections_c8ce35651d051f04
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:27.660473+00:00
-- url     : https://prove2.me/theorems/f0209a56-e10a-4557-a51c-948a5c4f6a34
-- title:
--   Gaga Sections
-- statement:
--   Definitions and structural lemmas for Gaga Sections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Geometry₂/GagaSections.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
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
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
def GagaSections : Prop :=
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ), IsProper s → Smooth s → ∀ (L : LB X), L.IsLB →
    ∀ h : L.ι → (Sp ℂ ⟶ X) → ℂ,
      (∀ (i : L.ι) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y →
        (∀ b ∈ B, y b ≫ s = 𝟙 _ ∧ ⊤ ≤ y b ⁻¹ᵁ L.U i) → DifferentiableOn ℂ (fun b => h i (y b)) B) →
      (∀ (i j : L.ι) (x : Sp ℂ ⟶ X), x ≫ s = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) →
        h i x = valAt' x (L.U i ⊓ L.U j) (L.g i j).val * h j x) →
      ∃ σ : L.Sec, ∀ (i : L.ι) (x : Sp ℂ ⟶ X), x ≫ s = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ L.U i → valAt' x (L.U i) (σ.f i) = h i x
end GlobalTheory.CompanionTheory.Ar.Flat


