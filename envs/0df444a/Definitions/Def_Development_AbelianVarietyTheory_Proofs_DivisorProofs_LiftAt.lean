-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftAt
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftAt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:35.627319+00:00
-- url     : https://prove2.me/theorems/255f18cc-0fee-4b40-9ee7-76d6e4933523
-- title:
--   Lift At
-- statement:
--   Definitions and structural lemmas for Lift At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LiftAt.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.SecLift
def LiftAt {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (X : Over (Sp R))
    (g₀ : Sp R₀ ⟶ X.left) (f : R) : Prop :=
  ∃ e : Sp (Localization.Away f) ⟶ X.left,
    e ≫ X.hom = spMap (algebraMap R (Localization.Away f)) ∧
    spMap (Localization.awayMap π f) ≫ e = spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀
def LiftIn {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (X : Over (Sp R))
    (g₀ : Sp R₀ ⟶ X.left) (f : R) (V : X.left.Opens) : Prop :=
  ∃ e : Sp (Localization.Away f) ⟶ X.left,
    e ≫ X.hom = spMap (algebraMap R (Localization.Away f)) ∧
    spMap (Localization.awayMap π f) ≫ e = spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀ ∧
    e ⁻¹ᵁ V = ⊤
end GlobalTheory.SecLift


