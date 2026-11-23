-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_ThetaCharacteristics_ThetaCharZero
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_ThetaCharacteristics_ThetaCharZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:55:41.014797+00:00
-- url     : https://prove2.me/theorems/2adfd28d-b551-4c74-8c73-c8218d9259ca
-- title:
--   Theta Char Zero
-- statement:
--   Definitions and structural lemmas for Theta Char Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/ThetaCharacteristics/ThetaCharZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.Published
def CanonKeySt : Prop :=
  ∃ κ : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R], KeyIn R → Rˣ,
    (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R], GlobalTheory.KeyPow.ClauseH R (fun _ => 1) 1 (κ R)) ∧
    (∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R]
      [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsPrincipalIdealRing R'] (f : R →+* R') (x : KeyIn R) (x' : KeyIn R'),
      KeyPB x' x f → (κ R' x' : R') = f (κ R x)) ∧
    ∀ (x : KeyIn ℂ) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ), GlobalTheory.KeyPow.NormalAt x τ 1 0 0 1 → κ ℂ x = 1
namespace CanonKeySt
end CanonKeySt
end GlobalTheory.Published
abbrev GlobalTheory.KeyPow.CanonKey : Prop := GlobalTheory.Published.CanonKeySt


