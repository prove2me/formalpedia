-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueTwistedSectionOfCompatibleLevels
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueTwistedSectionOfCompatibleLevels
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-27T06:20:03.307991+00:00
-- url     : https://prove2.me/theorems/e1b2bddc-cbe1-5c55-b9ff-e9434bd3cde1
-- title:
--   Exists Unique Twisted Section Of Compatible Levels
-- statement:
--   Definitions and structural lemmas for Exists Unique Twisted Section Of Compatible Levels, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueTwistedSectionOfCompatibleLevels.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.SecLimit
section Twist
variable {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (k : ℕ) (α : D.X)
abbrev twφ (T : Over (Spec (CommRingCat.of V))) : Fin 2 → ((T ⊗ D.P.A).left ⟶ D.P.A.left) :=
  ![(snd T D.P.A).left, (translPt D.P.A (toUnit T ≫ D.c α)).left]
abbrev ptφ : Fin 2 → (Spec (CommRingCat.of V) ⟶ D.P.A.left) := ![(D.c α).left, (η[D.P.A]).left]
abbrev famVals {Y : Scheme.{0}} (π : Y ⟶ D.P.A.left) : Set (Vals D.P.L Y) :=
  secVals D.P.L (fun i => π ≫ D.famφB α i) (DegPre.famε k)
variable {D k α}
variable [IsLocalRing V]
abbrev resPt (V : Type) [CommRing V] [IsLocalRing V] : Over (Spec (CommRingCat.of V)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) ≫ 𝟙 _)
end Twist
end GlobalTheory.SecLimit


