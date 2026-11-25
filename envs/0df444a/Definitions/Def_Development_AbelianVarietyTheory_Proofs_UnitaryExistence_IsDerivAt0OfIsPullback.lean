-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDerivAt0OfIsPullback
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDerivAt0OfIsPullback
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T13:49:43.048261+00:00
-- url     : https://prove2.me/theorems/33d18ccf-45f7-5d6b-9096-d39ce7169463
-- title:
--   Is Deriv At0 Of Is Pullback
-- statement:
--   Definitions and structural lemmas for Is Deriv At0 Of Is Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsDerivAt0OfIsPullback.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology
namespace GlobalTheory
namespace FibreDeriv
variable {g : ℕ} {X Y : Scheme.{0}}
def jet (w : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ) : DualNumber ℂ :=
  TrivSqZeroExt.inl (F 0) + TrivSqZeroExt.inr (fderiv ℂ F 0 w)
def evEps (v : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) : Γ(X, U) →+* DualNumber ℂ :=
  (v.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom).hom
end FibreDeriv
end GlobalTheory


