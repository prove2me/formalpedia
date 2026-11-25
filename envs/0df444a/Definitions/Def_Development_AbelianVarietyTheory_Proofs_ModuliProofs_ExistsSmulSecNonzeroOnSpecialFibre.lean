-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibre
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibre
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T14:44:18.089956+00:00
-- url     : https://prove2.me/theorems/c79a2595-fa49-4fd1-a3e3-409c6e60ea73
-- title:
--   Exists Smul Sec Nonzero On Special Fibre
-- statement:
--   Definitions and structural lemmas for Exists Smul Sec Nonzero On Special Fibre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmulSecNonzeroOnSpecialFibre.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.PrimSec
section General
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
theorem pre_le (π : X' ⟶ X) {U V : X.Opens} (h : V ≤ U) : π ⁻¹ᵁ V ≤ π ⁻¹ᵁ U := fun _ hy => h hy
end General
section Generic
variable {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
  {X XK : Scheme.{0}} {f : X ⟶ Sp O} {j : XK ⟶ X} {fK : XK ⟶ Sp K}
  (H : IsPullback j fK f (spMap (algebraMap O K)))
include H
end Generic
section Sections
variable {X XK : Scheme.{0}} {j : XK ⟶ X} {M : LB X}
def loc (σ : LB.Sec (M.pull j)) (i : M.ι) {V : X.Opens} (hV : V ≤ M.U i) : Γ(XK, j ⁻¹ᵁ V) :=
  rs XK (le_pull M j hV) (σ.f (fun _ => i))
end Sections
section Main
variable {O K : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  {X XK : Scheme.{0}} {f : X ⟶ Sp O} {j : XK ⟶ X} {fK : XK ⟶ Sp K}
  (H : IsPullback j fK f (spMap (algebraMap O K))) {M : LB X} (σ : LB.Sec (M.pull j))
include H
end Main
end GlobalTheory.PrimSec


