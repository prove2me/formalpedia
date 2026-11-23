-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:51.668719+00:00
-- url     : https://prove2.me/theorems/9042980b-d3ea-494e-b4fc-0218caee073d
-- title:
--   Weil Is Alternating Skew Natural
-- statement:
--   Definitions and structural lemmas for Weil Is Alternating Skew Natural, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsAlternatingSkewNatural.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}
def tval {T : Over S} (θ : ThetaGrp A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : (Z.presheaf.stalk z)ˣ :=
  val (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ r z J
end GlobalTheory.CommPairing
namespace GlobalTheory
end GlobalTheory


