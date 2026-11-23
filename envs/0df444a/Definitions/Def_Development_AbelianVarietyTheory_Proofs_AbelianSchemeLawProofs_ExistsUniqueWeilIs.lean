-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:31:02.218782+00:00
-- url     : https://prove2.me/theorems/b432f188-fd0b-41a7-82a3-64dbdae94b22
-- title:
--   Exists Unique Weil Is
-- statement:
--   Definitions and structural lemmas for Exists Unique Weil Is, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueWeilIs.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.CommutatorPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable {L : LB A.left} {k : ℤ}
def thetaVal {T Z : Over S} (θ : ThetaGrp A L k T) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left)
    (J : (Z.left ⟶ A.left) → L.ι) : (Z.left.presheaf.stalk z)ˣ :=
  val (L := L) (K := Fin 2) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (lift t a).left z J
def commVal {T Z : Over S} (θx θy : ThetaGrp A L k T) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left)
    (J : (Z.left ⟶ A.left) → L.ι) : (Z.left.presheaf.stalk z)ˣ :=
  thetaVal θx t a z J * thetaVal θy t ((t ≫ θx.pt) * a) z J *
    (thetaVal θy t a z J * thetaVal θx t ((t ≫ θy.pt) * a) z J)⁻¹
def overLE {T : Over S} {V W : T.left.Opens} (h : V ≤ W) : overRes V ⟶ overRes W :=
  Over.homMk (T.left.homOfLE h) (by
    show T.left.homOfLE h ≫ W.ι ≫ T.hom = V.ι ≫ T.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])
end GlobalTheory.CommutatorPairing


