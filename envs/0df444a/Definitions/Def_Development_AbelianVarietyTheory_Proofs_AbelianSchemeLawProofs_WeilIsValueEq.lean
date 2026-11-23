-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsValueEq
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsValueEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:20.220274+00:00
-- url     : https://prove2.me/theorems/33ceda15-14f4-4206-9d63-756dedf875b0
-- title:
--   Weil Is Value Eq
-- statement:
--   Definitions and structural lemmas for Weil Is Value Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsValueEq.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
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
open GlobalTheory.CommutatorPairing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PairingLevels
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left)
def pt {Y : Over S} (a : Y ⟶ A) : FreeAbelianGroup (Y.left ⟶ A.left) := FreeAbelianGroup.of a.left
abbrev ValFam (Y : Over S) : Type 1 :=
  ∀ (Z : Over S) (_ : Z ⟶ Y) (z : Z.left) (_ : (Z.left ⟶ A.left) → L.ι), (Z.left.presheaf.stalk z)ˣ
def Rep {Y : Over S} (D : FreeAbelianGroup (Y.left ⟶ A.left)) (f : ValFam L Y) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y.left ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
    t.IsGen ∧ ∑ k, ε k • FreeAbelianGroup.of (φ k) = D ∧
      ∀ (Z : Over S) (r : Z ⟶ Y) (z : Z.left) (J), Good L z J → val t r.left z J = f Z r z J
variable {L} {Y : Over S} {D D' : FreeAbelianGroup (Y.left ⟶ A.left)} {f f' : ValFam L Y}
def cubeVal (t : LB.Gen (Theta A L)) {Z : Over S} (z : Z.left) (J : (Z.left ⟶ A.left) → L.ι) (a b c : Z ⟶ A) :
    (Z.left.presheaf.stalk z)ˣ := val (L := L) (φ := thφ A (x3 A)) (ε := thε) t (lift a (lift b c)).left z J
end GlobalTheory.PairingLevels


