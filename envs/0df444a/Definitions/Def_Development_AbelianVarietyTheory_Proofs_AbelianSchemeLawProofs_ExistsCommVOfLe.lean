-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:35:43.841972+00:00
-- url     : https://prove2.me/theorems/aff48af9-71ed-4203-afc6-d72614debfff
-- title:
--   Exists Comm VOf Le
-- statement:
--   Definitions and structural lemmas for Exists Comm VOf Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsCommVOfLe.lean

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
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.WeilMul
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}
def tv {T T' : Over S} (θ : ThetaGrp A L k T) (t : T' ⟶ T) (a : T' ⟶ A) (z : T'.left)
    (J : (T'.left ⟶ A.left) → L.ι) : (T'.left.presheaf.stalk z)ˣ :=
  val (L := L) (K := Fin 2) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (lift t a).left z J
def CommV {T T₀ : Over S} (θx θy : ThetaGrp A L k T) (g : T ⟶ T₀) (c : Γ(T₀.left, ⊤)ˣ) : Prop :=
  ∀ (T' : Over S) (t : T' ⟶ T) (a : T' ⟶ A) (z : T'.left) (J), Good L z J →
    tv θx t a z J * tv θy t ((t ≫ θx.pt) * a) z J =
      tv θy t a z J * tv θx t ((t ≫ θy.pt) * a) z J * gm (t ≫ g).left z ⊤ c
end GlobalTheory.WeilMul
namespace GlobalTheory
end GlobalTheory


