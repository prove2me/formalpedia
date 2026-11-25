-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T15:23:43.649498+00:00
-- url     : https://prove2.me/theorems/474e69a9-1412-4f26-80ec-108b1e4e376a
-- title:
--   Exists Stalk Hom
-- statement:
--   Definitions and structural lemmas for Exists Stalk Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsStalkHom.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Theorems.Thm_GlobalTheory_UU_IsWt_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU TopologicalSpace
noncomputable section
namespace GlobalTheory.EquivDesc
variable {S : Scheme.{0}}
abbrev opn {G : Over S} (U : G.left.Opens) : Over S := Over.mk (U.ι ≫ G.hom)
abbrev opnι {G : Over S} (U : G.left.Opens) : opn U ⟶ G := Over.homMk U.ι rfl
section Action
variable {G H : Over S} [GrpObj G] [GrpObj H] {i : H ⟶ G} {L : LB G.left}
abbrev actφ (i : H ⟶ G) : Fin 2 → ((H ⊗ G).left ⟶ G.left) := ![((fst H G ≫ i) * snd H G).left, (snd H G).left]
def av (a : LB.Gen (LB.LinComb L (actφ i) ![1, -1])) {T : Over S} (t : T ⟶ H) (x : T ⟶ G) (z : T.left)
    (k₁ k₂ : L.ι) : (T.left.presheaf.stalk z)ˣ :=
  gm (lift t x).left z (LB.wchart L (actφ i) ![k₁, k₂]) (a.s ![k₁, k₂])
variable {a : LB.Gen (LB.LinComb L (actφ i) ![1, -1])}
def IsAct (a : LB.Gen (LB.LinComb L (actφ i) ![1, -1])) : Prop :=
  ∀ (T : Over S) (t t' : T ⟶ H) (x : T ⟶ G) (z : T.left) (J), Good L z J →
    val a (lift (t * t') x).left z J = val a (lift t ((t' ≫ i) * x)).left z J * val a (lift t' x).left z J
end Action
section Local
variable {G B H : Over S} [GrpObj G] [GrpObj B] [GrpObj H] {q : G ⟶ B} {i : H ⟶ G} [IsMonHom q] [IsMonHom i]
  {L : LB G.left} {a : LB.Gen (LB.LinComb L (actφ i) ![1, -1])}
structure InvGen (q : G ⟶ B) (a : LB.Gen (LB.LinComb L (actφ i) ![1, -1])) (V : B.left.Opens)
    (e : ∀ k, Γ(G.left, q.left ⁻¹ᵁ V ⊓ L.U k)ˣ) : Prop where
  gen : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (k k' : L.ι), q.left (f y) ∈ V → f y ∈ L.U k → f y ∈ L.U k' →
    gm f y _ (e k) = gm f y _ (L.g k k') * gm f y _ (e k')
  inv : ∀ (T : Over S) (t : T ⟶ H) (x : T ⟶ G) (z : T.left) (k₁ k₂ : L.ι), q.left (x.left z) ∈ V →
    ((t ≫ i) * x).left z ∈ L.U k₁ → x.left z ∈ L.U k₂ →
    gm ((t ≫ i) * x).left z _ (e k₁) = av a t x z k₁ k₂ * gm x.left z _ (e k₂)
end Local
section Global
variable {G B H : Over S} [GrpObj G] [GrpObj B] [GrpObj H] {q : G ⟶ B} {i : H ⟶ G} [IsMonHom q] [IsMonHom i]
  {L : LB G.left} {a : LB.Gen (LB.LinComb L (actφ i) ![1, -1])}
end Global
end GlobalTheory.EquivDesc
end


