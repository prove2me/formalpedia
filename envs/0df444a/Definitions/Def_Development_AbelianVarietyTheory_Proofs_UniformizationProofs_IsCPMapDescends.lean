-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapDescends
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapDescends
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T14:42:41.061938+00:00
-- url     : https://prove2.me/theorems/b9a8017e-12df-4afa-ad78-9bca5207dd3e
-- title:
--   Is CPMap Descends
-- statement:
--   Definitions and structural lemmas for Is CPMap Descends, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsCPMapDescends.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
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
namespace GlobalTheory.IsoDesc
section Schemes
variable {X Y Z : Scheme.{0}}
def kap (σ : Z ⟶ Y) (z : Z) : (Y.presheaf.stalk (σ z))ˣ →* (Z.presheaf.stalk z)ˣ :=
  Units.map (σ.stalkMap z).hom.toMonoidHom
variable {G B' B : Scheme.{0}} {L : LB G} {M' : LB B'} {M : LB B} {q : G ⟶ B'} {β : B' ⟶ B}
abbrev dom (M' : LB B') (M : LB B) (β : B' ⟶ B) (j : M.ι) (i : M'.ι) : B'.Opens :=
  (M.pull β).U (fun _ => j) ⊓ M'.U i
def IsQuot (u : LB.Iso L (M'.pull q)) (w : LB.Iso L (M.pull (q ≫ β)))
    (s : ∀ j i, Γ(G, q ⁻¹ᵁ dom M' M β j i)ˣ) : Prop :=
  ∀ (Y : Scheme.{0}) (f : Y ⟶ G) (y : Y) (j : M.ι) (i : M'.ι) (k : L.ι), β (q (f y)) ∈ M.U j → q (f y) ∈ M'.U i →
    f y ∈ L.U k → gw w f y j k = gm f y _ (s j i) * gw u f y i k
end Schemes
section Groups
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G B' : Over S'} {B : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj B']
  [IsCommMonObj B'] [GrpObj B] [IsCommMonObj B] {P : CP G} {M' : CP B'} {M : CP B} {q : G ⟶ B'}
  {β : B'.left ⟶ B.left} {hβ : β ≫ B.hom = B'.hom ≫ f}
def Eqns (M' : CP B') (M : CP B) (hβ : β ≫ B.hom = B'.hom ≫ f) {T : Over S'} (z : T.left)
    (I : (T.left ⟶ B'.left) → M'.L.L.ι) (J : (T.left ⟶ B.left) → M.L.L.ι) {A : Type} [Group A] (π : A → (T ⟶ B'))
    (V : A → (T.left.presheaf.stalk z)ˣ) : Prop :=
  (val (L := M.L.L) (φ := fun _ : PUnit => eSec B) (ε := fun _ => 1) M.L.rig (T.hom ≫ f) z J =
    V 1 * val (L := M'.L.L) (φ := fun _ : PUnit => eSec B') (ε := fun _ => 1) M'.L.rig T.hom z I) ∧
  (∀ x, val M.sym ((π x).left ≫ β) z J * V x = V x⁻¹ * val M'.sym (π x).left z I) ∧
  ∀ x y u, @id (T.left.presheaf.stalk z)ˣ (cubV M.c (T := Over.mk (T.hom ≫ f)) z J (toBase hβ (π x))
      (toBase hβ (π y)) (toBase hβ (π u))) * V (x * y) * V (x * u) * V (y * u) * V 1 =
    V (x * y * u) * V x * V y * V u * cubV M'.c z I (π x) (π y) (π u)
end Groups
section Torus
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] (Y : Over S) [ConnectedSpace Y.left]
end Torus
section Main
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] [Module.Free ℤ X] {G : Over S'} {B : Over S}
  [GrpObj G] [IsCommMonObj G] [ConnectedSpace G.left] [GrpObj B] [IsCommMonObj B] {Q : TQ G X} {P : CP G}
  {M' : CP Q.B} {M : CP B} {β : Q.B.left ⟶ B.left} {hβ : β ≫ B.hom = Q.B.hom ≫ f}
end Main
end GlobalTheory.IsoDesc
end


