-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGrpObjSplitExtensionOfGenerators
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGrpObjSplitExtensionOfGenerators
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T14:19:52.255795+00:00
-- url     : https://prove2.me/theorems/352de035-ea4e-41cb-a089-b8f156956cae
-- title:
--   Exists Grp Obj Split Extension Of Generators
-- statement:
--   Definitions and structural lemmas for Exists Grp Obj Split Extension Of Generators, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGrpObjSplitExtensionOfGenerators.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_PrimitiveCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.GeneratorLaw
section Rep
variable {X Y Y' : Scheme.{0}} {L : LB X}
abbrev Form (Y X : Scheme.{0}) := ∀ (V : Type) [CommGroup V], ((Y ⟶ X) → V) → V
abbrev Vals (L : LB X) (Y : Scheme.{0}) :=
  ∀ (Z : Scheme.{0}), (Z ⟶ Y) → ∀ z : Z, ((Z ⟶ X) → L.ι) → (Z.presheaf.stalk z)ˣ
variable (L) in

def Rep (σ : Form Y X) (F : Vals L Y) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (V : Type) [CommGroup V] (h : (Y ⟶ X) → V), ∏ k, h (φ k) ^ ε k = σ V h) ∧
    ∀ Z r z J, Good L z J → val t r z J = F Z r z J
theorem Rep.pull {σ : Form Y X} {F : Vals L Y} (h : Rep L σ F) (f : Y' ⟶ Y) :
    Rep L (fun V _ k => σ V fun a => k (f ≫ a)) (fun Z r z J => F Z (r ≫ f) z J) := by
  obtain ⟨K, _, φ, ε, t, ht, hs, hv⟩ := h
  refine ⟨K, inferInstance, _, _, LB.pullGen L _ _ t f, DVR.pullGen_isGen _ _ _ _ ht _,
    fun V _ k => hs V fun a => k (f ≫ a), fun Z r z J hJ => ?_⟩
  rw [val_pull hJ, hv _ _ _ _ hJ]
end Rep
section Points
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {κ : Type} (O : κ → RigLB B) {G : Over S} (q : G ⟶ B)
  (u : ∀ k (i : (O k).L.ι), Γ(G.left, q.left ⁻¹ᵁ (O k).L.U i)ˣ)
abbrev PV (W : Over S) : Type :=
  ∀ (k : κ) (z : W.left) (_ : {J // Good (O k).L z J}), (W.left.presheaf.stalk z)ˣ
def cv (k : κ) : Vals (O k).L G.left :=
  fun _ g z J => gm g z (q.left ⁻¹ᵁ (O k).L.U (J (g ≫ q.left))) (u k _)
def rv (k : κ) : Vals (O k).L S :=
  fun _ e z J => val (L := (O k).L) (φ := fun _ : PUnit => eSec B) (ε := fun _ => 1) (O k).rig e z J
def nv {W : Over S} (x : W ⟶ G) : PV O W :=
  fun k z J => cv O q u k _ x.left z J.1 * rv O k _ W.hom z J.1
def av {Y W : Over S} (a : κ → Γ(Y.left, ⊤)ˣ) (r : W ⟶ Y) : PV O W := fun k z _ => gm r.left z ⊤ (a k)
variable {O q u}
variable [IsCommMonObj B] (t : ∀ k, LB.Gen (abelian₂ B (O k).L))
def vv {W : Over S} (x y : W ⟶ B) : PV O W := fun k z J =>
  val (L := (O k).L) (φ := PrimCocycle.lamφ B) (ε := PrimCocycle.lamε) (t k) (lift x y).left z J.1
variable {t}
end Points
section Torus
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {W : Over S}
end Torus
section Main
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {κ : Type} {O : κ → RigLB B} {G : Over S}
  {q : G ⟶ B} {u : ∀ k (i : (O k).L.ι), Γ(G.left, q.left ⁻¹ᵁ (O k).L.U i)ˣ}
end Main
section Chart
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {κ : Type} {O : κ → RigLB B} {G : Over S} [GrpObj G]
  {q : G ⟶ B} {u : ∀ k (i : (O k).L.ι), Γ(G.left, q.left ⁻¹ᵁ (O k).L.U i)ˣ}
end Chart
end GlobalTheory.GeneratorLaw


