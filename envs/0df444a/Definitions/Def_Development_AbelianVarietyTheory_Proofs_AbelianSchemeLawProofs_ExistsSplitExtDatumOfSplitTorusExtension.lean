-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtension
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:39:51.57612+00:00
-- url     : https://prove2.me/theorems/2c5db6b6-6fbd-4f03-8aeb-03471303cf56
-- title:
--   Exists Split Ext Datum Of Split Torus Extension
-- statement:
--   Definitions and structural lemmas for Exists Split Ext Datum Of Split Torus Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitExtDatumOfSplitTorusExtension.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace ToSplit
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
section Germs
variable {X Y Z : Scheme.{0}}
theorem gm_res_pull (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) {U : X.Opens} {V : Y.Opens} (hle : V ≤ f ⁻¹ᵁ U)
    (h : r z ∈ V) (a : Γ(X, U)ˣ) : gm r z V (res hle (pullU f U a)) = gm (r ≫ f) z U a :=
  (gm_res r z hle h _).trans (gm_pull r f z U (hle h) a)
theorem gm_id_res_pull (f : Y ⟶ X) (y : Y) {U : X.Opens} {V : Y.Opens} (hle : V ≤ f ⁻¹ᵁ U)
    (h : y ∈ V) (a : Γ(X, U)ˣ) : gm (𝟙 Y) y V (res hle (pullU f U a)) = gm f y U a := by
  rw [gm_res_pull (𝟙 Y) f y hle h, Category.id_comp]
end Germs
section Descent
variable {S : Scheme.{0}} {X Y : Over S} (π : Y ⟶ X) [Flat π.left] [Surjective π.left]
  [QuasiCompact π.left]
end Descent
section Weight
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
noncomputable def charGerm {Z : Over S} (z : Z.left) :
    (Z ⟶ splitTorus S X) →* (Multiplicative X →* (Z.left.presheaf.stalk z)ˣ) :=
  (MonoidHom.compHom (gm (𝟙 Z.left) z ⊤)).comp (splitTorusPointsEquiv S X Z).toMonoidHom
def HasWeight (q : G ⟶ B) (i : splitTorus S X ⟶ G) (χ : X) (V : B.left.Opens)
    (u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ) : Prop :=
  ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left), q.left (g.left z) ∈ V →
    gm ((t ≫ i) * g).left z _ u = charGerm z t (Multiplicative.ofAdd χ) * gm g.left z _ u
variable {q : G ⟶ B} {i : splitTorus S X ⟶ G} [IsMonHom q]
  (hk : IsPullback i (toUnit _) q (η[B]))
include hk
omit hk [GrpObj B] [IsMonHom q] in
theorem HasWeight.appLE {χ : X} {V : B.left.Opens} {u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ}
    (hu : HasWeight q i χ V u) (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G)
    (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ (q.left ⁻¹ᵁ V)) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)) :
    (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom u.val =
      t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom u.val := by
  have : res h₁ (pullU _ _ u) =
      splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd χ) * res h₂ (pullU _ _ u) :=
    unit_ext fun z hz => by
      rw [gm_id_res_pull _ z h₁ hz, hu Z t g z (h₂ hz), map_mul, gm_id_res_pull _ z h₂ hz]
      rfl
  rw [← splitTorusPointsEquiv_val]
  exact congrArg Units.val this
end Weight
section Sums
variable {S : Scheme.{0}}
end Sums
section Bundle
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
def IsFrame (q : G ⟶ B) (i : splitTorus S X ⟶ G) (χ : X) (O : RigLB B)
    (u : ∀ j, Γ(G.left, q.left ⁻¹ᵁ O.L.U j)ˣ) : Prop :=
  (∀ j, HasWeight q i χ (O.L.U j) (u j)) ∧
  (∀ j j' (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z), q.left (r z) ∈ O.L.U j →
    q.left (r z) ∈ O.L.U j' → gm (r ≫ q.left) z (O.L.U j ⊓ O.L.U j') (O.L.g j j') =
      gm r z _ (u j') / gm r z _ (u j)) ∧
  ∀ j (z : (𝟙_ (Over S)).left), eSec B z ∈ O.L.U j →
    gm (𝟙 _) z ((O.L.pull (eSec B)).U (fun _ => j)) (O.rig.s (fun _ => j)) =
      (gm (eSec G) z _ (u j))⁻¹
variable {q : G ⟶ B} {i : splitTorus S X ⟶ G} [IsMonHom q] [IsMonHom i]
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
  (hk : IsPullback i (toUnit _) q (η[B]))
include hk
end Bundle
section Laws
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
  {q : G ⟶ B} {i : splitTorus S X ⟶ G} [IsMonHom q] [IsMonHom i]
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
  (hk : IsPullback i (toUnit _) q (η[B]))
include hk
end Laws
section Datum
attribute [local instance] SplitExt.free SplitExt.finite
variable {S : Scheme.{0}} (E : SplitExt S) {G : Over S} [GrpObj G]
  {q : G ⟶ E.B} {i : splitTorus S E.X ⟶ G} [IsMonHom q] [IsMonHom i]
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
  (hk : IsPullback i (toUnit _) q (η[E.B]))
include hk
end Datum
end ToSplit
end GlobalTheory


