-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ObjMapIdCompCancel
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ObjMapIdCompCancel
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T13:31:04.333544+00:00
-- url     : https://prove2.me/theorems/8be3a1b6-32e0-4666-b4ca-3911ddfe54e7
-- title:
--   Obj Map Id Comp Cancel
-- statement:
--   Definitions and structural lemmas for Obj Map Id Comp Cancel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ObjMapIdCompCancel.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isPullCubical_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mul_left_congr

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
namespace GlobalTheory.ObjComp
section Bundle
variable {X : Scheme.{0}}
def idPullIso (L : LB X) : LB.Iso L (L.pull (𝟙 X)) :=
  ⟨fun p => res (fun _ hy => ⟨mem_pull.1 hy.1, hy.2⟩ :
    (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2) (L.g (p.1 PUnit.unit) p.2)⟩
theorem gw_idPullIso (L : LB X) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j k : L.ι) (hj : f y ∈ L.U j)
    (hk : f y ∈ L.U k) : gw (idPullIso L) f y j k = gm f y _ (L.g j k) := by
  have hm : f y ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k := ⟨mem_pull.2 hj, hk⟩
  show gm f y _ (res _ (L.g j k)) = _
  exact gm_res f y _ hm _
theorem pgen_idPullIso {L : LB X} (hL : L.IsLB) : PGen (idPullIso L) := by
  intro Y f y j j' k k' hj hj' hk hk'
  have hj₀ : f y ∈ L.U j := hj
  have hj₀' : f y ∈ L.U j' := hj'
  rw [gw_idPullIso L f y j k hj₀ hk, gw_idPullIso L f y j' k' hj₀' hk', Category.comp_id]
  have a := gm_cocycle hL f y hj₀ hk hk'
  have b := gm_cocycle hL f y hj₀ hj₀' hk'
  rw [mul_right_comm, b, ← a, mul_inv_cancel_right]
theorem pmaps_idPullIso (L : LB X) {K : Type} [Fintype K] {Y : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : PMaps (idPullIso L) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  have hp₀ : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  have hm : r z ∈ LB.wchart L φ p ⊓ LB.wchart L φ q := ⟨Set.mem_iInter.2 hp₀, Set.mem_iInter.2 hq⟩
  have e := congrArg (gm r z (LB.wchart L φ p ⊓ LB.wchart L φ q)) (ht p q)
  rw [Category.comp_id]
  refine (gm_res r z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  rw [gw_idPullIso L (r ≫ φ k) z (p k) (q k) (hp₀ k) (hq k)]
  exact (gm_res r z _ hm _).trans (gm_pull r (φ k) z (L.U (p k) ⊓ L.U (q k)) ⟨hp₀ k, hq k⟩ _)
end Bundle
section Group
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]
theorem isGrpPullback_id : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (mul_left_congr (b := T.hom) (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _))
    (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm
variable [IsCommMonObj G]
def cubeMapId : CubeMap G G where
  F := 𝟙 _
  F3 := 𝟙 _
  e := 𝟙 _
  e_comm := by rw [Category.comp_id, Category.id_comp]
  psum_comm := fun _ => by rw [Category.comp_id, Category.id_comp]
theorem isPullCubical_id {L : RigLB G} (c : CubicalStr G L) : (cubeMapId G).IsPullCubical c c :=
  (isPullCubical_iff _ c c).2 ⟨idPullIso L.L, pgen_idPullIso L.isLB,
    pmaps_idPullIso L.L _ _ L.rig L.rigGen, pmaps_idPullIso L.L _ _ c.t c.isGen⟩
end Group
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def sabMapId {S : Scheme.{0}} (t : SAB H S) : SABMap t t (𝟙 S) where
  cm := cubeMapId t.G
  cart := isGrpPullback_id t.G
  base := rfl
  act := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm
  lin := isPullCubical_id t.G t.cub
variable {D : Datum H} {l : Level H}
def objMapId {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s) :
    ObjMap o o (𝟙 S) where
  toSABMap := sabMapId o.t
  eta := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm
  etaA := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm
section
variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {b : Base l B} {b' : Base l B'} {b'' : Base l B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {o : Obj D l b s} {o' : Obj D l b' s'} {o'' : Obj D l b'' s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
end
end GlobalTheory.ObjComp
namespace GlobalTheory
end GlobalTheory


