-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsPullCubicalId
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsPullCubicalId
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:31:50.572875+00:00
-- url     : https://prove2.me/theorems/6af8fc55-b993-5430-bfde-cb6c8144ca91
-- title:
--   Is Pull Cubical Id
-- statement:
--   Definitions and structural lemmas for Is Pull Cubical Id, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsPullCubicalId.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.ObjRebase
def pullIdIso {X : Scheme.{0}} (L : LB X) : LB.Iso L (L.pull (𝟙 X)) where
  s := fun p => res (X := X) (U := L.U (p.1 PUnit.unit) ⊓ L.U p.2)
    (V := (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2) (fun _ hx => ⟨mem_pull.1 hx.1, hx.2⟩) (L.g (p.1 PUnit.unit) p.2)
theorem gw_pullIdIso {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (y : Y) (j k : L.ι) (hj : f y ∈ L.U j)
    (hk : f y ∈ L.U k) : gw (pullIdIso L) f y j k = gm f y (L.U j ⊓ L.U k) (L.g j k) := by
  have hm : f y ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k := ⟨mem_pull.2 hj, hk⟩
  exact gm_res f y _ hm _
theorem pgen_pullIdIso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : PGen (pullIdIso L) := by
  intro Y f y j j' k k' hj hj' hk hk'
  have hj₁ : f y ∈ L.U j := hj
  have hj₂ : f y ∈ L.U j' := hj'
  rw [gw_pullIdIso L f y j k hj₁ hk, gw_pullIdIso L f y j' k' hj₂ hk', Category.comp_id]
  have a := gm_cocycle hL f y hj₁ hk hk'
  have b := gm_cocycle hL f y hj₁ hj₂ hk'
  rw [mul_right_comm, b, ← a, mul_inv_cancel_right]
theorem pmaps_pullIdIso {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : PMaps (pullIdIso L) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  have hp' : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  have hm : r z ∈ LB.wchart L φ p ⊓ LB.wchart L φ q := ⟨Set.mem_iInter.2 hp', Set.mem_iInter.2 hq⟩
  have e := congrArg (gm r z (LB.wchart L φ p ⊓ LB.wchart L φ q)) (ht p q)
  rw [Category.comp_id]
  refine (gm_res r z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  refine (gm_res r z _ hm _).trans ((gm_pull r (φ k) z (L.U (p k) ⊓ L.U (q k)) ⟨hp' k, hq k⟩ _).trans ?_)
  exact (gw_pullIdIso L (r ≫ φ k) z (p k) (q k) (hp' k) (hq k)).symm
def cubeMapId {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] : CubeMap G G where
  F := 𝟙 _
  F3 := 𝟙 _
  e := 𝟙 _
  e_comm := by rw [Category.comp_id, Category.id_comp]
  psum_comm := fun _ => by rw [Category.comp_id, Category.id_comp]
theorem isPullCubical_id {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {L : RigLB G}
    (c : CubicalStr G L) : (cubeMapId G).IsPullCubical c c :=
  (isPullCubical_iff _ _ _).2 ⟨pullIdIso L.L, pgen_pullIdIso L.isLB,
    pmaps_pullIdIso (K := PUnit) (fun _ => eSec G) (fun _ => 1) L.rig L.rigGen,
    pmaps_pullIdIso (thφ G (x3 G)) thε c.t c.isGen⟩
theorem isGrpPullback_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (mul_left_congr (G := G) (Category.comp_id T.hom) x₀ y₀ x y (hx.trans (Category.comp_id _))
    (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def sabMapId {S : Scheme.{0}} (t : SAB H S) : SABMap t t (𝟙 S) where
  cm := cubeMapId t.G
  cart := isGrpPullback_id t.G
  base := rfl
  act := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm
  lin := isPullCubical_id t.G t.cub
theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl
theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)
theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (x : Sp B ⟶ Sp A) : ∃ f : A →+* B, x = spMap f :=
  ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
variable {D : Datum H} {l : Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}
def up (j : B →+* B') (hρ : j b.ρ = b'.ρ) (hζ : j b.ζ = b'.ζ) {S : Scheme.{0}} {s' : S ⟶ Sp B'}
    (o : Obj D l b (s' ≫ spMap j)) : Obj D l b' s' :=
  { t := o.t, proper := o.proper, ample := o.ample, ktriv := o.ktriv
    eta := o.eta, eta_add := o.eta_add, eta_ker := o.eta_ker
    etaA := o.etaA, etaA_add := o.etaA_add, etaA_ker := o.etaA_ker
    geom := fun k _ _ x β hx => by
      have h := o.geom k x (β.comp j) (by rw [← Category.assoc, hx, spMap_comp'])
      rwa [RingHom.comp_apply, RingHom.comp_apply, hρ, hζ] at h }
def down (j : B →+* B') (hρ : j b.ρ = b'.ρ) (hζ : j b.ζ = b'.ζ) {S : Scheme.{0}} {s' : S ⟶ Sp B'}
    (o : Obj D l b' s') : Obj D l b (s' ≫ spMap j) :=
  { t := o.t, proper := o.proper, ample := o.ample, ktriv := o.ktriv
    eta := o.eta, eta_add := o.eta_add, eta_ker := o.eta_ker
    etaA := o.etaA, etaA_add := o.etaA_add, etaA_ker := o.etaA_ker
    geom := fun k _ _ x β hx => by
      obtain ⟨β', hβ'⟩ := exists_spMap (x ≫ s')
      obtain rfl : β'.comp j = β := spMap_inj (by rw [spMap_comp', ← hβ', Category.assoc, hx])
      have h := o.geom k x β' hβ'
      rwa [RingHom.comp_apply, RingHom.comp_apply, hρ, hζ] }
end GlobalTheory.ObjRebase


