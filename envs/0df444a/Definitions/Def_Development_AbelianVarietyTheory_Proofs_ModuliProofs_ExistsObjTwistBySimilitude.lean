-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsObjTwistBySimilitude
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsObjTwistBySimilitude
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T13:57:21.438647+00:00
-- url     : https://prove2.me/theorems/abe50157-77e2-5ab0-8a2c-1ea42e4fb8e4
-- title:
--   Exists Obj Twist By Similitude
-- statement:
--   Definitions and structural lemmas for Exists Obj Twist By Similitude, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsObjTwistBySimilitude.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_of_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isPullCubical_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.LevelTwist
section Identity
variable {X : Scheme.{0}}
def selfIso (L : LB X) : LB.Iso L (L.pull (𝟙 X)) :=
  ⟨fun p => res (show (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2 from
    fun _ hx => ⟨mem_pull (F := 𝟙 X).1 hx.1, hx.2⟩) (L.g (p.1 PUnit.unit) p.2)⟩
theorem gw_selfIso (L : LB X) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j k : L.ι) (hj : f y ∈ L.U j)
    (hk : f y ∈ L.U k) : gw (selfIso L) f y j k = gm f y _ (L.g j k) :=
  gm_res f y _ (show f y ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k from ⟨mem_pull (F := 𝟙 X).2 hj, hk⟩) _
theorem pgen_selfIso {L : LB X} (hL : L.IsLB) : PGen (selfIso L) := by
  intro Y f y j j' k k' hj hj' hk hk'
  rw [gw_selfIso L f y j k hj hk, gw_selfIso L f y j' k' hj' hk', Category.comp_id, mul_right_comm,
    gm_cocycle hL f y hj hj' hk', ← gm_cocycle hL f y hj hk hk', mul_inv_cancel_right]
theorem pmaps_selfIso {L : LB X} {K : Type} [Fintype K] {Y : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : PMaps (selfIso L) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  have hm : r z ∈ LB.wchart L φ p ⊓ LB.wchart L φ q := ⟨Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩
  have h := congrArg (gm r z (LB.wchart L φ p ⊓ LB.wchart L φ q)) (ht p q)
  rw [Category.comp_id]
  refine (gm_res r z _ hm _).symm.trans (h.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ =>
    (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact ((gm_res r z _ hm _).trans (gm_pull r (φ k) z (L.U (p k) ⊓ L.U (q k)) ⟨hp k, hq k⟩ _)).trans
    (gw_selfIso L (r ≫ φ k) z (p k) (q k) (hp k) (hq k)).symm
variable {S : Scheme.{0}}
def cubeMapId (G : Over S) [GrpObj G] [IsCommMonObj G] : CubeMap G G where
  F := 𝟙 _
  F3 := 𝟙 _
  e := 𝟙 _
  e_comm := by rw [Category.id_comp, Category.comp_id]
  psum_comm := fun I => by rw [Category.id_comp, Category.comp_id]
theorem isPullCubical_id {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) :
    (cubeMapId G).IsPullCubical c c :=
  (isPullCubical_iff _ c c).2 ⟨selfIso L.L, pgen_selfIso L.isLB, pmaps_selfIso _ _ L.rig L.rigGen,
    pmaps_selfIso _ _ c.t c.isGen⟩
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def sabMapId (t : SAB H S) : SABMap t t (𝟙 S) where
  cm := cubeMapId t.G
  cart := @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl t.G) (inferInstanceAs (IsMonHom (𝟙 t.G)))
  base := rfl
  act := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm
  lin := isPullCubical_id t.cub
end Identity
section Twist
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
theorem ev_congr (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) {a a' : D.La} (h : D.ModN n (a - a')) :
    I.ev n a = I.ev n a' := by
  have : a = (a - a') + a' := (sub_add_cancel a a').symm
  rw [this, I.add, (I.ker n hn _).2 h, _root_.one_mul]
theorem zeta_zpow_congr (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) {i j : ℤ} (h : (n : ℤ) ∣ i - j) :
    I.ζ n ^ i = I.ζ n ^ j := by
  have : i = (i - j) + j := (sub_add_cancel i j).symm
  rw [this, zpow_add, ((I.ζ_prim n hn).zpow_eq_one_iff_dvd _).2 h, _root_.one_mul]
def twist (I : TateIso D k Q act e) (g : Sim D)
    (hν : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) :
    TateIso D k Q act e where
  ζ n := I.ζ n ^ g.ν n
  ζ_prim n hn := (I.ζ_prim n hn).zpow_of_gcd_eq_one _ (Int.isCoprime_iff_gcd_eq_one.1 (hν n 1 hn one_pos).2)
  ζ_pow n m hn hm := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm (g.ν _), zpow_mul, zpow_natCast, I.ζ_pow n m hn hm]
    exact zeta_zpow_congr I hn (hν n m hn hm).1
  ev n a := I.ev n (g.f n a)
  add n a b := by rw [map_add, I.add]
  lin n c a := by rw [map_smul, I.lin]
  ker n hn a := by
    rw [I.ker n hn]
    obtain ⟨g', hg'⟩ := g.inv n hn
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨c, hc⟩ := (hg' a).1
      refine ⟨g' b - c, ?_⟩
      rw [smul_sub, ← hc, hb, map_nsmul, sub_sub_cancel]
    · rintro ⟨b, rfl⟩
      exact ⟨g.f n b, map_nsmul _ _ _⟩
  onto n hn x := by
    rw [I.onto n hn]
    obtain ⟨g', hg'⟩ := g.inv n hn
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨g' a, ev_congr I hn (hg' a).2⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, rfl⟩
  tower n m hn hm a := by
    rw [I.tower n m hn hm]
    exact ev_congr I hn (g.tower n m hn hm a)
  isom n hn a b := by
    rw [← zpow_mul, ← zeta_zpow_congr I hn (g.mult n hn a b)]
    exact I.isom n hn _ _
@[simp] theorem twist_ζ (I : TateIso D k Q act e) (g : Sim D)
    (hν : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) (n : ℕ) :
    (twist I g hν).ζ n = I.ζ n ^ g.ν n := rfl
theorem map_mem_smul_top (f : D.La →ₗ[𝓞 E] D.La) (J : Ideal (𝓞 E)) {a : D.La}
    (ha : a ∈ J • (⊤ : Submodule (𝓞 E) D.La)) : f a ∈ J • (⊤ : Submodule (𝓞 E) D.La) := by
  have h := Submodule.mem_map_of_mem (f := f) ha
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h
variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}
def objTwist (o : Obj D l b s) (g : Sim D)
    (hν : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ))
    (hA : (l.A : ℤ) ∣ g.ν l.A - 1) : Obj D l b s where
  t := o.t
  proper := o.proper
  ample := o.ample
  ktriv := o.ktriv
  eta a := o.eta (g.f l.M a)
  eta_add a c := by rw [map_add, o.eta_add]
  eta_ker a ha := o.eta_ker _ (map_mem_smul_top _ _ ha)
  etaA a := o.etaA (g.f l.A a)
  etaA_add a c := by rw [map_add, o.etaA_add]
  etaA_ker a := by rw [map_nsmul, o.etaA_ker]
  geom k _ _ x β hx := by
    obtain ⟨hd, I, hζ, hA', hM⟩ := o.geom k x β hx
    refine ⟨hd, twist I g hν, ?_, fun a => hA' _, fun a ha => hM _ (map_mem_smul_top _ _ ha)⟩
    rw [twist_ζ, zeta_zpow_congr I l.A_pos hA, zpow_one, hζ]
end Twist
end GlobalTheory.LevelTwist
namespace GlobalTheory
end GlobalTheory


