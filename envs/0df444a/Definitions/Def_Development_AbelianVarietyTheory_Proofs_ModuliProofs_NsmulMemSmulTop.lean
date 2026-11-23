-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NsmulMemSmulTop
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_NsmulMemSmulTop
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:00:56.403983+00:00
-- url     : https://prove2.me/theorems/122ccb6a-6469-4ef5-9c8c-80bdb64ae3d8
-- title:
--   Nsmul Mem Smul Top
-- statement:
--   Definitions and structural lemmas for Nsmul Mem Smul Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NsmulMemSmulTop.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ObjLower
section Identity
variable {X : Scheme.{0}}
def idIso (L : LB X) : LB.Iso L (L.pull (𝟙 X)) where
  s := fun p => res (fun _ hx => ⟨mem_pull.1 hx.1, hx.2⟩ :
    (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2) (L.g (p.1 PUnit.unit) p.2)
theorem gw_idIso (L : LB X) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j k : L.ι) (hj : f y ∈ L.U j) (hk : f y ∈ L.U k) :
    gw (idIso L) f y j k = gm f y _ (L.g j k) :=
  gm_res f y _ (show f y ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k from ⟨mem_pull.2 hj, hk⟩) _
theorem pgen_idIso {L : LB X} (hL : L.IsLB) : PGen (idIso L) := by
  intro Y f y j j' k k' hj hj' hk hk'
  rw [gw_idIso L f y j k hj hk, gw_idIso L f y j' k' hj' hk', Category.comp_id,
    ← gm_cocycle hL f y hj' hk hk', ← gm_cocycle hL f y hj hj' hk]
  generalize gm f y _ (L.g j j') = A
  generalize gm f y _ (L.g j' k) = B
  generalize gm f y _ (L.g k k') = C
  rw [_root_.mul_assoc, mul_comm B C, inv_mul_cancel_left]
theorem pmaps_idIso (L : LB X) {K : Type} [Fintype K] {Y : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : PMaps (idIso L) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  have hm : r z ∈ LB.wchart L φ p ⊓ LB.wchart L φ q := ⟨Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩
  have e := congrArg (gm r z (LB.wchart L φ p ⊓ LB.wchart L φ q)) (ht p q)
  rw [Category.comp_id]
  refine (gm_res r z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans ?_))
  refine congrArg₂ (· * ·) ?_ (gm_res r z _ hm _)
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  rw [gw_idIso L (r ≫ φ k) z (p k) (q k) (hp k) (hq k)]
  exact (gm_res r z _ hm _).trans (gm_pull r (φ k) z (L.U (p k) ⊓ L.U (q k)) ⟨hp k, hq k⟩ _)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}
def cubeId (G : Over S) [GrpObj G] [IsCommMonObj G] : CubeMap G G where
  F := 𝟙 _
  F3 := 𝟙 _
  e := 𝟙 _
  e_comm := by rw [Category.comp_id, Category.id_comp]
  psum_comm := fun _ => by rw [Category.comp_id, Category.id_comp]
def sabId (t : SAB H S) : SABMap t t (𝟙 S) where
  cm := cubeId t.G
  cart := by
    refine ⟨(IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback (𝟙 t.G.left) t.G.hom t.G.hom (𝟙 S)),
      fun T x y x₀ y₀ hx hy => ?_⟩
    refine Eq.trans ?_ (Category.comp_id _).symm
    exact mul_left_congr (b := T.hom) (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _))
      (hy.trans (Category.comp_id _))
  base := rfl
  act := fun a => by
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    rw [Category.comp_id, Category.id_comp]
  lin := (isPullCubical_iff _ _ _).2 ⟨idIso t.PP.L, pgen_idIso t.PP.isLB,
    pmaps_idIso _ _ _ _ t.PP.rigGen, pmaps_idIso _ _ _ _ t.cub.isGen⟩
end Identity
section Ideals
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
theorem quot_mul_mem {l l₂ : Level H} (h : l.Dvd l₂) {x : 𝓞 E} (hx : x ∈ l.Mb) :
    ((l₂.M / l.M : ℕ) : 𝓞 E) * x ∈ l₂.Mb := by
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 h.2.1
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have h0 : Ideal.span {(l.M : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast hM
  have e : Ideal.span {(l.M : 𝓞 E)} * (J * J.map (H.bar : 𝓞 E →+* 𝓞 E)) =
      Ideal.span {(l.M : 𝓞 E)} * Ideal.span {((l₂.M / l.M : ℕ) : 𝓞 E)} := by
    rw [Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul, Nat.mul_div_cancel' h.1, ← l₂.prod, ← l.prod, hJ,
      Ideal.map_mul]
    ring
  have hk : ((l₂.M / l.M : ℕ) : 𝓞 E) ∈ J := by
    apply (Ideal.mul_le_left : J * J.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ J)
    rw [mul_left_cancel₀ h0 e]
    exact Ideal.mem_span_singleton_self _
  rw [hJ, mul_comm _ x]
  exact Ideal.mul_mem_mul hx hk
theorem quot_mul_mem_map {l l₂ : Level H} (h : l.Dvd l₂) {x : 𝓞 E}
    (hx : x ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) :
    ((l₂.M / l.M : ℕ) : 𝓞 E) * x ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 hx
  have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) (quot_mul_mem h hy)
  rwa [map_mul, map_natCast] at this
theorem nsmul_mem_smul_top {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {I J : Ideal R} {n : ℕ}
    (h : ∀ x ∈ I, (n : R) * x ∈ J) {a : M} (ha : a ∈ I • (⊤ : Submodule R M)) :
    n • a ∈ J • (⊤ : Submodule R M) := by
  refine Submodule.smul_induction_on ha (fun r hr m _ => ?_) (fun x y hx hy => ?_)
  · rw [← Nat.cast_smul_eq_nsmul R, smul_smul]
    exact Submodule.smul_mem_smul (h r hr) trivial
  · rw [smul_add]; exact add_mem hx hy
end Ideals
theorem map_nsmul_of_add {A Q : Type*} [AddCommGroup A] [Group Q] (f : A → Q) (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : A) : f (n • a) = f a ^ n := by
  induction n with
  | zero =>
    have := hf 0 0
    rw [add_zero] at this
    rw [zero_nsmul, pow_zero]
    exact left_eq_mul.1 this
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}
  {B : Type} [CommRing B] {b : Base l B} {b₂ : Base l₂ B} {S : Scheme.{0}} {s : S ⟶ Sp B}
def lower (o₂ : Obj D l₂ b₂ s) (h : l.Dvd l₂) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A)) : Obj D l b s where
  t := o₂.t
  proper := o₂.proper
  ample := o₂.ample
  ktriv := o₂.ktriv
  eta a := o₂.eta a ^ (l₂.M / l.M)
  eta_add a c := by rw [o₂.eta_add, mul_pow]
  eta_ker a ha := by
    rw [← map_nsmul_of_add _ o₂.eta_add]
    exact o₂.eta_ker _ (nsmul_mem_smul_top (fun _ hx => quot_mul_mem h hx) ha)
  etaA a := o₂.etaA a ^ (l₂.A / l.A)
  etaA_add a c := by rw [o₂.etaA_add, mul_pow]
  etaA_ker a := by
    rw [← map_nsmul_of_add _ o₂.etaA_add, smul_smul, Nat.div_mul_cancel h.2.2, o₂.etaA_ker]
  geom k _ _ x β hx := by
    obtain ⟨hd, I, h₁, h₂, h₃⟩ := o₂.geom k x β hx
    have hA : 0 < l₂.A / l.A := Nat.div_pos (Nat.le_of_dvd l₂.A_pos h.2.2) l.A_pos
    have hM₁ : 0 < l.M := by have := l.three_le; omega
    have hM₂ : 0 < l₂.M := by have := l₂.three_le; omega
    have hM : 0 < l₂.M / l.M := Nat.div_pos (Nat.le_of_dvd hM₂ h.1) hM₁
    refine ⟨hρ ▸ hd, I, ?_, fun a => ?_, fun a ha => ?_⟩
    · rw [hζ, map_pow, ← h₁, ← I.ζ_pow l.A _ l.A_pos hA, Nat.mul_div_cancel' h.2.2, Units.val_pow_eq_pow_val]
    · rw [MonObj.comp_pow, h₂, ← I.tower l.A _ l.A_pos hA, Nat.mul_div_cancel' h.2.2]
    · rw [← map_nsmul_of_add _ o₂.eta_add,
        h₃ _ (nsmul_mem_smul_top (fun _ hx => quot_mul_mem_map h hx) ha),
        map_nsmul_of_add _ (I.add _), ← I.tower l.M _ hM₁ hM, Nat.mul_div_cancel' h.1]
end GlobalTheory.ObjLower
namespace GlobalTheory
end GlobalTheory


