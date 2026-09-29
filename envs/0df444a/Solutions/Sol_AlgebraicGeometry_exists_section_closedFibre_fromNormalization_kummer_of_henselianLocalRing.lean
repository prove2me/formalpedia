-- Prove2me | solution 1 for AlgebraicGeometry.exists_section_closedFibre_fromNormalization_kummer_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/8261f1ba-5d92-5fce-b1fe-162899019f80

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicGeometry_exists_root_fromNormalization_kummer_existsUnique_lift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_section_closedFibre_fromNormalization_kummer_of_henselianLocalRing

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial Opposite TopologicalSpace"

namespace KSec

section thin

variable {Z : Scheme.{u}}

lemma map_op_congr {A B : Z.Opens} (i j : B ⟶ A) (s : Γ(Z, A)) :
    Z.presheaf.map i.op s = Z.presheaf.map j.op s := by
  rw [Subsingleton.elim i j]

lemma map_congr' {A B : Z.Opens} (i j : op A ⟶ op B) (s : Γ(Z, A)) :
    Z.presheaf.map i s = Z.presheaf.map j s := by
  rw [← i.op_unop, ← j.op_unop, Subsingleton.elim i.unop j.unop]

lemma map_map_eq {A B C : Z.Opens} (i : op A ⟶ op B) (j : op B ⟶ op C) (s : Γ(Z, A)) :
    Z.presheaf.map j (Z.presheaf.map i s) = Z.presheaf.map (i ≫ j) s := by
  rw [Z.presheaf.map_comp]; rfl

lemma map_injective_of_eq_top {A B : Z.Opens} (hA : A = ⊤) (e : A ≤ B) :
    Function.Injective (Z.presheaf.map (homOfLE e).op) := by
  have hB : B = ⊤ := top_le_iff.mp (hA ▸ e)
  subst hA hB
  have : homOfLE e = 𝟙 _ := Subsingleton.elim _ _
  rw [this, op_id, Z.presheaf.map_id]
  exact fun a b h => by simpa using h

lemma app_map_top {Z' : Scheme.{u}} (q : Z' ⟶ Z) (W : Z.Opens) (x : Γ(Z, ⊤)) :
    q.app W (Z.presheaf.map (homOfLE le_top).op x) =
      Z'.presheaf.map (homOfLE le_top).op (q.appTop x) := by
  have := congrArg (fun φ => φ.hom x) (q.naturality (homOfLE (le_top : W ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
  rw [this]
  exact map_op_congr _ _ _

lemma app_map {Z' : Scheme.{u}} (q : Z' ⟶ Z) {W W' : Z.Opens} (e : W' ≤ W) (x : Γ(Z, W)) :
    q.app W' (Z.presheaf.map (homOfLE e).op x) =
      Z'.presheaf.map (homOfLE (q.preimage_mono e)).op (q.app W x) := by
  have := congrArg (fun φ => φ.hom x) (q.naturality (homOfLE e).op)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
  rw [this]
  exact map_op_congr _ _ _

lemma comp_app_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (x : Γ(Z, U)) :
    (f ≫ g).app U x = f.app (g ⁻¹ᵁ U) (g.app U x) := rfl

lemma comp_appTop_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    (f ≫ g).appTop x = f.appTop (g.appTop x) := rfl

lemma map_one₃ {A B C D : CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) (χ : C ⟶ D) : χ (ψ (φ 1)) = 1 := by
  simp

lemma app_comp_lift_self {P Q Y X : Scheme.{u}} (π : Y ⟶ X) (Ua : X.Opens) (Ta : Γ(Y, π ⁻¹ᵁ Ua))
    (p : P ⟶ Q) (sa : Q ⟶ Y) (τa : Γ(Q, ⊤))
    (hsa : sa.app (π ⁻¹ᵁ Ua) Ta = Q.presheaf.map (homOfLE le_top).op τa) :
    (p ≫ sa).app (π ⁻¹ᵁ Ua) Ta = P.presheaf.map (homOfLE le_top).op (p.appTop τa) := by
  rw [comp_app_apply, hsa, app_map_top]
  exact map_op_congr _ _ _

lemma app_comp_lift_other {P Q Y X S : Scheme.{u}} (π : Y ⟶ X) (ι : S ⟶ X) {Ua Ub : X.Opens}
    (Ta : Γ(Y, π ⁻¹ᵁ Ua)) (Tb : Γ(Y, π ⁻¹ᵁ Ub)) (w : Γ(X, Ua ⊓ Ub))
    (hwT : Y.presheaf.map (homOfLE (π.preimage_mono inf_le_left)).op Ta =
      π.app (Ua ⊓ Ub) w * Y.presheaf.map (homOfLE (π.preimage_mono inf_le_right)).op Tb)
    (hw1 : ι.app (Ua ⊓ Ub) w = 1)
    (ιb : Q ⟶ S) (sb : Q ⟶ Y) (d : Γ(S, ⊤))
    (hsb1 : sb ≫ π = ιb ≫ ι)
    (hsb2 : sb.app (π ⁻¹ᵁ Ub) Tb = Q.presheaf.map (homOfLE le_top).op (ιb.appTop d))
    (p : P ⟶ Q) (hpa : (p ≫ ιb ≫ ι) ⁻¹ᵁ Ua = ⊤) (hpb : (p ≫ ιb ≫ ι) ⁻¹ᵁ Ub = ⊤) :
    (p ≫ sb).app (π ⁻¹ᵁ Ua) Ta = P.presheaf.map (homOfLE le_top).op ((p ≫ ιb).appTop d) := by
  have hmπ : (p ≫ sb) ≫ π = p ≫ ιb ≫ ι := by rw [Category.assoc, hsb1]
  have htop : (p ≫ sb) ⁻¹ᵁ (π ⁻¹ᵁ (Ua ⊓ Ub)) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, hmπ, Scheme.Hom.preimage_inf, hpa, hpb, top_inf_eq]
  apply map_injective_of_eq_top htop ((p ≫ sb).preimage_mono (π.preimage_mono inf_le_left))
  rw [← app_map _ (π.preimage_mono inf_le_left) Ta, hwT, map_mul]
  have h1 : (p ≫ sb).app (π ⁻¹ᵁ (Ua ⊓ Ub)) (π.app (Ua ⊓ Ub) w) = 1 := by
    rw [← comp_app_apply, Scheme.Hom.congr_app hmπ (Ua ⊓ Ub), CommRingCat.comp_apply,
      comp_app_apply, comp_app_apply, hw1]
    exact map_one₃ _ _ _
  rw [h1, one_mul, app_map _ (π.preimage_mono inf_le_right) Tb, comp_app_apply, hsb2, app_map_top,
    comp_appTop_apply]
  exact (map_map_eq _ _ _).trans ((map_congr' _ _ _).trans (map_map_eq _ _ _).symm)

end thin

section base

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

local notation "sκ" => Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

lemma fst_appTop_base_eq_zero (t : R) (ht : t ∈ IsLocalRing.maximalIdeal R) :
    (pullback.fst f sκ).appTop (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv t)) = 0 := by
  have h2 := congrArg (fun φ => φ.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv t))
    (pullback.condition (f := f) (g := sκ))
  have h3 := congrArg (fun φ => φ.hom t)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (IsLocalRing.residue R)))
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at h2 h3
  rw [h2, ← h3, (IsLocalRing.residue_eq_zero_iff t).mpr ht, map_zero, map_zero]

end base

section cocycle

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of R))

local notation "sκ" => Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

lemma germ_eq_one_add {V : X.Opens} (w : Γ(X, V)) (x : X) (hx : x ∈ V)
    (ha hb : X.functionField) (hha : ha ≠ 0)
    (hw : algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ V x hx w) = hb / ha)
    (hcoc : ∃ t ∈ IsLocalRing.maximalIdeal R,
      ∃ s ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range,
        ha = hb * (1 + AlgebraicCurve.SemistableModel.baseToFunctionField f t * s)) :
    ∃ t ∈ IsLocalRing.maximalIdeal R, ∃ s' : X.presheaf.stalk x,
      X.presheaf.germ V x hx w =
        1 + X.presheaf.germ ⊤ x trivial (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv t)) * s' := by
  obtain ⟨t, ht, s, ⟨s₁, rfl⟩, hc⟩ := hcoc
  set φ := algebraMap (X.presheaf.stalk x) X.functionField with hφdef
  have hφ : Function.Injective φ := IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  set tx := X.presheaf.germ ⊤ x trivial (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv t)) with htx
  have hB : AlgebraicCurve.SemistableModel.baseToFunctionField f t = φ tx := by
    change (X.presheaf.germ ⊤ (genericPoint X) trivial)
        (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv t)) =
      (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial))
        (X.presheaf.germ ⊤ x trivial (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv t)))
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  refine ⟨t, ht, -(s₁ * X.presheaf.germ V x hx w), ?_⟩
  have key : X.presheaf.germ V x hx w * (1 + tx * s₁) = 1 := by
    apply hφ
    rw [map_mul, map_one, map_add, map_one, map_mul, hw, ← hB, div_mul_eq_mul_div, ← hc, div_self hha]
  linear_combination key

omit [IsIntegral X] in

lemma fst_app_eq_one {V : X.Opens} (w : Γ(X, V))
    (hw : ∀ (x : X) (hx : x ∈ V), ∃ t ∈ IsLocalRing.maximalIdeal R, ∃ s' : X.presheaf.stalk x,
      X.presheaf.germ V x hx w =
        1 + X.presheaf.germ ⊤ x trivial (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv t)) * s') :
    (pullback.fst f sκ).app V w = 1 := by
  apply TopCat.Presheaf.section_ext (pullback f sκ).sheaf
  intro y hy
  obtain ⟨t, ht, s', hw'⟩ := hw ((pullback.fst f sκ) y) hy
  have h0 : (pullback.fst f sκ).app ⊤ (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv t)) = 0 :=
    fst_appTop_base_eq_zero f t ht
  change (pullback f sκ).presheaf.germ _ y hy ((pullback.fst f sκ).app V w) =
    (pullback f sκ).presheaf.germ _ y hy 1
  rw [map_one, ← Scheme.Hom.germ_stalkMap_apply (pullback.fst f sκ) V y hy, hw', map_add, map_one,
    map_mul, Scheme.Hom.germ_stalkMap_apply, h0, map_zero, zero_mul, add_zero]

end cocycle

section root

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

local notation "sκ" => Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

lemma exists_pow_eq_of_surjective
    (hconn : Function.Surjective (pullback.snd f sκ).appTop)
    (k : ℕ) (hk : 0 < k) (c : Γ(pullback f sκ, ⊤)) :
    ∃ d : Γ(pullback f sκ, ⊤), d ^ k = c := by
  obtain ⟨c₁, rfl⟩ := hconn c
  let e := Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField R))
  obtain ⟨d₀, hd₀⟩ := IsAlgClosed.exists_pow_nat_eq (e.hom c₁) hk
  refine ⟨(pullback.snd f sκ).appTop (e.inv d₀), ?_⟩
  rw [← map_pow, ← map_pow, hd₀]
  congr 1
  change (e.hom ≫ e.inv) c₁ = c₁
  rw [e.hom_inv_id]
  rfl

end root

section main

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
  {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of R))

local notation "sκ" => Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

theorem exists_section
    (k : ℕ) (hk : 0 < k)
    (r : ℕ) (U : Fin r → X.Opens) (hU : (⨆ a, U a) = ⊤) (h : Fin r → X.functionField) (hh : ∀ a, h a ≠ 0)
    (hcoc : ∀ a b (x : X), x ∈ U a → x ∈ U b →
      ∃ t ∈ IsLocalRing.maximalIdeal R, ∃ s ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range,
        h a = h b * (1 + AlgebraicCurve.SemistableModel.baseToFunctionField f t * s))
    (hconn : Function.Surjective (pullback.snd f sκ).appTop)
    {Y : Scheme.{u}} (π : Y ⟶ X) (u : ∀ a, Γ(X, U a)) (T : ∀ a, Γ(Y, π ⁻¹ᵁ (U a)))
    (hcomp : ∀ a b, ∃ w : Γ(X, U a ⊓ U b),
        (∀ (x : X) (hx : x ∈ U a ⊓ U b),
          algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ (U a ⊓ U b) x hx w) = h b / h a) ∧
        X.presheaf.map (homOfLE inf_le_left).op (u a) = w ^ k * X.presheaf.map (homOfLE inf_le_right).op (u b) ∧
        Y.presheaf.map (homOfLE (π.preimage_mono inf_le_left)).op (T a) =
          π.app (U a ⊓ U b) w * Y.presheaf.map (homOfLE (π.preimage_mono inf_le_right)).op (T b))
    (hlift : ∀ a (Z : Scheme.{u}) (z : Z ⟶ X), z ⁻¹ᵁ (U a) = ⊤ →
        ∀ τ : Γ(Z, ⊤), Z.presheaf.map (homOfLE le_top).op τ ^ k = z.app (U a) (u a) →
          ∃! s : Z ⟶ Y, s ≫ π = z ∧ s.app (π ⁻¹ᵁ (U a)) (T a) = Z.presheaf.map (homOfLE le_top).op τ) :
    ∃ s₀ : pullback f sκ ⟶ Y, s₀ ≫ π = pullback.fst f sκ := by

  choose w hwgerm hwu hwT using hcomp
  have hw1 : ∀ a b, (pullback.fst f sκ).app (U a ⊓ U b) (w a b) = 1 := fun a b =>
    fst_app_eq_one f (w a b) fun x hx =>
      germ_eq_one_add f (w a b) x hx (h a) (h b) (hh a) (hwgerm a b x hx) (hcoc a b x hx.1 hx.2)

  have hV : (⨆ a, pullback.fst f sκ ⁻¹ᵁ U a) = ⊤ := by
    simp only [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]
  obtain ⟨c, hc, -⟩ := (pullback f sκ).sheaf.existsUnique_gluing' (fun a => pullback.fst f sκ ⁻¹ᵁ U a) ⊤
      (fun a => homOfLE le_top) hV.ge
      (fun a => (pullback.fst f sκ).app (U a) (u a)) (by
        intro a b
        have e := congrArg ((pullback.fst f sκ).app (U a ⊓ U b)) (hwu a b)
        rw [map_mul, map_pow, hw1, one_pow, one_mul, app_map, app_map] at e
        exact (map_op_congr _ _ _).trans (e.trans (map_op_congr _ _ _)))
  replace hc : ∀ a, (pullback f sκ).presheaf.map (homOfLE (le_top : pullback.fst f sκ ⁻¹ᵁ U a ≤ ⊤)).op c =
      (pullback.fst f sκ).app (U a) (u a) := hc

  obtain ⟨d, hd⟩ := exists_pow_eq_of_surjective f hconn k hk c

  have hτ : ∀ a {Z : Scheme.{u}} (q : Z ⟶ pullback f sκ),
      Z.presheaf.map (homOfLE le_top).op (q.appTop d) ^ k =
        (q ≫ pullback.fst f sκ).app (U a) (u a) := by
    intro a Z q
    rw [← map_pow, ← map_pow, hd, comp_app_apply, ← hc a, app_map_top]
    exact map_op_congr _ _ _

  have hVtop : ∀ a, ((pullback.fst f sκ ⁻¹ᵁ U a).ι ≫ pullback.fst f sκ) ⁻¹ᵁ (U a) = ⊤ := fun a => by
    rw [Scheme.Hom.comp_preimage]; exact (pullback.fst f sκ ⁻¹ᵁ U a).ι_preimage_self
  have hex := fun a =>
    hlift a (pullback.fst f sκ ⁻¹ᵁ U a) ((pullback.fst f sκ ⁻¹ᵁ U a).ι ≫ pullback.fst f sκ) (hVtop a) ((pullback.fst f sκ ⁻¹ᵁ U a).ι.appTop d) (hτ a (pullback.fst f sκ ⁻¹ᵁ U a).ι)
  choose s hs using hex

  let 𝒰 := (pullback f sκ).openCoverOfIsOpenCover (fun a => pullback.fst f sκ ⁻¹ᵁ U a) hV
  have hglue : ∀ a b, pullback.fst (𝒰.f a) (𝒰.f b) ≫ s a = pullback.snd (𝒰.f a) (𝒰.f b) ≫ s b := by
    intro a b
    change pullback.fst (pullback.fst f sκ ⁻¹ᵁ U a).ι (pullback.fst f sκ ⁻¹ᵁ U b).ι ≫ s a = pullback.snd (pullback.fst f sκ ⁻¹ᵁ U a).ι (pullback.fst f sκ ⁻¹ᵁ U b).ι ≫ s b
    have hz : ((pullback.fst (pullback.fst f sκ ⁻¹ᵁ U a).ι (pullback.fst f sκ ⁻¹ᵁ U b).ι ≫ (pullback.fst f sκ ⁻¹ᵁ U a).ι) ≫ pullback.fst f sκ) ⁻¹ᵁ (U a) = ⊤ := by
      rw [Category.assoc, Scheme.Hom.comp_preimage, hVtop, Scheme.Hom.preimage_top]
    have hpa : (pullback.snd (pullback.fst f sκ ⁻¹ᵁ U a).ι (pullback.fst f sκ ⁻¹ᵁ U b).ι ≫ (pullback.fst f sκ ⁻¹ᵁ U b).ι ≫ pullback.fst f sκ) ⁻¹ᵁ (U a) = ⊤ := by
      rw [← Category.assoc, ← pullback.condition]; exact hz
    have hpb : (pullback.snd (pullback.fst f sκ ⁻¹ᵁ U a).ι (pullback.fst f sκ ⁻¹ᵁ U b).ι ≫ (pullback.fst f sκ ⁻¹ᵁ U b).ι ≫ pullback.fst f sκ) ⁻¹ᵁ (U b) = ⊤ := by
      rw [Scheme.Hom.comp_preimage, hVtop, Scheme.Hom.preimage_top]
    have e4 := app_comp_lift_other π (pullback.fst f sκ) (T a) (T b) (w a b) (hwT a b) (hw1 a b)
      (pullback.fst f sκ ⁻¹ᵁ U b).ι (s b) d (hs b).1.1 (hs b).1.2 (pullback.snd (pullback.fst f sκ ⁻¹ᵁ U a).ι (pullback.fst f sκ ⁻¹ᵁ U b).ι) hpa hpb
    rw [← pullback.condition] at e4
    refine (hlift a _ ((pullback.fst (pullback.fst f sκ ⁻¹ᵁ U a).ι (pullback.fst f sκ ⁻¹ᵁ U b).ι ≫ (pullback.fst f sκ ⁻¹ᵁ U a).ι) ≫ pullback.fst f sκ) hz
      ((pullback.fst (pullback.fst f sκ ⁻¹ᵁ U a).ι (pullback.fst f sκ ⁻¹ᵁ U b).ι ≫ (pullback.fst f sκ ⁻¹ᵁ U a).ι).appTop d) (hτ a _)).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · rw [Category.assoc, (hs a).1.1, Category.assoc]
    · rw [comp_appTop_apply]
      exact app_comp_lift_self π (U a) (T a) _ (s a) _ (hs a).1.2
    · rw [Category.assoc, (hs b).1.1, ← Category.assoc, ← pullback.condition]
    · exact e4

  refine ⟨𝒰.glueMorphisms s hglue, ?_⟩
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun a => ?_
  rw [Scheme.Cover.ι_glueMorphisms_assoc]
  exact (hs a).1.1

end main

end KSec

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (k : ℕ) (hk : IsUnit ((k : ℕ) : R))
    (g : X.functionField) (hg : g ≠ 0)
    (r : ℕ) (U : Fin r → X.Opens) (hU : (⨆ a, U a) = ⊤) (h : Fin r → X.functionField) (hh : ∀ a, h a ≠ 0)
    (hdiv : ∀ a (x : X), x ∈ U a →
      g / h a ^ k ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range ∧
      h a ^ k / g ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range)
    (hcoc : ∀ a b (x : X), x ∈ U a → x ∈ U b →
      ∃ t ∈ IsLocalRing.maximalIdeal R, ∃ s ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range,
        h a = h b * (1 + AlgebraicCurve.SemistableModel.baseToFunctionField f t * s))
    (hconn : Function.Bijective
      (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).appTop) :
    let π := (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
      X.fromSpecStalk (genericPoint X)).fromNormalization
    ∃ s₀ : pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ⟶ (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
        X.fromSpecStalk (genericPoint X)).normalization,
      s₀ ≫ π = pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) := by
  intro π
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      have h0 : IsUnit (0 : R) := by exact_mod_cast hk
      exact absurd (isUnit_zero_iff.mp h0) zero_ne_one
    · exact hk0
  obtain ⟨u, T, -, -, -, hcomp, hlift⟩ :=
    AlgebraicGeometry.exists_root_fromNormalization_kummer_existsUnique_lift f hnorm k hk g hg r U hU h hh hdiv
  exact KSec.exists_section f k hk0 r U hU h hh hcoc hconn.2 π u T hcomp hlift

end S_AlgebraicGeometry_exists_section_closedFibre_fromNormalization_kummer_of_henselianLocalRing
end P2MW
export P2MW.S_AlgebraicGeometry_exists_section_closedFibre_fromNormalization_kummer_of_henselianLocalRing (solution)
