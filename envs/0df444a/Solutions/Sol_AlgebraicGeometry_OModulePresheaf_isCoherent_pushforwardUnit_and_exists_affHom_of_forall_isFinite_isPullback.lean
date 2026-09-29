-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/fea19c17-fc18-5bcb-af5b-592fd8ff1b22

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace P2mSysAlg

open AlgebraicGeometry.OModulePresheaf

section PushoutSurj

variable {A B C P : CommRingCat.{u}} {f : A ⟶ C} {q : A ⟶ B} {inl : C ⟶ P} {inr : B ⟶ P}

theorem surjective_and_ker_eq_of_isPushout (h : IsPushout f q inl inr) (hq : Function.Surjective q.hom) :
    Function.Surjective inl.hom ∧ RingHom.ker inl.hom = Ideal.map f.hom (RingHom.ker q.hom) := by
  classical
  set J : Ideal C := Ideal.map f.hom (RingHom.ker q.hom) with hJ

  have hJle : J ≤ RingHom.ker inl.hom := by
    rw [hJ, Ideal.map_le_iff_le_comap]
    intro a ha
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    have hw := congrArg (fun φ : A ⟶ P => φ.hom a) h.w
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hw
    rw [hw, RingHom.mem_ker.mp ha, map_zero]

  let toQ : C ⟶ CommRingCat.of (C ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  have hker : RingHom.ker q.hom ≤ RingHom.ker ((Ideal.Quotient.mk J).comp f.hom) := by
    intro a ha
    simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  let k₀ : B →+* C ⧸ J := RingHom.liftOfSurjective q.hom hq ⟨(Ideal.Quotient.mk J).comp f.hom, hker⟩
  have hk₀ : ∀ a, k₀ (q.hom a) = Ideal.Quotient.mk J (f.hom a) := fun a =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ a
  let k : B ⟶ CommRingCat.of (C ⧸ J) := CommRingCat.ofHom k₀
  have w : f ≫ toQ = q ≫ k := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, toQ, k, CommRingCat.hom_ofHom]
    exact (hk₀ a).symm
  let d : P ⟶ CommRingCat.of (C ⧸ J) := h.desc toQ k w
  have hd : inl ≫ d = toQ := h.inl_desc toQ k w
  let u₀ : C ⧸ J →+* P := Ideal.Quotient.lift J inl.hom fun c hc => hJle hc
  have hu₀ : ∀ c, u₀ (Ideal.Quotient.mk J c) = inl.hom c := fun c => Ideal.Quotient.lift_mk J _ _
  let u : CommRingCat.of (C ⧸ J) ⟶ P := CommRingCat.ofHom u₀
  have hu : toQ ≫ u = inl := by
    refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, toQ, u, CommRingCat.hom_ofHom]
    exact hu₀ c

  have hdu : d ≫ u = 𝟙 P := by
    apply h.hom_ext
    · rw [← Category.assoc, hd, hu, Category.comp_id]
    · rw [Category.comp_id, ← Category.assoc, h.inr_desc toQ k w]
      refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
      obtain ⟨a, rfl⟩ := hq b
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, k, u, CommRingCat.hom_ofHom]
      rw [hk₀ a, hu₀]
      have hw := congrArg (fun φ : A ⟶ P => φ.hom a) h.w
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hw
      exact hw

  have hud : u ≫ d = 𝟙 _ := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id, RingHom.id_apply,
      u, CommRingCat.hom_ofHom]
    rw [hu₀]
    have := congrArg (fun φ : C ⟶ _ => φ.hom c) hd
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, toQ, CommRingCat.hom_ofHom] at this
    exact this
  have hu_surj : Function.Surjective u.hom := by
    intro p
    refine ⟨d.hom p, ?_⟩
    have := congrArg (fun φ : P ⟶ P => φ.hom p) hdu
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at this
    exact this
  have hu_inj : Function.Injective u.hom := by
    intro x y hxy
    have hx := congrArg (fun φ : CommRingCat.of (C ⧸ J) ⟶ _ => φ.hom x) hud
    have hy := congrArg (fun φ : CommRingCat.of (C ⧸ J) ⟶ _ => φ.hom y) hud
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at hx hy
    rw [← hx, ← hy, hxy]
  have hinl : ∀ c, inl.hom c = u.hom (Ideal.Quotient.mk J c) := fun c => (hu₀ c).symm
  refine ⟨?_, ?_⟩
  · intro p
    obtain ⟨x, hx⟩ := hu_surj p
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨c, (hinl c).trans hx⟩
  · ext c
    rw [RingHom.mem_ker, hinl, ← Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro hc
      exact hu_inj (hc.trans (map_zero u.hom).symm)
    · intro hc
      rw [hc, map_zero]

end PushoutSurj

section PushUnit

variable {R : Type u} [CommRing R] {V Z : Scheme.{u}} (π : V ⟶ Spec (.of R)) (ι : Z ⟶ V)

theorem res_rfl (W : Z.Opens) (x : Γ(Z, W)) : Z.presheaf.map (homOfLE (le_refl W)).op x = x := by
  rw [Subsingleton.elim (homOfLE (le_refl W)).op (𝟙 (op W)), Z.presheaf.map_id]; rfl

theorem appLE_rfl_apply (U : V.Opens) (a : Γ(V, U)) : ι.appLE U (ι ⁻¹ᵁ U) le_rfl a = ι.app U a := by
  show Z.presheaf.map (homOfLE (le_refl _)).op (ι.app U a) = _
  exact res_rfl (ι ⁻¹ᵁ U) _

theorem isCoherent_pushforwardUnit [IsFinite ι] : (pushforwardUnit π ι).IsCoherent := by
  intro U
  have hfin : (ι.app U.1).hom.Finite := IsFinite.finite_app ι U.1 U.2

  have hmod : (pushforwardUnit π ι).moduleSections U.1 =
      (ι.app U.1).hom.toAlgebra.toModule := by
    refine Module.ext' _ _ fun a x => ?_
    show ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a * (show Γ(Z, ι ⁻¹ᵁ U.1) from x) =
      ι.app U.1 a * (show Γ(Z, ι ⁻¹ᵁ U.1) from x)
    rw [appLE_rfl_apply]
  rw [hmod]
  exact hfin

theorem loc_core [IsAffineHom ι] (U : V.affineOpens) (g : Γ(Z, ι ⁻¹ᵁ U.1)) (W' : Z.Opens) (hle : W' ≤ ι ⁻¹ᵁ U.1)
    (hW' : W' = Z.basicOpen g) :
    (∀ x : Γ(Z, W'), ∃ (n : ℕ) (y : Γ(Z, ι ⁻¹ᵁ U.1)),
        Z.presheaf.map (homOfLE hle).op y = Z.presheaf.map (homOfLE hle).op (g ^ n) * x) ∧
      (∀ y : Γ(Z, ι ⁻¹ᵁ U.1), Z.presheaf.map (homOfLE hle).op y = 0 → ∃ n : ℕ, g ^ n * y = 0) := by
  subst hW'
  have hW : IsAffineOpen (ι ⁻¹ᵁ U.1) := U.2.preimage ι
  haveI : IsLocalization.Away g Γ(Z, Z.basicOpen g) := hW.isLocalization_basicOpen g
  have halg : ∀ y : Γ(Z, ι ⁻¹ᵁ U.1),
      algebraMap Γ(Z, ι ⁻¹ᵁ U.1) Γ(Z, Z.basicOpen g) y = Z.presheaf.map (homOfLE hle).op y := fun y => by
    rw [Subsingleton.elim (homOfLE hle) (homOfLE (Z.basicOpen_le g))]; rfl
  constructor
  · intro x
    obtain ⟨⟨y, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers g) x
    refine ⟨n, y, ?_⟩
    rw [← halg, ← halg, ← h, mul_comm]
  · intro y hy
    rw [← halg] at hy
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).mp hy
    exact ⟨n, hn⟩

theorem preimage_basicOpen_eq (U : V.affineOpens) (f : Γ(V, U.1)) :
    ι ⁻¹ᵁ V.basicOpen f = Z.basicOpen (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl f) := by
  rw [appLE_rfl_apply]; exact Scheme.preimage_basicOpen ι f

theorem pre_le (U : V.affineOpens) (f : Γ(V, U.1)) : ι ⁻¹ᵁ V.basicOpen f ≤ ι ⁻¹ᵁ U.1 :=
  fun _ hx => V.basicOpen_le f hx

theorem smul_basicOpen (U : V.affineOpens) (f : Γ(V, U.1)) (a : Γ(V, U.1)) (x : Γ(Z, ι ⁻¹ᵁ V.basicOpen f)) :
    ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom a •
        (show (pushforwardUnit π ι).obj (V.basicOpen f) from x)) =
      (show (pushforwardUnit π ι).obj (V.basicOpen f) from
        Z.presheaf.map (homOfLE (pre_le ι U f)).op (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a) * x) := by
  show ι.appLE (V.basicOpen f) (ι ⁻¹ᵁ V.basicOpen f) le_rfl ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op) a) * x
    = _
  congr 1
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem smul_top (U : V.affineOpens) (a : Γ(V, U.1)) (y : Γ(Z, ι ⁻¹ᵁ U.1)) :
    (a • (show (pushforwardUnit π ι).obj U.1 from y)) =
      (show (pushforwardUnit π ι).obj U.1 from ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a * y) := rfl

theorem res_eq (U : V.affineOpens) (f : Γ(V, U.1)) (y : Γ(Z, ι ⁻¹ᵁ U.1)) :
    (pushforwardUnit π ι).res (V.basicOpen_le f) (show (pushforwardUnit π ι).obj U.1 from y) =
      (show (pushforwardUnit π ι).obj (V.basicOpen f) from Z.presheaf.map (homOfLE (pre_le ι U f)).op y) := by
  show Z.presheaf.map _ y = _
  rw [Subsingleton.elim (homOfLE ((Opens.map ι.base).monotone (V.basicOpen_le f))) (homOfLE (pre_le ι U f))]

theorem isQuasicoherent_pushforwardUnit [IsAffineHom ι] : (pushforwardUnit π ι).IsQuasicoherent := by
  intro U f
  set g : Γ(Z, ι ⁻¹ᵁ U.1) := ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl f with hg
  obtain ⟨h1, h2⟩ := loc_core ι U g (ι ⁻¹ᵁ V.basicOpen f) (pre_le ι U f) (preimage_basicOpen_eq ι U f)
  constructor
  · intro x
    obtain ⟨n, y, hy⟩ := h1 x
    refine ⟨n, y, ?_⟩
    rw [res_eq, smul_basicOpen]
    show Z.presheaf.map (homOfLE (pre_le ι U f)).op y =
      Z.presheaf.map (homOfLE (pre_le ι U f)).op (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl (f ^ n)) *
        (show Γ(Z, ι ⁻¹ᵁ V.basicOpen f) from x)
    rw [map_pow (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom]
    exact hy
  · intro y hy
    rw [res_eq] at hy
    obtain ⟨n, hn⟩ := h2 y hy
    refine ⟨n, ?_⟩
    rw [smul_top]
    show ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl (f ^ n) * (show Γ(Z, ι ⁻¹ᵁ U.1) from y) = 0
    rw [map_pow (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom]
    exact hn

end PushUnit

section Torsion

variable {R : Type u} [CommRing R] {V Z : Scheme.{u}} (π : V ⟶ Spec (.of R)) (ι : Z ⟶ V)

theorem appLE_congr_hom {X Y : Scheme.{u}} {k k' : X ⟶ Y} (e : k = k') (U : Y.Opens) (W : X.Opens)
    (h : W ≤ k ⁻¹ᵁ U) (h' : W ≤ k' ⁻¹ᵁ U) : k.appLE U W h = k'.appLE U W h' := by
  subst e; rfl

theorem algebraMap_eq_of_fac {A : Type u} [CommRing A] [Algebra R A] (p : Z ⟶ Spec (.of A))
    (hp : ι ≫ π = p ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))) (W : Z.Opens) (r : R) :
    (Scheme.TwoAffineOpenCover.algebraOfHom (ι ≫ π) W).algebraMap r =
      (p.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (.of A)).inv.hom (algebraMap R A r)) := by
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  rw [appLE_congr_hom hp ⊤ W le_top le_top]
  have h1 : (Spec.map (CommRingCat.ofHom (algebraMap R A))).appLE ⊤ ⊤ le_top ≫ p.appLE ⊤ W le_top =
      (p ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))).appLE ⊤ W le_top :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  rw [← h1, CommRingCat.comp_apply]
  congr 1
  have h2 : CommRingCat.ofHom (algebraMap R A) ≫ (Scheme.ΓSpecIso (.of A)).inv =
      (Scheme.ΓSpecIso (.of R)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop :=
    Scheme.ΓSpecIso_inv_naturality _
  have h3 : (Spec.map (CommRingCat.ofHom (algebraMap R A))).appLE ⊤ ⊤ le_top =
      (Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [h3, ← CommRingCat.comp_apply, ← h2, CommRingCat.comp_apply]
  rfl

theorem smul_top_eq_bot_of_fac {A : Type u} [CommRing A] [Algebra R A] (p : Z ⟶ Spec (.of A))
    (hp : ι ≫ π = p ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))) (J : Ideal R)
    (hJ : ∀ r ∈ J, algebraMap R A r = 0) (U : V.Opens) :
    J • (⊤ : Submodule R ((pushforwardUnit π ι).obj U)) = ⊥ := by
  refine le_bot_iff.mp (Submodule.smul_le.mpr fun r hr x _ => ?_)
  rw [Submodule.mem_bot]
  show (Scheme.TwoAffineOpenCover.algebraOfHom (ι ≫ π) (ι ⁻¹ᵁ U)).algebraMap r * (show Γ(Z, ι ⁻¹ᵁ U) from x) = 0
  rw [algebraMap_eq_of_fac π ι p hp, hJ r hr, map_zero, map_zero, zero_mul]

end Torsion

section Transition

variable {R : Type u} [CommRing R] {V Z₀ Z₁ : Scheme.{u}} (π : V ⟶ Spec (.of R)) (ι₁ : Z₁ ⟶ V) (ι₀ : Z₀ ⟶ V)
  (y : Z₀ ⟶ Z₁) (hy : y ≫ ι₁ = ι₀)

include hy in
theorem preimage_le (U : V.Opens) : ι₀ ⁻¹ᵁ U ≤ y ⁻¹ᵁ ι₁ ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, hy]

noncomputable def tauLin (U : V.Opens) : (pushforwardUnit π ι₁).obj U →ₗ[R] (pushforwardUnit π ι₀).obj U where
  toFun x := show Γ(Z₀, ι₀ ⁻¹ᵁ U) from y.appLE (ι₁ ⁻¹ᵁ U) (ι₀ ⁻¹ᵁ U) (preimage_le ι₁ ι₀ y hy U) x
  map_add' a b := map_add _ _ _
  map_smul' r x := by
    show y.appLE (ι₁ ⁻¹ᵁ U) (ι₀ ⁻¹ᵁ U) (preimage_le ι₁ ι₀ y hy U)
        ((Scheme.TwoAffineOpenCover.algebraOfHom (ι₁ ≫ π) (ι₁ ⁻¹ᵁ U)).algebraMap r * (show Γ(Z₁, ι₁ ⁻¹ᵁ U) from x)) =
      (Scheme.TwoAffineOpenCover.algebraOfHom (ι₀ ≫ π) (ι₀ ⁻¹ᵁ U)).algebraMap r *
        y.appLE (ι₁ ⁻¹ᵁ U) (ι₀ ⁻¹ᵁ U) (preimage_le ι₁ ι₀ y hy U) (show Γ(Z₁, ι₁ ⁻¹ᵁ U) from x)
    rw [map_mul]
    congr 1
    rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom,
      ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    congr 2
    exact appLE_congr_hom (by rw [← Category.assoc, hy]) ⊤ _ _ le_top

theorem tauLin_apply (U : V.Opens) (x : (pushforwardUnit π ι₁).obj U) :
    tauLin π ι₁ ι₀ y hy U x =
      (show Γ(Z₀, ι₀ ⁻¹ᵁ U) from y.appLE (ι₁ ⁻¹ᵁ U) (ι₀ ⁻¹ᵁ U) (preimage_le ι₁ ι₀ y hy U) x) := rfl

noncomputable def tau : AffHom (pushforwardUnit π ι₁) (pushforwardUnit π ι₀) where
  app U := tauLin π ι₁ ι₀ y hy U.1
  app_smul U a x := by
    show y.appLE (ι₁ ⁻¹ᵁ U.1) (ι₀ ⁻¹ᵁ U.1) (preimage_le ι₁ ι₀ y hy U.1)
        (ι₁.appLE U.1 (ι₁ ⁻¹ᵁ U.1) le_rfl a * (show Γ(Z₁, ι₁ ⁻¹ᵁ U.1) from x)) =
      ι₀.appLE U.1 (ι₀ ⁻¹ᵁ U.1) le_rfl a *
        y.appLE (ι₁ ⁻¹ᵁ U.1) (ι₀ ⁻¹ᵁ U.1) (preimage_le ι₁ ι₀ y hy U.1) (show Γ(Z₁, ι₁ ⁻¹ᵁ U.1) from x)
    rw [map_mul]
    congr 1
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    rw [appLE_congr_hom hy U.1 (ι₀ ⁻¹ᵁ U.1) _ le_rfl]
  naturality {U U'} h := by
    refine LinearMap.ext fun x => ?_
    show y.appLE (ι₁ ⁻¹ᵁ U.1) (ι₀ ⁻¹ᵁ U.1) (preimage_le ι₁ ι₀ y hy U.1)
        (Z₁.presheaf.map (homOfLE ((Opens.map ι₁.base).monotone h)).op (show Γ(Z₁, ι₁ ⁻¹ᵁ U'.1) from x)) =
      Z₀.presheaf.map (homOfLE ((Opens.map ι₀.base).monotone h)).op
        (y.appLE (ι₁ ⁻¹ᵁ U'.1) (ι₀ ⁻¹ᵁ U'.1) (preimage_le ι₁ ι₀ y hy U'.1) (show Γ(Z₁, ι₁ ⁻¹ᵁ U'.1) from x))
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem tau_app (U : V.affineOpens) (x : (pushforwardUnit π ι₁).obj U.1) :
    (tau π ι₁ ι₀ y hy).app U x =
      (show Γ(Z₀, ι₀ ⁻¹ᵁ U.1) from y.appLE (ι₁ ⁻¹ᵁ U.1) (ι₀ ⁻¹ᵁ U.1) (preimage_le ι₁ ι₀ y hy U.1) x) := rfl

end Transition

section RingCat

variable {X Y Z : CommRingCat.{u}}

theorem surj_hom_of_isIso (a : X ⟶ Y) [IsIso a] : Function.Surjective a.hom := fun y =>
  ⟨(inv a).hom y, by rw [← CommRingCat.comp_apply, IsIso.inv_hom_id]; rfl⟩

theorem inj_hom_of_isIso (a : X ⟶ Y) [IsIso a] : Function.Injective a.hom := fun x x' h => by
  have := congrArg (inv a).hom h
  rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, IsIso.hom_inv_id] at this

theorem ker_comp_of_injective (b : X ⟶ Y) (c : Y ⟶ Z) (hc : Function.Injective c.hom) :
    RingHom.ker (b ≫ c).hom = RingHom.ker b.hom := by
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  constructor
  · intro h
    exact hc (h.trans (map_zero c.hom).symm)
  · intro h
    rw [h, map_zero]

theorem ker_comp_eq_comap (a : X ⟶ Y) (b : Y ⟶ Z) :
    RingHom.ker (a ≫ b).hom = (RingHom.ker b.hom).comap a.hom := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply]

theorem surjective_comp_iff_of_isIso_right (b : X ⟶ Y) (c : Y ⟶ Z) [IsIso c] :
    Function.Surjective (b ≫ c).hom ↔ Function.Surjective b.hom := by
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h (c.hom y)
    exact ⟨x, inj_hom_of_isIso c hx⟩
  · intro h
    exact (surj_hom_of_isIso c).comp h

theorem surjective_comp_iff_of_isIso_left (a : X ⟶ Y) (b : Y ⟶ Z) [IsIso a] :
    Function.Surjective (a ≫ b).hom ↔ Function.Surjective b.hom := by
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  constructor
  · intro h
    exact Function.Surjective.of_comp h
  · intro h
    exact h.comp (surj_hom_of_isIso a)

theorem comap_hom_eq_map_inv (e : X ≅ Y) (K : Ideal Y) : K.comap e.hom.hom = K.map e.inv.hom := by
  apply le_antisymm
  · intro x hx
    have hx' : x = e.inv.hom (e.hom.hom x) := by rw [← CommRingCat.comp_apply, e.hom_inv_id]; rfl
    rw [hx']
    exact Ideal.mem_map_of_mem _ hx
  · rw [Ideal.map_le_iff_le_comap]
    intro z hz
    rw [Ideal.mem_comap, Ideal.mem_comap, ← CommRingCat.comp_apply, e.inv_hom_id]
    exact hz

theorem map_hom_comap_hom (e : X ≅ Y) (K : Ideal Y) : (K.comap e.hom.hom).map e.hom.hom = K :=
  Ideal.map_comap_of_surjective _ (surj_hom_of_isIso e.hom) K

theorem map_inv_map_hom (e : X ≅ Y) (K : Ideal X) : (K.map e.hom.hom).map e.inv.hom = K := by
  rw [Ideal.map_map, ← CommRingCat.hom_comp, e.hom_inv_id, CommRingCat.hom_id, Ideal.map_id]

theorem map_hom_map_inv (e : X ≅ Y) (K : Ideal Y) : (K.map e.inv.hom).map e.hom.hom = K := by
  rw [Ideal.map_map, ← CommRingCat.hom_comp, e.inv_hom_id, CommRingCat.hom_id, Ideal.map_id]

end RingCat

section Kernel

variable {R : Type u} [CommRing R] {V Z₀ Z₁ : Scheme.{u}} (π : V ⟶ Spec (.of R)) (ι₁ : Z₁ ⟶ V) (ι₀ : Z₀ ⟶ V)
  (y : Z₀ ⟶ Z₁) (hy : y ≫ ι₁ = ι₀)
  {A' A : Type u} [CommRing A'] [CommRing A] [Algebra R A'] (φ : A' →+* A) (hφ : Function.Surjective φ)
  (p₁ : Z₁ ⟶ Spec (.of A')) (p₀ : Z₀ ⟶ Spec (.of A))
  (H : IsPullback y p₀ p₁ (Spec.map (CommRingCat.ofHom φ)))
  (hp₁ : ι₁ ≫ π = p₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R A')))

theorem appTop_SpecMap :
    (Spec.map (CommRingCat.ofHom φ)).appTop =
      (Scheme.ΓSpecIso (.of A')).hom ≫ CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of A)).inv := by
  rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem appLE_top_top {S T : Scheme.{u}} (t : T ⟶ S) : t.appLE ⊤ ⊤ le_top = t.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

include hφ H in

theorem surjective_and_ker_appLE_core (W₁ : Z₁.Opens) (hW₁ : IsAffineOpen W₁) :
    Function.Surjective (y.appLE W₁ (y ⁻¹ᵁ W₁ ⊓ p₀ ⁻¹ᵁ ⊤) (by simp)) ∧
      RingHom.ker (y.appLE W₁ (y ⁻¹ᵁ W₁ ⊓ p₀ ⁻¹ᵁ ⊤) (by simp)).hom =
        ((RingHom.ker φ).map (Scheme.ΓSpecIso (.of A')).inv.hom).map (p₁.appLE ⊤ W₁ le_top).hom := by
  set UY : Z₀.Opens := y ⁻¹ᵁ W₁ ⊓ p₀ ⁻¹ᵁ ⊤ with hUY
  have Hres := Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := ⊤) (UX := W₁) le_top le_top (UY := UY) hUY
  haveI : IsAffine W₁ := hW₁
  haveI : IsAffine (⊤ : (Spec (CommRingCat.of A')).Opens) := isAffineOpen_top _
  haveI : IsAffine (⊤ : (Spec (CommRingCat.of A)).Opens) := isAffineOpen_top _
  have hpo := isPushout_appTop_of_isPullback Hres

  have hg' : Function.Surjective ((Spec.map (CommRingCat.ofHom φ)).resLE ⊤ ⊤ le_top).appTop.hom := by
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, appLE_top_top, appTop_SpecMap,
      surjective_comp_iff_of_isIso_left, surjective_comp_iff_of_isIso_right, surjective_comp_iff_of_isIso_left,
      surjective_comp_iff_of_isIso_right]
    exact hφ
  obtain ⟨hsurj, hker⟩ := surjective_and_ker_eq_of_isPushout hpo hg'
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top] at hsurj hker
  rw [surjective_comp_iff_of_isIso_left, surjective_comp_iff_of_isIso_right] at hsurj
  refine ⟨hsurj, ?_⟩
  rw [ker_comp_eq_comap, ker_comp_of_injective _ _ (inj_hom_of_isIso _)] at hker

  have hker' := congrArg (Ideal.map (W₁.topIso.hom.hom)) hker
  rw [map_hom_comap_hom] at hker'
  rw [hker']

  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, appLE_top_top,
    appTop_SpecMap]
  rw [ker_comp_eq_comap, ker_comp_of_injective _ _ (inj_hom_of_isIso _), ker_comp_eq_comap,
    ker_comp_of_injective _ _ (inj_hom_of_isIso _), CommRingCat.hom_ofHom]
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, ← Ideal.map_map, ← Ideal.map_map]
  rw [map_hom_comap_hom, comap_hom_eq_map_inv, map_hom_map_inv]

include hy in
theorem preimage_eq_inf (U : V.Opens) : ι₀ ⁻¹ᵁ U = y ⁻¹ᵁ ι₁ ⁻¹ᵁ U ⊓ p₀ ⁻¹ᵁ ⊤ := by
  rw [← Scheme.Hom.comp_preimage, hy]
  ext1
  simp

include hy in
theorem appLE_eq_comp (U : V.Opens) :
    y.appLE (ι₁ ⁻¹ᵁ U) (ι₀ ⁻¹ᵁ U) (preimage_le ι₁ ι₀ y hy U) =
      y.appLE (ι₁ ⁻¹ᵁ U) (y ⁻¹ᵁ ι₁ ⁻¹ᵁ U ⊓ p₀ ⁻¹ᵁ ⊤) (by simp) ≫
        Z₀.presheaf.map (eqToHom (preimage_eq_inf ι₁ ι₀ y hy p₀ U)).op :=
  (Scheme.Hom.appLE_map y _ _).symm

include hφ H hp₁ in

theorem surjective_and_ker_tau_app [IsAffineHom ι₁] (J : Ideal R)
    (hJ : RingHom.ker φ = J.map (algebraMap R A')) (U : V.affineOpens) :
    Function.Surjective ((tau π ι₁ ι₀ y hy).app U) ∧
      LinearMap.ker ((tau π ι₁ ι₀ y hy).app U) = J • (⊤ : Submodule R ((pushforwardUnit π ι₁).obj U.1)) := by
  have hW₁ : IsAffineOpen (ι₁ ⁻¹ᵁ U.1) := U.2.preimage ι₁
  obtain ⟨hs, hk⟩ := surjective_and_ker_appLE_core y φ hφ p₁ p₀ H (ι₁ ⁻¹ᵁ U.1) hW₁
  have hfun : ∀ x : (pushforwardUnit π ι₁).obj U.1, (tau π ι₁ ι₀ y hy).app U x =
      (y.appLE (ι₁ ⁻¹ᵁ U.1) (y ⁻¹ᵁ ι₁ ⁻¹ᵁ U.1 ⊓ p₀ ⁻¹ᵁ ⊤) (by simp) ≫
        Z₀.presheaf.map (eqToHom (preimage_eq_inf ι₁ ι₀ y hy p₀ U.1)).op) x := by
    intro x
    rw [tau_app, appLE_eq_comp ι₁ ι₀ y hy p₀ U.1]
  refine ⟨?_, ?_⟩
  · intro z
    obtain ⟨x, hx⟩ := (surjective_comp_iff_of_isIso_right _
      (Z₀.presheaf.map (eqToHom (preimage_eq_inf ι₁ ι₀ y hy p₀ U.1)).op)).mpr hs z
    exact ⟨x, (hfun x).trans hx⟩
  · letI := Scheme.TwoAffineOpenCover.algebraOfHom (ι₁ ≫ π) (ι₁ ⁻¹ᵁ U.1)
    have halg : algebraMap R Γ(Z₁, ι₁ ⁻¹ᵁ U.1) =
        ((p₁.appLE ⊤ (ι₁ ⁻¹ᵁ U.1) le_top).hom.comp (Scheme.ΓSpecIso (.of A')).inv.hom).comp (algebraMap R A') :=
      RingHom.ext fun r => algebraMap_eq_of_fac π ι₁ p₁ hp₁ (ι₁ ⁻¹ᵁ U.1) r
    have hker : RingHom.ker (y.appLE (ι₁ ⁻¹ᵁ U.1) (y ⁻¹ᵁ ι₁ ⁻¹ᵁ U.1 ⊓ p₀ ⁻¹ᵁ ⊤) (by simp) ≫
        Z₀.presheaf.map (eqToHom (preimage_eq_inf ι₁ ι₀ y hy p₀ U.1)).op).hom =
        J.map (algebraMap R Γ(Z₁, ι₁ ⁻¹ᵁ U.1)) := by
      rw [ker_comp_of_injective _ _ (inj_hom_of_isIso _), hk, hJ, Ideal.map_map, Ideal.map_map, halg]
    have hsm : (SetLike.coe (J • (⊤ : Submodule R ((pushforwardUnit π ι₁).obj U.1))) :
        Set (Z₁.presheaf.obj (op (ι₁ ⁻¹ᵁ U.1)))) =
        (J.map (algebraMap R (Z₁.presheaf.obj (op (ι₁ ⁻¹ᵁ U.1)))) : Set (Z₁.presheaf.obj (op (ι₁ ⁻¹ᵁ U.1)))) := by
      have := Ideal.smul_top_eq_map (R := R) (S := (Z₁.presheaf.obj (op (ι₁ ⁻¹ᵁ U.1)))) J
      exact congrArg (fun N : Submodule R (Z₁.presheaf.obj (op (ι₁ ⁻¹ᵁ U.1))) =>
        (N : Set (Z₁.presheaf.obj (op (ι₁ ⁻¹ᵁ U.1))))) this
    refine Submodule.ext fun x => ?_
    have hx := Set.ext_iff.mp hsm x
    rw [SetLike.mem_coe, SetLike.mem_coe] at hx
    rw [LinearMap.mem_ker]
    refine Iff.trans ?_ hx.symm
    rw [← hker, RingHom.mem_ker, ← hfun]
    exact Iff.rfl

end Kernel

section Main

variable (R : Type u) [CommRing R] (I : Ideal R) (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
  (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
  (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
  (tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1 + 1))))
  (htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n)
  (xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1)))
  (hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n))
  (hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n)
  (Y : ℕ → Scheme.{u}) (g : ∀ n : ℕ, Y n ⟶ Limits.pullback f (sR n))
  (yn : ∀ n : ℕ, Y n ⟶ Y (n + 1))
  (hY : ∀ n : ℕ, IsPullback (yn n) (g n) (g (n + 1)) (xn n))

abbrev q (n : ℕ) : R ⧸ I ^ (n + 1 + 1) →+* R ⧸ I ^ (n + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ _))

theorem q_surjective (n : ℕ) : Function.Surjective (q R I n) := Ideal.Quotient.factor_surjective _

theorem ker_q (n : ℕ) : RingHom.ker (q R I n) = (I ^ (n + 1)).map (algebraMap R (R ⧸ I ^ (n + 1 + 1))) := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.algebraMap_eq,
    Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr (Ideal.pow_le_pow_right (Nat.le_succ _))]

include hsR in
theorem isFinite_sR (n : ℕ) : IsFinite (sR n) := by
  rw [hsR n, IsFinite.SpecMap_iff, CommRingCat.hom_ofHom, Ideal.Quotient.algebraMap_eq]
  exact RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective

include hsR htR in
theorem tR_eq (n : ℕ) : tR n = Spec.map (CommRingCat.ofHom (q R I n)) := by
  haveI : IsClosedImmersion (sR (n + 1)) := by
    rw [hsR (n + 1)]
    exact IsClosedImmersion.spec_of_surjective _ (by
      show Function.Surjective (algebraMap R (R ⧸ I ^ (n + 1 + 1)))
      rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)
  have e1 : Spec.map (CommRingCat.ofHom (q R I n)) ≫ sR (n + 1) = sR n := by
    rw [hsR (n + 1), hsR n, ← Spec.map_comp]
    rfl
  exact (cancel_mono (sR (n + 1))).mp ((htR n).trans e1.symm)

include hsR in

theorem fac (n : ℕ) :
    (g n ≫ pullback.fst f (sR n)) ≫ f =
      (g n ≫ pullback.snd f (sR n)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))) := by
  simp only [Category.assoc, pullback.condition]
  exact congrArg (g n ≫ pullback.snd f (sR n) ≫ ·) (hsR n)

include hxn₁ hY in
theorem comm (n : ℕ) : yn n ≫ g (n + 1) ≫ pullback.fst f (sR (n + 1)) = g n ≫ pullback.fst f (sR n) := by
  rw [← Category.assoc, (hY n).w, Category.assoc, hxn₁]

include hsR htR hxn₁ hxn₂ hY in

theorem isPullback_yn (n : ℕ) :
    IsPullback (yn n) (g n ≫ pullback.snd f (sR n)) (g (n + 1) ≫ pullback.snd f (sR (n + 1)))
      (Spec.map (CommRingCat.ofHom (q R I n))) := by
  have t : IsPullback (pullback.fst f (sR (n + 1))) (pullback.snd f (sR (n + 1))) f (sR (n + 1)) :=
    IsPullback.of_hasPullback f (sR (n + 1))
  have outer : IsPullback (xn n ≫ pullback.fst f (sR (n + 1))) (pullback.snd f (sR n)) f (tR n ≫ sR (n + 1)) := by
    convert IsPullback.of_hasPullback f (sR n) using 1
    · exact hxn₁ n
    · exact htR n
  have Xsq : IsPullback (xn n) (pullback.snd f (sR n)) (pullback.snd f (sR (n + 1))) (tR n) :=
    IsPullback.of_right outer (hxn₂ n) t
  have Hsq := (hY n).paste_vert Xsq
  rwa [tR_eq R I sR hsR tR htR n] at Hsq

include hsR htR hxn₁ hxn₂ hY in
theorem main [IsNoetherianRing R] [IsAdicComplete I R] [IsProper f] [∀ n : ℕ, IsFinite (g n)] :
    (∀ n : ℕ, (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))).IsCoherent ∧
      (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))).IsQuasicoherent) ∧
    (∀ (n : ℕ) (U : X.Opens),
      I ^ (n + 1) • (⊤ : Submodule R ((OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))).obj U)) = ⊥) ∧
    ∃ τ : ∀ n : ℕ, OModulePresheaf.AffHom
        (OModulePresheaf.pushforwardUnit f (g (n + 1) ≫ pullback.fst f (sR (n + 1))))
        (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))),
      (∀ (n : ℕ) (U : X.affineOpens)
        (x : (OModulePresheaf.pushforwardUnit f (g (n + 1) ≫ pullback.fst f (sR (n + 1)))).obj U.1),
        (τ n).app U x =
          ((yn n).appLE ((g (n + 1) ≫ pullback.fst f (sR (n + 1))) ⁻¹ᵁ U.1)
            ((g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1)
            (by rw [← Scheme.Hom.comp_preimage, ← Category.assoc, (hY n).w, Category.assoc, hxn₁])).hom x) ∧
      (∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((τ n).app U)) ∧
      (∀ (n : ℕ) (U : X.affineOpens),
        LinearMap.ker ((τ n).app U) =
          I ^ (n + 1) • (⊤ : Submodule R
            ((OModulePresheaf.pushforwardUnit f (g (n + 1) ≫ pullback.fst f (sR (n + 1)))).obj U.1))) := by
  have hfin : ∀ n : ℕ, IsFinite (g n ≫ pullback.fst f (sR n)) := fun n => by
    haveI := isFinite_sR R I sR hsR n
    infer_instance
  refine ⟨fun n => ?_, fun n U => ?_, ?_⟩
  · haveI := hfin n
    exact ⟨isCoherent_pushforwardUnit f _, isQuasicoherent_pushforwardUnit f _⟩
  · refine smul_top_eq_bot_of_fac f _ (g n ≫ pullback.snd f (sR n)) (fac R I X f sR hsR Y g n) (I ^ (n + 1))
      (fun r hr => ?_) U
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
  · refine ⟨fun n => tau f (g (n + 1) ≫ pullback.fst f (sR (n + 1))) (g n ≫ pullback.fst f (sR n)) (yn n)
      (comm R I X f sR xn hxn₁ Y g yn hY n), fun n U x => rfl, fun n U => ?_, fun n U => ?_⟩
    · haveI := hfin (n + 1)
      exact (surjective_and_ker_tau_app f _ _ (yn n) (comm R I X f sR xn hxn₁ Y g yn hY n) (q R I n)
        (q_surjective R I n) _ _ (isPullback_yn R I X f sR hsR tR htR xn hxn₁ hxn₂ Y g yn hY n)
        (fac R I X f sR hsR Y g (n + 1)) (I ^ (n + 1)) (ker_q R I n) U).1
    · haveI := hfin (n + 1)
      exact (surjective_and_ker_tau_app f _ _ (yn n) (comm R I X f sR xn hxn₁ Y g yn hY n) (q R I n)
        (q_surjective R I n) _ _ (isPullback_yn R I X f sR hsR tR htR xn hxn₁ hxn₂ Y g yn hY n)
        (fac R I X f sR hsR Y g (n + 1)) (I ^ (n + 1)) (ker_q R I n) U).2

end Main

end P2mSysAlg

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1 + 1))))
    (htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n)

    (xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1)))
    (hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n))
    (hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n)

    (Y : ℕ → Scheme.{u}) (g : ∀ n : ℕ, Y n ⟶ Limits.pullback f (sR n)) [∀ n : ℕ, IsFinite (g n)]
    (yn : ∀ n : ℕ, Y n ⟶ Y (n + 1))
    (hY : ∀ n : ℕ, IsPullback (yn n) (g n) (g (n + 1)) (xn n)) :
    (∀ n : ℕ, (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))).IsCoherent ∧
      (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))).IsQuasicoherent) ∧
    (∀ (n : ℕ) (U : X.Opens),
      I ^ (n + 1) • (⊤ : Submodule R ((OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))).obj U)) = ⊥) ∧
    ∃ τ : ∀ n : ℕ, OModulePresheaf.AffHom
        (OModulePresheaf.pushforwardUnit f (g (n + 1) ≫ pullback.fst f (sR (n + 1))))
        (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))),
      (∀ (n : ℕ) (U : X.affineOpens)
        (x : (OModulePresheaf.pushforwardUnit f (g (n + 1) ≫ pullback.fst f (sR (n + 1)))).obj U.1),
        (τ n).app U x =
          ((yn n).appLE ((g (n + 1) ≫ pullback.fst f (sR (n + 1))) ⁻¹ᵁ U.1)
            ((g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1)
            (by rw [← Scheme.Hom.comp_preimage, ← Category.assoc, (hY n).w, Category.assoc, hxn₁])).hom x) ∧
      (∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((τ n).app U)) ∧
      (∀ (n : ℕ) (U : X.affineOpens),
        LinearMap.ker ((τ n).app U) =
          I ^ (n + 1) • (⊤ : Submodule R
            ((OModulePresheaf.pushforwardUnit f (g (n + 1) ≫ pullback.fst f (sR (n + 1)))).obj U.1))) :=
  P2mSysAlg.main R I X f sR hsR tR htR xn hxn₁ hxn₂ Y g yn hY

end S_AlgebraicGeometry_OModulePresheaf_isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback (solution)
