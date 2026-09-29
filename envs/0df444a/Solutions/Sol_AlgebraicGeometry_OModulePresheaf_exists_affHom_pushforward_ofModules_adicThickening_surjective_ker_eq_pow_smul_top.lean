-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_affHom_pushforward_ofModules_adicThickening_surjective_ker_eq_pow_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/9bccd955-ece7-58cd-a1e2-3a3b942df5af

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_pushforward_ofModules_adicThickening_surjective_ker_eq_pow_smul_top
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace P2mAdicSysLB

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

theorem map_hom_map_inv (e : X ≅ Y) (K : Ideal Y) : (K.map e.inv.hom).map e.hom.hom = K := by
  rw [Ideal.map_map, ← CommRingCat.hom_comp, e.inv_hom_id, CommRingCat.hom_id, Ideal.map_id]

end RingCat

section Kernel

variable {R : Type u} [CommRing R] {V Z₀ Z₁ : Scheme.{u}} (π : V ⟶ Spec (.of R)) (ι₁ : Z₁ ⟶ V)
  (y : Z₀ ⟶ Z₁)
  {A' A : Type u} [CommRing A'] [CommRing A] [Algebra R A'] (φ : A' →+* A) (hφ : Function.Surjective φ)
  (p₁ : Z₁ ⟶ Spec (.of A')) (p₀ : Z₀ ⟶ Spec (.of A))
  (H : IsPullback y p₀ p₁ (Spec.map (CommRingCat.ofHom φ)))
  (hp₁ : ι₁ ≫ π = p₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R A')))

theorem appLE_congr_hom {X Y : Scheme.{u}} {k k' : X ⟶ Y} (e : k = k') (U : Y.Opens) (W : X.Opens)
    (h : W ≤ k ⁻¹ᵁ U) (h' : W ≤ k' ⁻¹ᵁ U) : k.appLE U W h = k'.appLE U W h' := by
  subst e; rfl

include hp₁ in

theorem algebraMap_eq_of_fac (W : Z₁.Opens) (r : R) :
    (Scheme.TwoAffineOpenCover.algebraOfHom (ι₁ ≫ π) W).algebraMap r =
      (p₁.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (.of A')).inv.hom (algebraMap R A' r)) := by
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  rw [appLE_congr_hom hp₁ ⊤ W le_top le_top]
  have h1 : (Spec.map (CommRingCat.ofHom (algebraMap R A'))).appLE ⊤ ⊤ le_top ≫ p₁.appLE ⊤ W le_top =
      (p₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R A'))).appLE ⊤ W le_top :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  rw [← h1, CommRingCat.comp_apply]
  congr 1
  have h2 : CommRingCat.ofHom (algebraMap R A') ≫ (Scheme.ΓSpecIso (.of A')).inv =
      (Scheme.ΓSpecIso (.of R)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap R A'))).appTop :=
    Scheme.ΓSpecIso_inv_naturality _
  have h3 : (Spec.map (CommRingCat.ofHom (algebraMap R A'))).appLE ⊤ ⊤ le_top =
      (Spec.map (CommRingCat.ofHom (algebraMap R A'))).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [h3, ← CommRingCat.comp_apply, ← h2, CommRingCat.comp_apply]
  rfl

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

theorem preimage_eq_inf' (W₁ : Z₁.Opens) : y ⁻¹ᵁ W₁ = y ⁻¹ᵁ W₁ ⊓ p₀ ⁻¹ᵁ ⊤ := by
  ext1
  simp

theorem app_eq_comp (W₁ : Z₁.Opens) :
    y.app W₁ = y.appLE W₁ (y ⁻¹ᵁ W₁ ⊓ p₀ ⁻¹ᵁ ⊤) (by simp) ≫
        Z₀.presheaf.map (eqToHom (preimage_eq_inf' y p₀ W₁)).op := by
  rw [Scheme.Hom.app_eq_appLE]
  exact (Scheme.Hom.appLE_map' y _ _).symm

include hφ H hp₁ in

theorem surjective_and_ker_app [IsAffineHom ι₁] (J : Ideal R)
    (hJ : RingHom.ker φ = J.map (algebraMap R A')) (U : V.affineOpens) :
    Function.Surjective (y.app (ι₁ ⁻¹ᵁ U.1)).hom ∧
      RingHom.ker (y.app (ι₁ ⁻¹ᵁ U.1)).hom =
        letI := Scheme.TwoAffineOpenCover.algebraOfHom (ι₁ ≫ π) (ι₁ ⁻¹ᵁ U.1)
        J.map (algebraMap R Γ(Z₁, ι₁ ⁻¹ᵁ U.1)) := by
  have hW₁ : IsAffineOpen (ι₁ ⁻¹ᵁ U.1) := U.2.preimage ι₁
  obtain ⟨hs, hk⟩ := surjective_and_ker_appLE_core y φ hφ p₁ p₀ H (ι₁ ⁻¹ᵁ U.1) hW₁
  rw [app_eq_comp y p₀ (ι₁ ⁻¹ᵁ U.1)]
  refine ⟨?_, ?_⟩
  · exact (surjective_comp_iff_of_isIso_right _ _).mpr hs
  · letI := Scheme.TwoAffineOpenCover.algebraOfHom (ι₁ ≫ π) (ι₁ ⁻¹ᵁ U.1)
    have halg : algebraMap R Γ(Z₁, ι₁ ⁻¹ᵁ U.1) =
        ((p₁.appLE ⊤ (ι₁ ⁻¹ᵁ U.1) le_top).hom.comp (Scheme.ΓSpecIso (.of A')).inv.hom).comp (algebraMap R A') :=
      RingHom.ext fun r => algebraMap_eq_of_fac π ι₁ p₁ hp₁ (ι₁ ⁻¹ᵁ U.1) r
    rw [ker_comp_of_injective _ _ (inj_hom_of_isIso _), hk, hJ, Ideal.map_map, Ideal.map_map, halg]

end Kernel

section Tensor

variable {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]

theorem ker_mk_one (hσ : Function.Surjective (algebraMap A B)) :
    LinearMap.ker (TensorProduct.mk A B M 1) = (RingHom.ker (algebraMap A B)) • (⊤ : Submodule A M) := by
  set K : Ideal A := RingHom.ker (algebraMap A B) with hK
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker, TensorProduct.mk_apply] at hx
    let eBK : (A ⧸ K) ≃ₐ[A] B := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B) hσ
    have heBK1 : eBK.symm 1 = 1 := map_one _
    have h1 : (LinearEquiv.rTensor M eBK.symm.toLinearEquiv) ((1 : B) ⊗ₜ[A] x) = (1 : A ⧸ K) ⊗ₜ[A] x := by
      rw [LinearEquiv.rTensor_tmul]
      exact congrArg (· ⊗ₜ[A] x) heBK1
    rw [hx, map_zero] at h1
    have := congrArg (TensorProduct.quotTensorEquivQuotSMul M K) h1.symm
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero, Submodule.Quotient.mk_eq_zero] at this
    exact this
  · refine Submodule.smul_le.mpr fun a ha m _ => ?_
    rw [LinearMap.mem_ker, TensorProduct.mk_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.smul_def, mul_one, RingHom.mem_ker.mp ha, TensorProduct.zero_tmul]

end Tensor

section Sections

variable {X : Scheme.{u}}

def isoSections {L L' : X.Modules} (φ : L ≅ L') (U : X.Opens) : Γ(L, U) ≃ₗ[Γ(X, U)] Γ(L', U) where
  toFun := φ.hom.app U
  invFun := φ.inv.app U
  map_add' x y := map_add _ x y
  map_smul' r x := Scheme.Modules.Hom.app_smul _ r x
  left_inv x := by
    change (φ.hom.app U ≫ φ.inv.app U) x = x
    rw [← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
  right_inv x := by
    change (φ.inv.app U ≫ φ.hom.app U) x = x
    rw [← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl

theorem app_map {M M' : X.Modules} (φ : M ⟶ M') {U₁ U₂ : X.Opens} (i : U₁ ⟶ U₂) (x : Γ(M, U₂)) :
    φ.app U₁ (M.presheaf.map i.op x) = M'.presheaf.map i.op (φ.app U₂ x) :=
  PresheafOfModules.naturality_apply φ.val i.op x

private theorem _root_.P2mAdicSysLB.map_map (M : X.Modules) {W₁ W₂ W₃ : X.Opens} (i : W₁ ⟶ W₂) (j : W₂ ⟶ W₃) (k : W₁ ⟶ W₃) (z : Γ(M, W₃)) :
    M.presheaf.map i.op (M.presheaf.map j.op z) = M.presheaf.map k.op z := by
  rw [Subsingleton.elim k (i ≫ j), op_comp, M.presheaf.map_comp]; rfl

p2m_export "P2mAdicSysLB" "map_map"
theorem map_self (M : X.Modules) {O : X.Opens} (i : O ⟶ O) (z : Γ(M, O)) : M.presheaf.map i.op z = z := by
  rw [Subsingleton.elim i (𝟙 O), op_id, M.presheaf.map_id]; rfl

theorem bijective_map_of_eq (M : X.Modules) {W₁ W₂ : X.Opens} (h : W₁ = W₂) (i : W₁ ⟶ W₂) :
    Function.Bijective (M.presheaf.map i.op) := by
  subst h
  have : ∀ z, M.presheaf.map i.op z = z := map_self M i
  exact ⟨fun a b hab => by rwa [this, this] at hab, fun z => ⟨z, this z⟩⟩

end Sections

section LocMod

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} (πZ : Z ⟶ Spec (.of R)) (M : Z.Modules)
  (htriv : ∀ x : Z, ∃ (U : Z.Opens), x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))

include πZ htriv in
theorem loc_core_mod (W : Z.affineOpens) (g : Γ(Z, W.1)) (W' : Z.Opens) (hle : W' ≤ W.1)
    (hW' : W' = Z.basicOpen g) :
    (∀ x : Γ(M, W'), ∃ (n : ℕ) (z : Γ(M, W.1)),
        M.presheaf.map (homOfLE hle).op z = (Z.presheaf.map (homOfLE hle).op).hom (g ^ n) • x) ∧
      (∀ z : Γ(M, W.1), M.presheaf.map (homOfLE hle).op z = 0 → ∃ n : ℕ, (g ^ n) • z = 0) := by
  subst hW'
  exact (isQuasicoherent_ofModules_of_locallyTrivial πZ M htriv) W g

end LocMod

section System

variable {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  (L : ∀ n : ℕ, (adicThickening f I n).Modules)

abbrev Fsh (n : ℕ) : OModulePresheaf f :=
  pushforward f (adicThickeningι f I n) (ofModules (adicThickeningι f I n ≫ f) (L n))

theorem Fsh_obj (n : ℕ) (U : X.Opens) : (Fsh I f L n).obj U = Γ(L n, adicThickeningι f I n ⁻¹ᵁ U) := rfl

theorem pre_eq (n : ℕ) (U : X.Opens) :
    adicThickeningTransition f I n ⁻¹ᵁ (adicThickeningι f I (n + 1) ⁻¹ᵁ U) = adicThickeningι f I n ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, adicThickeningTransition_ι]

theorem pre_le (n : ℕ) (U : X.Opens) :
    adicThickeningι f I n ⁻¹ᵁ U ≤ adicThickeningTransition f I n ⁻¹ᵁ (adicThickeningι f I (n + 1) ⁻¹ᵁ U) :=
  (pre_eq I f n U).ge

end System

section Eta

variable {Z₀ Z₁ : Scheme.{u}} (γ : Z₀ ⟶ Z₁) (N : Z₁.Modules)

abbrev pb : Z₀.Modules := (Scheme.Modules.pullback γ).obj N

abbrev unitHom : N ⟶ (Scheme.Modules.pushforward γ).obj (pb γ N) :=
  (Scheme.Modules.pullbackPushforwardAdjunction γ).unit.app N

def eta (W : Z₁.Opens) (s : Γ(N, W)) : Γ(pb γ N, γ ⁻¹ᵁ W) := (unitHom γ N).app W s

theorem eta_add (W : Z₁.Opens) (s₁ s₂ : Γ(N, W)) : eta γ N W (s₁ + s₂) = eta γ N W s₁ + eta γ N W s₂ :=
  map_add _ s₁ s₂

theorem eta_smul (W : Z₁.Opens) (a : Γ(Z₁, W)) (s : Γ(N, W)) : eta γ N W (a • s) = γ.app W a • eta γ N W s := by
  unfold eta
  rw [Scheme.Modules.Hom.app_smul]
  rfl

theorem map_eta {W₁ W₂ : Z₁.Opens} (i : W₁ ⟶ W₂) (k : γ ⁻¹ᵁ W₁ ⟶ γ ⁻¹ᵁ W₂) (s : Γ(N, W₂)) :
    (pb γ N).presheaf.map k.op (eta γ N W₂ s) = eta γ N W₁ (N.presheaf.map i.op s) := by
  rw [Subsingleton.elim k ((Opens.map γ.base).map i)]
  exact (app_map (unitHom γ N) i s).symm

theorem exists_beta (hN : Scheme.Modules.IsInvertible N) (W : Z₁.Opens) (hW : IsAffineOpen W)
    (hγW : IsAffineOpen (γ ⁻¹ᵁ W)) :
    letI := (γ.app W).hom.toAlgebra
    ∃ β : Γ(Z₀, γ ⁻¹ᵁ W) ⊗[Γ(Z₁, W)] Γ(N, W) ≃ₗ[Γ(Z₀, γ ⁻¹ᵁ W)] Γ(pb γ N, γ ⁻¹ᵁ W),
      ∀ s : Γ(N, W), β (1 ⊗ₜ s) = eta γ N W s :=
  Scheme.Modules.IsInvertible.exists_baseChange_sections_linearEquiv_pullback γ hN W hW hγW

end Eta

section Phi

variable {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  (L : ∀ n : ℕ, (adicThickening f I n).Modules)

abbrev pbL (n : ℕ) : (adicThickening f I n).Modules :=
  pb (adicThickeningTransition f I n) (L (n + 1))

def phiRaw (n : ℕ) (U : X.Opens) (s : Γ(L (n + 1), adicThickeningι f I (n + 1) ⁻¹ᵁ U)) :
    Γ(pbL I f L n, adicThickeningι f I n ⁻¹ᵁ U) :=
  (pbL I f L n).presheaf.map (homOfLE (pre_le I f n U)).op
    (eta (adicThickeningTransition f I n) (L (n + 1)) (adicThickeningι f I (n + 1) ⁻¹ᵁ U) s)

variable (e : ∀ n : ℕ, pbL I f L n ≅ L n)

def phiFun (n : ℕ) (U : X.Opens) (s : Γ(L (n + 1), adicThickeningι f I (n + 1) ⁻¹ᵁ U)) :
    Γ(L n, adicThickeningι f I n ⁻¹ᵁ U) :=
  (e n).hom.app _ (phiRaw I f L n U s)

theorem phiFun_add (n : ℕ) (U : X.Opens) (s₁ s₂ : Γ(L (n + 1), adicThickeningι f I (n + 1) ⁻¹ᵁ U)) :
    phiFun I f L e n U (s₁ + s₂) = phiFun I f L e n U s₁ + phiFun I f L e n U s₂ := by
  simp only [phiFun, phiRaw, eta_add, map_add]

theorem phiFun_smul (n : ℕ) (U : X.Opens) (a : Γ(adicThickening f I (n + 1), adicThickeningι f I (n + 1) ⁻¹ᵁ U))
    (s : Γ(L (n + 1), adicThickeningι f I (n + 1) ⁻¹ᵁ U)) :
    phiFun I f L e n U (a • s) =
      (adicThickeningTransition f I n).appLE (adicThickeningι f I (n + 1) ⁻¹ᵁ U) (adicThickeningι f I n ⁻¹ᵁ U)
        (pre_le I f n U) a • phiFun I f L e n U s := by
  simp only [phiFun, phiRaw]
  rw [eta_smul, Scheme.Modules.map_smul, Scheme.Modules.Hom.app_smul]
  rfl

theorem phiFun_map (n : ℕ) {U U' : X.Opens} (h : U ≤ U') (s : Γ(L (n + 1), adicThickeningι f I (n + 1) ⁻¹ᵁ U')) :
    phiFun I f L e n U ((L (n + 1)).presheaf.map
        (homOfLE ((Opens.map (adicThickeningι f I (n + 1)).base).monotone h)).op s) =
      (L n).presheaf.map (homOfLE ((Opens.map (adicThickeningι f I n).base).monotone h)).op
        (phiFun I f L e n U' s) := by
  simp only [phiFun, phiRaw]
  rw [← map_eta (adicThickeningTransition f I n) (L (n + 1)) (homOfLE ((Opens.map (adicThickeningι f I (n + 1)).base).monotone h))
    (homOfLE ((Opens.map (adicThickeningTransition f I n).base).monotone
      ((Opens.map (adicThickeningι f I (n + 1)).base).monotone h))) s]
  rw [map_map (pbL I f L n) _ _ (homOfLE ((pre_le I f n U).trans
      ((Opens.map (adicThickeningTransition f I n).base).monotone
        ((Opens.map (adicThickeningι f I (n + 1)).base).monotone h))))]
  rw [← map_map (pbL I f L n) (homOfLE ((Opens.map (adicThickeningι f I n).base).monotone h))
      (homOfLE (pre_le I f n U')) (homOfLE ((pre_le I f n U).trans
      ((Opens.map (adicThickeningTransition f I n).base).monotone
        ((Opens.map (adicThickeningι f I (n + 1)).base).monotone h))))]
  exact app_map (e n).hom _ _

theorem appLE_algebraMap (n : ℕ) (U : X.Opens) (r : R) :
    (adicThickeningTransition f I n).appLE (adicThickeningι f I (n + 1) ⁻¹ᵁ U) (adicThickeningι f I n ⁻¹ᵁ U)
        (pre_le I f n U) ((Scheme.TwoAffineOpenCover.algebraOfHom (adicThickeningι f I (n + 1) ≫ f)
          (adicThickeningι f I (n + 1) ⁻¹ᵁ U)).algebraMap r) =
      (Scheme.TwoAffineOpenCover.algebraOfHom (adicThickeningι f I n ≫ f) (adicThickeningι f I n ⁻¹ᵁ U)).algebraMap r := by
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom,
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  congr 2
  exact appLE_congr_hom (by rw [← Category.assoc, adicThickeningTransition_ι]) ⊤ _ _ le_top

theorem appLE_appLE (n : ℕ) (U : X.Opens) (a : Γ(X, U)) :
    (adicThickeningTransition f I n).appLE (adicThickeningι f I (n + 1) ⁻¹ᵁ U) (adicThickeningι f I n ⁻¹ᵁ U)
        (pre_le I f n U) ((adicThickeningι f I (n + 1)).appLE U (adicThickeningι f I (n + 1) ⁻¹ᵁ U) le_rfl a) =
      (adicThickeningι f I n).appLE U (adicThickeningι f I n ⁻¹ᵁ U) le_rfl a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact congrFun (congrArg (fun k => (CommRingCat.Hom.hom k : Γ(X, U) → _))
    (appLE_congr_hom (adicThickeningTransition_ι f I n) U _ _ le_rfl)) a

def phiLin (n : ℕ) (U : X.Opens) : (Fsh I f L (n + 1)).obj U →ₗ[R] (Fsh I f L n).obj U where
  toFun s := show Γ(L n, adicThickeningι f I n ⁻¹ᵁ U) from phiFun I f L e n U s
  map_add' s₁ s₂ := phiFun_add I f L e n U s₁ s₂
  map_smul' r s := by
    show phiFun I f L e n U ((Scheme.TwoAffineOpenCover.algebraOfHom (adicThickeningι f I (n + 1) ≫ f)
          (adicThickeningι f I (n + 1) ⁻¹ᵁ U)).algebraMap r •
            (show Γ(L (n + 1), adicThickeningι f I (n + 1) ⁻¹ᵁ U) from s)) =
      (Scheme.TwoAffineOpenCover.algebraOfHom (adicThickeningι f I n ≫ f) (adicThickeningι f I n ⁻¹ᵁ U)).algebraMap r •
        phiFun I f L e n U s
    rw [phiFun_smul, appLE_algebraMap]

theorem phiLin_apply (n : ℕ) (U : X.Opens) (s : (Fsh I f L (n + 1)).obj U) :
    phiLin I f L e n U s = (show Γ(L n, adicThickeningι f I n ⁻¹ᵁ U) from phiFun I f L e n U s) := rfl

def phi (n : ℕ) : AffHom (Fsh I f L (n + 1)) (Fsh I f L n) where
  app U := phiLin I f L e n U.1
  app_smul U a s := by
    show phiFun I f L e n U.1
        ((adicThickeningι f I (n + 1)).appLE U.1 (adicThickeningι f I (n + 1) ⁻¹ᵁ U.1) le_rfl a •
          (show Γ(L (n + 1), adicThickeningι f I (n + 1) ⁻¹ᵁ U.1) from s)) =
      (adicThickeningι f I n).appLE U.1 (adicThickeningι f I n ⁻¹ᵁ U.1) le_rfl a • phiFun I f L e n U.1 s
    rw [phiFun_smul, appLE_appLE]
  naturality {U U'} h := by
    refine LinearMap.ext fun s => ?_
    exact phiFun_map I f L e n h s

theorem phi_app (n : ℕ) (U : X.affineOpens) (s : (Fsh I f L (n + 1)).obj U.1) :
    (phi I f L e n).app U s = (show Γ(L n, adicThickeningι f I n ⁻¹ᵁ U.1) from phiFun I f L e n U.1 s) := rfl

end Phi

section CohQc

variable {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  (L : ∀ n : ℕ, (adicThickening f I n).Modules) (hL : ∀ n, Scheme.Modules.IsInvertible (L n))

theorem appLE_rfl_apply {V Z : Scheme.{u}} (ι : Z ⟶ V) (U : V.Opens) (a : Γ(V, U)) :
    ι.appLE U (ι ⁻¹ᵁ U) le_rfl a = ι.app U a := by
  rw [Scheme.Hom.appLE_eq_app]

include hL in
theorem isCoherent_Fsh (n : ℕ) : (Fsh I f L n).IsCoherent := by
  intro U
  set ι := adicThickeningι f I n with hι
  have hW : IsAffineOpen (ι ⁻¹ᵁ U.1) := U.2.preimage ι
  haveI hfinL : Module.Finite Γ(adicThickening f I n, ι ⁻¹ᵁ U.1) Γ(L n, ι ⁻¹ᵁ U.1) :=
    (isCoherent_ofModules_of_locallyTrivial (ι ≫ f) (L n) (hL n).1) ⟨ι ⁻¹ᵁ U.1, hW⟩
  have hfin : (ι.app U.1).hom.Finite := IsFinite.finite_app ι U.1 U.2
  letI alg : Algebra Γ(X, U.1) Γ(adicThickening f I n, ι ⁻¹ᵁ U.1) := (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  haveI : Module.Finite Γ(X, U.1) Γ(adicThickening f I n, ι ⁻¹ᵁ U.1) := by
    have : ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl = ι.app U.1 := Scheme.Hom.appLE_eq_app _
    change (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.Finite
    rw [this]
    exact hfin
  letI modXU : Module Γ(X, U.1) Γ(L n, ι ⁻¹ᵁ U.1) := Module.compHom _ (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom
  haveI : IsScalarTower Γ(X, U.1) Γ(adicThickening f I n, ι ⁻¹ᵁ U.1) Γ(L n, ι ⁻¹ᵁ U.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hres : Module.Finite Γ(X, U.1) Γ(L n, ι ⁻¹ᵁ U.1) :=
    Module.Finite.trans Γ(adicThickening f I n, ι ⁻¹ᵁ U.1) Γ(L n, ι ⁻¹ᵁ U.1)
  exact hres

theorem preimage_basicOpen_eq {V Z : Scheme.{u}} (ι : Z ⟶ V) (U : V.affineOpens) (r : Γ(V, U.1)) :
    ι ⁻¹ᵁ V.basicOpen r = Z.basicOpen (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl r) := by
  rw [appLE_rfl_apply]; exact Scheme.preimage_basicOpen ι r

theorem pre_le' {V Z : Scheme.{u}} (ι : Z ⟶ V) (U : V.affineOpens) (r : Γ(V, U.1)) :
    ι ⁻¹ᵁ V.basicOpen r ≤ ι ⁻¹ᵁ U.1 :=
  fun _ hx => V.basicOpen_le r hx

include hL in
theorem isQuasicoherent_Fsh (n : ℕ) : (Fsh I f L n).IsQuasicoherent := by
  intro U r
  set ι := adicThickeningι f I n with hι
  have hW : IsAffineOpen (ι ⁻¹ᵁ U.1) := U.2.preimage ι
  set g : Γ(adicThickening f I n, ι ⁻¹ᵁ U.1) := ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl r with hg
  obtain ⟨h1, h2⟩ := loc_core_mod (ι ≫ f) (L n) (hL n).1 ⟨ι ⁻¹ᵁ U.1, hW⟩ g (ι ⁻¹ᵁ X.basicOpen r)
    (pre_le' ι U r) (preimage_basicOpen_eq ι U r)
  have hres : ∀ z : (Fsh I f L n).obj U.1, (Fsh I f L n).res (X.basicOpen_le r) z =
      (show (Fsh I f L n).obj (X.basicOpen r) from (L n).presheaf.map (homOfLE (pre_le' ι U r)).op z) := by
    intro z
    show (L n).presheaf.map _ z = _
    rw [Subsingleton.elim (homOfLE ((Opens.map ι.base).monotone (X.basicOpen_le r))) (homOfLE (pre_le' ι U r))]
  have hsm : ∀ (a : Γ(X, U.1)) (x : (Fsh I f L n).obj (X.basicOpen r)),
      ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom a • x) =
        (show (Fsh I f L n).obj (X.basicOpen r) from
          ((adicThickening f I n).presheaf.map (homOfLE (pre_le' ι U r)).op).hom (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a) •
            (show Γ(L n, ι ⁻¹ᵁ X.basicOpen r) from x)) := by
    intro a x
    show ι.appLE (X.basicOpen r) (ι ⁻¹ᵁ X.basicOpen r) le_rfl ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op) a) •
        (show Γ(L n, ι ⁻¹ᵁ X.basicOpen r) from x) = _
    congr 1
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  constructor
  · intro x
    obtain ⟨m, z, hz⟩ := h1 x
    refine ⟨m, z, ?_⟩
    rw [hres, hsm, map_pow (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom]
    exact hz
  · intro z hz
    rw [hres] at hz
    obtain ⟨m, hm⟩ := h2 z hz
    refine ⟨m, ?_⟩
    show ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl (r ^ m) • (show Γ(L n, ι ⁻¹ᵁ U.1) from z) = 0
    rw [map_pow (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom]
    exact hm

end CohQc

section SurjKer

variable {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  (L : ∀ n : ℕ, (adicThickening f I n).Modules) (hL : ∀ n, Scheme.Modules.IsInvertible (L n))
  (e : ∀ n : ℕ, pbL I f L n ≅ L n)

abbrev qR (n : ℕ) : R ⧸ I ^ (n + 1 + 1) →+* R ⧸ I ^ (n + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))

theorem qR_surjective (n : ℕ) : Function.Surjective (qR I n) := Ideal.Quotient.factor_surjective _

theorem ker_qR (n : ℕ) : RingHom.ker (qR I n) = (I ^ (n + 1)).map (algebraMap R (R ⧸ I ^ (n + 1 + 1))) := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.algebraMap_eq,
    Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr (Ideal.pow_le_pow_right (Nat.le_succ _))]

theorem isPullback_transition (n : ℕ) :
    IsPullback (adicThickeningTransition f I n) (adicThickeningToBase f I n) (adicThickeningToBase f I (n + 1))
      (Spec.map (CommRingCat.ofHom (qR I n))) := by
  have t : IsPullback (adicThickeningι f I (n + 1)) (adicThickeningToBase f I (n + 1)) f
      (adicThickeningBase I (n + 1)) :=
    IsPullback.of_hasPullback f (adicThickeningBase I (n + 1))
  have outer : IsPullback (adicThickeningTransition f I n ≫ adicThickeningι f I (n + 1))
      (adicThickeningToBase f I n) f (Spec.map (CommRingCat.ofHom (qR I n)) ≫ adicThickeningBase I (n + 1)) := by
    rw [adicThickeningTransition_ι, adicThickeningBase_succ_comp]
    exact IsPullback.of_hasPullback f (adicThickeningBase I n)
  exact IsPullback.of_right outer (adicThickeningTransition_toBase f I n) t

theorem ι_comp_fac (n : ℕ) :
    adicThickeningι f I n ≫ f =
      adicThickeningToBase f I n ≫ Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))) := by
  rw [adicThickeningι_comp, Ideal.Quotient.algebraMap_eq]

theorem surj_and_ker_of_chain {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {M : Type u} [AddCommGroup M] [Module A M]
    {P : Type u} [AddCommGroup P] [Module B P]
    {Q T : Type u} [AddCommGroup Q] [AddCommGroup T]
    (hσ : Function.Surjective (algebraMap A B))
    (β : B ⊗[A] M ≃ₗ[B] P) (g₃ : P → Q) (hg₃0 : g₃ 0 = 0) (hg₃ : Function.Bijective g₃)
    (g₄ : Q → T) (hg₄0 : g₄ 0 = 0) (hg₄ : Function.Bijective g₄)
    (Φ : M → T) (hΦ : ∀ s, Φ s = g₄ (g₃ (β ((1 : B) ⊗ₜ[A] s)))) :
    Function.Surjective Φ ∧
      ∀ s, Φ s = 0 ↔ s ∈ (RingHom.ker (algebraMap A B)) • (⊤ : Submodule A M) := by
  have hg₃0' : ∀ z, g₃ z = 0 ↔ z = 0 := fun z =>
    ⟨fun h => hg₃.1 (h.trans hg₃0.symm), fun h => by rw [h]; exact hg₃0⟩
  have hg₄0' : ∀ z, g₄ z = 0 ↔ z = 0 := fun z =>
    ⟨fun h => hg₄.1 (h.trans hg₄0.symm), fun h => by rw [h]; exact hg₄0⟩
  refine ⟨?_, fun s => ?_⟩
  · intro t
    obtain ⟨z₄, rfl⟩ := hg₄.2 t
    obtain ⟨z₃, rfl⟩ := hg₃.2 z₄
    obtain ⟨z₂, rfl⟩ := β.surjective z₃
    obtain ⟨s, rfl⟩ := TensorProduct.mk_surjective A M B hσ z₂
    exact ⟨s, hΦ s⟩
  · rw [hΦ, hg₄0', hg₃0', β.map_eq_zero_iff, ← ker_mk_one hσ, LinearMap.mem_ker, TensorProduct.mk_apply]

theorem ringFacts (n : ℕ) (U : X.affineOpens) :
    Function.Surjective ((adicThickeningTransition f I n).app (adicThickeningι f I (n + 1) ⁻¹ᵁ U.1)).hom ∧
      RingHom.ker ((adicThickeningTransition f I n).app (adicThickeningι f I (n + 1) ⁻¹ᵁ U.1)).hom =
        letI := Scheme.TwoAffineOpenCover.algebraOfHom (adicThickeningι f I (n + 1) ≫ f)
          (adicThickeningι f I (n + 1) ⁻¹ᵁ U.1)
        (I ^ (n + 1)).map (algebraMap R Γ(adicThickening f I (n + 1), adicThickeningι f I (n + 1) ⁻¹ᵁ U.1)) :=
  surjective_and_ker_app f (adicThickeningι f I (n + 1)) (adicThickeningTransition f I n) (qR I n)
    (qR_surjective I n) (adicThickeningToBase f I (n + 1)) (adicThickeningToBase f I n)
    (isPullback_transition I f n) (ι_comp_fac I f (n + 1)) (I ^ (n + 1)) (ker_qR I n) U

include hL e in

theorem surjective_and_ker_phiFun (n : ℕ) (U : X.affineOpens) :
    Function.Surjective (phiFun I f L e n U.1) ∧
      ∀ s, phiFun I f L e n U.1 s = 0 ↔
        letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (adicThickeningι f I (n + 1) ≫ f) (L (n + 1))
          (adicThickeningι f I (n + 1) ⁻¹ᵁ U.1)
        s ∈ I ^ (n + 1) • (⊤ : Submodule R Γ(L (n + 1), adicThickeningι f I (n + 1) ⁻¹ᵁ U.1)) := by

  have hW : IsAffineOpen (adicThickeningι f I (n + 1) ⁻¹ᵁ U.1) := U.2.preimage _
  have hτW : adicThickeningTransition f I n ⁻¹ᵁ (adicThickeningι f I (n + 1) ⁻¹ᵁ U.1) =
      adicThickeningι f I n ⁻¹ᵁ U.1 := pre_eq I f n U.1
  have hpW : IsAffineOpen (adicThickeningTransition f I n ⁻¹ᵁ (adicThickeningι f I (n + 1) ⁻¹ᵁ U.1)) := by
    rw [hτW]; exact U.2.preimage _

  letI algRA : Algebra R Γ(adicThickening f I (n + 1), adicThickeningι f I (n + 1) ⁻¹ᵁ U.1) :=
    Scheme.TwoAffineOpenCover.algebraOfHom (adicThickeningι f I (n + 1) ≫ f) (adicThickeningι f I (n + 1) ⁻¹ᵁ U.1)
  letI algAB : Algebra Γ(adicThickening f I (n + 1), adicThickeningι f I (n + 1) ⁻¹ᵁ U.1)
      Γ(adicThickening f I n, adicThickeningTransition f I n ⁻¹ᵁ (adicThickeningι f I (n + 1) ⁻¹ᵁ U.1)) :=
    ((adicThickeningTransition f I n).app (adicThickeningι f I (n + 1) ⁻¹ᵁ U.1)).hom.toAlgebra
  letI modRL : Module R Γ(L (n + 1), adicThickeningι f I (n + 1) ⁻¹ᵁ U.1) :=
    Scheme.TwoAffineOpenCover.moduleSectionsOfHom (adicThickeningι f I (n + 1) ≫ f) (L (n + 1))
      (adicThickeningι f I (n + 1) ⁻¹ᵁ U.1)
  haveI : IsScalarTower R Γ(adicThickening f I (n + 1), adicThickeningι f I (n + 1) ⁻¹ᵁ U.1)
      Γ(L (n + 1), adicThickeningι f I (n + 1) ⁻¹ᵁ U.1) :=
    Scheme.TwoAffineOpenCover.isScalarTower_sections (adicThickeningι f I (n + 1) ≫ f) (L (n + 1)) _
  obtain ⟨hσs, hσk⟩ := ringFacts I f n U

  obtain ⟨β, hβ⟩ := exists_beta (adicThickeningTransition f I n) (L (n + 1)) (hL (n + 1))
    (adicThickeningι f I (n + 1) ⁻¹ᵁ U.1) hW hpW
  have key := surj_and_ker_of_chain hσs β
    (fun z => (pbL I f L n).presheaf.map (homOfLE (pre_le I f n U.1)).op z) (map_zero _)
    (bijective_map_of_eq (pbL I f L n) hτW.symm _)
    (fun z => (e n).hom.app (adicThickeningι f I n ⁻¹ᵁ U.1) z) (map_zero _)
    (isoSections (e n) (adicThickeningι f I n ⁻¹ᵁ U.1)).bijective
    (phiFun I f L e n U.1) (fun s => by rw [hβ s]; rfl)
  have hσk' : RingHom.ker (algebraMap Γ(adicThickening f I (n + 1), adicThickeningι f I (n + 1) ⁻¹ᵁ U.1)
      Γ(adicThickening f I n, adicThickeningTransition f I n ⁻¹ᵁ (adicThickeningι f I (n + 1) ⁻¹ᵁ U.1))) =
      (I ^ (n + 1)).map (algebraMap R Γ(adicThickening f I (n + 1), adicThickeningι f I (n + 1) ⁻¹ᵁ U.1)) := hσk
  refine ⟨key.1, fun s => ?_⟩
  rw [key.2 s, hσk', ← Submodule.restrictScalars_mem R, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

include hL e in

theorem surjective_and_ker_phi (n : ℕ) (U : X.affineOpens) :
    Function.Surjective ((phi I f L e n).app U) ∧
      LinearMap.ker ((phi I f L e n).app U) = I ^ (n + 1) • (⊤ : Submodule R ((Fsh I f L (n + 1)).obj U.1)) := by
  obtain ⟨h1, h2⟩ := surjective_and_ker_phiFun I f L hL e n U
  refine ⟨h1, Submodule.ext fun s => ?_⟩
  rw [LinearMap.mem_ker]
  exact h2 s

end SurjKer

theorem main {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (L : ∀ n : ℕ, (adicThickening f I n).Modules)
    (hL : ∀ n, Scheme.Modules.IsInvertible (L n))
    (hcompat : ∀ n, Nonempty
      ((Scheme.Modules.pullback (adicThickeningTransition f I n)).obj (L (n + 1)) ≅ L n)) :
    (∀ n : ℕ, (OModulePresheaf.pushforward f (adicThickeningι f I n)
        (OModulePresheaf.ofModules (adicThickeningι f I n ≫ f) (L n))).IsCoherent) ∧
    (∀ n : ℕ, (OModulePresheaf.pushforward f (adicThickeningι f I n)
        (OModulePresheaf.ofModules (adicThickeningι f I n ≫ f) (L n))).IsQuasicoherent) ∧
    ∃ φ : ∀ n : ℕ, OModulePresheaf.AffHom
        (OModulePresheaf.pushforward f (adicThickeningι f I (n + 1))
          (OModulePresheaf.ofModules (adicThickeningι f I (n + 1) ≫ f) (L (n + 1))))
        (OModulePresheaf.pushforward f (adicThickeningι f I n)
          (OModulePresheaf.ofModules (adicThickeningι f I n ≫ f) (L n))),
      (∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((φ n).app U)) ∧
      (∀ (n : ℕ) (U : X.affineOpens), LinearMap.ker ((φ n).app U) =
        I ^ (n + 1) • (⊤ : Submodule R ((OModulePresheaf.pushforward f (adicThickeningι f I (n + 1))
          (OModulePresheaf.ofModules (adicThickeningι f I (n + 1) ≫ f) (L (n + 1)))).obj U.1))) := by
  let e : ∀ n : ℕ, pbL I f L n ≅ L n := fun n => (hcompat n).some
  exact ⟨fun n => isCoherent_Fsh I f L hL n, fun n => isQuasicoherent_Fsh I f L hL n,
    ⟨fun n => phi I f L e n, fun n U => (surjective_and_ker_phi I f L hL e n U).1,
      fun n U => (surjective_and_ker_phi I f L hL e n U).2⟩⟩

end P2mAdicSysLB

end

theorem solution
    {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (L : ∀ n : ℕ, (adicThickening f I n).Modules)
    (hL : ∀ n, Scheme.Modules.IsInvertible (L n))
    (hcompat : ∀ n, Nonempty
      ((Scheme.Modules.pullback (adicThickeningTransition f I n)).obj (L (n + 1)) ≅ L n)) :
    (∀ n : ℕ, (OModulePresheaf.pushforward f (adicThickeningι f I n)
        (OModulePresheaf.ofModules (adicThickeningι f I n ≫ f) (L n))).IsCoherent) ∧
    (∀ n : ℕ, (OModulePresheaf.pushforward f (adicThickeningι f I n)
        (OModulePresheaf.ofModules (adicThickeningι f I n ≫ f) (L n))).IsQuasicoherent) ∧
    ∃ φ : ∀ n : ℕ, OModulePresheaf.AffHom
        (OModulePresheaf.pushforward f (adicThickeningι f I (n + 1))
          (OModulePresheaf.ofModules (adicThickeningι f I (n + 1) ≫ f) (L (n + 1))))
        (OModulePresheaf.pushforward f (adicThickeningι f I n)
          (OModulePresheaf.ofModules (adicThickeningι f I n ≫ f) (L n))),
      (∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((φ n).app U)) ∧
      (∀ (n : ℕ) (U : X.affineOpens), LinearMap.ker ((φ n).app U) =
        I ^ (n + 1) • (⊤ : Submodule R ((OModulePresheaf.pushforward f (adicThickeningι f I (n + 1))
          (OModulePresheaf.ofModules (adicThickeningι f I (n + 1) ≫ f) (L (n + 1)))).obj U.1))) :=
  P2mAdicSysLB.main I f L hL hcompat

end S_AlgebraicGeometry_OModulePresheaf_exists_affHom_pushforward_ofModules_adicThickening_surjective_ker_eq_pow_smul_top
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_pushforward_ofModules_adicThickening_surjective_ker_eq_pow_smul_top (solution)
