-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.flat_subschemeIota_mul_comp_of_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/ac26d6d2-275a-5e2b-924a-321a141cdd14

import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_flat_subschemeIota_mul_comp_of_isInvertible

universe u

open TensorProduct LinearMap

namespace FlatMulAux

theorem flat_of_exact
    {R : Type*} [CommRing R] {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    [Module.Flat R M] [Module.Flat R P] : Module.Flat R N := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I

  have hφP : Function.Injective (lTensor P I.subtype) := (Module.Flat.iff_lTensor_injective'.mp inferInstance) I
  have hφM : Function.Injective (lTensor M I.subtype) := (Module.Flat.iff_lTensor_injective'.mp inferInstance) I

  have hnatP : lTensor P I.subtype ∘ₗ rTensor I g = rTensor R g ∘ₗ lTensor N I.subtype := by
    ext n i; simp
  have hnatM : lTensor N I.subtype ∘ₗ rTensor I f = rTensor R f ∘ₗ lTensor M I.subtype := by
    ext m i; simp

  have hex : Function.Exact (rTensor (↥I) f) (rTensor (↥I) g) := _root_.rTensor_exact (↥I) hfg hg
  have hinjR : Function.Injective (rTensor R f) := Module.Flat.rTensor_preserves_injective_linearMap (M := R) f hf

  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have h1 : lTensor P I.subtype (rTensor I g x) = 0 := by
    have := LinearMap.congr_fun hnatP x
    simp only [LinearMap.coe_comp, Function.comp_apply] at this
    rw [this, hx, map_zero]
  have h2 : rTensor I g x = 0 := hφP (by rw [h1, map_zero])
  obtain ⟨y, rfl⟩ := (hex x).mp h2
  have h3 : rTensor R f (lTensor M I.subtype y) = 0 := by
    have := LinearMap.congr_fun hnatM y
    simp only [LinearMap.coe_comp, Function.comp_apply] at this
    rw [← this, hx]
  have h4 : lTensor M I.subtype y = 0 := hinjR (by rw [h3, map_zero])
  have h5 : y = 0 := hφM (by rw [h4, map_zero])
  rw [h5, map_zero]

theorem flat_quotient_span_singleton_mul {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (g : S) (hg : g ∈ nonZeroDivisors S) (J : Ideal S)
    [Module.Flat A (S ⧸ Ideal.span ({g} : Set S))] [Module.Flat A (S ⧸ J)] :
    Module.Flat A (S ⧸ (Ideal.span ({g} : Set S) * J)) := by

  have hle : J ≤ Submodule.comap (LinearMap.mulLeft S g) (Ideal.span ({g} : Set S) * J) := by
    intro j hj
    simp only [Submodule.mem_comap, LinearMap.mulLeft_apply]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self g) hj
  let f : (S ⧸ J) →ₗ[A] (S ⧸ (Ideal.span ({g} : Set S) * J)) :=
    (Submodule.mapQ J (Ideal.span ({g} : Set S) * J) (LinearMap.mulLeft S g) hle).restrictScalars A
  have hle' : Ideal.span ({g} : Set S) * J ≤ Submodule.comap (LinearMap.id : S →ₗ[S] S) (Ideal.span ({g} : Set S)) := by
    intro x hx
    simpa using Ideal.mul_le_left hx
  let q : (S ⧸ (Ideal.span ({g} : Set S) * J)) →ₗ[A] (S ⧸ Ideal.span ({g} : Set S)) :=
    (Submodule.mapQ _ _ LinearMap.id hle').restrictScalars A
  have hf : ∀ s : S, f (Submodule.Quotient.mk s) = Submodule.Quotient.mk (g * s) := fun s => rfl
  have hq : ∀ s : S, q (Submodule.Quotient.mk s) = Submodule.Quotient.mk s := fun s => rfl
  refine flat_of_exact f q ?_ ?_ ?_
  ·
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective J x
    rw [LinearMap.mem_ker, hf, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton_mul] at hx
    obtain ⟨j, hj, hgj⟩ := hx
    have : t = j := by
      have h0 : g * (t - j) = 0 := by rw [mul_sub, hgj, sub_self]
      have := (mem_nonZeroDivisors_iff_right.mp hg) _ (by rwa [mul_comm] at h0)
      exact sub_eq_zero.mp this
    rw [Submodule.Quotient.mk_eq_zero, this]
    exact hj
  ·
    intro y
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [hq, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hs
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hs
      exact ⟨Submodule.Quotient.mk t, by rw [hf]; exact congrArg _ (mul_comm g t)⟩
    · rintro ⟨x, hx⟩
      obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective J x
      rw [hf, Submodule.Quotient.eq] at hx

      have h1 : g * t - s ∈ Ideal.span ({g} : Set S) := Ideal.mul_le_left hx
      have h2 : g * t ∈ Ideal.span ({g} : Set S) := Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g)
      have h3 : s = g * t - (g * t - s) := by ring
      rw [h3]
      exact Ideal.sub_mem _ h2 h1
  ·
    intro y
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk s, hq s⟩

end FlatMulAux

namespace FlatMulAux

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

theorem module_ext_quotient {A S : Type*} [CommRing A] [CommRing S] (φ : A →+* S) (𝔦 : Ideal S) :
    (((Ideal.Quotient.mk 𝔦).comp φ).toAlgebra).toModule = (letI := φ.toAlgebra; inferInstance : Module A (S ⧸ 𝔦)) := by
  letI := φ.toAlgebra
  refine Module.ext' _ _ fun a x => ?_
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  show Ideal.Quotient.mk 𝔦 (φ a) * Ideal.Quotient.mk 𝔦 s = Ideal.Quotient.mk 𝔦 (a • s)
  rw [← map_mul, Algebra.smul_def]
  rfl

theorem moduleFlat_quotient_of_ringHom_flat {A S : Type*} [CommRing A] [CommRing S] (φ : A →+* S) (𝔦 : Ideal S)
    (h : ((Ideal.Quotient.mk 𝔦).comp φ).Flat) :
    letI := φ.toAlgebra; Module.Flat A (S ⧸ 𝔦) := by
  have key : @Module.Flat A (S ⧸ 𝔦) _ _ (((Ideal.Quotient.mk 𝔦).comp φ).toAlgebra).toModule := h
  rw [module_ext_quotient] at key
  exact key

theorem ringHom_flat_of_moduleFlat_quotient {A S : Type*} [CommRing A] [CommRing S] (φ : A →+* S) (𝔦 : Ideal S)
    (h : letI := φ.toAlgebra; Module.Flat A (S ⧸ 𝔦)) :
    ((Ideal.Quotient.mk 𝔦).comp φ).Flat := by
  show @Module.Flat A (S ⧸ 𝔦) _ _ (((Ideal.Quotient.mk 𝔦).comp φ).toAlgebra).toModule
  rw [module_ext_quotient]
  exact h

theorem appLE_subschemeι_comp {X T : Scheme} (q : X ⟶ T) (K : X.IdealSheafData) (W : T.Opens) (U : X.affineOpens)
    (e : (U : X.Opens) ≤ q ⁻¹ᵁ W) :
    (K.subschemeι ≫ q).appLE W (K.subschemeι ⁻¹ᵁ (U : X.Opens)) (Scheme.Hom.preimage_mono _ e) =
      q.appLE W U e ≫ CommRingCat.ofHom (Ideal.Quotient.mk (K.ideal U)) ≫ (K.subschemeObjIso U).inv := by
  have h1 := Scheme.Hom.appLE_comp_appLE K.subschemeι q W (U : X.Opens) (K.subschemeι ⁻¹ᵁ (U : X.Opens)) e le_rfl
  have h2 : K.subschemeι.appLE (U : X.Opens) (K.subschemeι ⁻¹ᵁ (U : X.Opens)) le_rfl = K.subschemeι.app U := by
    simp [Scheme.Hom.appLE]
  rw [h2, Scheme.IdealSheafData.subschemeι_app] at h1
  exact h1.symm

theorem flat_appLE_subschemeι_comp_iff {X T : Scheme} (q : X ⟶ T) (K : X.IdealSheafData) (W : T.Opens) (U : X.affineOpens)
    (e : (U : X.Opens) ≤ q ⁻¹ᵁ W) :
    ((K.subschemeι ≫ q).appLE W (K.subschemeι ⁻¹ᵁ (U : X.Opens)) (Scheme.Hom.preimage_mono _ e)).hom.Flat ↔
      ((Ideal.Quotient.mk (K.ideal U)).comp (q.appLE W U e).hom).Flat := by
  rw [appLE_subschemeι_comp q K W U e]

  have hcomp : (q.appLE W U e ≫ CommRingCat.ofHom (Ideal.Quotient.mk (K.ideal U)) ≫ (K.subschemeObjIso U).inv).hom =
      (K.subschemeObjIso U).inv.hom.comp ((Ideal.Quotient.mk (K.ideal U)).comp (q.appLE W U e).hom) := by
    rfl
  rw [hcomp]
  have hinv : Function.Bijective (K.subschemeObjIso U).inv.hom := ConcreteCategory.bijective_of_isIso (K.subschemeObjIso U).inv
  have hhom : Function.Bijective (K.subschemeObjIso U).hom.hom := ConcreteCategory.bijective_of_isIso (K.subschemeObjIso U).hom
  constructor
  · intro h
    have h2 := RingHom.Flat.comp h (RingHom.Flat.of_bijective hhom)
    have hid : (K.subschemeObjIso U).hom.hom.comp (K.subschemeObjIso U).inv.hom = RingHom.id _ := by
      have := congrArg CommRingCat.Hom.hom (K.subschemeObjIso U).inv_hom_id
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_id] using this
    rw [← RingHom.comp_assoc, hid, RingHom.id_comp] at h2
    exact h2
  · intro h
    exact RingHom.Flat.comp h (RingHom.Flat.of_bijective hinv)

theorem isAffineOpen_preimage_subschemeι {X : Scheme} (K : X.IdealSheafData) (U : X.affineOpens) :
    IsAffineOpen (K.subschemeι ⁻¹ᵁ (U : X.Opens)) := by
  rw [← Scheme.IdealSheafData.opensRange_subschemeCover_map]
  exact isAffineOpen_opensRange _

end FlatMulAux

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace in
theorem solution
    {X T : Scheme.{u}} (q : X ⟶ T) (I J : X.IdealSheafData) (hI : I.IsInvertible)
    [Flat (I.subschemeι ≫ q)] [Flat (J.subschemeι ≫ q)] :
    Flat ((I * J).subschemeι ≫ q) := by
  classical
  have hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource @RingHom.Flat :=
    (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway RingHom.Flat.holdsForLocalizationAway).left
  rw [HasRingHomProperty.iff_exists_appLE (P := @Flat) hQ]
  intro z
  set x : X := (I * J).subschemeι.base z with hx

  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q.base x)) isOpen_univ

  obtain ⟨W₀, f, hxf, g, hg, hIg⟩ := hI x

  have hDf : IsAffineOpen (X.basicOpen f) := (X.affineBasicOpen f).2
  obtain ⟨r, hrle, hxr⟩ := hDf.exists_basicOpen_le (V := q ⁻¹ᵁ W ⊓ X.basicOpen f) ⟨x, ⟨hxW, hxf⟩⟩ hxf
  let Dr : X.affineOpens := ⟨X.basicOpen r, hDf.basicOpen r⟩
  have hDr_le_W : (Dr : X.Opens) ≤ q ⁻¹ᵁ W := hrle.trans inf_le_left

  haveI : IsLocalization.Away r Γ(X, X.basicOpen r) := hDf.isLocalization_basicOpen r
  have hIr : I.ideal Dr = Ideal.span {(X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom g} := by
    have := I.map_ideal_basicOpen (X.affineBasicOpen f) r
    rw [hIg, Ideal.map_span, Set.image_singleton] at this
    exact this.symm
  have hgr : (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom g ∈ nonZeroDivisors Γ(X, X.basicOpen r) :=
    IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers r) Γ(X, X.basicOpen r) hg

  refine ⟨⟨W, hW⟩, ⟨(I * J).subschemeι ⁻¹ᵁ (Dr : X.Opens), FlatMulAux.isAffineOpen_preimage_subschemeι _ Dr⟩, hxr,
    Scheme.Hom.preimage_mono _ hDr_le_W, ?_⟩
  show ((((I * J).subschemeι ≫ q).appLE W ((I * J).subschemeι ⁻¹ᵁ (Dr : X.Opens)) (Scheme.Hom.preimage_mono _ hDr_le_W))).hom.Flat
  rw [FlatMulAux.flat_appLE_subschemeι_comp_iff q (I * J) W Dr hDr_le_W]

  have hIflat := HasRingHomProperty.appLE (@Flat) (I.subschemeι ≫ q) inferInstance ⟨W, hW⟩
    ⟨I.subschemeι ⁻¹ᵁ (Dr : X.Opens), FlatMulAux.isAffineOpen_preimage_subschemeι I Dr⟩ (Scheme.Hom.preimage_mono _ hDr_le_W)
  have hJflat := HasRingHomProperty.appLE (@Flat) (J.subschemeι ≫ q) inferInstance ⟨W, hW⟩
    ⟨J.subschemeι ⁻¹ᵁ (Dr : X.Opens), FlatMulAux.isAffineOpen_preimage_subschemeι J Dr⟩ (Scheme.Hom.preimage_mono _ hDr_le_W)
  rw [FlatMulAux.flat_appLE_subschemeι_comp_iff q I W Dr hDr_le_W] at hIflat
  rw [FlatMulAux.flat_appLE_subschemeι_comp_iff q J W Dr hDr_le_W] at hJflat

  let φ : Γ(T, W) →+* Γ(X, Dr) := (q.appLE W Dr hDr_le_W).hom
  letI : Algebra Γ(T, W) Γ(X, Dr) := φ.toAlgebra
  haveI hI' := FlatMulAux.moduleFlat_quotient_of_ringHom_flat φ _ hIflat
  haveI hJ' := FlatMulAux.moduleFlat_quotient_of_ringHom_flat φ _ hJflat
  rw [hIr] at hI'
  apply FlatMulAux.ringHom_flat_of_moduleFlat_quotient φ
  show Module.Flat Γ(T, W) (Γ(X, Dr) ⧸ (I * J).ideal Dr)
  rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, hIr]
  exact FlatMulAux.flat_quotient_span_singleton_mul _ hgr _

#print axioms solution

end S_AlgebraicGeometry_Scheme_IdealSheafData_flat_subschemeIota_mul_comp_of_isInvertible
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_flat_subschemeIota_mul_comp_of_isInvertible (solution)
