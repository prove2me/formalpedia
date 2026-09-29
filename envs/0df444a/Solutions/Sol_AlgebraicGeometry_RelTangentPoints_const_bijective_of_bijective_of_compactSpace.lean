-- Prove2me | solution 1 for AlgebraicGeometry.RelTangentPoints.const_bijective_of_bijective_of_compactSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/1dad8bfa-5c0a-502e-ba98-c1a4d1ecc796

import Mathlib
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Theorems.Thm_AlgebraicGeometry_isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelTangentPoints_const_bijective_of_bijective_of_compactSpace

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace I4cTangentConstAux

theorem comp_bijective_of_appTop_bijective {Z S T : Scheme.{u}} [IsAffine T] (g : Z ⟶ S)
    (hg : Function.Bijective g.appTop.hom) :
    Function.Bijective (fun f : S ⟶ T => g ≫ f) := by
  haveI : IsIso g.appTop := (ConcreteCategory.isIso_iff_bijective g.appTop).mpr hg
  refine ⟨fun f₁ f₂ h => ?_, fun w => ?_⟩
  · apply ext_of_isAffine
    have h' : (g ≫ f₁).appTop = (g ≫ f₂).appTop := by rw [show g ≫ f₁ = g ≫ f₂ from h]
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h'
    exact (cancel_mono g.appTop).mp h'
  · refine ⟨S.toSpecΓ ≫ Spec.map (w.appTop ≫ inv g.appTop) ≫ T.isoSpec.inv, ?_⟩
    show g ≫ S.toSpecΓ ≫ Spec.map (w.appTop ≫ inv g.appTop) ≫ T.isoSpec.inv = w
    calc g ≫ S.toSpecΓ ≫ Spec.map (w.appTop ≫ inv g.appTop) ≫ T.isoSpec.inv
        = Z.toSpecΓ ≫ (Spec.map g.appTop ≫ Spec.map (w.appTop ≫ inv g.appTop)) ≫ T.isoSpec.inv := by
          rw [Scheme.toSpecΓ_naturality_assoc, Category.assoc]
      _ = Z.toSpecΓ ≫ Spec.map w.appTop ≫ T.isoSpec.inv := by
          rw [← Spec.map_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      _ = w ≫ T.toSpecΓ ≫ T.isoSpec.inv := by rw [Scheme.toSpecΓ_naturality_assoc]
      _ = w := by rw [Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]

theorem bijective_appLE_top_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    Function.Bijective (f.appLE ⊤ ⊤ e).hom ↔ Function.Bijective f.appTop.hom := by
  rw [Scheme.Hom.appLE_congr f e rfl (show (⊤ : X.Opens) = f ⁻¹ᵁ ⊤ by simp)
    (fun φ => Function.Bijective φ.hom), Scheme.Hom.appLE_eq_app]
  exact Iff.rfl

section Glob

variable {k : Type u} [Field k]
  (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
  {Z₀ Z : Scheme.{u}} (f₀ : Z₀ ⟶ Spec (CommRingCat.of k))
  (q₁ : Z ⟶ Z₀) (q₂ : Z ⟶ SquareZero.spec k V) (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase k V))

include hZ in

theorem appTop_snd_bijective [CompactSpace Z₀] [QuasiSeparatedSpace Z₀]
    (h₀ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f₀.appTop).hom) :
    Function.Bijective q₂.appTop.hom := by
  haveI : Flat (SquareZero.toBase k V) := by
    rw [SquareZero.toBase, Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance

  haveI : IsIso ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f₀.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr h₀
  haveI hf₀ : IsIso f₀.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of k)).inv _
  have hUSX : (⊤ : Z₀.Opens) ≤ f₀ ⁻¹ᵁ ⊤ := by simp
  have hUST : (⊤ : (SquareZero.spec k V).Opens) ≤ SquareZero.toBase k V ⁻¹ᵁ ⊤ := by simp
  have hUY : (⊤ : Z.Opens) = q₁ ⁻¹ᵁ ⊤ ⊓ q₂ ⁻¹ᵁ ⊤ := by simp
  haveI : IsIso (f₀.appLE ⊤ ⊤ hUSX) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ((bijective_appLE_top_iff f₀ hUSX).mpr (ConcreteCategory.bijective_of_isIso f₀.appTop))
  haveI hps := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right hZ hUST hUSX hUY
    (isAffineOpen_top _) (isAffineOpen_top _)
    (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ) (by rw [TopologicalSpace.Opens.coe_top]; exact isQuasiSeparated_univ)
  have hcomp : pushout.inr (f₀.appLE ⊤ ⊤ hUSX) ((SquareZero.toBase k V).appLE ⊤ ⊤ hUST) ≫
      pushoutSection hZ hUST hUSX hUY = q₂.appLE ⊤ ⊤ (by simp) :=
    pushout.inr_desc _ _ _
  have hiso : IsIso (q₂.appLE ⊤ ⊤ (by simp)) := by
    rw [← hcomp]
    infer_instance
  exact (bijective_appLE_top_iff q₂ _).mp (ConcreteCategory.bijective_of_isIso (q₂.appLE ⊤ ⊤ _))

theorem isPullback_zeroSection :
    IsPullback (SquareZero.zeroSection V f₀ q₁ q₂ hZ) f₀ q₂ (SquareZero.basePoint k V) := by
  refine IsPullback.of_right ?_ (SquareZero.zeroSection_snd V f₀ q₁ q₂ hZ) hZ
  rw [SquareZero.zeroSection_fst, SquareZero.basePoint_toBase]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

theorem zeroSection_surjective : Surjective (SquareZero.zeroSection V f₀ q₁ q₂ hZ) := by
  have hsurj : Function.Surjective (TrivSqZeroExt.fstHom k k V).toRingHom := fun a =>
    ⟨TrivSqZeroExt.inl a, rfl⟩
  have hnil : IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom k k V).toRingHom) :=
    ⟨2, TrivSqZeroExt.kerIdeal_sq k V⟩
  exact (AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
    (TrivSqZeroExt.fstHom k k V).toRingHom hsurj hnil q₂ f₀
    (SquareZero.zeroSection V f₀ q₁ q₂ hZ) (isPullback_zeroSection V f₀ q₁ q₂ hZ)).2.1

end Glob

theorem subsingleton_spec {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V] :
    Subsingleton ↥(SquareZero.spec k V) := by
  change Subsingleton (PrimeSpectrum (TrivSqZeroExt k V))
  have aux : ∀ p q : PrimeSpectrum (TrivSqZeroExt k V), p.asIdeal ≤ q.asIdeal := by
    intro p q a ha
    have hker : TrivSqZeroExt.kerIdeal k V ≤ q.asIdeal :=
      (Ideal.IsPrime.pow_le_iff (I := TrivSqZeroExt.kerIdeal k V) (P := q.asIdeal) two_ne_zero).mp
        (by rw [TrivSqZeroExt.kerIdeal_sq]; exact bot_le)
    apply hker
    have hna : ¬ IsUnit a := fun hu => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, not_not] at hna
    rw [TrivSqZeroExt.mem_kerIdeal_iff_inr]
    ext <;> simp [hna]
  exact ⟨fun p q => PrimeSpectrum.ext (le_antisymm (aux p q) (aux q p))⟩

end I4cTangentConstAux

open I4cTangentConstAux in
theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (pt : Spec (CommRingCat.of k) ⟶ X) (hpt : pt ≫ x = 𝟙 (Spec (CommRingCat.of k)))
    (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V] [Module.Finite k V]
    {Z₀ Z : Scheme.{u}} [CompactSpace Z₀] [QuasiSeparatedSpace Z₀] (f₀ : Z₀ ⟶ Spec (CommRingCat.of k))
    (h₀ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f₀.appTop).hom)
    (q₁ : Z ⟶ Z₀) (q₂ : Z ⟶ SquareZero.spec k V) (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase k V)) :
    Function.Bijective (RelTangentPoints.const x pt V f₀ q₁ q₂ hZ) := by

  have hq₂ : Function.Bijective q₂.appTop.hom := appTop_snd_bijective V f₀ q₁ q₂ hZ h₀
  have hf₀ : Function.Bijective f₀.appTop.hom := by
    haveI : IsIso ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f₀.appTop) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr h₀
    haveI : IsIso f₀.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of k)).inv _
    exact ConcreteCategory.bijective_of_isIso f₀.appTop

  haveI : Subsingleton (Spec (CommRingCat.of k)) :=
    (inferInstance : Subsingleton (PrimeSpectrum k))
  let s₀ : ↥(Spec (CommRingCat.of k)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  haveI : Subsingleton ↥(SquareZero.spec k V) := subsingleton_spec (k := k) V
  let p : X := pt s₀
  let 𝒰 := X.affineCover
  let j := 𝒰.idx p
  have hjp : p ∈ Set.range (𝒰.f j) := 𝒰.covers p

  have hrange_pt : Set.range pt ⊆ Set.range (𝒰.f j) := by
    rintro _ ⟨s, rfl⟩
    rw [Subsingleton.elim s s₀]
    exact hjp

  haveI hzs : Surjective (SquareZero.zeroSection V f₀ q₁ q₂ hZ) := zeroSection_surjective V f₀ q₁ q₂ hZ
  refine ⟨?_, ?_⟩
  ·
    intro v₁ v₂ h
    have h' : q₂ ≫ v₁.1 = q₂ ≫ v₂.1 := congrArg Subtype.val h

    have hr : ∀ v : TangentPoints x pt V, Set.range v.1 ⊆ Set.range (𝒰.f j) := by
      intro v
      rintro _ ⟨d, rfl⟩
      have hd : d = SquareZero.basePoint k V s₀ := Subsingleton.elim _ _
      rw [hd, ← Scheme.Hom.comp_apply, v.2.2]
      exact hrange_pt ⟨s₀, rfl⟩
    have hl₁ := IsOpenImmersion.lift_fac (𝒰.f j) v₁.1 (hr v₁)
    have hl₂ := IsOpenImmersion.lift_fac (𝒰.f j) v₂.1 (hr v₂)
    apply TangentPoints.ext
    rw [← hl₁, ← hl₂]
    congr 1
    apply (comp_bijective_of_appTop_bijective (T := 𝒰.X j) q₂ hq₂).1
    show q₂ ≫ _ = q₂ ≫ _
    rw [← cancel_mono (𝒰.f j), Category.assoc, Category.assoc, hl₁, hl₂, h']
  ·
    intro w
    have hwr : Set.range w.1 ⊆ Set.range (𝒰.f j) := by
      rintro _ ⟨z, rfl⟩
      obtain ⟨z₀, rfl⟩ := (SquareZero.zeroSection V f₀ q₁ q₂ hZ).surjective z
      rw [← Scheme.Hom.comp_apply, w.2.2, Scheme.Hom.comp_apply]
      exact hrange_pt ⟨_, rfl⟩
    let w' := IsOpenImmersion.lift (𝒰.f j) w.1 hwr
    have hw' : w' ≫ 𝒰.f j = w.1 := IsOpenImmersion.lift_fac _ _ _
    obtain ⟨v', hv'⟩ := (comp_bijective_of_appTop_bijective (T := 𝒰.X j) q₂ hq₂).2 w'
    have hv'w : q₂ ≫ v' = w' := hv'
    let pt' := IsOpenImmersion.lift (𝒰.f j) pt hrange_pt
    have hpt' : pt' ≫ 𝒰.f j = pt := IsOpenImmersion.lift_fac _ _ _
    refine ⟨⟨v' ≫ 𝒰.f j, ?_, ?_⟩, ?_⟩
    ·
      apply (comp_bijective_of_appTop_bijective (T := Spec (CommRingCat.of k)) q₂ hq₂).1
      show q₂ ≫ (v' ≫ 𝒰.f j) ≫ x = q₂ ≫ SquareZero.toBase k V
      rw [← Category.assoc, ← Category.assoc, hv'w, hw', w.2.1]
    ·
      rw [← Category.assoc, ← hpt']
      congr 1
      apply (comp_bijective_of_appTop_bijective (T := 𝒰.X j) f₀ hf₀).1
      show f₀ ≫ SquareZero.basePoint k V ≫ v' = f₀ ≫ pt'
      rw [← cancel_mono (𝒰.f j), Category.assoc, Category.assoc, Category.assoc, hpt',
        ← SquareZero.zeroSection_snd_assoc V f₀ q₁ q₂ hZ, reassoc_of% hv'w, hw', w.2.2]
    · apply RelTangentPoints.ext
      show q₂ ≫ v' ≫ 𝒰.f j = w.1
      rw [← Category.assoc, hv'w, hw']

end S_AlgebraicGeometry_RelTangentPoints_const_bijective_of_bijective_of_compactSpace
end P2MW
export P2MW.S_AlgebraicGeometry_RelTangentPoints_const_bijective_of_bijective_of_compactSpace (solution)
