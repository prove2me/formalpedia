-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.finite_prime_constant_etale_cohomology_prime_to_characteristic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-20T16:18:21.238177+00:00
-- url     : https://prove2.me/submissions/2748df6c-c058-4a7e-abb7-f724526d5ee5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_finite_prime_constant_etale_cohomology_prime_to_characteristic_of_isReduced

noncomputable section

section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace PhilipponReducedClosedSubscheme

theorem radical_eq_of_isReduced {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsReduced I.subscheme] : I.radical = I := by
  apply Scheme.IdealSheafData.ext
  funext U
  change (I.ideal U).radical = I.ideal U
  apply Ideal.radical_eq_iff.mpr
  apply (Ideal.isRadical_iff_quotient_reduced (I.ideal U)).mpr
  exact isReduced_of_injective (I.subschemeObjIso U).inv.hom
    (I.subschemeObjIso U).symm.commRingCatIsoToRingEquiv.injective

theorem isReduced_of_radical_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    (h : I.radical = I) : IsReduced I.subscheme := by
  have hU (U : X.affineOpens) : (I.ideal U).IsRadical := by
    apply Ideal.radical_eq_iff.mp
    exact congrArg (fun J : X.IdealSheafData => J.ideal U) h
  haveI (U : X.affineOpens) : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) :=
    (Ideal.isRadical_iff_quotient_reduced (I.ideal U)).mp (hU U)
  haveI (U : X.affineOpens) : IsReduced (I.subschemeCover.openCover.X U) := by
    change IsReduced (Spec (CommRingCat.of (Γ(X, U) ⧸ I.ideal U)))
    infer_instance
  exact IsReduced.of_openCover I.subscheme I.subschemeCover.openCover

theorem isReduced_iff_radical_eq {X : Scheme.{u}} (I : X.IdealSheafData) :
    IsReduced I.subscheme ↔ I.radical = I :=
  ⟨fun h => @radical_eq_of_isReduced X I h, isReduced_of_radical_eq I⟩

theorem integral_of_prime_top {X : Scheme.{u}} [IsAffine X] (I : X.IdealSheafData)
    [(I.ideal ⟨⊤, isAffineOpen_top X⟩).IsPrime] : IsIntegral I.subscheme := by
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  haveI : (I.ideal U).IsPrime :=
    (inferInstance : (I.ideal ⟨⊤, isAffineOpen_top X⟩).IsPrime)
  haveI : IsDomain (Γ(X, U) ⧸ I.ideal U) := inferInstance
  let f := I.subschemeCover.f U
  haveI : Surjective f := by
    constructor
    intro x
    have hx : x ∈ f.opensRange := by
      change x ∈ (I.subschemeCover.f U).opensRange
      rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]
      trivial
    exact hx
  haveI : IsIso f := (isIso_iff_isOpenImmersion_and_surjective f).mpr
    ⟨inferInstance, inferInstance⟩
  haveI : IsIntegral (Spec (I.subschemeCover.X U)) := by
    change IsIntegral (Spec (CommRingCat.of (Γ(X, U) ⧸ I.ideal U)))
    infer_instance
  exact IsIntegral.of_isIso f

theorem radical_comap_open {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (f : X ⟶ Y) [IsOpenImmersion f] : (I.comap f).radical = I.radical.comap f := by
  apply Scheme.IdealSheafData.ext
  funext U
  change ((I.comap f).ideal U).radical = (I.radical.comap f).ideal U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Ideal.comap_radical _ _).symm

theorem eq_of_reduced_support {X : Scheme.{u}} (I J : X.IdealSheafData)
    (hI : I.radical = I) (hJ : J.radical = J) (hs : I.support = J.support) : I = J := by
  rw [← hI, ← Scheme.IdealSheafData.vanishingIdeal_support, hs,
    Scheme.IdealSheafData.vanishingIdeal_support, hJ]

end PhilipponReducedClosedSubscheme

end

section

set_option autoImplicit false
set_option maxHeartbeats 850000
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Polynomial
open scoped TensorProduct


namespace PhilipponEtaleThickeningLifts

universe u

/- The local algebra and scheme lifting arguments are adapted from the
Prove2Me Fermat's Last Theorem development. The chartwise nilpotence argument
uses local Noetherianity and surjectivity of the closed immersion. -/
private theorem eq_of_comp_eq_of_surjective {X Y T T₀ : Scheme.{u}} (q : Y ⟶ X)
    [FormallyUnramified q] [LocallyOfFiniteType q]
    (k : T₀ ⟶ T) [Surjective k] {s₁ s₂ : T ⟶ Y}
    (hq : s₁ ≫ q = s₂ ≫ q) (hk : k ≫ s₁ = k ≫ s₂) : s₁ = s₂ := by

  haveI : IsOpenImmersion (pullback.diagonal q) := inferInstance
  haveI : IsOpenImmersion (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) := inferInstance

  have hfac : k ≫ pullback.lift s₁ s₂ hq = (k ≫ s₁) ≫ pullback.diagonal q := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
    · simp only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, hk]
  have hk' : pullback.lift k (k ≫ s₁) hfac ≫ pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q) = k :=
    pullback.lift_fst _ _ _
  haveI : Surjective (pullback.lift k (k ≫ s₁) hfac ≫
      pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) := by rw [hk']; infer_instance
  haveI : Surjective (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) :=
    Surjective.of_comp (pullback.lift k (k ≫ s₁) hfac) _
  haveI : IsIso (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩

  have hp : pullback.lift s₁ s₂ hq =
      inv (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) ≫
        pullback.snd (pullback.lift s₁ s₂ hq) (pullback.diagonal q) ≫ pullback.diagonal q := by
    rw [← pullback.condition, IsIso.inv_hom_id_assoc]
  have h1 : s₁ = inv (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) ≫
      pullback.snd (pullback.lift s₁ s₂ hq) (pullback.diagonal q) := by
    calc s₁ = pullback.lift s₁ s₂ hq ≫ pullback.fst q q := (pullback.lift_fst _ _ _).symm
      _ = (inv (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) ≫
            pullback.snd (pullback.lift s₁ s₂ hq) (pullback.diagonal q) ≫ pullback.diagonal q) ≫
              pullback.fst q q := by rw [← hp]
      _ = _ := by simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
  have h2 : s₂ = inv (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) ≫
      pullback.snd (pullback.lift s₁ s₂ hq) (pullback.diagonal q) := by
    calc s₂ = pullback.lift s₁ s₂ hq ≫ pullback.snd q q := (pullback.lift_snd _ _ _).symm
      _ = (inv (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) ≫
            pullback.snd (pullback.lift s₁ s₂ hq) (pullback.diagonal q) ≫ pullback.diagonal q) ≫
              pullback.snd q q := by rw [← hp]
      _ = _ := by simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
  rw [h1, ← h2]

private theorem affine_kernel_nilpotent {T T₀ : Scheme.{u}} [IsLocallyNoetherian T]
    (k : T₀ ⟶ T) [IsClosedImmersion k] [Surjective k] (U : T.affineOpens) :
    IsNilpotent (RingHom.ker (k.app U.val).hom) := by
  have hsupport : k.ker.support = ⊤ := by
    ext1
    rw [Scheme.Hom.support_ker, k.surjective.range_eq]
    simp
  have hle := Scheme.IdealSheafData.le_radical k.ker
  rw [← Scheme.IdealSheafData.vanishingIdeal_support, hsupport,
    Scheme.IdealSheafData.vanishingIdeal_top] at hle
  have hU := hle U
  rw [Scheme.Hom.ker_apply] at hU
  haveI := IsLocallyNoetherian.component_noetherian U
  exact (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)).mpr hU

private theorem exists_of_forall_exists_nhd {X Y T T₀ : Scheme.{u}} (q : Y ⟶ X)
    [FormallyUnramified q] [LocallyOfFiniteType q]
    (k : T₀ ⟶ T) [Surjective k] (t : T ⟶ X) (s₀ : T₀ ⟶ Y)
    (H : ∀ p : T, ∃ (U : T.Opens) (_ : p ∈ U) (sU : (U : Scheme.{u}) ⟶ Y),
      sU ≫ q = U.ι ≫ t ∧ (k ∣_ U) ≫ sU = (k ⁻¹ᵁ U).ι ≫ s₀) :
    ∃ s : T ⟶ Y, s ≫ q = t ∧ k ≫ s = s₀ := by
  choose U hpU sU hsUq hsUk using H
  let 𝒰 : T.OpenCover :=
    { I₀ := T, X := fun i => (U i), f := fun i => (U i).ι,
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x ↦ ⟨x, by simpa using hpU x⟩, inferInstance⟩ }

  have hcompat : ∀ i j : T, pullback.fst (𝒰.f i) (𝒰.f j) ≫ sU i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ sU j := by
    intro i j
    let g : pullback (𝒰.f i) (𝒰.f j) ⟶ T := pullback.fst (𝒰.f i) (𝒰.f j) ≫ (U i).ι
    have hg : pullback.snd (𝒰.f i) (𝒰.f j) ≫ (U j).ι = g := (pullback.condition).symm

    have key : ∀ (l : T) (m : pullback (𝒰.f i) (𝒰.f j) ⟶ (U l : Scheme.{u})) (hm : m ≫ (U l).ι = g),
        pullback.snd k g ≫ m ≫ sU l = pullback.fst k g ≫ s₀ := by
      intro l m hm
      have w : (pullback.snd k g ≫ m) ≫ (U l).ι = pullback.fst k g ≫ k := by
        rw [Category.assoc, hm, pullback.condition]
      let n := (isPullback_morphismRestrict k (U l)).lift (pullback.snd k g ≫ m) (pullback.fst k g) w
      have hn1 : n ≫ (k ∣_ U l) = pullback.snd k g ≫ m := IsPullback.lift_fst _ _ _ _
      have hn2 : n ≫ (k ⁻¹ᵁ U l).ι = pullback.fst k g := IsPullback.lift_snd _ _ _ _
      rw [← Category.assoc, ← hn1, Category.assoc, hsUk, ← Category.assoc, hn2]
    haveI : Surjective (pullback.snd k g) := inferInstance
    refine eq_of_comp_eq_of_surjective q (pullback.snd k g) ?_ ?_
    · rw [Category.assoc, hsUq, Category.assoc, hsUq, ← Category.assoc, ← Category.assoc, pullback.condition]
    · rw [key i (pullback.fst (𝒰.f i) (𝒰.f j)) rfl, key j (pullback.snd (𝒰.f i) (𝒰.f j)) hg]
  refine ⟨𝒰.glueMorphisms sU hcompat, ?_, ?_⟩
  · refine Scheme.Cover.hom_ext 𝒰 _ _ fun i ↦ ?_
    rw [Scheme.Cover.ι_glueMorphisms_assoc, hsUq]
  ·
    let 𝒱 : T₀.OpenCover :=
      { I₀ := T, X := fun i => (k ⁻¹ᵁ U i), f := fun i => (k ⁻¹ᵁ U i).ι,
        mem₀ := by
          rw [Scheme.presieve₀_mem_precoverage_iff]
          refine ⟨fun x ↦ ⟨k.base x, by simpa using hpU (k.base x)⟩, inferInstance⟩ }
    refine Scheme.Cover.hom_ext 𝒱 _ _ fun i ↦ ?_
    show (k ⁻¹ᵁ U i).ι ≫ k ≫ 𝒰.glueMorphisms sU hcompat = (k ⁻¹ᵁ U i).ι ≫ s₀
    rw [← morphismRestrict_ι_assoc, show (U i).ι = 𝒰.f i from rfl, Scheme.Cover.ι_glueMorphisms, hsUk]

private theorem appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

private theorem exists_nhd_lift {X Y T T₀ : Scheme.{u}} (q : Y ⟶ X) [Etale q]
    (k : T₀ ⟶ T) [IsClosedImmersion k] [Surjective k] [IsLocallyNoetherian T]
    (t : T ⟶ X) (s₀ : T₀ ⟶ Y) (hs₀ : s₀ ≫ q = k ≫ t) (p : T) :
    ∃ (U : T.Opens) (_ : p ∈ U) (sU : (U : Scheme.{u}) ⟶ Y),
      sU ≫ q = U.ι ≫ t ∧ (k ∣_ U) ≫ sU = (k ⁻¹ᵁ U).ι ≫ s₀ := by
  obtain ⟨p₀, hp₀⟩ := k.surjective p

  obtain ⟨_, ⟨R', hR', rfl⟩, hpR', -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (t.base p)) isOpen_univ

  have hqs : q.base (s₀.base p₀) = t.base p := by
    have := congrArg (fun f : T₀ ⟶ X => f.base p₀) hs₀
    simpa [hp₀] using this
  have hy : s₀.base p₀ ∈ q ⁻¹ᵁ R' := by
    show q.base (s₀.base p₀) ∈ R'
    rw [hqs]; exact hpR'
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWR'⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hy (q ⁻¹ᵁ R').isOpen
  change W ≤ q ⁻¹ᵁ R' at hWR'

  let O : T.Opens := ⟨(k.base '' ((s₀ ⁻¹ᵁ W : T₀.Opens) : Set T₀)ᶜ)ᶜ, by
    rw [isOpen_compl_iff]
    exact k.isClosedEmbedding.isClosedMap _ (isClosed_compl_iff.mpr (s₀ ⁻¹ᵁ W).isOpen)⟩
  have hpO : p ∈ O := by
    rintro ⟨x, hx, hxp⟩
    apply hx
    have : x = p₀ := k.isClosedEmbedding.injective (hxp.trans hp₀.symm)
    subst this
    exact hyW

  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, hUle⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
    (show p ∈ ((t ⁻¹ᵁ R' ⊓ O : T.Opens) : Set T) from ⟨hpR', hpO⟩) (t ⁻¹ᵁ R' ⊓ O).isOpen
  have hUR' : U ≤ t ⁻¹ᵁ R' := fun x hx => (hUle hx).1
  have hkUW : k ⁻¹ᵁ U ≤ s₀ ⁻¹ᵁ W := by
    intro x hx
    by_contra hxW
    exact (hUle hx).2 ⟨x, hxW, rfl⟩
  have hkU : IsAffineOpen (k ⁻¹ᵁ U) := hU.preimage k
  have hkUR' : k ⁻¹ᵁ U ≤ (k ≫ t) ⁻¹ᵁ R' := fun x hx => hUR' hx

  have hφ : (q.appLE R' W hWR').hom.Etale :=
    HasRingHomProperty.appLE (P := @Etale) q inferInstance ⟨R', hR'⟩ ⟨W, hW⟩ hWR'
  algebraize [(q.appLE R' W hWR').hom, (t.appLE R' U hUR').hom, ((k ≫ t).appLE R' (k ⁻¹ᵁ U) hkUR').hom]
  let σ : Γ(Y, W) →ₐ[Γ(X, R')] Γ(T₀, k ⁻¹ᵁ U) := ⟨(s₀.appLE W (k ⁻¹ᵁ U) hkUW).hom, fun r ↦ by
    simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
    rw [appLE_congr_hom hs₀]⟩
  let κ : Γ(T, U) →ₐ[Γ(X, R')] Γ(T₀, k ⁻¹ᵁ U) := ⟨(k.appLE U (k ⁻¹ᵁ U) le_rfl).hom, fun r ↦ by
    simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]⟩
  have hκs : Function.Surjective κ := by
    show Function.Surjective (k.appLE U (k ⁻¹ᵁ U) le_rfl).hom
    rw [← Scheme.Hom.app_eq_appLE]
    exact k.app_surjective U hU
  have hκn : IsNilpotent (RingHom.ker (κ : Γ(T, U) →+* Γ(T₀, k ⁻¹ᵁ U))) := by
    show IsNilpotent (RingHom.ker (k.appLE U (k ⁻¹ᵁ U) le_rfl).hom)
    rw [← Scheme.Hom.app_eq_appLE]
    exact affine_kernel_nilpotent k ⟨U, hU⟩
  let ψ : Γ(Y, W) →ₐ[Γ(X, R')] Γ(T, U) := Algebra.FormallySmooth.liftOfSurjective σ κ hκs hκn
  have hψ : κ.comp ψ = σ := Algebra.FormallySmooth.comp_liftOfSurjective σ κ hκs hκn

  refine ⟨U, hpU, hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hW.fromSpec, ?_, ?_⟩
  ·
    have h1 : q.appLE R' W hWR' ≫ CommRingCat.ofHom ψ.toRingHom = t.appLE R' U hUR' := by
      ext r
      change ψ (algebraMap Γ(X, R') Γ(Y, W) r) = algebraMap Γ(X, R') Γ(T, U) r
      exact ψ.commutes r
    rw [Category.assoc, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec q hR' hW hWR',
      ← Spec.map_comp_assoc, h1, IsAffineOpen.SpecMap_appLE_fromSpec t hR' hU hUR',
      ← hU.isoSpec_inv_ι]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  ·
    have h2 : CommRingCat.ofHom ψ.toRingHom ≫ k.appLE U (k ⁻¹ᵁ U) le_rfl = s₀.appLE W (k ⁻¹ᵁ U) hkUW := by
      ext a
      change κ (ψ a) = σ a
      rw [← hψ]; rfl
    have h3 : Spec.map (k.appLE U (k ⁻¹ᵁ U) le_rfl) ≫ hU.isoSpec.inv = hkU.isoSpec.inv ≫ (k ∣_ U) := by
      rw [← cancel_mono (Scheme.Opens.ι U), Category.assoc, Category.assoc, hU.isoSpec_inv_ι, morphismRestrict_ι,
        IsAffineOpen.SpecMap_appLE_fromSpec k hU hkU le_rfl, ← hkU.isoSpec_inv_ι, Category.assoc]
    rw [← cancel_epi hkU.isoSpec.inv, ← Category.assoc, ← h3, Category.assoc, Iso.inv_hom_id_assoc,
      ← Spec.map_comp_assoc, h2, IsAffineOpen.SpecMap_appLE_fromSpec s₀ hW hkU hkUW, ← Category.assoc, hkU.isoSpec_inv_ι]

theorem existsUnique_lift {X Y T T₀ : Scheme.{u}} (q : Y ⟶ X) [Etale q]
    (k : T₀ ⟶ T) [IsClosedImmersion k] [Surjective k] [IsLocallyNoetherian T]
    (t : T ⟶ X) (s₀ : T₀ ⟶ Y) (hs₀ : s₀ ≫ q = k ≫ t) :
    ∃! s : T ⟶ Y, s ≫ q = t ∧ k ≫ s = s₀ := by
  obtain ⟨s, hs, hks⟩ := exists_of_forall_exists_nhd q k t s₀ (exists_nhd_lift q k t s₀ hs₀)
  refine ⟨s, ⟨hs, hks⟩, fun s' hs' => ?_⟩
  exact eq_of_comp_eq_of_surjective q k (hs'.1.trans hs.symm) (hs'.2.trans hks.symm)

private theorem lift_standardEtale
    {C C₀ : Type u} [CommRing C] [CommRing C₀] [Algebra C C₀] (hC : Function.Surjective (algebraMap C C₀))
    (S₀ : Type u) [CommRing S₀] [Algebra C₀ S₀] [Algebra.IsStandardEtale C₀ S₀] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra C S), Algebra.IsStandardEtale C S ∧ Nonempty (C₀ ⊗[C] S ≃ₐ[C₀] S₀) := by
  classical
  obtain ⟨P₀⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := C₀) (S := S₀)
  rcases subsingleton_or_nontrivial C₀ with hC₀ | hC₀
  ·
    haveI : Subsingleton S₀ := Module.subsingleton C₀ S₀
    refine ⟨C, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
    exact AlgEquiv.ofBijective ((Algebra.ofId C₀ S₀).comp (Algebra.TensorProduct.rid C C₀ C₀).toAlgHom)
      ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩

  set φ : C →+* C₀ := algebraMap C C₀ with hφ
  obtain ⟨f, hf, -, hfm⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic (f := φ) ((mem_lifts _).mpr (map_surjective φ hC P₀.f)) P₀.monic_f
  obtain ⟨p₁, p₂, n, hP⟩ := P₀.cond
  obtain ⟨g, hg⟩ := map_surjective φ hC P₀.g
  obtain ⟨q₁, hq₁⟩ := map_surjective φ hC p₁
  obtain ⟨q₂, hq₂⟩ := map_surjective φ hC p₂
  let P : StandardEtalePair C :=
    { f := f, monic_f := hfm, g := g * (derivative f * q₁ + f * q₂), cond := ⟨g * q₁, g * q₂, 1, by ring⟩ }
  have hPf : P.f.map φ = P₀.f := hf
  have hPg : P.g.map φ = P₀.g ^ (n + 1) := by
    show (g * (derivative f * q₁ + f * q₂)).map φ = P₀.g ^ (n + 1)
    simp only [Polynomial.map_mul, Polynomial.map_add, ← Polynomial.derivative_map, hf, hg, hq₁, hq₂, hP]
    ring

  letI : Algebra C S₀ := ((algebraMap C₀ S₀).comp φ).toAlgebra
  haveI : IsScalarTower C C₀ S₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have key : ∀ (T : Type u) [CommRing T] [Algebra C₀ T] [Algebra C T] [IsScalarTower C C₀ T] (t : T),
      P.HasMap t ↔ P₀.HasMap t := by
    intro T _ _ _ _ t
    simp only [StandardEtalePair.HasMap]
    rw [← aeval_map_algebraMap C₀ t P.f, ← aeval_map_algebraMap C₀ t P.g, ← hφ, hPf, hPg, map_pow,
      isUnit_pow_iff (Nat.succ_ne_zero n)]
  have h1 : P.HasMap P₀.x := (key S₀ P₀.x).mpr P₀.hasMap
  have h2' : P.HasMap ((1 : C₀) ⊗ₜ[C] P.X) :=
    (StandardEtalePair.hasMap_X (P := P)).map
      (Algebra.TensorProduct.includeRight (R := C) (A := C₀) (B := P.Ring))
  have h2 : P₀.HasMap ((1 : C₀) ⊗ₜ[C] P.X) := (key (C₀ ⊗[C] P.Ring) _).mp h2'
  let F : C₀ ⊗[C] P.Ring →ₐ[C₀] S₀ :=
    Algebra.TensorProduct.lift (Algebra.ofId C₀ S₀) (P.lift P₀.x h1) (fun _ _ => .all _ _)
  let G : S₀ →ₐ[C₀] C₀ ⊗[C] P.Ring := (P₀.lift ((1 : C₀) ⊗ₜ[C] P.X) h2).comp P₀.equivRing.toAlgHom
  have hF : F ((1 : C₀) ⊗ₜ[C] P.X) = P₀.x := by
    simp [F, Algebra.TensorProduct.lift_tmul, StandardEtalePair.lift_X]
  have hG : G P₀.x = (1 : C₀) ⊗ₜ[C] P.X := by
    simp [G, StandardEtalePresentation.equivRing_x, StandardEtalePair.lift_X]
  refine ⟨P.Ring, inferInstance, inferInstance, inferInstance, ⟨AlgEquiv.ofAlgHom F G ?_ ?_⟩⟩
  · apply P₀.hom_ext
    simp only [AlgHom.comp_apply, AlgHom.id_apply, hG, hF]
  · apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · apply StandardEtalePair.hom_ext
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
        AlgHom.id_apply, hF, hG]

theorem exists_local_model
    {X X₀ Y₀ : Scheme.{u}} (i : X₀ ⟶ X) [IsClosedImmersion i] (q₀ : Y₀ ⟶ X₀) [Etale q₀] (y : Y₀) :
    ∃ (V₀ : Y₀.Opens) (_ : y ∈ V₀) (V : Scheme.{u}) (qV : V ⟶ X) (_ : Etale qV) (jV : (V₀ : Scheme.{u}) ⟶ V),
      IsPullback jV (V₀.ι ≫ q₀) qV i := by
  classical

  obtain ⟨U, hUa, hxU, -⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show i (q₀ y) ∈ (⊤ : X.Opens) from trivial)
  replace hUa : IsAffineOpen U := hUa

  have hU₀a : IsAffineOpen (i ⁻¹ᵁ U) := hUa.preimage i

  obtain ⟨W, hWa, hyW, hWle⟩ := (Opens.isBasis_iff_nbhd.mp Y₀.isBasis_affineOpens)
    (show y ∈ q₀ ⁻¹ᵁ (i ⁻¹ᵁ U) from hxU)
  replace hWa : IsAffineOpen W := hWa

  letI algA : Algebra Γ(X, U) Γ(X₀, i ⁻¹ᵁ U) := (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  letI algB : Algebra Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, W) := (q₀.appLE (i ⁻¹ᵁ U) W hWle).hom.toAlgebra
  have ha : Function.Surjective (algebraMap Γ(X, U) Γ(X₀, i ⁻¹ᵁ U)) := by
    show Function.Surjective (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom
    rw [← Scheme.Hom.app_eq_appLE]
    exact i.app_surjective U hUa
  have hEt : Algebra.Etale Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, W) := Etale.etale_appLE q₀ hU₀a hWa hWle
  haveI := hEt.formallyEtale
  haveI := hEt.finitePresentation

  set p : PrimeSpectrum Γ(Y₀, W) := hWa.primeIdealOf ⟨y, hyW⟩ with hp
  obtain ⟨g, hgp, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := Γ(X₀, i ⁻¹ᵁ U)) p.asIdeal
  have hV₀a : IsAffineOpen (Y₀.basicOpen g) := hWa.basicOpen g
  have hV₀le : Y₀.basicOpen g ≤ q₀ ⁻¹ᵁ (i ⁻¹ᵁ U) := (Y₀.basicOpen_le g).trans hWle
  have hyV₀ : y ∈ Y₀.basicOpen g := by
    have h1 : hWa.fromSpec p = y := hWa.fromSpec_primeIdealOf ⟨y, hyW⟩
    rw [← h1]
    show p ∈ hWa.fromSpec ⁻¹ᵁ Y₀.basicOpen g
    rw [hWa.fromSpec_preimage_basicOpen]
    exact hgp
  letI algS₀ : Algebra Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, Y₀.basicOpen g) :=
    (q₀.appLE (i ⁻¹ᵁ U) (Y₀.basicOpen g) hV₀le).hom.toAlgebra
  haveI : IsScalarTower Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, W) Γ(Y₀, Y₀.basicOpen g) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      show (q₀.appLE (i ⁻¹ᵁ U) (Y₀.basicOpen g) hV₀le).hom r =
        (Y₀.presheaf.map (homOfLE (Y₀.basicOpen_le g)).op).hom ((q₀.appLE (i ⁻¹ᵁ U) W hWle).hom r)
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map])
  haveI : IsLocalization.Away g Γ(Y₀, Y₀.basicOpen g) := hWa.isLocalization_basicOpen g
  haveI : Algebra.IsStandardEtale Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, Y₀.basicOpen g) :=
    Algebra.IsStandardEtale.of_equiv
      ((IsLocalization.algEquiv (.powers g) (Localization.Away g) Γ(Y₀, Y₀.basicOpen g)).restrictScalars
        Γ(X₀, i ⁻¹ᵁ U))

  obtain ⟨S, _, _, hS, ⟨e⟩⟩ :=
    lift_standardEtale ha
      Γ(Y₀, Y₀.basicOpen g)
  have hSe : (algebraMap Γ(X, U) S).Etale := RingHom.etale_algebraMap.mpr inferInstance
  haveI : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) S))) := HasRingHomProperty.Spec_iff.mpr hSe
  let ψ : S →+* Γ(Y₀, Y₀.basicOpen g) :=
    e.toRingEquiv.toRingHom.comp (Algebra.TensorProduct.includeRight (R := Γ(X, U)) (A := Γ(X₀, i ⁻¹ᵁ U)) (B := S))
  refine ⟨Y₀.basicOpen g, hyV₀, Spec (.of S),
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) S)) ≫ hUa.fromSpec, inferInstance,
    hV₀a.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ), ?_⟩

  have top : IsPullback (Spec.map (CommRingCat.ofHom ψ))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, Y₀.basicOpen g))))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) S)))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X₀, i ⁻¹ᵁ U)))) := by
    have H := (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X₀, i ⁻¹ᵁ U))))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) S)))).flip
    refine H.of_iso
      (pullbackSpecIso Γ(X, U) Γ(X₀, i ⁻¹ᵁ U) S ≪≫ Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op)
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · simp only [Iso.refl_hom, Category.comp_id, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
        Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc]
      rw [← Spec.map_comp, ← pullbackSpecIso_hom_snd]
      congr 2
      ext x
      symm
      change e.symm (e (Algebra.TensorProduct.includeRight x)) = Algebra.TensorProduct.includeRight x
      exact e.symm_apply_apply _
    · simp only [Iso.refl_hom, Category.comp_id, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
        Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc]
      rw [← Spec.map_comp, ← pullbackSpecIso_hom_fst]
      congr 2
      ext x
      symm
      change e.symm (algebraMap _ _ x) = Algebra.TensorProduct.includeLeftRingHom x
      rw [e.symm.commutes x]
      rfl
  have bot : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X₀, i ⁻¹ᵁ U))))
      hU₀a.fromSpec hUa.fromSpec i := by
    have e1 : CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X₀, i ⁻¹ᵁ U)) = i.appLE U (i ⁻¹ᵁ U) le_rfl := rfl
    rw [e1]
    have comm : Spec.map (i.appLE U (i ⁻¹ᵁ U) le_rfl) ≫ hUa.isoSpec.inv = hU₀a.isoSpec.inv ≫ (i ∣_ U) := by
      rw [← cancel_mono (Scheme.Opens.ι U), Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι, morphismRestrict_ι,
        ← Category.assoc, IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.SpecMap_appLE_fromSpec]
    have sq : IsPullback (Spec.map (i.appLE U (i ⁻¹ᵁ U) le_rfl)) hU₀a.isoSpec.inv hUa.isoSpec.inv (i ∣_ U) :=
      IsPullback.of_vert_isIso ⟨comm⟩
    have := sq.paste_vert (isPullback_morphismRestrict i U)
    simpa only [IsAffineOpen.isoSpec_inv_ι] using this
  have big := top.paste_vert bot
  refine big.of_iso hV₀a.isoSpec.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) ?_ (by simp) (by simp)
  have e2 : CommRingCat.ofHom (algebraMap Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, Y₀.basicOpen g)) =
      q₀.appLE (i ⁻¹ᵁ U) (Y₀.basicOpen g) hV₀le := rfl
  simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
  rw [e2, IsAffineOpen.SpecMap_appLE_fromSpec q₀ hU₀a hV₀a hV₀le, ← Category.assoc, IsAffineOpen.isoSpec_inv_ι]

end PhilipponEtaleThickeningLifts

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


namespace PhilipponEtaleThickeningModels

open PhilipponEtaleThickeningLifts

universe u v

private theorem isPullback_of_iSup_eq_top {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    {ι : Type v} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, IsPullback (fst ∣_ U i) ((fst ⁻¹ᵁ U i).ι ≫ snd) ((U i).ι ≫ f) g) :
    IsPullback fst snd f g := by
  let 𝒰 : X.OpenCover := X.openCoverOfIsOpenCover U hU
  refine Scheme.isPullback_of_openCover fst snd f g 𝒰 fun i => ?_

  refine (h i).of_iso' (pullbackRestrictIsoRestrict fst (U i)) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom]
    exact pullbackRestrictIsoRestrict_hom_morphismRestrict fst (U i)
  · simp only [Iso.refl_hom, Category.comp_id, ← Category.assoc]
    congr 1
    exact pullbackRestrictIsoRestrict_hom_ι fst (U i)
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/- Adapted from the Prove2Me Fermat's Last Theorem gluing proof over an
affine nilpotent base. Here the thickening is a surjective closed immersion
of schemes with locally Noetherian target. -/

variable {X X₀ Y₀ : Scheme.{u}} (ι₀ : X₀ ⟶ X)
  [IsClosedImmersion ι₀] [Surjective ι₀] [IsLocallyNoetherian X]
  (q₀ : Y₀ ⟶ X₀)

structure Piece (V : Y₀.Opens) where
  Y : Scheme.{u}
  q : Y ⟶ X
  etale : Etale q
  j : (V : Scheme.{u}) ⟶ Y
  isPullback : IsPullback j (V.ι ≫ q₀) q (ι₀)

def Liftable (V : Y₀.Opens) : Prop := Nonempty (Piece ι₀ q₀ V)

omit [Surjective ι₀] [IsLocallyNoetherian X] in
theorem loc_exists [Etale q₀] (y : Y₀) : ∃ V : Y₀.Opens, y ∈ V ∧ Liftable ι₀ q₀ V := by
  obtain ⟨V₀, hy, V, qV, hV, jV, hpb⟩ := exists_local_model ι₀ q₀ y
  exact ⟨V₀, hy, ⟨⟨V, qV, hV, jV, hpb⟩⟩⟩

namespace Piece

variable {ι₀ q₀} {V : Y₀.Opens} (P : Piece ι₀ q₀ V)

instance isClosedImmersion_j : IsClosedImmersion P.j :=
  MorphismProperty.of_isPullback P.isPullback.flip inferInstance

instance surjective_j : Surjective P.j :=
  MorphismProperty.of_isPullback P.isPullback.flip inferInstance

instance locallyNoetherian_model : IsLocallyNoetherian P.Y :=
  have : Etale P.q := P.etale
  LocallyOfFiniteType.isLocallyNoetherian P.q

omit [IsLocallyNoetherian X] in
theorem isHomeomorph_j : IsHomeomorph P.j.base := by
  exact isHomeomorph_iff_isEmbedding_surjective.mpr ⟨P.j.isClosedEmbedding.isEmbedding, P.j.surjective⟩

def resOpens (V' : Y₀.Opens) : P.Y.Opens :=
  ⟨P.j.base '' ((V.ι ⁻¹ᵁ V' : (V : Scheme.{u}).Opens) : Set (V : Scheme.{u})),
    (P.isHomeomorph_j).isOpenMap _ (V.ι ⁻¹ᵁ V').2⟩

theorem preimage_resOpens (V' : Y₀.Opens) : P.j ⁻¹ᵁ (P.resOpens V') = V.ι ⁻¹ᵁ V' := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← P.j.isClosedEmbedding.injective hyx]
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem range_preimage_ι {V' : Y₀.Opens} (h : V' ≤ V) :
    Set.range ((P.j ⁻¹ᵁ (P.resOpens V')).ι ≫ V.ι) = Set.range V'.ι := by
  rw [P.preimage_resOpens V', Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
    Scheme.Opens.range_ι]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro hy
    exact ⟨⟨y, h hy⟩, hy, rfl⟩

noncomputable def resIso {V' : Y₀.Opens} (h : V' ≤ V) :
    ((P.j ⁻¹ᵁ (P.resOpens V') : (V : Scheme.{u}).Opens) : Scheme.{u}) ≅ (V' : Scheme.{u}) :=
  IsOpenImmersion.isoOfRangeEq ((P.j ⁻¹ᵁ (P.resOpens V')).ι ≫ V.ι) V'.ι (P.range_preimage_ι h)

theorem resIso_hom_ι {V' : Y₀.Opens} (h : V' ≤ V) :
    (P.resIso h).hom ≫ V'.ι = (P.j ⁻¹ᵁ (P.resOpens V')).ι ≫ V.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem resIso_inv_ι {V' : Y₀.Opens} (h : V' ≤ V) :
    (P.resIso h).inv ≫ (P.j ⁻¹ᵁ (P.resOpens V')).ι ≫ V.ι = V'.ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

noncomputable def restrict {V' : Y₀.Opens} (h : V' ≤ V) : Piece ι₀ q₀ V' where
  Y := (P.resOpens V' : Scheme.{u})
  q := (P.resOpens V').ι ≫ P.q
  etale := by haveI := P.etale; infer_instance
  j := (P.resIso h).inv ≫ (P.j ∣_ P.resOpens V')
  isPullback := by
    have big := (isPullback_morphismRestrict P.j (P.resOpens V')).paste_vert P.isPullback
    refine big.of_iso (P.resIso h) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, ← Category.assoc, ← P.resIso_hom_ι h, Category.assoc]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]

@[scoped simp] theorem restrict_Y {V' : Y₀.Opens} (h : V' ≤ V) :
    (P.restrict h).Y = (P.resOpens V' : Scheme.{u}) := rfl
@[scoped simp] theorem restrict_q {V' : Y₀.Opens} (h : V' ≤ V) :
    (P.restrict h).q = (P.resOpens V').ι ≫ P.q := rfl

theorem restrict_j_ι {V' : Y₀.Opens} (h : V' ≤ V) :
    (P.restrict h).j ≫ (P.resOpens V').ι = Y₀.homOfLE h ≫ P.j := by
  show ((P.resIso h).inv ≫ (P.j ∣_ P.resOpens V')) ≫ (P.resOpens V').ι = Y₀.homOfLE h ≫ P.j
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc]
  congr 1
  rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι]
  exact P.resIso_inv_ι h

end Piece

theorem liftable_of_le {V V' : Y₀.Opens} (h : V' ≤ V) (hV : Liftable ι₀ q₀ V) :
    Liftable ι₀ q₀ V' :=
  ⟨(Classical.choice hV).restrict h⟩

abbrev Idx : Type u := {V : Y₀.Opens // Liftable ι₀ q₀ V}

scoped instance : Preorder (Idx ι₀ q₀) := Preorder.lift (fun V => V.1)

noncomputable def piece (V : Idx ι₀ q₀) : Piece ι₀ q₀ V.1 := Classical.choice V.2

theorem existsUnique_transition {V' V : Idx ι₀ q₀} (h : V' ≤ V) :
    ∃! φ : (piece ι₀ q₀ V').Y ⟶ (piece ι₀ q₀ V).Y,
      φ ≫ (piece ι₀ q₀ V).q = (piece ι₀ q₀ V').q ∧
      (piece ι₀ q₀ V').j ≫ φ = Y₀.homOfLE h ≫ (piece ι₀ q₀ V).j := by
  haveI := (piece ι₀ q₀ V).etale
  refine existsUnique_lift (piece ι₀ q₀ V).q (piece ι₀ q₀ V').j (piece ι₀ q₀ V').q
    (Y₀.homOfLE h ≫ (piece ι₀ q₀ V).j) ?_
  rw [Category.assoc, (piece ι₀ q₀ V).isPullback.w, (piece ι₀ q₀ V').isPullback.w,
    ← Scheme.homOfLE_ι Y₀ h]
  simp only [Category.assoc]

theorem transition_spec {V' V : Idx ι₀ q₀} (h : V' ≤ V) :
    (existsUnique_transition ι₀ q₀ h).choose ≫ (piece ι₀ q₀ V).q = (piece ι₀ q₀ V').q ∧
      (piece ι₀ q₀ V').j ≫ (existsUnique_transition ι₀ q₀ h).choose = Y₀.homOfLE h ≫ (piece ι₀ q₀ V).j :=
  (existsUnique_transition ι₀ q₀ h).choose_spec.1

theorem transition_unique {V' V : Idx ι₀ q₀} (h : V' ≤ V)
    (φ : (piece ι₀ q₀ V').Y ⟶ (piece ι₀ q₀ V).Y)
    (h1 : φ ≫ (piece ι₀ q₀ V).q = (piece ι₀ q₀ V').q)
    (h2 : (piece ι₀ q₀ V').j ≫ φ = Y₀.homOfLE h ≫ (piece ι₀ q₀ V).j) :
    φ = (existsUnique_transition ι₀ q₀ h).choose :=
  (existsUnique_transition ι₀ q₀ h).unique ⟨h1, h2⟩ (transition_spec ι₀ q₀ h)

noncomputable abbrev F : Idx ι₀ q₀ ⥤ Scheme.{u} where
  obj V := (piece ι₀ q₀ V).Y
  map h := (existsUnique_transition ι₀ q₀ h.le).choose
  map_id V := by
    symm
    refine transition_unique ι₀ q₀ le_rfl (𝟙 _) (Category.id_comp _) ?_
    rw [Category.comp_id]
    have : Y₀.homOfLE (le_refl V.1) = 𝟙 _ := by
      rw [← cancel_mono V.1.ι, Scheme.homOfLE_ι, Category.id_comp]
    rw [this, Category.id_comp]
  map_comp {V₁ V₂ V₃} h₁ h₂ := by
    symm
    obtain ⟨a1, a2⟩ := transition_spec ι₀ q₀ h₁.le
    obtain ⟨b1, b2⟩ := transition_spec ι₀ q₀ h₂.le
    refine transition_unique ι₀ q₀ (h₁ ≫ h₂).le _ ?_ ?_
    · rw [Category.assoc, b1, a1]
    · rw [← Category.assoc, a2, Category.assoc, b2, ← Category.assoc]
      congr 1
      rw [← cancel_mono V₃.1.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι]

namespace Piece

variable {ι₀ q₀}

theorem exists_iso {V : Y₀.Opens} (P Q : Piece ι₀ q₀ V) :
    ∃ e : P.Y ≅ Q.Y, e.hom ≫ Q.q = P.q ∧ P.j ≫ e.hom = Q.j := by
  haveI := P.etale
  haveI := Q.etale
  have wP := P.isPullback.w
  have wQ := Q.isPullback.w
  obtain ⟨α, ⟨hα1, hα2⟩, -⟩ := existsUnique_lift Q.q P.j P.q Q.j (by rw [wP, wQ])
  obtain ⟨β, ⟨hβ1, hβ2⟩, -⟩ := existsUnique_lift P.q Q.j Q.q P.j (by rw [wP, wQ])
  have hαβ : α ≫ β = 𝟙 _ :=
    (existsUnique_lift P.q P.j P.q P.j rfl).unique
      ⟨by rw [Category.assoc, hβ1, hα1], by rw [← Category.assoc, hα2, hβ2]⟩
      ⟨Category.id_comp _, Category.comp_id _⟩
  have hβα : β ≫ α = 𝟙 _ :=
    (existsUnique_lift Q.q Q.j Q.q Q.j rfl).unique
      ⟨by rw [Category.assoc, hα1, hβ1], by rw [← Category.assoc, hβ2, hα2]⟩
      ⟨Category.id_comp _, Category.comp_id _⟩
  exact ⟨⟨α, β, hαβ, hβα⟩, hα1, hα2⟩

end Piece

theorem F_map_isOpenImmersion {V' V : Idx ι₀ q₀} (h : V' ⟶ V) :
    IsOpenImmersion ((F ι₀ q₀).map h) := by
  obtain ⟨e, he1, he2⟩ :=
    Piece.exists_iso (piece ι₀ q₀ V') ((piece ι₀ q₀ V).restrict h.le)
  have key : (F ι₀ q₀).map h = e.hom ≫ ((piece ι₀ q₀ V).resOpens V'.1).ι := by
    symm
    refine transition_unique ι₀ q₀ h.le _ ?_ ?_
    · rw [Category.assoc]
      exact he1
    · rw [← Category.assoc, he2]
      exact (piece ι₀ q₀ V).restrict_j_ι h.le
  haveI h1 : IsOpenImmersion e.hom := inferInstance
  haveI h2 : IsOpenImmersion ((piece ι₀ q₀ V).resOpens V'.1).ι := inferInstance
  rw [key]
  exact MorphismProperty.comp_mem @IsOpenImmersion _ _ h1 h2

scoped instance {V' V : Idx ι₀ q₀} (h : V' ⟶ V) : IsOpenImmersion ((F ι₀ q₀).map h) :=
  F_map_isOpenImmersion ι₀ q₀ h

scoped instance : ((F ι₀ q₀) ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  intro i j k fi fj xi xj heq

  simp only [Functor.comp_obj, Scheme.forget_obj, Functor.comp_map, Scheme.forget_map] at xi xj heq ⊢
  change ((F ι₀ q₀).map fi).base xi = ((F ι₀ q₀).map fj).base xj at heq
  obtain ⟨yi, rfl⟩ := (piece ι₀ q₀ i).j.surjective xi
  obtain ⟨yj, rfl⟩ := (piece ι₀ q₀ j).j.surjective xj

  have sq : ∀ {V' V : Idx ι₀ q₀} (h : V' ⟶ V) (y : ↥(V'.1 : Scheme.{u})),
      ((F ι₀ q₀).map h).base ((piece ι₀ q₀ V').j.base y) =
        (piece ι₀ q₀ V).j.base ((Y₀.homOfLE h.le).base y) := by
    intro V' V h y
    have := (transition_spec ι₀ q₀ h.le).2
    have := congrArg (fun φ => φ.base y) this
    simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using this
  rw [sq fi yi, sq fj yj] at heq
  have hy : ((Y₀.homOfLE fi.le).base yi) = ((Y₀.homOfLE fj.le).base yj) :=
    (piece ι₀ q₀ k).j.isClosedEmbedding.injective heq
  have hy1 : yi.1 = yj.1 := by
    have hι := congrArg (fun z : (k.1 : Scheme.{u}) => k.1.ι z) hy
    simpa only [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι, Scheme.Opens.ι_apply] using hι

  let l : Idx ι₀ q₀ := ⟨i.1 ⊓ j.1, liftable_of_le ι₀ q₀ inf_le_left i.2⟩
  have hli : l ≤ i := show i.1 ⊓ j.1 ≤ i.1 from inf_le_left
  have hlj : l ≤ j := show i.1 ⊓ j.1 ≤ j.1 from inf_le_right
  let y : ↥(l.1 : Scheme.{u}) := ⟨yi.1, ⟨yi.2, hy1 ▸ yj.2⟩⟩
  refine ⟨l, homOfLE hli, homOfLE hlj, (piece ι₀ q₀ l).j.base y, ?_, ?_⟩
  · change ((F ι₀ q₀).map (homOfLE hli)).base ((piece ι₀ q₀ l).j.base y) = (piece ι₀ q₀ i).j.base yi
    rw [sq]
    congr 1
    exact Subtype.ext (Scheme.homOfLE_apply _ _)
  · change ((F ι₀ q₀).map (homOfLE hlj)).base ((piece ι₀ q₀ l).j.base y) = (piece ι₀ q₀ j).j.base yj
    rw [sq]
    congr 1
    exact Subtype.ext ((Scheme.homOfLE_apply _ _).trans hy1)

noncomputable abbrev Yg : Scheme.{u} := colimit (F ι₀ q₀)

noncomputable def qCocone : Cocone (F ι₀ q₀) where
  pt := X
  ι := { app := fun V => (piece ι₀ q₀ V).q
         naturality := fun {V' V} h => by
           simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
           exact (transition_spec ι₀ q₀ h.le).1 }

noncomputable abbrev qg : Yg ι₀ q₀ ⟶ X := colimit.desc _ (qCocone ι₀ q₀)

@[scoped simp] theorem ι_qg (V : Idx ι₀ q₀) : colimit.ι (F ι₀ q₀) V ≫ qg ι₀ q₀ = (piece ι₀ q₀ V).q :=
  colimit.ι_desc _ _

private theorem iSup_opensRange : ⨆ V : Idx ι₀ q₀, (colimit.ι (F ι₀ q₀) V).opensRange = ⊤ :=
  (Scheme.IsLocallyDirected.openCover (F ι₀ q₀)).iSup_opensRange

theorem opensRange_ι (V : Idx ι₀ q₀) :
    (colimit.ι (F ι₀ q₀) V).opensRange.ι =
      (colimit.ι (F ι₀ q₀) V).isoOpensRange.inv ≫ colimit.ι (F ι₀ q₀) V :=
  ((Iso.inv_comp_eq _).2 (Scheme.Hom.isoOpensRange_hom_ι _).symm).symm

theorem etale_qg : Etale (qg ι₀ q₀) := by
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale.{u}) _
    (iSup_opensRange ι₀ q₀) fun V => ?_
  rw [opensRange_ι, Category.assoc, ι_qg]
  have h1 : IsOpenImmersion (colimit.ι (F ι₀ q₀) V).isoOpensRange.inv := inferInstance
  have h1' : Etale (colimit.ι (F ι₀ q₀) V).isoOpensRange.inv := inferInstance
  exact MorphismProperty.comp_mem @Etale _ _ h1' (piece ι₀ q₀ V).etale

variable [Etale q₀]

noncomputable def coverY₀ : Y₀.OpenCover :=
  Scheme.Cover.mkOfCovers (Idx ι₀ q₀) (fun V => (V.1 : Scheme.{u})) (fun V => V.1.ι) fun y => by
    obtain ⟨V, hy, hV⟩ := loc_exists ι₀ q₀ y
    exact ⟨⟨V, hV⟩, ⟨y, hy⟩, rfl⟩

omit [Etale q₀] in
theorem homOfLE_j_ι {u V : Idx ι₀ q₀} (h : u ≤ V) :
    Y₀.homOfLE h ≫ (piece ι₀ q₀ V).j ≫ colimit.ι (F ι₀ q₀) V =
      (piece ι₀ q₀ u).j ≫ colimit.ι (F ι₀ q₀) u := by
  rw [← Category.assoc, ← (transition_spec ι₀ q₀ h).2, Category.assoc]
  congr 1
  exact colimit.w (F ι₀ q₀) (homOfLE h)

theorem j_compat (V W : Idx ι₀ q₀) :
    pullback.fst (V.1.ι) (W.1.ι) ≫ ((piece ι₀ q₀ V).j ≫ colimit.ι (F ι₀ q₀) V) =
      pullback.snd (V.1.ι) (W.1.ι) ≫ ((piece ι₀ q₀ W).j ≫ colimit.ι (F ι₀ q₀) W) := by
  let u : Idx ι₀ q₀ := ⟨V.1 ⊓ W.1, liftable_of_le ι₀ q₀ inf_le_left V.2⟩
  have hP := isPullback_opens_inf V.1 W.1
  rw [← cancel_epi hP.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
  have hl : u ≤ V := (inf_le_left : V.1 ⊓ W.1 ≤ V.1)
  have hr : u ≤ W := (inf_le_right : V.1 ⊓ W.1 ≤ W.1)
  exact (homOfLE_j_ι ι₀ q₀ hl).trans (homOfLE_j_ι ι₀ q₀ hr).symm

noncomputable abbrev jg : Y₀ ⟶ Yg ι₀ q₀ :=
  (coverY₀ ι₀ q₀).glueMorphisms (fun V => (piece ι₀ q₀ V).j ≫ colimit.ι (F ι₀ q₀) V)
    (j_compat ι₀ q₀)

@[scoped simp] theorem ι_jg (V : Idx ι₀ q₀) :
    V.1.ι ≫ jg ι₀ q₀ = (piece ι₀ q₀ V).j ≫ colimit.ι (F ι₀ q₀) V :=
  (coverY₀ ι₀ q₀).ι_glueMorphisms _ _ V

theorem ι_jg_qg (V : Idx ι₀ q₀) :
    V.1.ι ≫ (jg ι₀ q₀ ≫ qg ι₀ q₀) = V.1.ι ≫ (q₀ ≫ ι₀) := by
  have h1 := ι_jg ι₀ q₀ V
  have h2 := ι_qg ι₀ q₀ V
  have h3 := (piece ι₀ q₀ V).isPullback.w
  rw [← Category.assoc, h1, Category.assoc, h2, h3, Category.assoc]

theorem jg_w : jg ι₀ q₀ ≫ qg ι₀ q₀ = q₀ ≫ ι₀ :=
  Scheme.Cover.hom_ext (coverY₀ ι₀ q₀) _ _ fun V => ι_jg_qg ι₀ q₀ V

omit [Etale q₀] in
theorem F_map_j_apply {V' V : Idx ι₀ q₀} (h : V' ⟶ V) (y : (V'.1 : Scheme.{u})) :
    (F ι₀ q₀).map h ((piece ι₀ q₀ V').j y) = (piece ι₀ q₀ V).j (Y₀.homOfLE h.le y) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  exact congrArg (fun φ : (V'.1 : Scheme.{u}) ⟶ (piece ι₀ q₀ V).Y => φ y) (transition_spec ι₀ q₀ h.le).2

theorem jg_apply (V : Idx ι₀ q₀) (y : Y₀) (hy : y ∈ V.1) :
    jg ι₀ q₀ y = colimit.ι (F ι₀ q₀) V ((piece ι₀ q₀ V).j ⟨y, hy⟩) := by
  have h := congrArg (fun φ : (V.1 : Scheme.{u}) ⟶ Yg ι₀ q₀ => φ ⟨y, hy⟩) (ι_jg ι₀ q₀ V)
  exact h

theorem preimage_jg_opensRange (V : Idx ι₀ q₀) :
    jg ι₀ q₀ ⁻¹ᵁ (colimit.ι (F ι₀ q₀) V).opensRange = V.1 := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz⟩ : ∃ z, colimit.ι (F ι₀ q₀) V z = jg ι₀ q₀ y := hy
    obtain ⟨W₀, hyW, hW⟩ := loc_exists ι₀ q₀ y
    let W : Idx ι₀ q₀ := ⟨W₀, hW⟩
    rw [jg_apply ι₀ q₀ W y hyW] at hz
    obtain ⟨k, fk, fW, x, hxz, hxW⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (F ι₀ q₀)).mp hz
    obtain ⟨y', rfl⟩ := (piece ι₀ q₀ k).j.surjective x
    rw [F_map_j_apply ι₀ q₀ fW y'] at hxW
    have hyy : Y₀.homOfLE fW.le y' = ⟨y, hyW⟩ := (piece ι₀ q₀ W).j.isClosedEmbedding.injective hxW
    have : (y'.1 : Y₀) = y := by
      obtain ⟨y'', hy''⟩ := y'
      rw [Scheme.homOfLE_apply'] at hyy
      exact congrArg Subtype.val hyy
    rw [← this]
    exact fk.le y'.2
  · intro hy
    show ∃ z, colimit.ι (F ι₀ q₀) V z = jg ι₀ q₀ y
    exact ⟨_, (jg_apply ι₀ q₀ V y hy).symm⟩

theorem isPullback_jg_local (V : Idx ι₀ q₀) :
    IsPullback (jg ι₀ q₀ ∣_ (colimit.ι (F ι₀ q₀) V).opensRange)
      ((jg ι₀ q₀ ⁻¹ᵁ (colimit.ι (F ι₀ q₀) V).opensRange).ι ≫ q₀)
      ((colimit.ι (F ι₀ q₀) V).opensRange.ι ≫ qg ι₀ q₀) (ι₀) := by
  refine (piece ι₀ q₀ V).isPullback.of_iso (Y₀.isoOfEq (preimage_jg_opensRange ι₀ q₀ V).symm)
    (colimit.ι (F ι₀ q₀) V).isoOpensRange (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← cancel_mono (colimit.ι (F ι₀ q₀) V).opensRange.ι, Category.assoc, Category.assoc,
      Scheme.Hom.isoOpensRange_hom_ι, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc, ι_jg]
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, Scheme.isoOfEq_hom_ι]
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, ι_qg]
  · simp

theorem isPullback_jg : IsPullback (jg ι₀ q₀) q₀ (qg ι₀ q₀) (ι₀) := by
  exact isPullback_of_iSup_eq_top _ _ _ _ (fun V => (colimit.ι (F ι₀ q₀) V).opensRange)
    (iSup_opensRange ι₀ q₀) (isPullback_jg_local ι₀ q₀)


/-- Every étale object of a closed thickening of a locally Noetherian scheme
comes from an étale object over the original scheme. -/
theorem exists_model :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ X) (_ : Etale q) (j : Y₀ ⟶ Y),
      IsPullback j q₀ q ι₀ :=
  ⟨Yg ι₀ q₀, qg ι₀ q₀, etale_qg ι₀ q₀, jg ι₀ q₀, isPullback_jg ι₀ q₀⟩

end PhilipponEtaleThickeningModels

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite


namespace PhilipponEtaleBaseChangeComparison

universe u
variable {X Y : Scheme.{u}}

/-- Base change on the categories underlying the small étale sites. -/
abbrev baseChange (f : Y ⟶ X) : X.Etale ⥤ Y.Etale :=
  MorphismProperty.Over.pullback (@Etale) ⊤ f

private theorem map_isPullback (f : Y ⟶ X) {U V : X.Etale} (g : U ⟶ V) :
    IsPullback (pullback.fst U.hom f) ((baseChange f).map g).left g.left
      (pullback.fst V.hom f) := by
  have h₁ : g.left ≫ V.hom = U.hom := MorphismProperty.Over.w g
  have h₂ : ((baseChange f).map g).left ≫ pullback.snd V.hom f = pullback.snd U.hom f := by
    change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    rw [pullback.lift_snd]
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback V.hom f)
  · simpa only [h₁, h₂] using IsPullback.of_hasPullback U.hom f
  · symm
    change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    rw [pullback.lift_fst]

/-- Base change along a surjection preserves and reflects covering sieves.
This part does not need an equivalence of the underlying categories. -/
theorem covering_iff (f : Y ⟶ X) [Surjective f] {V : X.Etale} (S : Sieve V) :
    S.functorPushforward (baseChange f) ∈ Y.smallEtaleTopology _ ↔
      S ∈ X.smallEtaleTopology _ := by
  rw [← Sieve.ofArrows_category S, Sieve.functorPushforward_ofArrows,
    Scheme.ofArrows_mem_smallEtaleTopology_iff, Scheme.ofArrows_mem_smallEtaleTopology_iff]
  simp only [Set.eq_univ_iff_forall, Set.mem_iUnion, Set.mem_range]
  constructor
  · intro h v
    obtain ⟨w, hw⟩ := (show Function.Surjective (pullback.fst V.hom f) from
      (inferInstance : Surjective (pullback.fst V.hom f)).surj) v
    obtain ⟨g, z, hz⟩ := h w
    refine ⟨g, pullback.fst g.obj.left.hom f z, ?_⟩
    have hcomm := congrArg (fun a : (_ : Scheme) ⟶ (_ : Scheme) => a z)
      (map_isPullback f g.obj.hom).w
    exact hcomm.trans ((congrArg (pullback.fst V.hom f) hz).trans hw)
  · intro h w
    obtain ⟨g, z, hz⟩ := h (pullback.fst V.hom f w)
    obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback
      (map_isPullback f g.obj.hom) z w hz
    exact ⟨g, t, ht⟩

private def terminalObject (W : Scheme.{u}) : W.Etale := Scheme.Etale.mk (𝟙 W)

private def terminalWitness (W : Scheme.{u}) : IsTerminal (terminalObject W) :=
  IsTerminal.isTerminalOfObj (Scheme.Etale.forget W) _ Over.mkIdTerminal

variable (f : Y ⟶ X) [Surjective f] [(baseChange f).IsEquivalence]

local instance baseChange_dense :
    (baseChange f).IsDenseSubsite X.smallEtaleTopology Y.smallEtaleTopology where
  functorPushforward_mem_iff := covering_iff f _

private def sheafEquiv :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ≌ Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} := by
  let e := (baseChange f).asEquivalence.symm
  letI : e.inverse.IsDenseSubsite X.smallEtaleTopology Y.smallEtaleTopology :=
    baseChange_dense f
  exact (e.sheafCongr Y.smallEtaleTopology X.smallEtaleTopology AddCommGrpCat.{u}).symm

private def sectionsIso :
    (sheafEquiv f).inverse ⋙ (sheafSections _ _).obj (op (terminalObject X)) ≅
      (sheafSections _ _).obj (op (terminalObject Y)) := by
  let hT : IsTerminal ((baseChange f).obj (terminalObject X)) :=
    IsTerminal.isTerminalObj (baseChange f) _ (terminalWitness X)
  let e := (terminalWitness Y).uniqueUpToIso hT
  exact NatIso.ofComponents (fun F => F.obj.mapIso e.op) (fun {F G} a =>
    a.hom.naturality e.op.hom |>.symm)

private def constantIso :
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙ (sheafEquiv f).functor ≅
      constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  (Adjunction.ofNatIsoRight
    ((constantSheafAdj _ _ (terminalWitness X)).comp (sheafEquiv f).toAdjunction)
    (sectionsIso f)).leftAdjointUniq (constantSheafAdj _ _ (terminalWitness Y))

/-- A surjective base change inducing an equivalence of étale objects preserves
constant-coefficient étale cohomology in every degree. -/
def constantCohomologyEquiv (A : AddCommGrpCat.{u}) (q : ℕ) :
    ((constantSheaf X.smallEtaleTopology _).obj A).H q ≃+
      ((constantSheaf Y.smallEtaleTopology _).obj A).H q := by
  let G := (sheafEquiv f).functor
  let Q := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A
  letI : G.Additive := ⟨by intros; rfl⟩
  let e := AddEquiv.ofBijective (G.mapExtAddHom Q F q)
    (G.mapExt_bijective_of_preservesInjectiveObjects Q F q)
  let i := (constantIso f).app (AddCommGrpCat.of (ULift.{u} ℤ))
  let j := (constantIso f).app A
  let l := ((extFunctor q).mapIso i.symm.op).app (G.obj F)
  exact e.trans (l.addCommGroupIsoToAddEquiv.trans
    (((extFunctorObj _ q).mapIso j).addCommGroupIsoToAddEquiv))

end PhilipponEtaleBaseChangeComparison

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeComparison
open PhilipponEtaleThickeningLifts


namespace PhilipponEtaleThickeningCohomology

universe u

section Thickening

variable {X X₀ : Scheme.{u}} (f : X₀ ⟶ X)
  [IsClosedImmersion f] [Surjective f] [IsLocallyNoetherian X]

omit [IsClosedImmersion f] [Surjective f] [IsLocallyNoetherian X] in
private theorem map_fst {U V : X.Etale} (g : U ⟶ V) :
    ((baseChange f).map g).left ≫ pullback.fst V.hom f =
      pullback.fst U.hom f ≫ g.left :=
  pullback.lift_fst _ _ _

private theorem lift_arrow {U V : X.Etale} (g : (baseChange f).obj U ⟶ (baseChange f).obj V) :
    ∃! a : U.left ⟶ V.left, a ≫ V.hom = U.hom ∧
      pullback.fst U.hom f ≫ a = g.left ≫ pullback.fst V.hom f := by
  letI : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian (Y := X) U.hom
  apply existsUnique_lift (T := U.left) (Y := V.left) (X := X)
    V.hom (pullback.fst U.hom f) U.hom
  have hg : g.left ≫ pullback.snd V.hom f = pullback.snd U.hom f :=
    MorphismProperty.Over.w g
  rw [Category.assoc, pullback.condition, ← Category.assoc, hg, ← pullback.condition]

private theorem full : (baseChange f).Full where
  map_surjective {U V} g := by
    obtain ⟨a, ⟨ha, ha'⟩, _⟩ := lift_arrow f (U := U) (V := V) g
    let b : U ⟶ V := MorphismProperty.Over.homMk a ha trivial
    refine ⟨b, ?_⟩
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · exact (map_fst f b).trans ha'
    · exact (MorphismProperty.Over.w ((baseChange f).map b)).trans (MorphismProperty.Over.w g).symm

private theorem faithful : (baseChange f).Faithful where
  map_injective {U V} {a b} h := by
    apply MorphismProperty.Over.Hom.ext
    refine (lift_arrow f (U := U) (V := V) ((baseChange f).map a)).unique
      ⟨MorphismProperty.Over.w a, (map_fst f a).symm⟩
      ⟨MorphismProperty.Over.w b, ?_⟩
    rw [h]
    exact (map_fst f b).symm

private theorem essSurj : (baseChange f).EssSurj where
  mem_essImage V := by
    obtain ⟨U, a, hU, j, hp⟩ := PhilipponEtaleThickeningModels.exists_model f V.hom
    let U' := Scheme.Etale.mk a
    refine ⟨U', ⟨(MorphismProperty.Over.isoMk hp.isoPullback ?_).symm⟩⟩
    exact hp.isoPullback_hom_snd

/-- Pullback across a surjective closed immersion into a locally Noetherian
scheme is an equivalence on the categories of étale schemes. -/
theorem baseChange_isEquivalence : (baseChange f).IsEquivalence where
  faithful := faithful f
  full := full f
  essSurj := essSurj f

/-- The thickening preserves cohomology with all constant abelian coefficients. -/
def thickeningEquiv (A : AddCommGrpCat.{u}) (q : ℕ) :
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A).H q ≃+
      ((constantSheaf X₀.smallEtaleTopology AddCommGrpCat.{u}).obj A).H q :=
  have := baseChange_isEquivalence f
  constantCohomologyEquiv f A q

end Thickening

section Reduction

variable (X : Scheme.{u})

/-- The closed subscheme cut out by the nilradical. -/
abbrev reducedScheme := X.nilradical.subscheme

/-- The closed immersion of the reduction. -/
abbrev reductionι : reducedScheme X ⟶ X := X.nilradical.subschemeι

instance reduced_reducedScheme : IsReduced (reducedScheme X) := by
  apply PhilipponReducedClosedSubscheme.isReduced_of_radical_eq
  ext U : 2
  exact Ideal.radical_idem _

instance surjective_reductionι : Surjective (reductionι X) := by
  constructor
  rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι,
    Scheme.support_nilradical]
  rfl

/-- The reduction of a locally Noetherian scheme has the same constant
étale cohomology as the original scheme in every degree. -/
def reductionEquiv [IsLocallyNoetherian X] (A : AddCommGrpCat.{u}) (q : ℕ) :
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A).H q ≃+
      ((constantSheaf (reducedScheme X).smallEtaleTopology AddCommGrpCat.{u}).obj A).H q :=
  thickeningEquiv (reductionι X) A q

end Reduction

/-- Finiteness with fixed constant coefficients in a fixed degree for proper
reduced schemes over a locally Noetherian base implies finiteness for all
proper schemes over that base. -/
theorem finite_constant_of_reduced {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (π : X ⟶ S) [IsProper π] (A : AddCommGrpCat.{u}) (q : ℕ)
    (h : ∀ {Y : Scheme.{u}} [IsReduced Y] (σ : Y ⟶ S) [IsProper σ],
      Finite (((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A).H q)) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A).H q) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  exact (reductionEquiv X A q).toEquiv.finite_iff.mpr
    (h (reductionι X ≫ π))

end PhilipponEtaleThickeningCohomology

end

open AlgebraicGeometry CategoryTheory

universe u

theorem solution
    (K : Type u) [Field K] [IsSepClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] (p : ℕ) (hp : p.Prime)
    (hK : (p : K) ≠ 0) (q : ℕ) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat).obj
      (AddCommGrpCat.of (ULift.{u} (ZMod p)))).H q) := by
  exact PhilipponEtaleThickeningCohomology.finite_constant_of_reduced π
    (AddCommGrpCat.of (ULift.{u} (ZMod p))) q
    (fun σ => Scheme.finite_prime_constant_etale_cohomology_prime_to_characteristic_of_isReduced
      K σ p hp hK q)
