-- Prove2me | solution 1 for AlgebraicGeometry.Etale.existsUnique_comp_eq_of_isNilpotent_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/a53174ec-5236-5a60-91ae-f60b3a4151cb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Etale_existsUnique_comp_eq_of_isNilpotent_ker

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace S2SECT

theorem eq_of_comp_eq_of_surjective {X Y T T₀ : Scheme.{0}} (q : Y ⟶ X)
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

theorem surjective_of_isNilpotent_ker {T T₀ : Scheme.{0}} (k : T₀ ⟶ T) [IsClosedImmersion k]
    (hk : IsNilpotent k.ker) : Surjective k := by
  have : IsDominant k := by
    obtain ⟨n, hn⟩ := hk
    rw [isDominant_iff, denseRange_iff_closure_range, ← k.support_ker,
      ← k.ker.support_pow (n + 1) (by simp), pow_succ, hn]
    simp
  exact ⟨by rw [← Set.range_eq_univ, ← k.isClosedEmbedding.isClosed_range.closure_eq, k.denseRange.closure_range]⟩

theorem exists_of_forall_exists_nhd {X Y T T₀ : Scheme.{0}} (q : Y ⟶ X)
    [FormallyUnramified q] [LocallyOfFiniteType q]
    (k : T₀ ⟶ T) [Surjective k] (t : T ⟶ X) (s₀ : T₀ ⟶ Y) (hs₀ : s₀ ≫ q = k ≫ t)
    (H : ∀ p : T, ∃ (U : T.Opens) (_ : p ∈ U) (sU : (U : Scheme.{0}) ⟶ Y),
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

    have key : ∀ (l : T) (m : pullback (𝒰.f i) (𝒰.f j) ⟶ (U l : Scheme.{0})) (hm : m ≫ (U l).ι = g),
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

theorem appLE_congr_hom {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

theorem exists_nhd_lift {X Y T T₀ : Scheme.{0}} (q : Y ⟶ X) [Etale q]
    (k : T₀ ⟶ T) [IsClosedImmersion k] (hk : IsNilpotent k.ker)
    (t : T ⟶ X) (s₀ : T₀ ⟶ Y) (hs₀ : s₀ ≫ q = k ≫ t) (p : T) :
    ∃ (U : T.Opens) (_ : p ∈ U) (sU : (U : Scheme.{0}) ⟶ Y),
      sU ≫ q = U.ι ≫ t ∧ (k ∣_ U) ≫ sU = (k ⁻¹ᵁ U).ι ≫ s₀ := by
  haveI : Surjective k := surjective_of_isNilpotent_ker k hk
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
    obtain ⟨n, hn⟩ := hk
    exact ⟨n, by simpa using congr(($hn).ideal ⟨U, hU⟩)⟩
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

theorem existsUnique_comp_eq_of_isNilpotent_ker {X Y T T₀ : Scheme.{0}} (q : Y ⟶ X) [Etale q]
    (k : T₀ ⟶ T) [IsClosedImmersion k] (hk : IsNilpotent k.ker)
    (t : T ⟶ X) (s₀ : T₀ ⟶ Y) (hs₀ : s₀ ≫ q = k ≫ t) :
    ∃! s : T ⟶ Y, s ≫ q = t ∧ k ≫ s = s₀ := by
  haveI : Surjective k := surjective_of_isNilpotent_ker k hk
  obtain ⟨s, hs, hks⟩ := exists_of_forall_exists_nhd q k t s₀ hs₀ (exists_nhd_lift q k hk t s₀ hs₀)
  refine ⟨s, ⟨hs, hks⟩, fun s' hs' => ?_⟩
  exact eq_of_comp_eq_of_surjective q k (hs'.1.trans hs.symm) (hs'.2.trans hks.symm)

end S2SECT

theorem solution
    {X Y T T₀ : Scheme.{0}} (q : Y ⟶ X) [Etale q]
    (k : T₀ ⟶ T) [IsClosedImmersion k] (hk : IsNilpotent k.ker)
    (t : T ⟶ X) (s₀ : T₀ ⟶ Y) (hs₀ : s₀ ≫ q = k ≫ t) :
    ∃! s : T ⟶ Y, s ≫ q = t ∧ k ≫ s = s₀ :=
  S2SECT.existsUnique_comp_eq_of_isNilpotent_ker q k hk t s₀ hs₀

end S_AlgebraicGeometry_Etale_existsUnique_comp_eq_of_isNilpotent_ker
end P2MW
export P2MW.S_AlgebraicGeometry_Etale_existsUnique_comp_eq_of_isNilpotent_ker (solution)
