-- Prove2me | solution 1 for AlgebraicGeometry.bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/a403c2ea-c268-5da8-8042-b52a8a644660

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace SolFieldCaseH0

section Algebra

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

theorem subsingleton_maximalSpectrum_of_idem {S : Type*} [CommRing S] [IsArtinianRing S] [IsReduced S]
    (h : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) : Subsingleton (MaximalSpectrum S) := by
  classical
  by_contra hne
  rw [not_subsingleton_iff_nontrivial] at hne
  obtain ⟨m₁, m₂, hm⟩ := hne
  let φ := IsArtinianRing.equivPi S
  let e : S := φ.symm (Pi.single m₁ 1)
  have he : IsIdempotentElem e := by
    change e * e = e
    simp only [e, ← map_mul]
    congr 1
    ext i
    by_cases hi : i = m₁
    · subst hi; simp
    · simp [hi]
  rcases h e he with h0 | h1
  · have : (Pi.single m₁ (1 : S ⧸ m₁.asIdeal) : ∀ I : MaximalSpectrum S, S ⧸ I.asIdeal) = 0 := by
      apply φ.symm.injective; rw [map_zero]; exact h0
    have := congr_fun this m₁
    simp at this
  · have : (Pi.single m₁ (1 : S ⧸ m₁.asIdeal) : ∀ I : MaximalSpectrum S, S ⧸ I.asIdeal) = 1 := by
      apply φ.symm.injective; simpa [e] using h1
    have := congr_fun this m₂
    simp [hm.symm] at this

theorem isField_of_isReduced_of_isIntegral_of_idem [Nontrivial A] [IsReduced A]
    [Algebra.IsIntegral K A] (h : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) : IsField A := by
  classical
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha ↦ ?_⟩

  let S : Subalgebra K A := Algebra.adjoin K {a}
  have : Module.Finite K S :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral (R := K) a)
  have : IsArtinianRing S := IsArtinianRing.of_finite K S
  have : IsReduced S := isReduced_of_injective S.val Subtype.val_injective
  have hS : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    rcases h (e : A) (by simpa [IsIdempotentElem] using congr_arg Subtype.val he) with h0 | h1
    · left; exact_mod_cast h0
    · right; exact_mod_cast h1
  have : Subsingleton (MaximalSpectrum S) := subsingleton_maximalSpectrum_of_idem hS
  have : Nontrivial S := inferInstance
  have : IsLocalRing S := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal S
    refine IsLocalRing.of_unique_max_ideal ⟨m, hm, fun m' hm' ↦ ?_⟩
    have := Subsingleton.elim (⟨m', hm'⟩ : MaximalSpectrum S) ⟨m, hm⟩
    exact congr_arg MaximalSpectrum.asIdeal this
  have hSf : IsField S := IsArtinianRing.isField_of_isReduced_of_isLocalRing S
  have haS : (⟨a, Algebra.self_mem_adjoin_singleton K a⟩ : S) ≠ 0 := by
    intro h0; exact ha (congr_arg Subtype.val h0)
  obtain ⟨b, hb⟩ := hSf.mul_inv_cancel haS
  exact ⟨(b : A), by simpa using congr_arg Subtype.val hb⟩

end Algebra

section Idem

theorem idem_trivial_of_connectedSpace {Y : Scheme.{u}} [IsReduced Y] [ConnectedSpace Y]
    (e : Γ(Y, ⊤)) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have he' : IsIdempotentElem (1 - e) := he.one_sub

  have hdisj : Y.basicOpen e ⊓ Y.basicOpen (1 - e) = ⊥ := by
    rw [← Scheme.basicOpen_mul, he.mul_one_sub_self, Scheme.basicOpen_zero]
  have hcov : Y.basicOpen e ⊔ Y.basicOpen (1 - e) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    have h1 : IsUnit (Y.presheaf.germ ⊤ x trivial (e + (1 - e))) := by
      rw [add_sub_cancel, map_one]; exact isUnit_one
    rw [map_add] at h1
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h | h
    · exact Or.inl ((Scheme.mem_basicOpen_top _ _ _).mpr h)
    · exact Or.inr ((Scheme.mem_basicOpen_top _ _ _).mpr h)

  have hclopen : IsClopen (Y.basicOpen e : Set Y) := by
    refine ⟨⟨?_⟩, (Y.basicOpen e).isOpen⟩
    have : (Y.basicOpen e : Set Y)ᶜ = (Y.basicOpen (1 - e) : Set Y) := by
      apply Set.eq_of_subset_of_subset
      · intro x hx
        have : x ∈ (Y.basicOpen e ⊔ Y.basicOpen (1 - e) : Y.Opens) := by rw [hcov]; trivial
        rcases this with h | h
        · exact absurd h hx
        · exact h
      · intro x hx hx'
        have : x ∈ (Y.basicOpen e ⊓ Y.basicOpen (1 - e) : Y.Opens) := ⟨hx', hx⟩
        rw [hdisj] at this
        exact this
    rw [this]
    exact (Y.basicOpen (1 - e)).isOpen
  rcases isClopen_iff.mp hclopen with h | h
  · left
    have : Y.basicOpen e = ⊥ := by ext1; exact h
    exact (basicOpen_eq_bot_iff e).mp this
  · right
    have hbot : Y.basicOpen (1 - e) = ⊥ := by
      have : (Y.basicOpen (1 - e) : Set Y) = ∅ := by
        rw [← Set.compl_univ, ← h]
        apply Set.eq_of_subset_of_subset
        · intro x hx hx'
          have : x ∈ (Y.basicOpen e ⊓ Y.basicOpen (1 - e) : Y.Opens) := ⟨hx', hx⟩
          rw [hdisj] at this
          exact this
        · intro x hx
          have : x ∈ (Y.basicOpen e ⊔ Y.basicOpen (1 - e) : Y.Opens) := by rw [hcov]; trivial
          rcases this with h | h
          · exact absurd h hx
          · exact h
      ext1; exact this
    have := (basicOpen_eq_bot_iff (1 - e)).mp hbot
    exact (sub_eq_zero.mp this).symm

end Idem

theorem nontrivial_sections_top (Y : Scheme.{u}) [Nonempty Y] : Nontrivial Γ(Y, ⊤) := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  exact (Y.presheaf.germ ⊤ y trivial).hom.domain_nontrivial

section Main

open TensorProduct

variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [UniversallyClosed f] [GeometricallyReduced f] [GeometricallyConnected f]

set_option maxHeartbeats 3200000 in
theorem main : Function.Bijective f.appTop := by
  classical

  have : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton f
  have : Nonempty X := inferInstance
  have : Nontrivial Γ(X, ⊤) := nontrivial_sections_top X
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance

  set L : Type u := Γ(X, ⊤) with hL
  let algK : K →+* L := f.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  letI : Algebra K L := algK.toAlgebra
  have halg : algebraMap K L = algK := rfl

  have hint : (algebraMap K L).IsIntegral := by
    rw [halg]
    exact RingHom.IsIntegral.trans _ _
      ((Scheme.ΓSpecIso (.of K)).inv.hom.isIntegral_of_surjective
        (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.surjective)
      (isIntegral_appTop_of_universallyClosed f)

  let Kb : Type u := AlgebraicClosure K
  let j : Spec (.of Kb) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K Kb))
  let Y : Scheme.{u} := pullback f j
  have H : IsPullback (pullback.snd f j) (pullback.fst f j) j f := (IsPullback.of_hasPullback f j).flip
  have : IsReduced Y :=
    GeometricallyReduced.geometrically_isReduced (f := f) j _ _ (.of_hasPullback f j)
  have : ConnectedSpace Y :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) j _ _ (.of_hasPullback f j)
  have : Nonempty Y := inferInstance
  have : Nontrivial Γ(Y, ⊤) := nontrivial_sections_top Y

  have hUY : (⊤ : Y.Opens) = pullback.snd f j ⁻¹ᵁ ⊤ ⊓ pullback.fst f j ⁻¹ᵁ ⊤ := by simp
  have hmono := mono_pushoutSection_of_isCompact_of_flat_left H (US := ⊤) (UT := ⊤) (UX := ⊤)
    le_top le_top hUY (isAffineOpen_top _) (isAffineOpen_top _) (by simpa using isCompact_univ)
  set b' := j.appLE (⊤ : (Spec (.of K)).Opens) ⊤ le_top with hb'
  set a' := f.appLE (⊤ : (Spec (.of K)).Opens) ⊤ le_top with ha'
  have ha'' : a' = f.appTop := f.appLE_eq_app
  have hb'' : b' = j.appTop := j.appLE_eq_app

  have hT := CommRingCat.isPushout_tensorProduct K Kb L
  have h₁ : IsPushout b' a'
      ((Scheme.ΓSpecIso (.of Kb)).hom ≫ CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := K) (A := Kb) (B := L)).toRingHom) := by
    refine hT.of_iso (Scheme.ΓSpecIso (.of K)).symm (Scheme.ΓSpecIso (.of Kb)).symm (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ ?_
    ·
      rw [hb'']
      simp [j]
    · rw [ha'', halg]
      simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, algK]
      change CommRingCat.ofHom ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom = _
      rw [CommRingCat.ofHom_hom]
    · simp
    · simp
  let e := h₁.isoPushout
  let ψ : Kb ⊗[K] L →+* Γ(Y, ⊤) := (e.hom ≫ pushoutSection H le_top le_top hUY).hom
  have hψ : Function.Injective ψ := by
    have : Mono (e.hom ≫ pushoutSection H le_top le_top hUY) := mono_comp _ _
    exact ConcreteCategory.injective_of_mono_of_preservesPullback _

  have : Nontrivial (Kb ⊗[K] L) := ψ.domain_nontrivial
  have : IsReduced (Kb ⊗[K] L) := isReduced_of_injective ψ hψ
  have hidem : ∀ x : Kb ⊗[K] L, IsIdempotentElem x → x = 0 ∨ x = 1 := by
    intro x hx
    rcases idem_trivial_of_connectedSpace (ψ x) (hx.map ψ) with h0 | h1
    · left; apply hψ; simpa using h0
    · right; apply hψ; simpa using h1
  have : Algebra.IsIntegral Kb (Kb ⊗[K] L) :=
    algebraMap_isIntegral_iff.mp (RingHom.isIntegral_isStableUnderBaseChange.tensorProduct Kb hint)
  have hF : IsField (Kb ⊗[K] L) := isField_of_isReduced_of_isIntegral_of_idem (K := Kb) hidem
  have : IsDomain (Kb ⊗[K] L) := hF.isDomain
  have hbij : Function.Bijective (algebraMap Kb (Kb ⊗[K] L)) :=
    IsAlgClosed.ringHom_bijective_of_isIntegral _ (algebraMap_isIntegral_iff.mpr inferInstance)

  have hrank : Module.rank K L ≤ 1 := by
    let bL := Module.Free.chooseBasis K L
    let bT := Algebra.TensorProduct.basis Kb bL
    have h1 : Module.rank Kb (Kb ⊗[K] L) ≤ 1 := by
      rw [rank_le_one_iff]
      refine ⟨1, fun v ↦ ?_⟩
      obtain ⟨c, hc⟩ := hbij.2 v
      exact ⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩
    have e1 := bL.mk_eq_rank''
    have e2 := bT.mk_eq_rank''
    rw [← e1]; rw [← e2] at h1; exact h1
  have hsurj : Function.Surjective (algebraMap K L) := by
    obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.mp hrank
    obtain ⟨r₀, hr₀⟩ := hv₀ 1
    have hr₀0 : r₀ ≠ 0 := by rintro rfl; simp at hr₀
    intro l
    obtain ⟨r, hr⟩ := hv₀ l
    refine ⟨r * r₀⁻¹, ?_⟩
    have : v₀ = r₀⁻¹ • (1 : L) := by
      rw [← hr₀, smul_smul, inv_mul_cancel₀ hr₀0, one_smul]
    rw [← hr, this, smul_smul, Algebra.algebraMap_eq_smul_one]

  have hinjK : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  rw [halg] at hsurj hinjK
  have he : Function.Bijective (Scheme.ΓSpecIso (.of K)).hom :=
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.bijective
  have hcomp : (f.appTop : Γ(Spec (.of K), ⊤) → L) = algK ∘ (Scheme.ΓSpecIso (.of K)).hom := by
    ext x
    simp [algK]
  rw [hcomp]
  exact ⟨hinjK.comp he.1, hsurj.comp he.2⟩

end Main

end SolFieldCaseH0

theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [UniversallyClosed f] [GeometricallyReduced f] [GeometricallyConnected f] :
    Function.Bijective f.appTop :=
  SolFieldCaseH0.main f

end S_AlgebraicGeometry_bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected
end P2MW
export P2MW.S_AlgebraicGeometry_bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected (solution)
