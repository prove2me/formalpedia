-- Prove2me | solution 1 for AlgebraicGeometry.not_subsingleton_minimalPrimes_span_germ_iff_exists_two_minimalPrimes_le_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/77f369ba-2fac-56be-9c28-fa5e0d955dc5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_not_subsingleton_minimalPrimes_span_germ_iff_exists_two_minimalPrimes_le_of_chart

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (ι : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R S))) (ϖ : R) (q : ↥(Spec (CommRingCat.of S))) :
    ¬ ((Ideal.span {(X.presheaf.germ ⊤ (ι.base q) trivial).hom
        (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))} : Ideal (X.presheaf.stalk (ι.base q))).minimalPrimes).Subsingleton ↔
    ∃ 𝔭 ∈ (Ideal.span {algebraMap R S ϖ}).minimalPrimes, ∃ 𝔭' ∈ (Ideal.span {algebraMap R S ϖ}).minimalPrimes,
      𝔭 ≠ 𝔭' ∧ 𝔭 ≤ q.asIdeal ∧ 𝔭' ≤ q.asIdeal := by
  classical

  let e₁ := (asIso (ι.stalkMap q)).commRingCatIsoToRingEquiv
  let e₂ := (Spec.stalkIso (CommRingCat.of S) q).commRingCatIsoToRingEquiv
  let e := e₁.trans e₂
  have key₁ : (ι.stalkMap q).hom ((X.presheaf.germ ⊤ (ι.base q) trivial).hom
      (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))) =
      ((Spec (CommRingCat.of S)).presheaf.germ ⊤ q trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (algebraMap R S ϖ)) := by
    erw [Scheme.Hom.germ_stalkMap_apply ι ⊤ q trivial]
    congr 1
    show ((f.appTop ≫ ι.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)) = _
    rw [← Scheme.Hom.comp_appTop, hι]
    show ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap R S))).appTop).hom ϖ = _
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  have key₂ : (Spec.stalkIso (CommRingCat.of S) q).hom.hom (((Spec (CommRingCat.of S)).presheaf.germ ⊤ q trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (algebraMap R S ϖ))) =
      algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S ϖ) := by
    have h0 : CommRingCat.ofHom (algebraMap S (Localization.AtPrime q.asIdeal)) ≫ (Spec.stalkIso (CommRingCat.of S) q).inv =
        (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (Spec (CommRingCat.of S)).presheaf.germ ⊤ q trivial :=
      Spec.algebraMap_stalkIso_inv q
    have h := congrArg (fun φ : CommRingCat.of S ⟶ (Spec (CommRingCat.of S)).presheaf.stalk q =>
      (CommRingCat.Hom.hom φ) (algebraMap R S ϖ)) h0
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h

    rw [← h, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  have hkey : e ((X.presheaf.germ ⊤ (ι.base q) trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))) =
      algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S ϖ) := by
    show e₂ (e₁ _) = _
    show (Spec.stalkIso (CommRingCat.of S) q).hom.hom ((ι.stalkMap q).hom _) = _
    rw [key₁, key₂]

  set t := (X.presheaf.germ ⊤ (ι.base q) trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)) with ht
  have htrans : (Ideal.span {e t}).minimalPrimes = Ideal.comap e.symm.toRingHom '' (Ideal.span {t}).minimalPrimes := by
    rw [← Ideal.comap_minimalPrimes_eq_of_surjective e.symm.surjective]
    congr 1
    rw [show Ideal.comap e.symm.toRingHom (Ideal.span {t}) = (Ideal.span {t}).comap e.symm from rfl, Ideal.comap_symm,
      Ideal.map_span, Set.image_singleton]

  have hmap : Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S ϖ)} =
      (Ideal.span {algebraMap R S ϖ}).map (algebraMap S (Localization.AtPrime q.asIdeal)) := by
    rw [Ideal.map_span, Set.image_singleton]
  constructor
  · intro hz
    have hns : ¬ ((Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S ϖ)}).minimalPrimes).Subsingleton := by
      intro hsub
      rw [← hkey, htrans] at hsub
      apply hz
      intro a ha b hb
      exact Ideal.comap_injective_of_surjective _ e.symm.surjective (hsub ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)
    obtain ⟨P, hP, P', hP', hne⟩ : ∃ P ∈ (Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S ϖ)}).minimalPrimes,
        ∃ P' ∈ (Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S ϖ)}).minimalPrimes, P ≠ P' := by
      by_contra h; push Not at h; exact hns fun a ha b hb => h a ha b hb

    have hunder : ∀ Q ∈ (Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S ϖ)}).minimalPrimes,
        Q.under S ∈ (Ideal.span {algebraMap R S ϖ}).minimalPrimes := by
      intro Q hQ
      rw [hmap, IsLocalization.minimalPrimes_map q.asIdeal.primeCompl] at hQ
      exact hQ
    haveI := hP.1.1
    haveI := hP'.1.1
    refine ⟨P.under S, hunder P hP, P'.under S, hunder P' hP', fun heq => hne ?_, ?_, ?_⟩
    · rw [← IsLocalization.map_under q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal) P,
        ← IsLocalization.map_under q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal) P', heq]
    · calc P.under S ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).under S :=
            Ideal.comap_mono (IsLocalRing.le_maximalIdeal hP.1.1.ne_top)
        _ = q.asIdeal := IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q.asIdeal) q.asIdeal
    · calc P'.under S ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).under S :=
            Ideal.comap_mono (IsLocalRing.le_maximalIdeal hP'.1.1.ne_top)
        _ = q.asIdeal := IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q.asIdeal) q.asIdeal

  ·
    rintro ⟨𝔭, h𝔭, 𝔭', h𝔭', hne, hle, hle'⟩ hsub
    haveI := h𝔭.1.1
    haveI := h𝔭'.1.1
    have hdisj : ∀ {I : Ideal S}, I ≤ q.asIdeal → Disjoint (q.asIdeal.primeCompl : Set S) I := fun hI =>
      Set.disjoint_left.mpr fun x hx hxI => hx (hI hxI)
    let P := 𝔭.map (algebraMap S (Localization.AtPrime q.asIdeal))
    let P' := 𝔭'.map (algebraMap S (Localization.AtPrime q.asIdeal))
    have hPu : P.under S = 𝔭 := IsLocalization.under_map_of_isPrime_disjoint q.asIdeal.primeCompl _ h𝔭.1.1 (hdisj hle)
    have hP'u : P'.under S = 𝔭' := IsLocalization.under_map_of_isPrime_disjoint q.asIdeal.primeCompl _ h𝔭'.1.1 (hdisj hle')
    have hP : P ∈ (Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S ϖ)}).minimalPrimes := by
      rw [hmap, IsLocalization.minimalPrimes_map q.asIdeal.primeCompl]
      change Ideal.under S P ∈ (Ideal.span {algebraMap R S ϖ}).minimalPrimes
      rw [hPu]; exact h𝔭
    have hP' : P' ∈ (Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S ϖ)}).minimalPrimes := by
      rw [hmap, IsLocalization.minimalPrimes_map q.asIdeal.primeCompl]
      change Ideal.under S P' ∈ (Ideal.span {algebraMap R S ϖ}).minimalPrimes
      rw [hP'u]; exact h𝔭'
    have hPne : P ≠ P' := fun h => hne (by rw [← hPu, ← hP'u, h])

    rw [← hkey, htrans] at hP hP'
    obtain ⟨a, ha, haP⟩ := hP
    obtain ⟨b, hb, hbP⟩ := hP'
    exact hPne (by rw [← haP, ← hbP, hsub ha hb])

#print axioms solution

end S_AlgebraicGeometry_not_subsingleton_minimalPrimes_span_germ_iff_exists_two_minimalPrimes_le_of_chart
end P2MW
export P2MW.S_AlgebraicGeometry_not_subsingleton_minimalPrimes_span_germ_iff_exists_two_minimalPrimes_le_of_chart (solution)
