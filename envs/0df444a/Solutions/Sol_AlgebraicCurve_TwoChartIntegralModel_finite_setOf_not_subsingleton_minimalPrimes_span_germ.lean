-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.finite_setOf_not_subsingleton_minimalPrimes_span_germ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/27baeddf-fd90-5444-83ed-6589f5b7448c

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ringKrullDim_le_of_ringHom_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_finite_setOf_not_subsingleton_minimalPrimes_span_germ

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace CrossFinite

theorem finite_setOf_two_minimalPrimes_le
    {S : Type u} [CommRing S] [IsDomain S] [IsNoetherianRing S] (hdim : ringKrullDim S ≤ 2) (ϖ : S) (hϖ : ϖ ≠ 0) :
    {q : Ideal S | q.IsPrime ∧ ∃ 𝔭 ∈ (Ideal.span {ϖ}).minimalPrimes, ∃ 𝔭' ∈ (Ideal.span {ϖ}).minimalPrimes,
      𝔭 ≠ 𝔭' ∧ 𝔭 ≤ q ∧ 𝔭' ≤ q}.Finite := by
  have hfin := (Ideal.span {ϖ}).finite_minimalPrimes_of_isNoetherianRing
  refine ((hfin.biUnion fun 𝔭 _ => hfin.biUnion fun 𝔭' _ => (𝔭 ⊔ 𝔭').finite_minimalPrimes_of_isNoetherianRing)).subset ?_
  rintro q ⟨hq, 𝔭, h𝔭, 𝔭', h𝔭', hne, hle, hle'⟩
  simp only [Set.mem_iUnion]
  refine ⟨𝔭, h𝔭, 𝔭', h𝔭', ?_⟩
  haveI := hq
  haveI := h𝔭.1.1
  haveI := h𝔭'.1.1

  have h𝔭bot : (⊥ : Ideal S) < 𝔭 := by
    rw [bot_lt_iff_ne_bot]
    intro h
    exact hϖ (by simpa [h] using h𝔭.1.2 (Ideal.mem_span_singleton_self ϖ))
  have h1 : (1 : ℕ∞) ≤ 𝔭.height := by
    have := Ideal.height_strict_mono_of_isPrime_of_isPrime h𝔭bot
    rw [Ideal.height_bot] at this
    exact Order.one_le_iff_pos.mpr this
  have hlt : ∀ Q : Ideal S, Q.IsPrime → 𝔭 ⊔ 𝔭' ≤ Q → 𝔭 < Q := by
    intro Q hQ hQle
    refine lt_of_le_of_ne (le_sup_left.trans hQle) fun h => hne ?_

    have h' : 𝔭' ≤ 𝔭 := h ▸ (le_sup_right.trans hQle)
    exact le_antisymm (h𝔭.2 h𝔭'.1 h') h'
  refine ⟨⟨hq, sup_le hle hle'⟩, fun Q ⟨hQ, hQle⟩ hQq => ?_⟩

  by_contra hqQ
  have hQq' : Q < q := lt_of_le_of_ne hQq fun h => hqQ (h ▸ le_rfl)
  haveI := hQ
  have h2 : (2 : ℕ∞) ≤ Q.height := by
    have := Ideal.height_strict_mono_of_isPrime_of_isPrime (hlt Q hQ hQle)
    have h1' : (1 : ℕ∞) < Q.height := lt_of_le_of_lt h1 this
    exact Order.add_one_le_of_lt h1'
  have h3 : (3 : ℕ∞) ≤ q.height := by
    have := Ideal.height_strict_mono_of_isPrime_of_isPrime hQq'
    exact Order.add_one_le_of_lt (lt_of_le_of_lt h2 this)
  have h4 := Ideal.height_le_ringKrullDim_of_isPrime (I := q)
  have : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) := (WithBot.coe_le_coe.mpr h3).trans (h4.trans hdim)
  have h32 : (3 : ℕ∞) ≤ 2 := WithBot.coe_le_coe.mp this
  exact absurd (by exact_mod_cast h32 : (3 : ℕ) ≤ 2) (by omega)

theorem exists_two_minimalPrimes_le_of_chart
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (ι : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R S))) (ϖ : R) (q : ↥(Spec (CommRingCat.of S)))
    (hz : ¬ ((Ideal.span {(X.presheaf.germ ⊤ (ι.base q) trivial).hom
        (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))} : Ideal (X.presheaf.stalk (ι.base q))).minimalPrimes).Subsingleton) :
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
  have hns : ¬ ((Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S ϖ)}).minimalPrimes).Subsingleton := by
    intro hsub
    rw [← hkey, htrans] at hsub
    apply hz
    intro a ha b hb
    exact Ideal.comap_injective_of_surjective _ e.symm.surjective (hsub ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)
  obtain ⟨P, hP, P', hP', hne⟩ : ∃ P ∈ (Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S ϖ)}).minimalPrimes,
      ∃ P' ∈ (Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S ϖ)}).minimalPrimes, P ≠ P' := by
    by_contra h; push Not at h; exact hns fun a ha b hb => h a ha b hb

  have hmap : Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S ϖ)} =
      (Ideal.span {algebraMap R S ϖ}).map (algebraMap S (Localization.AtPrime q.asIdeal)) := by
    rw [Ideal.map_span, Set.image_singleton]
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

theorem ringKrullDim_chartAlg_singleton_le
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (s : F) :
    ringKrullDim ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}) ≤ ringKrullDim (Polynomial R) := by
  let ψ : Polynomial R →ₐ[R] ↥(Algebra.adjoin R ({s} : Set F)) :=
    (Polynomial.aeval s).codRestrict (Algebra.adjoin R ({s} : Set F))
      (fun P => by
        rw [Algebra.adjoin_singleton_eq_range_aeval]
        exact ⟨P, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨P, rfl⟩ := hy
    exact ⟨P, Subtype.ext rfl⟩
  let ι : ↥(Algebra.adjoin R ({s} : Set F)) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}) :=
    (Subalgebra.inclusion (AlgebraicCurve.TwoChartIntegralModel.adjoin_le_chartAlg R F {s})).toRingHom
  have hι : ι.IsIntegral := by
    intro x
    obtain ⟨P, hPm, hP⟩ := (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff R F).mp x.2
    refine ⟨P, hPm, ?_⟩
    apply Subtype.ext
    have h1 := Polynomial.hom_eval₂ P ι ((AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}).val.toRingHom) x
    have h2 : ((AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}).val.toRingHom).comp ι = algebraMap ↥(Algebra.adjoin R ({s} : Set F)) F := rfl
    rw [h2] at h1
    exact h1.trans hP
  calc ringKrullDim ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s})
      ≤ ringKrullDim ↥(Algebra.adjoin R ({s} : Set F)) := ringKrullDim_le_of_ringHom_isIntegral ι hι
    _ ≤ ringKrullDim (Polynomial R) :=
        ringKrullDim_le_of_ringHom_isIntegral ψ.toRingHom (RingHom.isIntegral_of_surjective _ hψ)

end CrossFinite

open CrossFinite in
theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}) :
    {z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j) |
      ¬ ((Ideal.span {(((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase R F j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)))} :
        Ideal ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z)).minimalPrimes).Subsingleton}.Finite := by
  classical

  obtain ⟨hftF, hftI⟩ := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf R K₀ F j htj hFD hsep
  haveI := hftF; haveI := hftI
  haveI : IsNoetherianRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j) := Algebra.FiniteType.isNoetherianRing R _
  haveI : IsNoetherianRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j) := Algebra.FiniteType.isNoetherianRing R _
  have hpoly : ringKrullDim (Polynomial R) ≤ 2 := by
    rw [Polynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one R]; rfl
  have hdimF : ringKrullDim ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j) ≤ 2 := (ringKrullDim_chartAlg_singleton_le R F j).trans hpoly
  have hdimI : ringKrullDim ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j) ≤ 2 := (ringKrullDim_chartAlg_singleton_le R F j⁻¹).trans hpoly
  have hinjF : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]
    exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)
  have hϖ0 : ϖ ≠ 0 := fun h => IsDiscreteValuationRing.not_a_field R (by rw [hϖ, h, Ideal.span_singleton_eq_bot])
  have hϖF : algebraMap R ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j) ϖ ≠ 0 := fun h => hϖ0 (hinjF (by
    have := congrArg (fun b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j) => (b : F)) h
    simpa using this))
  have hϖI : algebraMap R ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j) ϖ ≠ 0 := fun h => hϖ0 (hinjF (by
    have := congrArg (fun b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j) => (b : F)) h
    simpa using this))

  have finF := finite_setOf_two_minimalPrimes_le hdimF _ hϖF
  have finI := finite_setOf_two_minimalPrimes_le hdimI _ hϖI
  let SF : Set ↥(Spec (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j))) := {q | q.asIdeal ∈
    {q : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j) | q.IsPrime ∧ ∃ 𝔭 ∈ (Ideal.span {algebraMap R _ ϖ}).minimalPrimes,
      ∃ 𝔭' ∈ (Ideal.span {algebraMap R _ ϖ}).minimalPrimes, 𝔭 ≠ 𝔭' ∧ 𝔭 ≤ q ∧ 𝔭' ≤ q}}
  let SI : Set ↥(Spec (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j))) := {q | q.asIdeal ∈
    {q : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j) | q.IsPrime ∧ ∃ 𝔭 ∈ (Ideal.span {algebraMap R _ ϖ}).minimalPrimes,
      ∃ 𝔭' ∈ (Ideal.span {algebraMap R _ ϖ}).minimalPrimes, 𝔭 ≠ 𝔭' ∧ 𝔭 ≤ q ∧ 𝔭' ≤ q}}
  have hSF : SF.Finite := finF.preimage (fun a _ b _ h => PrimeSpectrum.ext h)
  have hSI : SI.Finite := finI.preimage (fun a _ b _ h => PrimeSpectrum.ext h)
  refine ((hSF.image (AlgebraicCurve.TwoChartIntegralModel.ιFin R F j).base).union (hSI.image (AlgebraicCurve.TwoChartIntegralModel.ιInf R F j).base)).subset ?_
  intro z hz
  rcases AlgebraicCurve.TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf R F j z with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · left
    refine ⟨q, ?_, rfl⟩
    obtain ⟨𝔭, h𝔭, 𝔭', h𝔭', hne, hle, hle'⟩ := exists_two_minimalPrimes_le_of_chart (AlgebraicCurve.TwoChartIntegralModel.toBase R F j)
      (AlgebraicCurve.TwoChartIntegralModel.ιFin R F j) (AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase R F j) ϖ q hz
    exact ⟨q.isPrime, 𝔭, h𝔭, 𝔭', h𝔭', hne, hle, hle'⟩
  · right
    refine ⟨q, ?_, rfl⟩
    obtain ⟨𝔭, h𝔭, 𝔭', h𝔭', hne, hle, hle'⟩ := exists_two_minimalPrimes_le_of_chart (AlgebraicCurve.TwoChartIntegralModel.toBase R F j)
      (AlgebraicCurve.TwoChartIntegralModel.ιInf R F j) (AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase R F j) ϖ q hz
    exact ⟨q.isPrime, 𝔭, h𝔭, 𝔭', h𝔭', hne, hle, hle'⟩

end S_AlgebraicCurve_TwoChartIntegralModel_finite_setOf_not_subsingleton_minimalPrimes_span_germ
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_finite_setOf_not_subsingleton_minimalPrimes_span_germ (solution)
