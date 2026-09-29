-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.finite_setOf_pullback_fst_mem_not_subsingleton_minimalPrimes_span_germ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/cdc5081e-7c51-5bc6-9841-602318c2a6d8

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ringKrullDim_le_of_ringHom_isIntegral
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_setOf_not_subsingleton_minimalPrimes_span_germ
import Theorems.Thm_AlgebraicGeometry_finite_setOf_pullback_fst_eq_of_isClosed_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_finite_setOf_pullback_fst_mem_not_subsingleton_minimalPrimes_span_germ

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FinGen

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

theorem isMaximal_of_two_minimalPrimes_le
    {S : Type u} [CommRing S] [IsDomain S] [IsNoetherianRing S] (hdim : ringKrullDim S ≤ 2) (ϖ : S) (hϖ : ϖ ≠ 0)
    {q : Ideal S} (hq : q.IsPrime)
    (h : ∃ 𝔭 ∈ (Ideal.span {ϖ}).minimalPrimes, ∃ 𝔭' ∈ (Ideal.span {ϖ}).minimalPrimes, 𝔭 ≠ 𝔭' ∧ 𝔭 ≤ q ∧ 𝔭' ≤ q) :
    q.IsMaximal := by
  obtain ⟨𝔭, h𝔭, 𝔭', h𝔭', hne, hle, hle'⟩ := h
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
  have hlt : 𝔭 < q := by
    refine lt_of_le_of_ne hle fun h => hne ?_
    have h' : 𝔭' ≤ 𝔭 := h ▸ hle'
    exact le_antisymm (h𝔭.2 h𝔭'.1 h') h'
  have h2 : (2 : ℕ∞) ≤ q.height := by
    have := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
    exact Order.add_one_le_of_lt (lt_of_le_of_lt h1 this)
  obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q hq.ne_top
  by_contra hqmax
  have hqM' : q < M := lt_of_le_of_ne hqM fun h => hqmax (h ▸ hM)
  haveI := hM.isPrime
  have h3 : (3 : ℕ∞) ≤ M.height := by
    have := Ideal.height_strict_mono_of_isPrime_of_isPrime hqM'
    exact Order.add_one_le_of_lt (lt_of_le_of_lt h2 this)
  have h4 := Ideal.height_le_ringKrullDim_of_isPrime (I := M)
  have : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) := (WithBot.coe_le_coe.mpr h3).trans (h4.trans hdim)
  have h32 : (3 : ℕ∞) ≤ 2 := WithBot.coe_le_coe.mp this
  exact absurd (by exact_mod_cast h32 : (3 : ℕ) ≤ 2) (by omega)

end FinGen

open FinGen AlgebraicCurve.TwoChartIntegralModel in
theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (Ω : Type u) [Field Ω] [Algebra R Ω] (hΩ : ∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R Ω a = 0) :
    {z : ↥(pullback (AlgebraicCurve.TwoChartIntegralModel.toBase R F j)
        (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) |
      ¬ ((Ideal.span {(((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤
          ((pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase R F j)
            (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).base z) trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase R F j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)))} :
        Ideal ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk
          ((pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase R F j)
            (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).base z))).minimalPrimes).Subsingleton}.Finite := by
  classical

  set X := AlgebraicCurve.TwoChartIntegralModel R F j with hX
  set f := AlgebraicCurve.TwoChartIntegralModel.toBase R F j with hf
  let cross : X → Prop := fun x =>
    ¬ ((Ideal.span {((X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)))} :
      Ideal (X.presheaf.stalk x)).minimalPrimes).Subsingleton
  show {z | cross ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).base z)}.Finite

  have hS : {x : X | cross x}.Finite :=
    AlgebraicCurve.TwoChartIntegralModel.finite_setOf_not_subsingleton_minimalPrimes_span_germ R K₀ F j htj hFD hsep ϖ hϖ

  obtain ⟨hftF, hftI⟩ := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf R K₀ F j htj hFD hsep
  haveI := hftF; haveI := hftI
  haveI : IsNoetherianRing ↥(chartAlgFin R F j) := Algebra.FiniteType.isNoetherianRing R _
  haveI : IsNoetherianRing ↥(chartAlgInf R F j) := Algebra.FiniteType.isNoetherianRing R _
  have hpoly : ringKrullDim (Polynomial R) ≤ 2 := by
    rw [Polynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one R]; rfl
  have hdimF : ringKrullDim ↥(chartAlgFin R F j) ≤ 2 := (ringKrullDim_chartAlg_singleton_le R F j).trans hpoly
  have hdimI : ringKrullDim ↥(chartAlgInf R F j) ≤ 2 := (ringKrullDim_chartAlg_singleton_le R F j⁻¹).trans hpoly
  have hinjF : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]
    exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)
  have hϖ0 : ϖ ≠ 0 := fun h => IsDiscreteValuationRing.not_a_field R (by rw [hϖ, h, Ideal.span_singleton_eq_bot])
  have hϖF : algebraMap R ↥(chartAlgFin R F j) ϖ ≠ 0 := fun h => hϖ0 (hinjF (by
    have := congrArg (fun b : ↥(chartAlgFin R F j) => (b : F)) h
    simpa using this))
  have hϖI : algebraMap R ↥(chartAlgInf R F j) ϖ ≠ 0 := fun h => hϖ0 (hinjF (by
    have := congrArg (fun b : ↥(chartAlgInf R F j) => (b : F)) h
    simpa using this))

  have hclosed : ∀ x : X, cross x → IsClosed ({x} : Set X) := by
    intro x hx

    have keyF : ∀ q : ↥(Spec (CommRingCat.of ↥(chartAlgFin R F j))), (ιFin R F j).base q = x →
        IsClosed ({q} : Set ↥(Spec (CommRingCat.of ↥(chartAlgFin R F j)))) := by
      intro q hq
      subst hq
      exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr
        (isMaximal_of_two_minimalPrimes_le hdimF _ hϖF q.isPrime
          (exists_two_minimalPrimes_le_of_chart f (ιFin R F j) (ιFin_toBase R F j) ϖ q hx))
    have keyI : ∀ q : ↥(Spec (CommRingCat.of ↥(chartAlgInf R F j))), (ιInf R F j).base q = x →
        IsClosed ({q} : Set ↥(Spec (CommRingCat.of ↥(chartAlgInf R F j)))) := by
      intro q hq
      subst hq
      exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr
        (isMaximal_of_two_minimalPrimes_le hdimI _ hϖI q.isPrime
          (exists_two_minimalPrimes_le_of_chart f (ιInf R F j) (ιInf_toBase R F j) ϖ q hx))
    have hpreF : IsClosed ((ιFin R F j).base ⁻¹' {x}) := by
      by_cases h : ∃ q, (ιFin R F j).base q = x
      · obtain ⟨q, hq⟩ := h
        have : (ιFin R F j).base ⁻¹' {x} = {q} := by
          ext q'
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          exact ⟨fun h' => (ιFin R F j).isOpenEmbedding.injective (h'.trans hq.symm), fun h' => h' ▸ hq⟩
        rw [this]; exact keyF q hq
      · have : (ιFin R F j).base ⁻¹' {x} = ∅ := by
          ext q'
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
          exact fun h' => h ⟨q', h'⟩
        rw [this]; exact isClosed_empty
    have hpreI : IsClosed ((ιInf R F j).base ⁻¹' {x}) := by
      by_cases h : ∃ q, (ιInf R F j).base q = x
      · obtain ⟨q, hq⟩ := h
        have : (ιInf R F j).base ⁻¹' {x} = {q} := by
          ext q'
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          exact ⟨fun h' => (ιInf R F j).isOpenEmbedding.injective (h'.trans hq.symm), fun h' => h' ▸ hq⟩
        rw [this]; exact keyI q hq
      · have : (ιInf R F j).base ⁻¹' {x} = ∅ := by
          ext q'
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
          exact fun h' => h ⟨q', h'⟩
        rw [this]; exact isClosed_empty

    have hcompl : ({x} : Set X)ᶜ = (ιFin R F j).base '' ((ιFin R F j).base ⁻¹' {x})ᶜ ∪
        (ιInf R F j).base '' ((ιInf R F j).base ⁻¹' {x})ᶜ := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_image, Set.mem_preimage]
      constructor
      · intro hy
        rcases mem_range_ιFin_or_mem_range_ιInf R F j y with ⟨q, rfl⟩ | ⟨q, rfl⟩
        · exact Or.inl ⟨q, hy, rfl⟩
        · exact Or.inr ⟨q, hy, rfl⟩
      · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) <;> exact hq
    rw [← isOpen_compl_iff, hcompl]
    exact ((ιFin R F j).isOpenEmbedding.isOpenMap _ hpreF.isOpen_compl).union
      ((ιInf R F j).isOpenEmbedding.isOpenMap _ hpreI.isOpen_compl)

  haveI hLOFT : LocallyOfFiniteType f := by
    refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
      (Scheme.IsLocallyDirected.openCover (span (fFin R F j) (fInf R F j))) fun i => ?_
    have hFin : LocallyOfFiniteType (ιFin R F j ≫ f) := by
      rw [hf, ιFin_toBase, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.finiteType_algebraMap.mpr hftF
    have hInf : LocallyOfFiniteType (ιInf R F j ≫ f) := by
      rw [hf, ιInf_toBase, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.finiteType_algebraMap.mpr hftI
    rcases i with (_ | _ | _)
    · have hw : (Scheme.IsLocallyDirected.openCover (span (fFin R F j) (fInf R F j))).f none =
          fFin R F j ≫ ιFin R F j :=
        (colimit.w (span (fFin R F j) (fInf R F j)) WalkingSpan.Hom.fst).symm
      rw [hw]
      haveI := hFin
      have h' : LocallyOfFiniteType (fFin R F j ≫ (ιFin R F j ≫ f)) := inferInstance
      exact (Category.assoc (fFin R F j) (ιFin R F j) f) ▸ h'
    · exact hFin
    · exact hInf

  let κ := IsLocalRing.ResidueField R
  let φ : κ →+* Ω := Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) (algebraMap R Ω) hΩ
  letI : Algebra κ Ω := φ.toAlgebra
  have hφ : (algebraMap κ Ω).comp (algebraMap R κ) = algebraMap R Ω :=
    RingHom.ext fun a => Ideal.Quotient.lift_mk (IsLocalRing.maximalIdeal R) (algebraMap R Ω) hΩ
  let gκ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R κ))
  let gΩ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of κ) := Spec.map (CommRingCat.ofHom (algebraMap κ Ω))
  have hfac : gΩ ≫ gκ = Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]

  let fs : pullback f gκ ⟶ Spec (CommRingCat.of κ) := pullback.snd f gκ
  haveI : LocallyOfFiniteType fs := inferInstance
  haveI : IsClosedImmersion gκ := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hinj : Function.Injective (pullback.fst f gκ).base := (pullback.fst f gκ).isClosedEmbedding.injective

  let E : pullback fs gΩ ≅ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) :=
    pullbackLeftPullbackSndIso f gκ gΩ ≪≫ pullback.congrHom rfl hfac
  have hE : E.hom ≫ pullback.fst f _ = pullback.fst fs gΩ ≫ pullback.fst f gκ := by
    show ((pullbackLeftPullbackSndIso f gκ gΩ).hom ≫ (pullback.congrHom rfl hfac).hom) ≫ _ = _
    rw [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      pullbackLeftPullbackSndIso_hom_fst]

  have hW : {w : ↥(pullback fs gΩ) | cross ((pullback.fst f gκ).base ((pullback.fst fs gΩ).base w))}.Finite := by
    have hT : {y : ↥(pullback f gκ) | cross ((pullback.fst f gκ).base y)}.Finite :=
      hS.preimage hinj.injOn
    have : {w : ↥(pullback fs gΩ) | cross ((pullback.fst f gκ).base ((pullback.fst fs gΩ).base w))} =
        ⋃ y ∈ {y : ↥(pullback f gκ) | cross ((pullback.fst f gκ).base y)}, {w | (pullback.fst fs gΩ).base w = y} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
      exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨y, hy, e⟩ => by rw [e]; exact hy⟩
    rw [this]
    refine hT.biUnion fun y hy => ?_
    have hyc : IsClosed ({y} : Set ↥(pullback f gκ)) := by
      have : ({y} : Set ↥(pullback f gκ)) = (pullback.fst f gκ).base ⁻¹' {(pullback.fst f gκ).base y} := by
        ext y'
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        exact ⟨fun h => h ▸ rfl, fun h => hinj h⟩
      rw [this]
      exact (hclosed _ hy).preimage (pullback.fst f gκ).continuous
    exact AlgebraicGeometry.finite_setOf_pullback_fst_eq_of_isClosed_singleton fs y hyc
  refine (hW.image E.hom.base).subset fun z hz => ?_
  refine ⟨E.inv.base z, ?_, ?_⟩
  · show cross _
    have h1 : (pullback.fst f gκ).base ((pullback.fst fs gΩ).base (E.inv.base z)) =
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).base z := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hE, ← Category.assoc, Iso.inv_hom_id,
        Category.id_comp]
    rw [h1]; exact hz
  · rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl

#print axioms solution

end S_AlgebraicCurve_TwoChartIntegralModel_finite_setOf_pullback_fst_mem_not_subsingleton_minimalPrimes_span_germ
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_finite_setOf_pullback_fst_mem_not_subsingleton_minimalPrimes_span_germ (solution)
