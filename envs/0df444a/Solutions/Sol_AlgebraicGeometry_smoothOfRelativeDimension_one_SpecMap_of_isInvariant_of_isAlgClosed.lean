-- Prove2me | solution 1 for AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/2e327286-06f2-5dea-b5d7-f6d3fee9d30f

import Mathlib
import Theorems.Thm_Algebra_IsInvariant_isDiscreteValuationRing_localization_atPrime_of_forall_isMaximal
import Theorems.Thm_Algebra_IsInvariant_moduleFinite_and_finiteType_of_finiteType
import Theorems.Thm_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_forall_isRegularLocalRing_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace QSFibreStab21

theorem nonempty_algEquiv_localization_atPrime {A : Type u} [CommRing A] (M : Submonoid A)
    (P : Ideal A) [P.IsPrime] (P' : Ideal (Localization M)) [P'.IsPrime]
    (h : P'.comap (algebraMap A (Localization M)) = P) :
    Nonempty (Localization.AtPrime P ≃ₐ[A] Localization.AtPrime P') := by
  subst h
  exact ⟨IsLocalization.localizationLocalizationAtPrimeIsoLocalization M P'⟩

theorem isDiscreteValuationRing_localization_atPrime_of_smoothOfRelativeDimension_one
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k A)))]
    (P : Ideal A) [hPmax : P.IsMaximal] :
    ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) := by
  classical
  have hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension.{u, u} 1) (algebraMap k A) :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mp ‹_›
  obtain ⟨s, hs, hstd⟩ := hloc
  have hex : ∃ t ∈ s, t ∉ P := by
    by_contra h
    apply hPmax.ne_top
    rw [eq_top_iff, ← hs]
    exact Ideal.span_le.mpr fun x hx => by_contra fun hxP => h ⟨x, hx, hxP⟩
  obtain ⟨t, hts, htP⟩ := hex
  let At := Localization.Away t
  let P' : Ideal At := Ideal.map (algebraMap A At) P
  have hdisj : Disjoint ((Submonoid.powers t : Submonoid A) : Set A) (P : Set A) :=
    (Ideal.disjoint_powers_iff_notMem t hPmax.isPrime.isRadical).mpr htP
  haveI hP'p : P'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers t) At P hPmax.isPrime hdisj
  have hunder : P'.comap (algebraMap A At) = P :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers t) At hPmax.isPrime hdisj
  haveI hP'max : P'.IsMaximal := by
    refine ⟨⟨hP'p.ne_top, fun Q hQ => ?_⟩⟩
    by_contra hQtop
    obtain ⟨m, hm, hQm⟩ := Ideal.exists_le_maximal Q hQtop
    have hle : P ≤ m.comap (algebraMap A At) := by
      rw [← hunder]; exact Ideal.comap_mono (hQ.le.trans hQm)
    have hmc : m.comap (algebraMap A At) = P :=
      (hPmax.eq_of_le (Ideal.comap_ne_top _ hm.ne_top) hle).symm
    have hmP' : m = P' := by
      rw [← IsLocalization.map_under (Submonoid.powers t) At m, Ideal.under_def, hmc]
    exact absurd (hQ.trans_le hQm) (hmP' ▸ lt_irrefl _)

  obtain ⟨hdom', hdvr'⟩ :=
    @Algebra.IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime
      k _ At _ ((algebraMap A At).comp (algebraMap k A)).toAlgebra (hstd t hts) P' hP'max

  obtain ⟨e⟩ := nonempty_algEquiv_localization_atPrime (Submonoid.powers t) P P' hunder
  haveI : IsDomain (Localization.AtPrime P) := Function.Injective.isDomain e.toRingEquiv.toRingHom
    (fun x y h => e.injective h)
  haveI := hdvr'
  exact ⟨‹_›, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm⟩

end QSFibreStab21

theorem solution
    {k S A : Type u} [Field k] [IsAlgClosed k] [CommRing S] [CommRing A]
    [Algebra k S] [Algebra k A] [Algebra S A] [IsScalarTower k S A] [FaithfulSMul S A]
    (G : Type u) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G k A] [SMulCommClass G S A]
    [Algebra.IsInvariant S A G]
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k A)))] :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k S))) := by

  have hsm : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
    SmoothOfRelativeDimension.smooth 1 _
  have hlft : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A))) := inferInstance
  have hftA : Algebra.FiniteType k A :=
    RingHom.finiteType_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hlft)

  haveI hftS : Algebra.FiniteType k S :=
    (Algebra.IsInvariant.moduleFinite_and_finiteType_of_finiteType k S A G).2
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S

  have hA : ∀ (P : Ideal A) (_ : P.IsMaximal),
      ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) :=
    fun P hP =>
      QSFibreStab21.isDiscreteValuationRing_localization_atPrime_of_smoothOfRelativeDimension_one (k := k) P

  refine AlgebraicGeometry.SmoothOfRelativeDimension.of_forall_isRegularLocalRing_of_isAlgClosed k S 1
    (fun q hq => ?_)
  haveI := hq
  obtain ⟨hdom, hdvr⟩ :=
    Algebra.IsInvariant.isDiscreteValuationRing_localization_atPrime_of_forall_isMaximal G hA q
  haveI := hdom
  haveI := hdvr
  refine ⟨inferInstance, ?_⟩
  rw [IsDiscreteValuationRing.ringKrullDim_eq_one]
  norm_num

end S_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAlgClosed (solution)
