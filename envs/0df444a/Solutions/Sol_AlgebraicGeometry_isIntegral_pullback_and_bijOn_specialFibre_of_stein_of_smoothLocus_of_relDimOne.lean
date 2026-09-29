-- Prove2me | solution 1 for AlgebraicGeometry.isIntegral_pullback_and_bijOn_specialFibre_of_stein_of_smoothLocus_of_relDimOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e15fcb40-a65b-56bc-891f-6c9cafa1d2e3

import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicGeometry_isProper_and_flat_and_locallyOfFinitePresentation_of_iso_pullback_specMap
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_iso_pullback_of_stein_of_isIntegrallyClosed_of_smoothLocus_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_base_genericPoint_eq_and_bijOn_specialFibre_of_iso_pullback_of_residue_surjective_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_mem_smoothLocus_iff_base_mem_smoothLocus_of_iso_pullback_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_exists_valuationSubring_eq_range_stalk_of_iso_pullback_of_mem_smoothLocus_of_isDiscreteValuationRing_of_specializes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIntegral_pullback_and_bijOn_specialFibre_of_stein_of_smoothLocus_of_relDimOne
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem solution
    {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (hn₀ : ∀ y : X₀, IsIntegrallyClosed (X₀.presheaf.stalk y))

    (hO : Function.Bijective (fun a : A₀ => toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))

    (hgen₀ : ∀ y : X₀, (toBase₀.base y).asIdeal = ⊥ → y ∈ toBase₀.smoothLocus)

    (hsm₀ : ∀ η₀ : X₀, toBase₀.base η₀ = closedPoint A₀ → (∃ y : X₀, η₀ ⤳ y ∧ y ≠ η₀) → η₀ ∈ toBase₀.smoothLocus)

    (hdim₀ : ∀ η y : X₀, toBase₀.base η = closedPoint A₀ → (∃ z : X₀, η ⤳ z ∧ z ≠ η) → η ⤳ y → y ≠ η →
      ∀ z : X₀, y ⤳ z → z = y)
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase) :
    let pr := iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))
    ∃ (_ : IsIntegral X) (_ : IsProper toBase) (_ : Flat toBase) (_ : LocallyOfFinitePresentation toBase),

      pr.base (genericPoint X) = genericPoint X₀ ∧
      (∀ x : X, toBase.base x = closedPoint ↥A ↔ toBase₀.base (pr.base x) = closedPoint A₀) ∧
      (∀ x y : X, toBase.base x = closedPoint ↥A → toBase.base y = closedPoint ↥A → pr.base x = pr.base y → x = y) ∧
      (∀ x₀ : X₀, toBase₀.base x₀ = closedPoint A₀ → ∃ x : X, pr.base x = x₀) ∧
      (∀ x y : X, toBase.base x = closedPoint ↥A → toBase.base y = closedPoint ↥A → (x ⤳ y ↔ pr.base x ⤳ pr.base y)) ∧

      (∀ x : X, x ∈ toBase.smoothLocus ↔ pr.base x ∈ toBase₀.smoothLocus) ∧

      (∀ η y : X, toBase.base η = closedPoint ↥A → (∃ z : X, η ⤳ z ∧ z ≠ η) → η ⤳ y → y ≠ η →
        ∀ z : X, y ⤳ z → z = y) ∧

      (∀ η : X, toBase.base η = closedPoint ↥A → (∃ y : X, η ⤳ y ∧ y ≠ η) →
        ∃ O : ValuationSubring X.functionField,
          O.toSubring = (algebraMap (X.presheaf.stalk η) X.functionField).range ∧
          ∀ (hgen : pr.base (genericPoint X) = genericPoint X₀) (g : X₀.functionField),
            (pr.stalkMap (genericPoint X)).hom
                ((X₀.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom g) ∈ O ↔
              g ∈ (algebraMap (X₀.presheaf.stalk (pr.base η)) X₀.functionField).range)  := by
  intro pr
  obtain ⟨hprop, hflat, hlfp⟩ := AlgebraicGeometry.isProper_and_flat_and_locallyOfFinitePresentation_of_iso_pullback_specMap A hrk hA A₀ ι hι hres halg X₀ toBase₀ hn₀ hO hgen₀ hsm₀ X toBase iso hiso
  haveI hint : IsIntegral X := AlgebraicGeometry.isIntegral_of_iso_pullback_of_stein_of_isIntegrallyClosed_of_smoothLocus_of_isDiscreteValuationRing A hrk hA A₀ ι hι hres halg X₀ toBase₀ hn₀ hO hgen₀ hsm₀ X toBase iso hiso
  haveI := hlfp
  obtain ⟨hgen, hsp, hinj, hsurj, hspec⟩ := AlgebraicGeometry.base_genericPoint_eq_and_bijOn_specialFibre_of_iso_pullback_of_residue_surjective_of_isDiscreteValuationRing A hrk hA A₀ ι hι hres halg X₀ toBase₀ hn₀ hO hgen₀ hsm₀ X toBase iso hiso
  have hsm := AlgebraicGeometry.mem_smoothLocus_iff_base_mem_smoothLocus_of_iso_pullback_of_isDiscreteValuationRing A hrk hA A₀ ι hι hres halg X₀ toBase₀ hn₀ hO hgen₀ hsm₀ X toBase iso hiso
  have hval := AlgebraicGeometry.exists_valuationSubring_eq_range_stalk_of_iso_pullback_of_mem_smoothLocus_of_isDiscreteValuationRing_of_specializes A hrk hA A₀ ι hι hres halg X₀ toBase₀ hn₀ hO hgen₀ hsm₀ hdim₀ X toBase iso hiso

  have hmaxA : IsClosed ({closedPoint ↥A} : Set (PrimeSpectrum ↥A)) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr (IsLocalRing.maximalIdeal.isMaximal ↥A)
  have hspA : ∀ x y : X, toBase.base x = closedPoint ↥A → x ⤳ y → toBase.base y = closedPoint ↥A := by
    intro x y hx hxy
    have h2 := hxy.map toBase.continuous
    rw [hx] at h2
    exact Set.mem_singleton_iff.mp (h2.mem_closed hmaxA rfl)

  have hdim : ∀ η y : X, toBase.base η = closedPoint ↥A → (∃ z : X, η ⤳ z ∧ z ≠ η) → η ⤳ y → y ≠ η →
      ∀ z : X, y ⤳ z → z = y := by
    intro η y hη hnc hηy hyη z hyz
    have hy : toBase.base y = closedPoint ↥A := hspA η y hη hηy
    have hz : toBase.base z = closedPoint ↥A := hspA y z hy hyz
    obtain ⟨w, hηw, hwη⟩ := hnc
    have hw : toBase.base w = closedPoint ↥A := hspA η w hη hηw
    have hη₀ : toBase₀.base (pr.base η) = closedPoint A₀ := (hsp η).mp hη
    have hnc₀ : ∃ z₀ : X₀, pr.base η ⤳ z₀ ∧ z₀ ≠ pr.base η :=
      ⟨pr.base w, (hspec η w hη hw).mp hηw, fun h => hwη (hinj w η hw hη h)⟩
    have hηy₀ : pr.base η ⤳ pr.base y := (hspec η y hη hy).mp hηy
    have hyη₀ : pr.base y ≠ pr.base η := fun h => hyη (hinj y η hy hη h)
    have hz₀ : pr.base z = pr.base y := hdim₀ (pr.base η) (pr.base y) hη₀ hnc₀ hηy₀ hyη₀ (pr.base z) ((hspec y z hy hz).mp hyz)
    exact hinj z y hz hy hz₀
  exact ⟨hint, hprop, hflat, hlfp, hgen, hsp, hinj, hsurj, hspec, hsm, hdim, hval⟩

end S_AlgebraicGeometry_isIntegral_pullback_and_bijOn_specialFibre_of_stein_of_smoothLocus_of_relDimOne
end P2MW
export P2MW.S_AlgebraicGeometry_isIntegral_pullback_and_bijOn_specialFibre_of_stein_of_smoothLocus_of_relDimOne (solution)
