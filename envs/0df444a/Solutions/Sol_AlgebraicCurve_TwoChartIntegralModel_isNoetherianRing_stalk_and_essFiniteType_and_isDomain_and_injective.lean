-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.isNoetherianRing_stalk_and_essFiniteType_and_isDomain_and_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/db0b6eac-dd9a-5391-bce1-a0553d4af54e

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isNoetherianRing_stalk_and_essFiniteType_and_isDomain_and_injective

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

namespace StalkProps

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] {F : Type u} [Field F] [Algebra R F]

set_option maxHeartbeats 3200000 in
theorem chart (hinj : Function.Injective (algebraMap R F)) (j : F) [Fact (j ≠ 0)]
    (C : Subalgebra R F) (hFT : Algebra.FiniteType R ↥C)
    (ι : Spec (CommRingCat.of ↥C) ⟶ AlgebraicCurve.TwoChartIntegralModel R F j) [IsOpenImmersion ι]
    (hι : ι ≫ toBase R F j = Spec.map (CommRingCat.ofHom (algebraMap R ↥C)))
    (y : ↥(Spec (CommRingCat.of ↥C)))
    [Algebra R ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk (ι.base y))]
    (halg : ∀ r : R, algebraMap R ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk (ι.base y)) r =
      (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ (ι.base y) trivial).hom
        (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))) :
    IsNoetherianRing ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk (ι.base y)) ∧
    Algebra.EssFiniteType R ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk (ι.base y)) ∧
    IsDomain ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk (ι.base y)) ∧
    Function.Injective (algebraMap R ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk (ι.base y))) := by
  classical
  haveI : IsIso (ι.stalkMap y) := (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 y
  let Loc := Localization.AtPrime y.asIdeal
  let eS : (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk (ι.base y) ≅ CommRingCat.of Loc := asIso (ι.stalkMap y) ≪≫ Spec.stalkIso (CommRingCat.of ↥C) y
  let rS : ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk (ι.base y) : Type u) ≃+* Loc := eS.commRingCatIsoToRingEquiv

  have key : ∀ r : R, rS (algebraMap R _ r) = algebraMap ↥C Loc (algebraMap R ↥C r) := by
    intro r
    rw [halg r]
    change (Spec.stalkIso (CommRingCat.of ↥C) y).hom (ι.stalkMap y ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ (ι.base y) trivial
      ((toBase R F j).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)))) = _
    erw [Scheme.Hom.germ_stalkMap_apply ι ⊤ y trivial]
    have s1 : ι.app ⊤ ((toBase R F j).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) =
        (Scheme.ΓSpecIso (CommRingCat.of ↥C)).inv (algebraMap R ↥C r) := by
      have h1 : ι.app ⊤ ((toBase R F j).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) =
          (ι ≫ toBase R F j).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
        rw [Scheme.Hom.comp_appTop]; rfl
      rw [h1, hι]
      have h2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R ↥C))
      have h3 := congrArg (fun g : CommRingCat.of R ⟶ Γ(Spec (CommRingCat.of ↥C), ⊤) => g.hom r) h2
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3
      exact h3.symm
    erw [s1]
    have s2 := congrArg (fun g : Γ(Spec (CommRingCat.of ↥C), ⊤) ⟶ CommRingCat.of Loc =>
      g.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥C)).inv (algebraMap R ↥C r))) (Spec.germ_stalkMapIso_hom y)
    simp only [CommRingCat.comp_apply] at s2
    erw [s2]
    simp
    rfl

  haveI : IsNoetherianRing ↥C := Algebra.FiniteType.isNoetherianRing R ↥C
  haveI : IsNoetherianRing Loc := IsLocalization.isNoetherianRing y.asIdeal.primeCompl Loc inferInstance
  haveI : Algebra.EssFiniteType ↥C Loc := Algebra.EssFiniteType.of_isLocalization Loc y.asIdeal.primeCompl
  haveI : Algebra.EssFiniteType R Loc := Algebra.EssFiniteType.comp R ↥C Loc
  haveI : IsDomain Loc := IsLocalization.isDomain_localization y.asIdeal.primeCompl_le_nonZeroDivisors
  have hinjC : Function.Injective (algebraMap R ↥C) := by
    intro a b hab
    apply hinj
    have := congrArg (fun c : ↥C => (c : F)) hab
    simpa using this
  have hinjLoc : Function.Injective (algebraMap R Loc) := by
    rw [IsScalarTower.algebraMap_eq R ↥C Loc]
    exact (IsLocalization.injective Loc y.asIdeal.primeCompl_le_nonZeroDivisors).comp hinjC

  let eA : ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk (ι.base y) : Type u) ≃ₐ[R] Loc := AlgEquiv.ofRingEquiv (f := rS) key
  refine ⟨isNoetherianRing_of_ringEquiv Loc rS.symm, ?_, MulEquiv.isDomain Loc rS.toMulEquiv, ?_⟩
  · exact (Algebra.EssFiniteType.iff_of_algEquiv eA).mpr inferInstance
  · intro a b hab
    apply hinjLoc
    have := congrArg rS hab
    rwa [key, key] at this

end StalkProps

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (F : Type u) [Field F] [Algebra R F]
    (hinj : Function.Injective (algebraMap R F)) (j : F) [Fact (j ≠ 0)]
    (hFT : Algebra.FiniteType R ↥(chartAlgFin R F j)) (hFT' : Algebra.FiniteType R ↥(chartAlgInf R F j))
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))

    [Algebra R ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z)]
    (halg : ∀ r : R, algebraMap R ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z) r =
      (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ z trivial).hom
        (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))) :
    IsNoetherianRing ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z) ∧
    Algebra.EssFiniteType R ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z) ∧
    IsDomain ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z) ∧
    Function.Injective (algebraMap R ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z)) := by
  rcases mem_range_ιFin_or_mem_range_ιInf R F j z with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact StalkProps.chart hinj j (chartAlgFin R F j) hFT (ιFin R F j) (ιFin_toBase R F j) y halg
  · exact StalkProps.chart hinj j (chartAlgInf R F j) hFT' (ιInf R F j) (ιInf_toBase R F j) y halg

end S_AlgebraicCurve_TwoChartIntegralModel_isNoetherianRing_stalk_and_essFiniteType_and_isDomain_and_injective
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isNoetherianRing_stalk_and_essFiniteType_and_isDomain_and_injective (solution)
