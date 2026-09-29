-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.forall_iff_mem_localRing_and_forall_iff_exists_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/823f0b4f-0ced-598b-957d-81dce8f6fef2

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_forall_iff_mem_localRing_and_forall_iff_exists_mem_maximalIdeal

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel IsLocalRing

universe u

namespace P2E133

theorem chart_dictionary
    {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] (B : Subalgebra R F)
    (X : Scheme.{u}) [IsIntegral X] (ι : Spec (CommRingCat.of ↥B) ⟶ X) [IsOpenImmersion ι]
    (φ : F ≃+* X.functionField)
    (y : PrimeSpectrum ↥B)
    (sec : ↥B → ↑(X.presheaf.obj (Opposite.op (ι ''ᵁ ⊤))))
    (hφ : ∀ b : ↥B, φ (b : F) = algebraMap (X.presheaf.stalk (ι.base y)) X.functionField
        ((X.presheaf.germ (ι ''ᵁ ⊤) (ι.base y) ⟨y, trivial, rfl⟩).hom (sec b)))
    (e : X.presheaf.stalk (ι.base y) ≅ CommRingCat.of (Localization.AtPrime y.asIdeal))
    (he : ∀ b : ↥B, e.hom.hom ((X.presheaf.germ (ι ''ᵁ ⊤) (ι.base y) ⟨y, trivial, rfl⟩).hom (sec b)) =
        algebraMap ↥B (Localization.AtPrime y.asIdeal) b)
    (f : F) :
    ((∃ g h : ↥B, h ∉ y.asIdeal ∧ f * (h : F) = (g : F)) ↔ f ∈ SemistableModel.localRing X φ (ι.base y)) ∧
    ((∃ g h : ↥B, h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : F) = (g : F)) ↔
      ∃ s ∈ maximalIdeal (X.presheaf.stalk (ι.base y)), f = φ.symm (algebraMap (X.presheaf.stalk (ι.base y)) X.functionField s)) := by
  classical
  let gm : ↥B → ↑(X.presheaf.stalk (ι.base y)) := fun b => (X.presheaf.germ (ι ''ᵁ ⊤) (ι.base y) ⟨y, trivial, rfl⟩).hom (sec b)
  have hgm : ∀ b, gm b = (X.presheaf.germ (ι ''ᵁ ⊤) (ι.base y) ⟨y, trivial, rfl⟩).hom (sec b) := fun b => rfl

  have hread : ∀ b : ↥B, φ.symm (algebraMap (X.presheaf.stalk (ι.base y)) X.functionField (gm b)) = (b : F) := by
    intro b; rw [hgm, ← hφ, RingEquiv.symm_apply_apply]

  let eR : ↑(X.presheaf.stalk (ι.base y)) ≃+* Localization.AtPrime y.asIdeal := e.commRingCatIsoToRingEquiv
  have heR : ∀ s, eR s = e.hom.hom s := fun s => rfl
  have hunit_of : ∀ s : (X.presheaf.stalk (ι.base y)), IsUnit (eR s) → IsUnit s := fun s h => by
    have := h.map eR.symm; rwa [RingEquiv.symm_apply_apply] at this
  have hunit_h : ∀ h : ↥B, h ∉ y.asIdeal → IsUnit (gm h) := by
    intro h hh
    apply hunit_of
    rw [heR, hgm, he]; exact IsLocalization.map_units _ (⟨h, hh⟩ : y.asIdeal.primeCompl)
  have hh0_of : ∀ h : ↥B, IsUnit (gm h) → (h : F) ≠ 0 := by
    intro h hu h0
    have := hread h
    rw [h0] at this
    have : algebraMap (X.presheaf.stalk (ι.base y)) X.functionField (gm h) = 0 := by
      have t := congrArg φ this; rwa [RingEquiv.apply_symm_apply, map_zero] at t
    exact hu.ne_zero ((IsFractionRing.injective (X.presheaf.stalk (ι.base y)) X.functionField) (by rw [this, map_zero]))
  have hinv : ∀ (h : ↥B) (hu : IsUnit (gm h)), φ.symm (algebraMap (X.presheaf.stalk (ι.base y)) X.functionField (↑(hu.unit⁻¹) : (X.presheaf.stalk (ι.base y)))) * (h : F) = 1 := by
    intro h hu
    rw [← hread h, ← map_mul, ← map_mul, IsUnit.val_inv_mul, map_one, map_one]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨g, h, hh, hfg⟩
    have hu := hunit_h h hh
    refine ⟨gm g * ↑(hu.unit⁻¹), ?_⟩
    show φ.symm (algebraMap (X.presheaf.stalk (ι.base y)) X.functionField (gm g * ↑(hu.unit⁻¹))) = f
    apply mul_right_cancel₀ (hh0_of h hu)
    rw [map_mul, map_mul, hread g, mul_assoc, hinv h hu, mul_one, hfg]
  · rintro ⟨s, hs⟩
    obtain ⟨⟨g, h⟩, hgh⟩ := IsLocalization.surj y.asIdeal.primeCompl (eR s)
    refine ⟨g, h, h.2, ?_⟩
    have h1 : s * gm h = gm g := by
      apply eR.injective
      rw [map_mul, heR (gm h), heR (gm g), hgm, hgm, he, he]
      exact hgh
    rw [← hs]
    show φ.symm (algebraMap (X.presheaf.stalk (ι.base y)) X.functionField s) * (h : F) = (g : F)
    rw [← hread g, ← hread h, ← map_mul, ← map_mul, h1]
  · rintro ⟨g, h, hh, hg, hfg⟩
    have hu := hunit_h h hh
    refine ⟨gm g * ↑(hu.unit⁻¹), ?_, ?_⟩
    · apply Ideal.mul_mem_right
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hug
      have : IsUnit (eR (gm g)) := hug.map eR
      rw [heR, hgm, he, IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime y.asIdeal) y.asIdeal g] at this
      exact this hg
    · apply mul_right_cancel₀ (hh0_of h hu)
      rw [map_mul, map_mul, hread g, mul_assoc, hinv h hu, mul_one, hfg]
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨⟨g, h⟩, hgh⟩ := IsLocalization.surj y.asIdeal.primeCompl (eR s)
    refine ⟨g, h, h.2, ?_, ?_⟩
    ·
      by_contra hg
      have hu1 : IsUnit (algebraMap ↥B (Localization.AtPrime y.asIdeal) g) :=
        IsLocalization.map_units _ (⟨g, hg⟩ : y.asIdeal.primeCompl)
      rw [← hgh] at hu1
      have hu2 : IsUnit (eR s) := isUnit_of_mul_isUnit_left hu1
      exact ((IsLocalRing.mem_maximalIdeal _).mp hs) (hunit_of s hu2)
    · have h1 : s * gm h = gm g := by
        apply eR.injective
        rw [map_mul, heR (gm h), heR (gm g), hgm, hgm, he, he]
        exact hgh
      rw [← hread g, ← hread h, ← map_mul, ← map_mul, h1]

end P2E133

set_option maxHeartbeats 3200000 in
theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j)]
    (φ : F ≃+* (AlgebraicCurve.TwoChartIntegralModel R F j).functionField)
    (hφFin : ∀ (y : ↥(XFin R F j)) (b : ↥(chartAlgFin R F j)),
        φ (b : F) = algebraMap ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y)) (AlgebraicCurve.TwoChartIntegralModel R F j).functionField
          (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιFin R F j) ''ᵁ ⊤) ((ιFin R F j).base y) ⟨y, trivial, rfl⟩).hom
            (((ιFin R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom b))))
    (hφInf : ∀ (y : ↥(XInf R F j)) (b : ↥(chartAlgInf R F j)),
        φ (b : F) = algebraMap ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιInf R F j).base y)) (AlgebraicCurve.TwoChartIntegralModel R F j).functionField
          (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιInf R F j) ''ᵁ ⊤) ((ιInf R F j).base y) ⟨y, trivial, rfl⟩).hom
            (((ιInf R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv.hom b))))
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) (f : F) :
    (((∀ y : ↥(XFin R F j), (ιFin R F j).base y = x →
          ∃ g h : ↥(chartAlgFin R F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F)) ∧
       (∀ y : ↥(XInf R F j), (ιInf R F j).base y = x →
          ∃ g h : ↥(chartAlgInf R F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F))) ↔
      f ∈ SemistableModel.localRing (AlgebraicCurve.TwoChartIntegralModel R F j) φ x) ∧
    (((∀ y : ↥(XFin R F j), (ιFin R F j).base y = x →
          ∃ g h : ↥(chartAlgFin R F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : F) = (g : F)) ∧
       (∀ y : ↥(XInf R F j), (ιInf R F j).base y = x →
          ∃ g h : ↥(chartAlgInf R F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : F) = (g : F))) ↔
      ∃ s ∈ maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x),
        f = φ.symm (algebraMap ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x) (AlgebraicCurve.TwoChartIntegralModel R F j).functionField s)) := by
  classical

  have dFin : ∀ (y : ↥(XFin R F j)), (ιFin R F j).base y = x →
      (((∃ g h : ↥(chartAlgFin R F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F)) ↔
          f ∈ SemistableModel.localRing (AlgebraicCurve.TwoChartIntegralModel R F j) φ x) ∧
       ((∃ g h : ↥(chartAlgFin R F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : F) = (g : F)) ↔
          ∃ s ∈ maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x),
            f = φ.symm (algebraMap _ (AlgebraicCurve.TwoChartIntegralModel R F j).functionField s))) := by
    intro y hy
    subst hy
    obtain ⟨e, -, he⟩ := AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_chartAlgFin R F j y ⟨y, trivial, rfl⟩
    exact P2E133.chart_dictionary (chartAlgFin R F j) (AlgebraicCurve.TwoChartIntegralModel R F j) (ιFin R F j) φ y
      (fun b => ((ιFin R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom b))
      (hφFin y) e he f
  have dInf : ∀ (y : ↥(XInf R F j)), (ιInf R F j).base y = x →
      (((∃ g h : ↥(chartAlgInf R F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F)) ↔
          f ∈ SemistableModel.localRing (AlgebraicCurve.TwoChartIntegralModel R F j) φ x) ∧
       ((∃ g h : ↥(chartAlgInf R F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : F) = (g : F)) ↔
          ∃ s ∈ maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x),
            f = φ.symm (algebraMap _ (AlgebraicCurve.TwoChartIntegralModel R F j).functionField s))) := by
    intro y hy
    subst hy
    obtain ⟨e, -, he⟩ := AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_chartAlgInf R F j y ⟨y, trivial, rfl⟩
    exact P2E133.chart_dictionary (chartAlgInf R F j) (AlgebraicCurve.TwoChartIntegralModel R F j) (ιInf R F j) φ y
      (fun b => ((ιInf R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv.hom b))
      (hφInf y) e he f
  rcases mem_range_ιFin_or_mem_range_ιInf R F j x with ⟨y₀, hy₀⟩ | ⟨y₀, hy₀⟩
  · refine ⟨⟨fun h => ((dFin y₀ hy₀).1).mp (h.1 y₀ hy₀), fun h => ⟨fun y hy => ((dFin y hy).1).mpr h, fun y hy => ((dInf y hy).1).mpr h⟩⟩,
      ⟨fun h => ((dFin y₀ hy₀).2).mp (h.1 y₀ hy₀), fun h => ⟨fun y hy => ((dFin y hy).2).mpr h, fun y hy => ((dInf y hy).2).mpr h⟩⟩⟩
  · refine ⟨⟨fun h => ((dInf y₀ hy₀).1).mp (h.2 y₀ hy₀), fun h => ⟨fun y hy => ((dFin y hy).1).mpr h, fun y hy => ((dInf y hy).1).mpr h⟩⟩,
      ⟨fun h => ((dInf y₀ hy₀).2).mp (h.2 y₀ hy₀), fun h => ⟨fun y hy => ((dFin y hy).2).mpr h, fun y hy => ((dInf y hy).2).mpr h⟩⟩⟩

end S_AlgebraicCurve_TwoChartIntegralModel_forall_iff_mem_localRing_and_forall_iff_exists_mem_maximalIdeal
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_forall_iff_mem_localRing_and_forall_iff_exists_mem_maximalIdeal (solution)
