-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.placeOfPoint_ofGenerator_iota0_comap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/915b77a6-4f55-5c02-b18d-061b35746065

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_placeOfPoint_ofGenerator_iota0_comap

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IntermediateField IsDedekindDomain

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "CurveModel.ofGenerator CurveModel Place Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring toValuationSubring"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

theorem mem_valuationSubring_iff_exists {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (w : HeightOneSpectrum R) (x : F) :
    x ∈ (w.valuation F).valuationSubring ↔
      ∃ a s : R, s ∉ w.asIdeal ∧ x = algebraMap R F a * (algebraMap R F s)⁻¹ := by
  rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring, ← ValuationSubring.mem_toSubring,
    HeightOneSpectrum.valuationSubringAtPrime_toSubring]
  change (∃ a s, ∃ (_ : s ∈ w.asIdeal.primeCompl), x = algebraMap R F a * (algebraMap R F s)⁻¹) ↔ _
  exact ⟨fun ⟨a, s, hs, h⟩ => ⟨a, s, hs, h⟩, fun ⟨a, s, hs, h⟩ => ⟨a, s, hs, h⟩⟩

theorem toSubring_ofHeightOneSpectrum_comap
    {K₀ K F₀ F : Type*} [Field K₀] [Field K] [Field F₀] [Field F] [Algebra K₀ F₀] [Algebra K F]
    {R₀ R : Type*} [CommRing R₀] [IsDedekindDomain R₀] [Algebra R₀ F₀] [IsFractionRing R₀ F₀]
    [Algebra K₀ R₀] [IsScalarTower K₀ R₀ F₀]
    [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
    [Algebra K R] [IsScalarTower K R F]
    (φ : F₀ →+* F) (ψ : R₀ →+* R) (hφψ : ∀ a : R₀, φ (algebraMap R₀ F₀ a) = algebraMap R F (ψ a))
    (w₀ : HeightOneSpectrum R₀) (w : HeightOneSpectrum R)
    (hw : w₀.asIdeal = w.asIdeal.comap ψ) :
    (Place.ofHeightOneSpectrum (K := K) w).toValuationSubring.toSubring.comap φ =
      (Place.ofHeightOneSpectrum (K := K₀) w₀).toValuationSubring.toSubring := by

  rw [Place.ofHeightOneSpectrum_toValuationSubring, Place.ofHeightOneSpectrum_toValuationSubring]
  have hmem : ∀ {a : R₀}, a ∈ w₀.asIdeal ↔ ψ a ∈ w.asIdeal := fun {a} => by rw [hw, Ideal.mem_comap]
  ext x
  simp only [Subring.mem_comap, ValuationSubring.mem_toSubring]
  constructor
  ·
    intro hx
    by_contra hx₀
    have hx0 : x ≠ 0 := by rintro rfl; exact hx₀ (ValuationSubring.zero_mem _)
    have hxi : x⁻¹ ∈ (w₀.valuation F₀).valuationSubring :=
      ((w₀.valuation F₀).valuationSubring.mem_or_inv_mem x).resolve_left hx₀
    obtain ⟨a, s, hs, hxas⟩ := (mem_valuationSubring_iff_exists w₀ x⁻¹).mp hxi
    have hs0 : (algebraMap R₀ F₀ s) ≠ 0 := by
      intro h; exact hs ((IsFractionRing.to_map_eq_zero_iff (K := F₀)).mp h ▸ w₀.asIdeal.zero_mem)
    have ha0 : a ≠ 0 := by
      rintro rfl; rw [map_zero, zero_mul] at hxas; exact inv_ne_zero hx0 hxas

    have ha : a ∈ w₀.asIdeal := by
      have hlt : (w₀.valuation F₀) x⁻¹ < 1 := by
        rw [Valuation.map_inv, inv_lt_one₀]
        · exact lt_of_not_ge fun h => hx₀ ((Valuation.mem_valuationSubring_iff _ _).mpr h)
        · exact (Valuation.pos_iff _).mpr hx0
      rw [hxas, Valuation.map_mul, Valuation.map_inv, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_eq_one_iff.mpr hs, inv_one, mul_one,
        HeightOneSpectrum.intValuation_lt_one_iff_mem] at hlt
      exact hlt

    have hψa : ψ a ∈ w.asIdeal := hmem.mp ha
    have hψs : ψ s ∉ w.asIdeal := fun h => hs (hmem.mpr h)
    have hψa0 : algebraMap R F (ψ a) ≠ 0 := by
      rw [← hφψ]; intro h
      exact ha0 ((IsFractionRing.injective R₀ F₀) (by rw [map_zero]; exact (map_eq_zero φ).mp h))
    have hφx : φ x = (algebraMap R F (ψ a))⁻¹ * algebraMap R F (ψ s) := by
      have : φ x⁻¹ = algebraMap R F (ψ a) * (algebraMap R F (ψ s))⁻¹ := by
        rw [hxas, map_mul, map_inv₀, hφψ, hφψ]
      rw [map_inv₀] at this
      rw [← inv_inv (φ x), this, mul_inv, inv_inv]
    have hgt : 1 < (w.valuation F) (φ x) := by
      rw [hφx, Valuation.map_mul, Valuation.map_inv, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.mpr hψs,
        mul_one, one_lt_inv₀]
      · exact (HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).mpr hψa
      · rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
        exact (Valuation.pos_iff _).mpr hψa0
    exact absurd ((Valuation.mem_valuationSubring_iff _ _).mp hx) (not_le.mpr hgt)
  ·
    intro hx
    obtain ⟨a, s, hs, rfl⟩ := (mem_valuationSubring_iff_exists w₀ x).mp hx
    have hψs : ψ s ∉ w.asIdeal := fun h => hs (hmem.mpr h)
    rw [Valuation.mem_valuationSubring_iff, map_mul, map_inv₀, hφψ, hφψ, Valuation.map_mul,
      Valuation.map_inv, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.mpr hψs,
      inv_one, mul_one]
    exact HeightOneSpectrum.intValuation_le_one _ _

end AlgebraicCurve.Place

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "CurveModel.ofGenerator CurveModel Place Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring"
namespace CurveModel
p2m_export "AlgebraicCurve.CurveModel" "X₀ XInf glued ι₀ ιInf gluedPlaceOfPoint gluedPlaceOfPoint_ι₀ gluedPlaceOfPoint_of_not_mem ofGenerator placeOfPoint C chartRing"
p2m_open "AlgebraicCurve.CurveModel AlgebraicCurve"

theorem gluedPlaceOfPoint_ι₀_comap
    (K₀ : Type u) [Field K₀] {L₀ : Type u} [Field L₀] [Algebra K₀ L₀] (t₀ : L₀)
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)
    [CharZero K₀] [Fact (t₀ ≠ 0)] [FiniteDimensional K₀⟮t₀⟯ L₀] [FiniteDimensional K₀⟮t₀⁻¹⟯ L₀]
    [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    (ht₀ : Transcendental K₀ t₀) (ht : Transcendental K t)
    (φ : L₀ →+* L) (ψ : chartRing K₀ ({t₀} : Set L₀) →+* chartRing K ({t} : Set L))
    (hφψ : ∀ a : chartRing K₀ ({t₀} : Set L₀), φ (a : L₀) = (ψ a : L))
    (xb : X₀ K t) (hxb : (ι₀ K t).base xb ∈ closedPoints (glued K t))
    (yb : X₀ K₀ t₀) (hyb : (ι₀ K₀ t₀).base yb ∈ closedPoints (glued K₀ t₀))
    (h : yb.asIdeal = xb.asIdeal.comap ψ) :
    (gluedPlaceOfPoint K t ht ⟨(ι₀ K t).base xb, hxb⟩).toValuationSubring.toSubring.comap φ =
      (gluedPlaceOfPoint K₀ t₀ ht₀ ⟨(ι₀ K₀ t₀).base yb, hyb⟩).toValuationSubring.toSubring := by
  rw [gluedPlaceOfPoint_ι₀, gluedPlaceOfPoint_ι₀]
  exact Place.toSubring_ofHeightOneSpectrum_comap φ ψ hφψ _ _ h

theorem gluedPlaceOfPoint_ιInf_comap
    (K₀ : Type u) [Field K₀] {L₀ : Type u} [Field L₀] [Algebra K₀ L₀] (t₀ : L₀)
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)
    [CharZero K₀] [Fact (t₀ ≠ 0)] [FiniteDimensional K₀⟮t₀⟯ L₀] [FiniteDimensional K₀⟮t₀⁻¹⟯ L₀]
    [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    (ht₀ : Transcendental K₀ t₀) (ht : Transcendental K t)
    (φ : L₀ →+* L) (ψ : chartRing K₀ ({t₀⁻¹} : Set L₀) →+* chartRing K ({t⁻¹} : Set L))
    (hφψ : ∀ a : chartRing K₀ ({t₀⁻¹} : Set L₀), φ (a : L₀) = (ψ a : L))
    (x : closedPoints (glued K t)) (hx : x.1 ∉ Set.range (ι₀ K t).base)
    (xb : XInf K t) (hxb : (ιInf K t).base xb = x.1)
    (y : closedPoints (glued K₀ t₀)) (hy : y.1 ∉ Set.range (ι₀ K₀ t₀).base)
    (yb : XInf K₀ t₀) (hyb : (ιInf K₀ t₀).base yb = y.1)
    (h : yb.asIdeal = xb.asIdeal.comap ψ) :
    (gluedPlaceOfPoint K t ht x).toValuationSubring.toSubring.comap φ =
      (gluedPlaceOfPoint K₀ t₀ ht₀ y).toValuationSubring.toSubring := by
  rw [gluedPlaceOfPoint_of_not_mem K t ht x hx xb hxb, gluedPlaceOfPoint_of_not_mem K₀ t₀ ht₀ y hy yb hyb]
  exact Place.toSubring_ofHeightOneSpectrum_comap φ ψ hφψ _ _ h

theorem placeOfPoint_ofGenerator_iota0_comap'
    (K₀ : Type u) [Field K₀] {L₀ : Type u} [Field L₀] [Algebra K₀ L₀] (t₀ : L₀)
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)
    [CharZero K₀] [Fact (t₀ ≠ 0)] [FiniteDimensional K₀⟮t₀⟯ L₀] [FiniteDimensional K₀⟮t₀⁻¹⟯ L₀]
    [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    (ht₀ : Transcendental K₀ t₀) (ht : Transcendental K t)
    (φ : L₀ →+* L) (ψ : chartRing K₀ ({t₀} : Set L₀) →+* chartRing K ({t} : Set L))
    (hφψ : ∀ a : chartRing K₀ ({t₀} : Set L₀), φ (a : L₀) = (ψ a : L))
    (xb : X₀ K t) (hxb : (ι₀ K t).base xb ∈ closedPoints (CurveModel.ofGenerator K t ht).C)
    (yb : X₀ K₀ t₀) (hyb : (ι₀ K₀ t₀).base yb ∈ closedPoints (CurveModel.ofGenerator K₀ t₀ ht₀).C)
    (h : yb.asIdeal = xb.asIdeal.comap ψ) :
    ((CurveModel.ofGenerator K t ht).placeOfPoint ⟨(ι₀ K t).base xb, hxb⟩).toValuationSubring.toSubring.comap φ =
      ((CurveModel.ofGenerator K₀ t₀ ht₀).placeOfPoint ⟨(ι₀ K₀ t₀).base yb, hyb⟩).toValuationSubring.toSubring :=
  gluedPlaceOfPoint_ι₀_comap K₀ t₀ K t ht₀ ht φ ψ hφψ xb hxb yb hyb h

theorem placeOfPoint_ofGenerator_iotaInf_comap
    (K₀ : Type u) [Field K₀] {L₀ : Type u} [Field L₀] [Algebra K₀ L₀] (t₀ : L₀)
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)
    [CharZero K₀] [Fact (t₀ ≠ 0)] [FiniteDimensional K₀⟮t₀⟯ L₀] [FiniteDimensional K₀⟮t₀⁻¹⟯ L₀]
    [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    (ht₀ : Transcendental K₀ t₀) (ht : Transcendental K t)
    (φ : L₀ →+* L) (ψ : chartRing K₀ ({t₀⁻¹} : Set L₀) →+* chartRing K ({t⁻¹} : Set L))
    (hφψ : ∀ a : chartRing K₀ ({t₀⁻¹} : Set L₀), φ (a : L₀) = (ψ a : L))
    (x : closedPoints (CurveModel.ofGenerator K t ht).C) (hx : x.1 ∉ Set.range (ι₀ K t).base)
    (xb : XInf K t) (hxb : (ιInf K t).base xb = x.1)
    (y : closedPoints (CurveModel.ofGenerator K₀ t₀ ht₀).C) (hy : y.1 ∉ Set.range (ι₀ K₀ t₀).base)
    (yb : XInf K₀ t₀) (hyb : (ιInf K₀ t₀).base yb = y.1)
    (h : yb.asIdeal = xb.asIdeal.comap ψ) :
    ((CurveModel.ofGenerator K t ht).placeOfPoint x).toValuationSubring.toSubring.comap φ =
      ((CurveModel.ofGenerator K₀ t₀ ht₀).placeOfPoint y).toValuationSubring.toSubring :=
  gluedPlaceOfPoint_ιInf_comap K₀ t₀ K t ht₀ ht φ ψ hφψ x hx xb hxb y hy yb hyb h

end AlgebraicCurve.CurveModel

#print axioms AlgebraicCurve.CurveModel.placeOfPoint_ofGenerator_iotaInf_comap

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_CurveModel_placeOfPoint_ofGenerator_iota0_comap.AlgebraicCurve AlgebraicCurve.CurveModel P2MW.S_AlgebraicCurve_CurveModel_placeOfPoint_ofGenerator_iota0_comap.AlgebraicCurve.CurveModel"

theorem solution
    (K₀ : Type u) [Field K₀] {L₀ : Type u} [Field L₀] [Algebra K₀ L₀] (t₀ : L₀)
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)
    [CharZero K₀] [Fact (t₀ ≠ 0)] [FiniteDimensional K₀⟮t₀⟯ L₀] [FiniteDimensional K₀⟮t₀⁻¹⟯ L₀]
    [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    (ht₀ : Transcendental K₀ t₀) (ht : Transcendental K t)
    (φ : L₀ →+* L) (ψ : chartRing K₀ ({t₀} : Set L₀) →+* chartRing K ({t} : Set L))
    (hφψ : ∀ a : chartRing K₀ ({t₀} : Set L₀), φ (a : L₀) = (ψ a : L))
    (xb : X₀ K t) (hxb : (ι₀ K t).base xb ∈ closedPoints (CurveModel.ofGenerator K t ht).C)
    (yb : X₀ K₀ t₀) (hyb : (ι₀ K₀ t₀).base yb ∈ closedPoints (CurveModel.ofGenerator K₀ t₀ ht₀).C)
    (h : yb.asIdeal = xb.asIdeal.comap ψ) :
    ((CurveModel.ofGenerator K t ht).placeOfPoint ⟨(ι₀ K t).base xb, hxb⟩).toValuationSubring.toSubring.comap φ =
      ((CurveModel.ofGenerator K₀ t₀ ht₀).placeOfPoint ⟨(ι₀ K₀ t₀).base yb, hyb⟩).toValuationSubring.toSubring :=
  AlgebraicCurve.CurveModel.placeOfPoint_ofGenerator_iota0_comap' K₀ t₀ K t ht₀ ht φ ψ hφψ xb hxb yb hyb h

end S_AlgebraicCurve_CurveModel_placeOfPoint_ofGenerator_iota0_comap
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_placeOfPoint_ofGenerator_iota0_comap (solution)
