-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.exists_map_ideal_eq_span_singleton_of_isInvertible_comap_of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a1675cbc-0ad0-5e35-980d-d695e8bc4e51

import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_map_ideal_eq_span_singleton_of_isInvertible_comap_of_isOpenImmersion

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GenInv

theorem mem_nonZeroDivisors_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) {g : R}
    (hg : g ∈ nonZeroDivisors R) : e g ∈ nonZeroDivisors S := by
  rw [mem_nonZeroDivisors_iff_right]
  intro s hs
  have : e.symm s * g = 0 := by
    apply e.injective
    rw [map_mul, e.apply_symm_apply, map_zero, hs]
  have h0 : e.symm s = 0 := (mem_nonZeroDivisors_iff_right.mp hg) _ this
  simpa using congrArg e h0

end GenInv

open GenInv in
theorem solution
    {X Y : Scheme.{u}} (φ : X ⟶ Y) [IsOpenImmersion φ] (J : Y.IdealSheafData)
    (hJ : (J.comap φ).IsInvertible) (x : X) :
    ∃ (U : Y.affineOpens) (hxU : φ.base x ∈ (U : Y.Opens)) (g : Γ(Y, U)), g ∈ J.ideal U ∧
      (J.ideal U).map (algebraMap Γ(Y, U) (Localization.AtPrime (U.2.primeIdealOf ⟨φ.base x, hxU⟩).asIdeal)) =
        Ideal.span {algebraMap Γ(Y, U) (Localization.AtPrime (U.2.primeIdealOf ⟨φ.base x, hxU⟩).asIdeal) g} ∧
      algebraMap Γ(Y, U) (Localization.AtPrime (U.2.primeIdealOf ⟨φ.base x, hxU⟩).asIdeal) g ∈
        nonZeroDivisors (Localization.AtPrime (U.2.primeIdealOf ⟨φ.base x, hxU⟩).asIdeal) := by
  classical
  obtain ⟨W, f, hxf, g', hg', hJg'⟩ := hJ x

  let W' : X.affineOpens := X.affineBasicOpen f
  let U : Y.affineOpens := ⟨φ ''ᵁ (W' : X.Opens), W'.2.image_of_isOpenImmersion φ⟩
  have hxU : φ.base x ∈ (U : Y.Opens) := ⟨x, hxf, rfl⟩

  let e : Γ(X, (W' : X.Opens)) ≃+* Γ(Y, (U : Y.Opens)) := ((φ.appIso (W' : X.Opens)).symm).commRingCatIsoToRingEquiv
  have hcomap : (J.comap φ).ideal W' = (J.ideal U).comap (φ.appIso (W' : X.Opens)).inv.hom :=
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion J φ W'
  have hJU : J.ideal U = Ideal.span {e g'} := by
    have h1 : J.ideal U = ((J.comap φ).ideal W').map (e : Γ(X, (W' : X.Opens)) →+* Γ(Y, (U : Y.Opens))) := by
      rw [hcomap, Ideal.map_comap_of_equiv]

      ext a
      simp only [Ideal.mem_comap]
      change a ∈ J.ideal U ↔ (φ.appIso (W' : X.Opens)).inv.hom ((φ.appIso (W' : X.Opens)).hom.hom a) ∈ J.ideal U
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
    rw [h1, hJg', Ideal.map_span, Set.image_singleton]
    rfl
  refine ⟨U, hxU, e g', ?_, ?_, ?_⟩
  · rw [hJU]; exact Ideal.mem_span_singleton_self _
  · rw [hJU, Ideal.map_span, Set.image_singleton]
  · haveI : IsLocalization.AtPrime (Localization.AtPrime (U.2.primeIdealOf ⟨φ.base x, hxU⟩).asIdeal)
        (U.2.primeIdealOf ⟨φ.base x, hxU⟩).asIdeal := inferInstance
    exact IsLocalization.nonZeroDivisors_le_comap (M := (U.2.primeIdealOf ⟨φ.base x, hxU⟩).asIdeal.primeCompl)
      (S := Localization.AtPrime (U.2.primeIdealOf ⟨φ.base x, hxU⟩).asIdeal) (mem_nonZeroDivisors_of_ringEquiv e hg')

end S_AlgebraicGeometry_Scheme_IdealSheafData_exists_map_ideal_eq_span_singleton_of_isInvertible_comap_of_isOpenImmersion
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_map_ideal_eq_span_singleton_of_isInvertible_comap_of_isOpenImmersion (solution)
