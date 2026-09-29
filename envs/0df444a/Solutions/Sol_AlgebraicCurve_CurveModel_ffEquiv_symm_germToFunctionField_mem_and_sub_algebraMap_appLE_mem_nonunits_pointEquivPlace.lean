-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/f9cead00-72dd-5c6f-a5f1-4e016c8e38d1

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u v

namespace P2mValueAtPoint

open AlgebraicCurve IsLocalRing

variable {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]

theorem base_closedPoint_eq (M : CurveModel K L)
    (z : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) :
    z.1.base (closedPoint K) = (pointEquivClosedPoint M.toBase z).1 :=
  (pointEquivClosedPoint_apply_coe M.toBase z).symm

noncomputable def theta (M : CurveModel K L) (x : M.C) : M.C.presheaf.stalk x →+* L :=
  (M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp
    (algebraMap (M.C.presheaf.stalk x) M.C.functionField)

omit [IsAlgClosed K] in
theorem theta_germ (M : CurveModel K L) (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
    (x : M.C) (hx : x ∈ U) (s : Γ(M.C, U)) :
    theta M x ((M.C.presheaf.germ U x hx).hom s) = M.ffEquiv.symm ((M.C.germToFunctionField U).hom s) := by
  unfold theta
  simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, Function.comp_apply]
  congr 1
  rw [RingHom.algebraMap_toAlgebra]
  exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _

omit [IsAlgClosed K] in
theorem range_theta (M : CurveModel K L) (x : closedPoints M.C) :
    (theta M x.1).range = (M.placeOfPoint x).toValuationSubring.toSubring :=
  M.range_stalk_eq x

omit [IsAlgClosed K] in

theorem theta_mem_nonunits (M : CurveModel K L) (x : closedPoints M.C)
    (g : M.C.presheaf.stalk x.1) (hg : ¬ IsUnit g) :
    theta M x.1 g ∈ (M.placeOfPoint x).toValuationSubring.nonunits := by
  set P := M.placeOfPoint x
  have hrange := range_theta M x
  have hmem : ∀ t, theta M x.1 t ∈ P.toValuationSubring := fun t => by
    have : theta M x.1 t ∈ (theta M x.1).range := ⟨t, rfl⟩
    rw [hrange] at this
    exact this

  let θ' : M.C.presheaf.stalk x.1 →+* P.toValuationSubring :=
    (theta M x.1).codRestrict P.toValuationSubring.toSubring hmem
  have hsurj : Function.Surjective θ' := by
    intro a
    have ha : (a : L) ∈ (theta M x.1).range := by rw [hrange]; exact a.2
    obtain ⟨t, ht⟩ := ha
    exact ⟨t, Subtype.ext ht⟩
  haveI : IsLocalHom θ' := IsLocalHom.of_surjective θ' hsurj
  have hnu : ¬ IsUnit (θ' g) := fun h => hg (isUnit_of_map_unit θ' g h)
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  exact ⟨hmem g, (IsLocalRing.mem_maximalIdeal _).mpr hnu⟩

noncomputable def constSec (M : CurveModel K L) (c : K) (U : M.C.Opens) : Γ(M.C, U) :=
  (M.toBase.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)

omit [IsAlgClosed K] in
theorem germToFunctionField_constSec (M : CurveModel K L) (c : K) (U : M.C.Opens)
    [Nonempty (Scheme.Opens.toScheme U)] :
    (M.C.germToFunctionField U).hom (constSec M c U) = M.ffEquiv (algebraMap K L c) := by
  rw [M.ffEquiv_algebraMap]
  unfold constSec baseToFunctionField
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [Scheme.Hom.appLE, CommRingCat.hom_comp]
  simp only [RingHom.coe_comp, Function.comp_apply]
  erw [TopCat.Presheaf.germ_res_apply]
  rfl

omit [IsAlgClosed K] in
theorem appLE_constSec (M : CurveModel K L) (c : K) (U : M.C.Opens)
    (z : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) (hz : ⊤ ≤ z.1 ⁻¹ᵁ U) :
    (z.1.appLE U ⊤ hz).hom (constSec M c U) = (Scheme.ΓSpecIso (CommRingCat.of K)).inv c := by
  unfold constSec
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have h : (z.1 ≫ M.toBase).appLE ⊤ ⊤ (le_top) = 𝟙 _ := by
    rw [z.2]
    rw [Scheme.Hom.appLE]
    simp
  have : (z.1 ≫ M.toBase).appLE ⊤ ⊤ (show (⊤ : (Spec (CommRingCat.of K)).Opens) ≤ (z.1 ≫ M.toBase) ⁻¹ᵁ ⊤ from le_top) =
      (z.1 ≫ M.toBase).appLE ⊤ ⊤ le_top := rfl
  rw [h]
  rfl

theorem main (M : CurveModel K L) (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)] (s : Γ(M.C, U))
    (z : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) (hz : ⊤ ≤ z.1 ⁻¹ᵁ U) :
    M.ffEquiv.symm ((M.C.germToFunctionField U).hom s) ∈ (M.pointEquivPlace z).toValuationSubring ∧
    M.ffEquiv.symm ((M.C.germToFunctionField U).hom s) -
        algebraMap K L ((Scheme.ΓSpecIso (CommRingCat.of K)).hom ((z.1.appLE U ⊤ hz).hom s)) ∈
      (M.pointEquivPlace z).toValuationSubring.nonunits := by
  set x : closedPoints M.C := pointEquivClosedPoint M.toBase z with hxdef
  have hxz : z.1.base (closedPoint K) = x.1 := base_closedPoint_eq M z
  have hxU : x.1 ∈ U := by
    rw [← hxz]
    exact hz (Set.mem_univ (closedPoint K))
  have hP : M.pointEquivPlace z = M.placeOfPoint x := M.pointEquivPlace_apply z
  rw [hP]
  refine ⟨?_, ?_⟩
  · have h1 : M.ffEquiv.symm ((M.C.germToFunctionField U).hom s) = theta M x.1 ((M.C.presheaf.germ U x.1 hxU).hom s) :=
      (theta_germ M U x.1 hxU s).symm
    rw [h1]
    have : theta M x.1 ((M.C.presheaf.germ U x.1 hxU).hom s) ∈ (theta M x.1).range := ⟨_, rfl⟩
    rw [range_theta M x] at this
    exact this
  · set c : K := (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((z.1.appLE U ⊤ hz).hom s) with hc

    have hconst : algebraMap K L c = M.ffEquiv.symm ((M.C.germToFunctionField U).hom (constSec M c U)) := by
      rw [germToFunctionField_constSec, RingEquiv.symm_apply_apply]
    rw [hconst, ← map_sub, ← map_sub, ← theta_germ M U x.1 hxU]
    refine theta_mem_nonunits M x _ ?_

    intro hunit
    have hmem : x.1 ∈ M.C.basicOpen (s - constSec M c U) := (M.C.mem_basicOpen _ _ hxU).mpr hunit
    have hz0 : (z.1.appLE U ⊤ hz).hom (s - constSec M c U) = 0 := by
      rw [map_sub, appLE_constSec, hc, Iso.hom_inv_id_apply, sub_self]
    have hbo : (Spec (CommRingCat.of K)).basicOpen ((z.1.appLE U ⊤ hz).hom (s - constSec M c U)) =
        ⊤ ⊓ z.1 ⁻¹ᵁ M.C.basicOpen (s - constSec M c U) := Scheme.basicOpen_appLE _ _ _ _ _
    rw [hz0, Scheme.basicOpen_zero] at hbo
    have hpt : closedPoint K ∈ (⊤ ⊓ z.1 ⁻¹ᵁ M.C.basicOpen (s - constSec M c U) : (Spec (CommRingCat.of K)).Opens) := by
      refine ⟨Set.mem_univ _, ?_⟩
      show z.1.base (closedPoint K) ∈ M.C.basicOpen (s - constSec M c U)
      rw [hxz]
      exact hmem
    rw [← hbo] at hpt
    exact hpt

end P2mValueAtPoint

open AlgebraicCurve in
theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (M : CurveModel K L) (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)] (s : Γ(M.C, U))
    (z : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) (hz : ⊤ ≤ z.1 ⁻¹ᵁ U) :
    M.ffEquiv.symm (M.C.germToFunctionField U s) ∈ (M.pointEquivPlace z).toValuationSubring ∧
    M.ffEquiv.symm (M.C.germToFunctionField U s) -
        algebraMap K L ((Scheme.ΓSpecIso (CommRingCat.of K)).hom (z.1.appLE U ⊤ hz s)) ∈
      (M.pointEquivPlace z).toValuationSubring.nonunits :=
  P2mValueAtPoint.main M U s z hz

end S_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace (solution)
