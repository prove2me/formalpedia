-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/05eb2d5f-c0b3-5fc3-bec3-9a53dcab6026

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Theorems.Thm_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_adicValuation_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.germToFunctionField SmoothOfRelativeDimension Scheme.Modules.presheaf Scheme.germToFunctionField_injective Spec IsIntegral Scheme IsAffineOpen Scheme.Modules"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "germToFunctionField ringCatSheaf Modules.presheaf germToFunctionField_injective Γ empty functionField Modules Opens"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf"
namespace UnitFF
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"
open AlgebraicCurve TopologicalSpace Opposite

variable {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]

noncomputable abbrev OU (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

omit [IsIntegral X] in

theorem smul_eq (U : X.Opens) (a : Γ(X, U)) (m : Γ(OU X, U)) :
    (show Γ(X, U) from a • m) = a * (show Γ(X, U) from m) := rfl

omit [IsIntegral X] in

theorem map_eq {U V : X.Opens} (h : V ≤ U) (m : Γ(OU X, U)) :
    (show Γ(X, V) from (OU X).presheaf.map (homOfLE h).op m) = X.presheaf.map (homOfLE h).op (show Γ(X, U) from m) :=
  rfl

noncomputable def φ (U : X.Opens) : Γ(OU X, U) →+ (X.functionField : Type u) :=
  open Classical in
  if h : Nonempty U then
    { toFun := fun m => (X.germToFunctionField U).hom (show Γ(X, U) from m)
      map_zero' := map_zero (X.germToFunctionField U).hom
      map_add' := fun m m' => map_add (X.germToFunctionField U).hom (show Γ(X, U) from m) (show Γ(X, U) from m') }
  else 0

theorem φ_apply (U : X.Opens) [h : Nonempty U] (m : Γ(OU X, U)) :
    φ U m = (X.germToFunctionField U).hom (show Γ(X, U) from m) := by
  simp only [φ, dif_pos h]
  rfl

theorem φ_nat {U V : X.Opens} (h : V ≤ U) [Nonempty U] [Nonempty V] (m : Γ(OU X, U)) :
    φ V ((OU X).presheaf.map (homOfLE h).op m) = φ U m := by
  rw [φ_apply, φ_apply, map_eq]
  show (X.presheaf.map (homOfLE h).op ≫ X.germToFunctionField V).hom _ = _
  unfold Scheme.germToFunctionField
  rw [TopCat.Presheaf.germ_res]

theorem φ_smul (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(OU X, U)) :
    φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m := by
  rw [φ_apply, φ_apply, smul_eq, map_mul]
  rfl

theorem φ_injective (U : X.Opens) [Nonempty U] : Function.Injective (φ (X := X) U) := by
  intro m m' h
  rw [φ_apply, φ_apply] at h
  exact Scheme.germToFunctionField_injective X U h

theorem range_φ [SmoothOfRelativeDimension 1 x] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (baseToFunctionField x).toAlgebra
    Set.range (φ (X := X) U) = (lSpaceOn (placesOf x U) (0 : Divisor K X.functionField) : Set X.functionField) := by
  letI := (baseToFunctionField x).toAlgebra
  have hsec := range_algebraMap_functionField_eq_iInf_of_isAffineOpen x U hU
  ext f
  have h1 : f ∈ Set.range (φ (X := X) U) ↔ f ∈ (algebraMap Γ(X, U) X.functionField).range := by
    simp only [Set.mem_range, RingHom.mem_range]
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨show Γ(X, U) from m, by rw [φ_apply]; rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨show Γ(OU X, U) from a, by rw [φ_apply]; rfl⟩
  rw [h1, hsec, SetLike.mem_coe, mem_lSpaceOn_iff]
  simp only [Subring.mem_iInf, Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
  constructor
  · intro hf v hv
    exact (Place.mem_iff_adicValuation_le_one v).mp (hf v hv)
  · intro hf v hv
    exact (Place.mem_iff_adicValuation_le_one v).mpr (hf v hv)

end AlgebraicGeometry.Scheme.Modules.UnitFF

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.germToFunctionField SmoothOfRelativeDimension Scheme.Modules.presheaf Scheme.germToFunctionField_injective Spec IsIntegral Scheme IsAffineOpen Scheme.Modules" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "germToFunctionField ringCatSheaf Modules.presheaf germToFunctionField_injective Γ empty functionField Modules Opens" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf" end AlgebraicGeometry.Scheme.Modules
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in
open AlgebraicGeometry.Scheme.Modules.UnitFF in

theorem AlgebraicGeometry.Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero'
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [SmoothOfRelativeDimension 1 x] :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ φ : ∀ U : X.Opens, Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U) →+ (X.functionField : Type u),
      (∀ (U : X.Opens) [Nonempty U] (m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)),
          φ U m = (X.germToFunctionField U).hom (show Γ(X, U) from m)) ∧
      (∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U),
            φ V ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf : X.Modules)).map (homOfLE h).op m)
              = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U)
            (0 : AlgebraicCurve.Divisor K X.functionField) : Set X.functionField)) := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  refine ⟨fun U => φ U, fun U _ m => φ_apply U m, ?_, fun U _ a m => φ_smul U a m,
    fun U hU => by haveI := hU; exact φ_injective U, fun U hU hne => by haveI := hne; exact range_φ x U hU⟩
  intro U V h hV m
  haveI := hV
  haveI : Nonempty U := let ⟨⟨z, hz⟩⟩ := hV; ⟨⟨z, h hz⟩⟩
  exact φ_nat h m

open AlgebraicGeometry.Scheme.Modules.UnitFF in
theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [SmoothOfRelativeDimension 1 x] :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ φ : ∀ U : X.Opens, Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U) →+ (X.functionField : Type u),
      (∀ (U : X.Opens) [Nonempty U] (m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)),
          φ U m = (X.germToFunctionField U).hom (show Γ(X, U) from m)) ∧
      (∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U),
            φ V ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf : X.Modules)).map (homOfLE h).op m)
              = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U)
            (0 : AlgebraicCurve.Divisor K X.functionField) : Set X.functionField)) :=
  AlgebraicGeometry.Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero' x

end S_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero (solution)
