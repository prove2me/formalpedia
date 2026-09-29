-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.nonempty_iso_unit_of_ne_zero_section_dual_slice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/59e3e5eb-ff3c-5f7b-ad4b-78f266a95125

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_unit_of_ne_zero_section_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_nonempty_iso_unit_of_ne_zero_section_dual_slice
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace FibreCritSlice

theorem comp_iso_hom_ne_zero {C : Type*} [Category C] [HasZeroMorphisms C] {P Q R : C} {t : P ⟶ Q} (ht : t ≠ 0) (e : Q ≅ R) :
    t ≫ e.hom ≠ 0 := fun h => ht (by rw [← Category.comp_id t, ← e.hom_inv_id, ← Category.assoc, h, zero_comp])

theorem iso_hom_comp_ne_zero {C : Type*} [Category C] [HasZeroMorphisms C] {P Q R : C} {t : Q ⟶ R} (ht : t ≠ 0) (e : P ≅ Q) :
    e.hom ≫ t ≠ 0 := fun h => ht (by rw [← Category.id_comp t, ← e.inv_hom_id, Category.assoc, h, comp_zero])

theorem faithful_pullback_of_isIso {X Y : Scheme.{0}} (e : X ⟶ Y) [IsIso e] : (Scheme.Modules.pullback e).Faithful := by
  have i : Scheme.Modules.pullback e ⋙ Scheme.Modules.pullback (inv e) ≅ 𝟭 _ :=
    Scheme.Modules.pullbackComp (inv e) e ≪≫ Scheme.Modules.pullbackCongr (by simp) ≪≫ Scheme.Modules.pullbackId Y
  exact Functor.Faithful.of_comp_iso i

end FibreCritSlice

open FibreCritSlice in
theorem solution
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (M : (pullback f (𝟙 (Spec (CommRingCat.of k)))).Modules) (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ _ ⟶ M) (s' : 𝟙_ _ ⟶ Scheme.Modules.dual M) (hs : s ≠ 0) (hs' : s' ≠ 0) :
    Nonempty (M ≅ 𝟙_ (pullback f (𝟙 (Spec (CommRingCat.of k)))).Modules) := by
  classical
  let P : Scheme.{0} := pullback f (𝟙 (Spec (CommRingCat.of k)))
  let π : P ⟶ A := pullback.fst f (𝟙 (Spec (CommRingCat.of k)))
  haveI : IsIso π := inferInstance
  let ρ : A ⟶ P := inv π
  let G := Scheme.Modules.pullback ρ
  haveI : G.Faithful := faithful_pullback_of_isIso ρ
  let M' : A.Modules := G.obj M
  have hM' : Scheme.Modules.IsInvertible M' := hM.pullback ρ

  let uA : G.obj (𝟙_ P.Modules) ≅ 𝟙_ A.Modules := Scheme.Modules.pullbackTensorUnitObjIso ρ
  have hGs : G.map s ≠ 0 := fun h => hs ((G.map_eq_zero_iff).1 h)
  let s₁ : 𝟙_ A.Modules ⟶ M' := uA.inv ≫ G.map s
  have hs₁ : s₁ ≠ 0 := iso_hom_comp_ne_zero hGs uA.symm

  obtain ⟨eD⟩ := hM.pullback_dual_monoidalV2 ρ
  have hGs' : G.map s' ≠ 0 := fun h => hs' ((G.map_eq_zero_iff).1 h)
  let s₁' : 𝟙_ A.Modules ⟶ Scheme.Modules.dual M' := uA.inv ≫ G.map s' ≫ eD.hom
  have hs₁' : s₁' ≠ 0 := by
    have h1 : G.map s' ≫ eD.hom ≠ 0 := comp_iso_hom_ne_zero hGs' eD
    exact iso_hom_comp_ne_zero h1 uA.symm
  obtain ⟨e'⟩ := GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_unit_of_ne_zero_section_dual L hA M' hM' s₁ s₁' hs₁ hs₁'

  have hπρ : π ≫ ρ = 𝟙 P := IsIso.hom_inv_id π
  refine ⟨?_⟩
  calc M ≅ (Scheme.Modules.pullback (𝟙 P)).obj M := ((Scheme.Modules.pullbackId P).app M).symm
    _ ≅ (Scheme.Modules.pullback (π ≫ ρ)).obj M := ((Scheme.Modules.pullbackCongr hπρ).app M).symm
    _ ≅ (Scheme.Modules.pullback π).obj (G.obj M) := ((Scheme.Modules.pullbackComp π ρ).app M).symm
    _ ≅ (Scheme.Modules.pullback π).obj (𝟙_ A.Modules) := (Scheme.Modules.pullback π).mapIso e'
    _ ≅ 𝟙_ P.Modules := Scheme.Modules.pullbackTensorUnitObjIso π

end
end S_AlgebraicGeometry_Polarisation_nonempty_iso_unit_of_ne_zero_section_dual_slice
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_nonempty_iso_unit_of_ne_zero_section_dual_slice (solution)
