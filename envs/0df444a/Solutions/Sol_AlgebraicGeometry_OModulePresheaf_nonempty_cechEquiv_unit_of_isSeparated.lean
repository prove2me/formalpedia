-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_unit_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/1e3332aa-1940-502a-8c71-e9899e23cfb2

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_unit_of_isSeparated
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U"

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace P2mCovindUnit

scoped instance opensMapFinal {X Y : Scheme.{u}} (f : X ⟶ Y) : (TopologicalSpace.Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

noncomputable def pullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  haveI h : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := inferInstance
  @asIso _ _ _ _ _ h

theorem unit_eq_ofModules {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) :
    OModulePresheaf.unit π = OModulePresheaf.ofModules π (SheafOfModules.unit V.ringCatSheaf) :=
  rfl

end P2mCovindUnit
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_unit_of_isSeparated.P2mCovindUnit"

open P2mCovindUnit in
theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π]
    (K K' : V.OrderedAffineCover) :
    Nonempty ((OModulePresheaf.unit π).H0 K ≃ₗ[R] (OModulePresheaf.unit π).H0 K') ∧
      ∀ i : ℕ, Nonempty ((OModulePresheaf.unit π).HSucc K i ≃ₗ[R] (OModulePresheaf.unit π).HSucc K' i) := by
  have hq : (OModulePresheaf.ofModules π (SheafOfModules.unit V.ringCatSheaf)).IsQuasicoherent :=
    OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial π _
      (fun x => ⟨⊤, trivial, ⟨pullbackUnitIso (⊤ : V.Opens).ι⟩⟩)
  rw [unit_eq_ofModules]
  exact OModulePresheaf.nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated π _ hq K K'

end S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_unit_of_isSeparated
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_unit_of_isSeparated (solution)
