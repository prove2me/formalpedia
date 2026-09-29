-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_shortExact_ker_module_tensor_of_isClosedImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/bae57a09-fa17-527c-834a-6e7577c16450

import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_epi_iff_locallySurjective
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_mono_whiskerLeft_moduleIota
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_shortExact_ker_module_tensor_of_isClosedImmersion
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_shortExact_ker_module_tensor_of_isClosedImmersion.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Modules.pushforwardCongr Scheme.Modules.pushforward Scheme.Modules.pushforwardComp Scheme.Modules.pullback Scheme.Modules.presheaf Scheme.Modules.pushforwardId Scheme.Modules.Hom Scheme Scheme.IdealSheafData.ker_subschemeι IsClosedImmersion Scheme.Modules.pullbackCongr IsClosedImmersion.lift IsClosedImmersion.lift_fac Scheme.Modules.pullbackPushforwardAdjunction Scheme.isBasis_affineOpens isClosedImmersion_iff_isAffineHom Scheme.Modules Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsLocallyFreeOfRank Scheme.Modules.Hom.epi_iff_locallySurjective Scheme.Modules.nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Modules.pushforwardCongr ringCatSheaf Modules.pushforward Modules.pushforwardComp Modules.pullback Hom mk Modules.presheaf Modules.pushforwardId Modules.Hom IdealSheafData.ker_subschemeι Modules.pullbackCongr Modules.pullbackPushforwardAdjunction isBasis_affineOpens Modules Opens IdealSheafData Modules.pullbackComp Modules.IsLocallyFreeOfRank Modules.Hom.epi_iff_locallySurjective Modules.nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion" namespace IdealSheafData p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "mk map subscheme ker_subschemeι map_comp inclusion subschemeι module moduleι mono_whiskerLeft_moduleIota" end AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.IdealSheafData
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData" in

private noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.uMod {X : Scheme.{u}} (I : X.IdealSheafData) :
    ((𝟙_ X.Modules : X.Modules) ⟶
      ((Scheme.Modules.pushforward I.subschemeι).obj (𝟙_ I.subscheme.Modules) : X.Modules)) :=
  I.subschemeι.unitToPushforwardUnit

end AlgebraicGeometry.Scheme.IdealSheafData
p2m_export "" "AlgebraicGeometry.Scheme.IdealSheafData.uMod"
namespace AlgebraicGeometry.Scheme.IdealSheafData
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData" in
private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.moduleι_comp_uMod {X : Scheme.{u}} (I : X.IdealSheafData) :
    I.moduleι ≫ I.uMod = 0 :=
  kernel.condition I.subschemeι.unitToPushforwardUnit

end AlgebraicGeometry.Scheme.IdealSheafData
p2m_export "" "AlgebraicGeometry.Scheme.IdealSheafData.moduleι_comp_uMod"
namespace AlgebraicGeometry.Scheme.IdealSheafData
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData" in

private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.mono_moduleι' {X : Scheme.{u}} (I : X.IdealSheafData) :
    Mono I.moduleι :=
  ⟨fun g g' w => (cancel_mono (kernel.ι I.subschemeι.unitToPushforwardUnit)).mp w⟩

end AlgebraicGeometry.Scheme.IdealSheafData
p2m_export "" "AlgebraicGeometry.Scheme.IdealSheafData.mono_moduleι'"
namespace AlgebraicGeometry.Scheme.IdealSheafData
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData" in
private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.epi_uMod
    {X : Scheme.{u}} (I : X.IdealSheafData) : Epi I.uMod := by
  refine (AlgebraicGeometry.Scheme.Modules.Hom.epi_iff_locallySurjective _).mpr ?_
  intro U s x hxU
  obtain ⟨V, hV, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)) hxU
  refine ⟨V, hVU, hxV, ?_⟩
  have hsurj := (isClosedImmersion_iff_isAffineHom.mp (inferInstance : IsClosedImmersion I.subschemeι)).2 V hV
  obtain ⟨a, ha⟩ := hsurj ((Scheme.Modules.presheaf ((SheafOfModules.pushforward I.subschemeι.toRingCatSheafHom).obj
    (SheafOfModules.unit I.subscheme.ringCatSheaf))).map (homOfLE hVU).op s)
  exact ⟨a, ha⟩

end AlgebraicGeometry.Scheme.IdealSheafData
p2m_export "" "AlgebraicGeometry.Scheme.IdealSheafData.epi_uMod"
namespace AlgebraicGeometry.Scheme.IdealSheafData
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData" in

private noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.unitSeq {X : Scheme.{u}} (I : X.IdealSheafData) :
    ShortComplex X.Modules :=
  ShortComplex.mk I.moduleι I.uMod I.moduleι_comp_uMod

end AlgebraicGeometry.Scheme.IdealSheafData
p2m_export "" "AlgebraicGeometry.Scheme.IdealSheafData.unitSeq"
namespace AlgebraicGeometry.Scheme.IdealSheafData
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData" in
private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.shortExact_unitSeq
    {X : Scheme.{u}} (I : X.IdealSheafData) : I.unitSeq.ShortExact := by
  haveI := I.epi_uMod
  haveI := I.mono_moduleι'
  refine ShortComplex.ShortExact.mk' ?_ (by change Mono I.moduleι; infer_instance) (by change Epi I.uMod; infer_instance)
  exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel I.subschemeι.unitToPushforwardUnit)

end AlgebraicGeometry.Scheme.IdealSheafData
p2m_export "" "AlgebraicGeometry.Scheme.IdealSheafData.shortExact_unitSeq"
namespace AlgebraicGeometry.Scheme.IdealSheafData
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData" in

private noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.tensorSeq {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (F ◁ I.moduleι) (F ◁ I.uMod)
    (by
      change (tensorLeft F).map _ ≫ (tensorLeft F).map _ = 0
      rw [← Functor.map_comp, I.moduleι_comp_uMod]
      exact Functor.map_zero _ _ _)

end AlgebraicGeometry.Scheme.IdealSheafData
p2m_export "" "AlgebraicGeometry.Scheme.IdealSheafData.tensorSeq"
namespace AlgebraicGeometry.Scheme.IdealSheafData
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData" in
private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.shortExact_tensorSeq {X : Scheme.{u}} (I : X.IdealSheafData)
    {n : ℕ} (F : X.Modules) (hF : Scheme.Modules.IsLocallyFreeOfRank n F) :
    (I.tensorSeq F).ShortExact := by
  haveI := I.mono_whiskerLeft_moduleIota F hF
  haveI := I.epi_uMod
  let G : X.Modules ⥤ X.Modules := tensorLeft F

  have hcok : IsColimit (CokernelCofork.ofπ (I.tensorSeq F).g (I.tensorSeq F).zero) := by
    have h0 := I.shortExact_unitSeq.gIsCokernel
    have h1 := CokernelCofork.mapIsColimit _ h0 G
    refine IsColimit.ofIsoColimit h1 (Cofork.ext (Iso.refl _) ?_)
    erw [Category.comp_id]
    rfl
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ hcok) ?_ ?_
  · change Mono (F ◁ I.moduleι); infer_instance
  · change Epi ((tensorLeft F).map I.uMod); infer_instance

end AlgebraicGeometry.Scheme.IdealSheafData
p2m_export "" "AlgebraicGeometry.Scheme.IdealSheafData.shortExact_tensorSeq"
namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pushforwardCongr Scheme.Modules.pushforward Scheme.Modules.pushforwardComp Scheme.Modules.pullback Scheme.Modules.presheaf Scheme.Modules.pushforwardId Scheme.Modules.Hom Scheme Scheme.IdealSheafData.ker_subschemeι IsClosedImmersion Scheme.Modules.pullbackCongr IsClosedImmersion.lift IsClosedImmersion.lift_fac Scheme.Modules.pullbackPushforwardAdjunction Scheme.isBasis_affineOpens isClosedImmersion_iff_isAffineHom Scheme.Modules Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsLocallyFreeOfRank Scheme.Modules.Hom.epi_iff_locallySurjective Scheme.Modules.nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pushforwardCongr ringCatSheaf Modules.pushforward Modules.pushforwardComp Modules.pullback Hom mk Modules.presheaf Modules.pushforwardId Modules.Hom IdealSheafData.ker_subschemeι Modules.pullbackCongr Modules.pullbackPushforwardAdjunction isBasis_affineOpens Modules Opens IdealSheafData Modules.pullbackComp Modules.IsLocallyFreeOfRank Modules.Hom.epi_iff_locallySurjective Modules.nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pushforwardCongr pushforward pushforwardComp pullback presheaf pushforwardId Hom pullbackCongr pullbackPushforwardAdjunction pullbackComp IsLocallyFreeOfRank Hom.epi_iff_locallySurjective nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

noncomputable def pushforwardPullbackObjIsoOfIsIso {Y Y' : Scheme.{u}} (φ : Y ⟶ Y') [IsIso φ] (N : Y'.Modules) :
    (Scheme.Modules.pushforward φ).obj ((Scheme.Modules.pullback φ).obj N) ≅ N := by
  let e₁ : Scheme.Modules.pushforward (inv φ) ⋙ Scheme.Modules.pushforward φ ≅ 𝟭 _ :=
    Scheme.Modules.pushforwardComp (inv φ) φ ≪≫ Scheme.Modules.pushforwardCongr (IsIso.inv_hom_id φ) ≪≫
      Scheme.Modules.pushforwardId Y'
  let e₂ : 𝟭 _ ≅ Scheme.Modules.pushforward φ ⋙ Scheme.Modules.pushforward (inv φ) :=
    (Scheme.Modules.pushforwardId Y).symm ≪≫ (Scheme.Modules.pushforwardCongr (IsIso.hom_inv_id φ)).symm ≪≫
      (Scheme.Modules.pushforwardComp φ (inv φ)).symm
  let adj : Scheme.Modules.pushforward (inv φ) ⊣ Scheme.Modules.pushforward φ :=
    (CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward (inv φ)) (Scheme.Modules.pushforward φ) e₁.symm e₂.symm).toAdjunction
  let e₃ : Scheme.Modules.pullback φ ≅ Scheme.Modules.pushforward (inv φ) :=
    (Scheme.Modules.pullbackPushforwardAdjunction φ).leftAdjointUniq adj
  exact (Scheme.Modules.pushforward φ).mapIso (e₃.app N) ≪≫ e₁.app N

noncomputable def pushforwardPullbackObjIsoOfFac {Z Z' X : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X) (e : Z ⟶ Z')
    [IsIso e] (fac : e ≫ i' = i) (F : X.Modules) :
    (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj F) ≅
      (Scheme.Modules.pushforward i').obj ((Scheme.Modules.pullback i').obj F) :=
  (Scheme.Modules.pushforwardCongr fac.symm).app _ ≪≫
    ((Scheme.Modules.pushforwardComp e i').symm.app _) ≪≫
    (Scheme.Modules.pushforward i').mapIso
      ((Scheme.Modules.pushforward e).mapIso
        (((Scheme.Modules.pullbackCongr fac.symm).app F) ≪≫ ((Scheme.Modules.pullbackComp e i').symm.app F)) ≪≫
        pushforwardPullbackObjIsoOfIsIso e _)

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry.Scheme.IdealSheafData _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_shortExact_ker_module_tensor_of_isClosedImmersion.AlgebraicGeometry.Scheme.IdealSheafData in
theorem solution {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] {n : ℕ} (F : X.Modules)
    (hF : Scheme.Modules.IsLocallyFreeOfRank n F) :
    ∃ S : ShortComplex X.Modules, S.ShortExact ∧
      Nonempty (S.X₁ ≅ i.ker.module ⊗ F) ∧ Nonempty (S.X₂ ≅ F) ∧
      Nonempty (S.X₃ ≅ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj F)) := by
  refine ⟨(i.ker).tensorSeq F, (i.ker).shortExact_tensorSeq F hF, ⟨β_ _ _⟩, ⟨ρ_ F⟩, ?_⟩

  let e : Z ⟶ i.ker.subscheme := IsClosedImmersion.lift i.ker.subschemeι i (by rw [Scheme.IdealSheafData.ker_subschemeι])
  have fac : e ≫ i.ker.subschemeι = i := IsClosedImmersion.lift_fac _ _ _
  let e' : i.ker.subscheme ⟶ Z := IsClosedImmersion.lift i i.ker.subschemeι (by rw [Scheme.IdealSheafData.ker_subschemeι])
  have fac' : e' ≫ i = i.ker.subschemeι := IsClosedImmersion.lift_fac _ _ _
  haveI : IsIso e := ⟨e', by rw [← cancel_mono i, Category.assoc, fac', fac, Category.id_comp],
    by rw [← cancel_mono i.ker.subschemeι, Category.assoc, fac, fac', Category.id_comp]⟩

  obtain ⟨epf⟩ := Scheme.Modules.nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion
    i.ker.subschemeι F hF
  exact ⟨β_ _ _ ≪≫ epf ≪≫ (Scheme.Modules.pushforwardPullbackObjIsoOfFac i i.ker.subschemeι e fac F).symm⟩

end S_AlgebraicGeometry_Scheme_Modules_exists_shortExact_ker_module_tensor_of_isClosedImmersion
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_shortExact_ker_module_tensor_of_isClosedImmersion (solution)
