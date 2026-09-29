-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_conj_app_top_one_eq_appTop
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/5bf21e1a-9d70-562f-b590-c54fd2afee93

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_conj_app_top_one_eq_appTop

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_conj_app_top_one_eq_appTop.AlgebraicGeometry Opposite TopologicalSpace"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Modules.pullback Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Scheme.Modules Scheme.Modules.pullbackUnitIso"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Modules.pullback Hom.id_app Hom Γ Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.id_app Modules.Hom.app Hom.comp_app Modules Opens Modules.pullbackUnitIso"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pullback presheaf Hom.comp_app Hom Hom.id_app Hom.app pullbackPushforwardAdjunction pullbackUnitIso"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

section conj

variable {S S' : Scheme.{u}} (p : S' ⟶ S)

noncomputable def unitConj
    (E : SheafOfModules.unit S.ringCatSheaf ≅ SheafOfModules.unit S.ringCatSheaf) :
    @Iso S'.Modules _ (SheafOfModules.unit S'.ringCatSheaf) (SheafOfModules.unit S'.ringCatSheaf) :=
  (pullbackUnitIso p).symm ≪≫ (pullback p).mapIso E ≪≫ pullbackUnitIso p

noncomputable def pls {L : S.Modules} {U : S.Opens} (s : Γ(L, U)) :
    Γ((pullback p).obj L, p ⁻¹ᵁ U) :=
  ((pullbackPushforwardAdjunction p).unit.app L).app U s

lemma pls_app {L L' : S.Modules} {U : S.Opens} (θ : L ⟶ L') (s : Γ(L, U)) :
    pls p (θ.app U s) = ((pullback p).map θ).app (p ⁻¹ᵁ U) (pls p s) := by
  have h := congrArg (fun k => Scheme.Modules.Hom.app k U s)
    ((pullbackPushforwardAdjunction p).unit.naturality θ)
  simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
    CategoryTheory.comp_apply] at h
  exact h

lemma pls_smul {L : S.Modules} {U : S.Opens} (r : Γ(S, U)) (s : Γ(L, U)) :
    pls p (r • s) = p.app U r • pls p s := by
  rw [pls, Scheme.Modules.Hom.app_smul]
  rfl

lemma app_pls {L : S.Modules} {N : S'.Modules} (g : (pullback p).obj L ⟶ N) {U : S.Opens} (s : Γ(L, U)) :
    g.app (p ⁻¹ᵁ U) (pls p s) =
      (((pullbackPushforwardAdjunction p).homEquiv L N g).app U s : Γ(N, p ⁻¹ᵁ U)) := by
  rw [Adjunction.homEquiv_unit]
  rfl

lemma pullbackUnitIso_hom_app_pls {U : S.Opens} (s : Γ(SheafOfModules.unit S.ringCatSheaf, U)) :
    (pullbackUnitIso p).hom.app (p ⁻¹ᵁ U) (pls p s) =
      (show Γ(SheafOfModules.unit S'.ringCatSheaf, p ⁻¹ᵁ U) from (p.app U).hom s) := by
  have h1 : (pullbackUnitIso p).hom =
      ((pullbackPushforwardAdjunction p).homEquiv _ _).symm
        (SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom) := rfl
  rw [h1, app_pls, Equiv.apply_symm_apply]
  rfl

lemma pullbackUnitIso_inv_app_one :
    (pullbackUnitIso p).inv.app ⊤ (1 : S'.presheaf.obj (op ⊤)) =
      (show Γ((pullback p).obj (SheafOfModules.unit S.ringCatSheaf), ⊤) from
        pls p (show Γ(SheafOfModules.unit S.ringCatSheaf, ⊤) from (1 : S.presheaf.obj (op ⊤)))) := by
  have hinj : Function.Injective ((pullbackUnitIso p).hom.app ⊤) := by
    intro x y hxy
    have := congrArg ((pullbackUnitIso p).inv.app ⊤) hxy
    simpa [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app] using this
  apply hinj
  have h2 := pullbackUnitIso_hom_app_pls p (U := ⊤)
    (show Γ(SheafOfModules.unit S.ringCatSheaf, ⊤) from (1 : S.presheaf.obj (op ⊤)))
  rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id, Scheme.Modules.Hom.id_app]
  refine (h2.trans ?_).symm
  exact map_one (p.app ⊤).hom

theorem unitConj_app_one (E : SheafOfModules.unit S.ringCatSheaf ≅ SheafOfModules.unit S.ringCatSheaf) :
    Scheme.Modules.Hom.app (unitConj p E).hom ⊤ (1 : S'.presheaf.obj (op ⊤)) =
      p.appTop.hom ((E.hom.val.app (op ⊤)).hom (1 : S.presheaf.obj (op ⊤))) := by
  set uE : S.presheaf.obj (op ⊤) := (E.hom.val.app (op ⊤)).hom (1 : S.presheaf.obj (op ⊤)) with huE
  simp only [unitConj, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Scheme.Modules.Hom.comp_app,
    CategoryTheory.comp_apply]
  rw [pullbackUnitIso_inv_app_one]
  change (pullbackUnitIso p).hom.app (p ⁻¹ᵁ ⊤)
      (((pullback p).map E.hom).app (p ⁻¹ᵁ ⊤)
        (pls p (show Γ(SheafOfModules.unit S.ringCatSheaf, ⊤) from (1 : S.presheaf.obj (op ⊤))))) = _
  rw [← pls_app]
  have hE : Scheme.Modules.Hom.app
        (E.hom : (SheafOfModules.unit S.ringCatSheaf : S.Modules) ⟶ (SheafOfModules.unit S.ringCatSheaf : S.Modules))
        ⊤ (show Γ(SheafOfModules.unit S.ringCatSheaf, ⊤) from (1 : S.presheaf.obj (op ⊤))) =
      uE • (show Γ(SheafOfModules.unit S.ringCatSheaf, ⊤) from (1 : S.presheaf.obj (op ⊤))) := by
    change uE = uE * 1
    exact (mul_one uE).symm
  rw [hE, pls_smul, Scheme.Modules.Hom.app_smul, pullbackUnitIso_hom_app_pls]
  change p.app ⊤ uE * p.app ⊤ 1 = _
  rw [map_one, mul_one]
  rfl

end conj

end AlgebraicGeometry.Scheme.Modules

theorem solution
    {S S' : Scheme.{u}} (p : S' ⟶ S)
    (e : SheafOfModules.unit S.ringCatSheaf ≅ SheafOfModules.unit S.ringCatSheaf) :
    ((((Scheme.Modules.pullbackUnitIso p).symm ≪≫ (Scheme.Modules.pullback p).mapIso e ≪≫
          Scheme.Modules.pullbackUnitIso p :
            SheafOfModules.unit S'.ringCatSheaf ≅ SheafOfModules.unit S'.ringCatSheaf)).hom.val.app (op ⊤)).hom
        (1 : S'.presheaf.obj (op ⊤)) =
      p.appTop.hom ((e.hom.val.app (op ⊤)).hom (1 : S.presheaf.obj (op ⊤))) :=
  AlgebraicGeometry.Scheme.Modules.unitConj_app_one p e

end S_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_conj_app_top_one_eq_appTop
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_conj_app_top_one_eq_appTop (solution)
