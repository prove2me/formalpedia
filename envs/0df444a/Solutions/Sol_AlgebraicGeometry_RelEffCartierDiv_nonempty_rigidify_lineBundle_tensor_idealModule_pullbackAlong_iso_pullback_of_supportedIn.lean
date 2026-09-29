-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.nonempty_rigidify_lineBundle_tensor_idealModule_pullbackAlong_iso_pullback_of_supportedIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/9004acc7-098f-51fd-8a00-f1e3a27ad8bc

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_nonempty_rigidify_lineBundle_tensor_idealModule_pullbackAlong_iso_pullback_of_supportedIn
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra"

namespace ENGINEprimeE2

theorem pullbackAlong_congr_hom {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {n : ℕ} {T T' : Scheme.{u}} {g : T ⟶ S}
    {g' : T' ⟶ S} (D : RelEffCartierDiv f n g') {φ₁ φ₂ : T ⟶ T'} (h : φ₁ = φ₂) (h₁ : φ₁ ≫ g' = g)
    (h₂ : φ₂ ≫ g' = g) : D.pullbackAlong φ₁ h₁ = D.pullbackAlong φ₂ h₂ := by
  subst h; rfl

end ENGINEprimeE2

open ENGINEprimeE2 in

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {ρ : ℕ} (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R)))) (hEU : E.SupportedIn U)
    {r : ℕ} {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (D : RelEffCartierDiv c r t) (hDU : D.SupportedIn U) :
    Nonempty (Scheme.Modules.rigidify (RelPicard.rigSection c t' ε) (pullback.snd c t')
          ((D.pullbackAlong ψ.1 ψ.2).lineBundle ⊗ (E.pullbackAlong t' (Category.comp_id t')).idealModule) ≅
      (Scheme.Modules.pullback (RelPicard.baseChangeSnd c ψ)).obj
        (Scheme.Modules.rigidify (RelPicard.rigSection c t ε) (pullback.snd c t)
          (D.lineBundle ⊗ (E.pullbackAlong t (Category.comp_id t)).idealModule))) := by

  let Ψ := RelPicard.baseChangeSnd c ψ
  let σ := RelPicard.rigSection c t ε
  let σ' := RelPicard.rigSection c t' ε

  have hσ : σ' ≫ Ψ = ψ.1 ≫ σ := RelPicard.rigSection_baseChangeSnd c ε ψ
  have hq : Ψ ≫ pullback.snd c t = pullback.snd c t' ≫ ψ.1 := by
    simp only [Ψ, RelPicard.baseChangeSnd, pullback.map, pullback.lift_snd]

  have hD : D.I.IsInvertible := RelEffCartierDiv.isInvertible_I_of_supportedIn U D hDU
  have hD' : (D.pullbackAlong ψ.1 ψ.2).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I_of_supportedIn U (D.pullbackAlong ψ.1 ψ.2) (hDU.pullbackAlong ψ.1 ψ.2)
  have hE : (E.pullbackAlong t (Category.comp_id t)).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I_of_supportedIn U _ (hEU.pullbackAlong t (Category.comp_id t))
  have hE' : (E.pullbackAlong t' (Category.comp_id t')).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I_of_supportedIn U _ (hEU.pullbackAlong t' (Category.comp_id t'))
  have hL : Scheme.Modules.IsInvertible (D.lineBundle ⊗ (E.pullbackAlong t (Category.comp_id t)).idealModule) :=
    hD.isInvertible_invModule.tensor hE.isInvertible_module

  obtain ⟨e₁⟩ := Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso
    (σ := σ) (q := pullback.snd c t) (σ' := σ') (q' := pullback.snd c t') ψ.1 Ψ hσ hq hL

  have hcomapD : (D.pullbackAlong ψ.1 ψ.2).I = D.I.comap Ψ := rfl
  obtain ⟨e₂⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Ψ hD (hcomapD ▸ hD')

  have hcomp : (E.pullbackAlong t (Category.comp_id t)).pullbackAlong ψ.1 ψ.2 =
      E.pullbackAlong t' (Category.comp_id t') :=
    (RelEffCartierDiv.pullbackAlong_comp _ _ _ _ _).trans (pullbackAlong_congr_hom E ψ.2 _ _)
  have hI : (E.pullbackAlong t' (Category.comp_id t')).I =
      (E.pullbackAlong t (Category.comp_id t)).I.comap Ψ := by
    rw [← hcomp]; rfl
  haveI := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Ψ hE (hI ▸ hE')
  let e₃ : (Scheme.Modules.pullback Ψ).obj (E.pullbackAlong t (Category.comp_id t)).idealModule ≅
      (E.pullbackAlong t' (Category.comp_id t')).idealModule :=
    asIso ((E.pullbackAlong t (Category.comp_id t)).I.pullbackModuleComparison Ψ) ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module hI).symm

  let eL : (Scheme.Modules.pullback Ψ).obj (D.lineBundle ⊗ (E.pullbackAlong t (Category.comp_id t)).idealModule) ≅
      (D.pullbackAlong ψ.1 ψ.2).lineBundle ⊗ (E.pullbackAlong t' (Category.comp_id t')).idealModule :=
    Scheme.Modules.pullbackTensorObjIso Ψ _ _ ≪≫ (e₂ ⊗ᵢ e₃)
  exact ⟨(Scheme.Modules.rigidifyMapIso σ' (pullback.snd c t') eL).symm ≪≫ e₁.symm⟩

end S_AlgebraicGeometry_RelEffCartierDiv_nonempty_rigidify_lineBundle_tensor_idealModule_pullbackAlong_iso_pullback_of_supportedIn
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_nonempty_rigidify_lineBundle_tensor_idealModule_pullbackAlong_iso_pullback_of_supportedIn (solution)
