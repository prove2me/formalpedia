-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_unit_pullbackUnitIso_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/fb0daf15-82be-5fa6-be1f-ce7d0947a87f

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unitAutSection_trans_and_unitAutSection_refl
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_unit_pullbackUnitIso_zero

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace UnitClassZero
p2m_open "AlgebraicGeometry.Scheme.Modules"

section coh
variable {T' T : Scheme.{u}}

lemma congr_unit_hom {f f' : T' ⟶ T} (H : f = f') :
    (pullbackCongr H).hom.app (SheafOfModules.unit T.ringCatSheaf) ≫ (pullbackUnitIso f').hom =
      (pullbackUnitIso f).hom := by
  subst H; simp [pullbackCongr]

lemma congr_unit_inv {f f' : T' ⟶ T} (H : f = f') :
    (pullbackCongr H).inv.app (SheafOfModules.unit T.ringCatSheaf) ≫ (pullbackUnitIso f).hom =
      (pullbackUnitIso f').hom := by
  subst H; simp [pullbackCongr]

lemma comp_inv_map_unit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullbackComp f g).inv.app (SheafOfModules.unit Z.ringCatSheaf) ≫
      (Scheme.Modules.pullback f).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso f).hom =
      (pullbackUnitIso (f ≫ g)).hom := by
  erw [← Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom f g]
  erw [Iso.inv_hom_id_app_assoc]

end coh

variable {X : Scheme.{u}}

noncomputable def canTriv (𝒰 : X.OrderedAffineCover) :
    CechTrivialisation 𝒰 (SheafOfModules.unit X.ringCatSheaf) := fun a => pullbackUnitIso (𝒰.U a).ι

lemma canTriv_restrict (𝒰 : X.OrderedAffineCover) {a : 𝒰.ι} {W : X.Opens} (h : W ≤ 𝒰.U a) :
    (canTriv 𝒰).restrict h = pullbackUnitIso W.ι := by
  apply Iso.ext
  change (pullbackCongr (X.homOfLE_ι h)).inv.app (SheafOfModules.unit X.ringCatSheaf) ≫
      (pullbackComp (X.homOfLE h) (𝒰.U a).ι).inv.app (SheafOfModules.unit X.ringCatSheaf) ≫
        (Scheme.Modules.pullback (X.homOfLE h)).map (pullbackUnitIso (𝒰.U a).ι).hom ≫
          (pullbackUnitIso (X.homOfLE h)).hom =
    (pullbackUnitIso W.ι).hom
  rw [comp_inv_map_unit]
  exact congr_unit_inv _

lemma uAS_eq_one_of_eq_refl {Y : Scheme.{u}} (W : Y.Opens)
    (e : SheafOfModules.unit ((W : Scheme.{u})).ringCatSheaf ≅ SheafOfModules.unit ((W : Scheme.{u})).ringCatSheaf)
    (h : e = Iso.refl _) : unitAutSection W e = 1 := by
  subst h
  exact (Scheme.Modules.unitAutSection_trans_and_unitAutSection_refl W).2

lemma uAS_symm_trans {Y : Scheme.{u}} (W : Y.Opens) {A : ((W : Scheme.{u})).Modules}
    (e : A ≅ SheafOfModules.unit ((W : Scheme.{u})).ringCatSheaf) :
    unitAutSection W (e.symm ≪≫ e) = 1 :=
  uAS_eq_one_of_eq_refl W _ (Iso.symm_self_id e)

lemma canTriv_transition (𝒰 : X.OrderedAffineCover) (s : 𝒰.Idx 1) : (canTriv 𝒰).transition s = 1 := by
  simp only [CechTrivialisation.transition, canTriv_restrict]
  exact uAS_symm_trans _ _

lemma canTriv_comap (𝒰 : X.OrderedAffineCover) {X₀ : Scheme.{u}} (g : X₀ ⟶ X) [IsAffineHom g] (a : 𝒰.ι) :
    (canTriv 𝒰).comap g a =
      (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).mapIso (pullbackUnitIso g) ≪≫
        pullbackUnitIso ((𝒰.comap g).U a).ι := by
  apply Iso.ext
  change (pullbackComp (g ⁻¹ᵁ 𝒰.U a).ι g).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
      (pullbackCongr (morphismRestrict_ι g (𝒰.U a)).symm).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
        (pullbackComp (g ∣_ 𝒰.U a) (𝒰.U a).ι).inv.app (SheafOfModules.unit X.ringCatSheaf) ≫
          (Scheme.Modules.pullback (g ∣_ 𝒰.U a)).map (pullbackUnitIso (𝒰.U a).ι).hom ≫
            (pullbackUnitIso (g ∣_ 𝒰.U a)).hom =
    (Scheme.Modules.pullback (g ⁻¹ᵁ 𝒰.U a).ι).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso (g ⁻¹ᵁ 𝒰.U a).ι).hom
  rw [comp_inv_map_unit, congr_unit_hom]
  exact Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom _ _

end UnitClassZero

theorem solution
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X X₀ Xk : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X) [IsAffineHom i]
    (g : X₀ ⟶ X) [IsAffineHom g] (𝒰 : X.OrderedAffineCover) :
    SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 (SheafOfModules.unit X.ringCatSheaf)
      (Scheme.Modules.pullbackUnitIso g) 0 := by
  refine ⟨UnitClassZero.canTriv 𝒰, fun _ => 1, fun _ => 1, fun _ => mul_one 1, fun a => ?_, fun s => ?_⟩
  ·
    rw [map_one, UnitClassZero.canTriv_comap]
    exact (UnitClassZero.uAS_symm_trans _ _).symm
  ·
    rw [UnitClassZero.canTriv_transition, map_one, map_one]
    refine ⟨0, fun _ => 0, fun _ => 0, ?_, fun ξ => ?_⟩
    · simp
    · simp only [LinearMap.comp_apply, map_zero, Finset.univ_eq_empty, Finset.sum_empty]
      rfl

end S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_unit_pullbackUnitIso_zero
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_unit_pullbackUnitIso_zero (solution)
