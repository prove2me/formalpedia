-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.nonempty_invModule_prod_pow_tensor_module_prod_pow_iso_tensorUnit_of_arithProg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/de96dafe-1b4b-581e-acc5-3a50e24420c7

import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ev_app_tensorUnit
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_invModule_prod_pow_iso_tensorUnit_of_prod_pow_eq_zeroSchemeIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_invModule_prod_pow_tensor_module_prod_pow_iso_tensorUnit_of_arithProg
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_invModule_prod_pow_tensor_module_prod_pow_iso_tensorUnit_of_arithProg.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.IdealSheafData Scheme.Modules.zeroSchemeIdeal Scheme.Modules.IsInvertible Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "empty Modules IdealSheafData Modules.zeroSchemeIdeal Modules.IsInvertible Modules.IsInvertible.isIso_ev_app_tensorUnit"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "ideal module invModule IsInvertible isInvertible_top nonempty_invModule_prod_pow_iso_tensorUnit_of_prod_pow_eq_zeroSchemeIdeal"
namespace VertTriv
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {Y : Scheme.{u}}

theorem isInvertible_prod {ι : Type*} (s : Finset ι) (J : ι → Y.IdealSheafData)
    (hJ : ∀ i ∈ s, (J i).IsInvertible) : (∏ i ∈ s, J i).IsInvertible := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isInvertible_top : (⊤ : Y.IdealSheafData).IsInvertible)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hJ a (Finset.mem_insert_self a s)).mul (ih fun i hi => hJ i (Finset.mem_insert_of_mem hi))

theorem nonempty_invModule_mul_pow_iso {J E : Y.IdealSheafData} (hJ : J.IsInvertible)
    (hE : E.IsInvertible) (hEtriv : Nonempty (E.invModule ≅ 𝟙_ Y.Modules)) (m : ℕ) :
    Nonempty ((J * E ^ m).invModule ≅ J.invModule) := by
  induction m with
  | zero => rw [pow_zero, mul_one]; exact ⟨Iso.refl _⟩
  | succ m ih =>
    obtain ⟨e₁⟩ := ih
    obtain ⟨e₀⟩ := hEtriv
    obtain ⟨e₂⟩ := (hJ.mul (hE.pow m)).nonempty_mul_invModule_iso_tensor hE
    rw [pow_succ, ← mul_assoc]
    exact ⟨e₂ ≪≫ tensorIso e₁ e₀ ≪≫ ρ_ _⟩

theorem nonempty_invModule_tensor_module_iso {N : Y.IdealSheafData} (hN : N.IsInvertible) :
    Nonempty (N.invModule ⊗ N.module ≅ 𝟙_ Y.Modules) := by
  exact ⟨β_ _ _ ≪≫ (@asIso _ _ _ _ ((ihom.ev N.module).app (𝟙_ Y.Modules))
    (Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit hN.isInvertible_module) :
      N.module ⊗ N.invModule ≅ 𝟙_ Y.Modules)⟩

theorem prod_pow_add_add_mul {e : ℕ} (I : Fin (e + 1) → Y.IdealSheafData) (v : Fin (e + 1) → ℕ)
    (m n : ℕ) :
    ∏ k, I k ^ (v k + m + (k : ℕ) * n) = (∏ k, I k ^ v k) * (∏ k, I k) ^ m * (∏ k, I k ^ (k : ℕ)) ^ n := by
  rw [← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [pow_add, pow_add, pow_mul]

end AlgebraicGeometry.Scheme.IdealSheafData.VertTriv

open _root_.AlgebraicGeometry.Scheme.IdealSheafData _root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_invModule_prod_pow_tensor_module_prod_pow_iso_tensorUnit_of_arithProg.AlgebraicGeometry.Scheme.IdealSheafData in
theorem solution
    {Y : Scheme.{u}} {e : ℕ} (I : Fin (e + 1) → Y.IdealSheafData) (hI : ∀ k, (I k).IsInvertible)
    (ϖ w : 𝟙_ Y.Modules ⟶ 𝟙_ Y.Modules)
    (hϖ : ∏ k, I k = Scheme.Modules.zeroSchemeIdeal ϖ)
    (hw : ∏ k, I k ^ (k : ℕ) = Scheme.Modules.zeroSchemeIdeal w)
    (vp vn : Fin (e + 1) → ℕ) (a₀ d : ℤ)
    (hAP : ∀ k : Fin (e + 1), (vp k : ℤ) - (vn k : ℤ) = a₀ + ((k : ℕ) : ℤ) * d) :
    Nonempty ((∏ k, I k ^ vp k).invModule ⊗ (∏ k, I k ^ vn k).module ≅ 𝟙_ Y.Modules) := by
  classical

  set ap := a₀.toNat with hap
  set an := (-a₀).toNat with han
  set dp := d.toNat with hdp
  set dn := (-d).toNat with hdn
  have ha : a₀ = ap - an := by rw [hap, han]; omega
  have hd : d = dp - dn := by rw [hdp, hdn]; omega
  have hexp : ∀ k : Fin (e + 1), vp k + an + (k : ℕ) * dn = vn k + ap + (k : ℕ) * dp := by
    intro k
    have h := hAP k
    rw [ha, hd] at h
    have : ((vp k + an + (k : ℕ) * dn : ℕ) : ℤ) = ((vn k + ap + (k : ℕ) * dp : ℕ) : ℤ) := by
      push_cast
      linear_combination h
    exact_mod_cast this

  have hideal : (∏ k, I k ^ vp k) * (∏ k, I k) ^ an * (∏ k, I k ^ (k : ℕ)) ^ dn =
      (∏ k, I k ^ vn k) * (∏ k, I k) ^ ap * (∏ k, I k ^ (k : ℕ)) ^ dp := by
    rw [← VertTriv.prod_pow_add_add_mul, ← VertTriv.prod_pow_add_add_mul]
    exact Finset.prod_congr rfl fun k _ => by rw [hexp k]

  have hP : (∏ k, I k ^ vp k).IsInvertible :=
    VertTriv.isInvertible_prod _ _ fun k _ => (hI k).pow _
  have hN : (∏ k, I k ^ vn k).IsInvertible :=
    VertTriv.isInvertible_prod _ _ fun k _ => (hI k).pow _
  have hΦ : (∏ k, I k).IsInvertible := VertTriv.isInvertible_prod _ _ fun k _ => hI k
  have hΨ : (∏ k, I k ^ (k : ℕ)).IsInvertible :=
    VertTriv.isInvertible_prod _ _ fun k _ => (hI k).pow _

  have h1' : ∏ x : ULift.{u} (Fin (e + 1)), I x.down = ∏ k, I k :=
    Fintype.prod_equiv Equiv.ulift (fun x => I x.down) I (fun _ => rfl)
  have h2' : ∏ x : ULift.{u} (Fin (e + 1)), I x.down ^ (x.down : ℕ) = ∏ k, I k ^ (k : ℕ) :=
    Fintype.prod_equiv Equiv.ulift (fun x => I x.down ^ (x.down : ℕ)) (fun k => I k ^ (k : ℕ))
      (fun _ => rfl)
  have hΦtriv : Nonempty ((∏ k, I k).invModule ≅ 𝟙_ Y.Modules) := by
    have key := nonempty_invModule_prod_pow_iso_tensorUnit_of_prod_pow_eq_zeroSchemeIdeal
      (ι := ULift.{u} (Fin (e + 1))) (fun k => I k.down) (fun k => hI k.down) (fun _ => 1) ϖ
      (by simp only [pow_one]; rw [← hϖ]; exact h1')
    simp only [pow_one] at key
    rw [h1'] at key
    exact key
  have hΨtriv : Nonempty ((∏ k, I k ^ (k : ℕ)).invModule ≅ 𝟙_ Y.Modules) := by
    have key := nonempty_invModule_prod_pow_iso_tensorUnit_of_prod_pow_eq_zeroSchemeIdeal
      (ι := ULift.{u} (Fin (e + 1))) (fun k => I k.down) (fun k => hI k.down)
      (fun k => (k.down : ℕ)) w (by beta_reduce; rw [← hw]; exact h2')
    beta_reduce at key
    rw [h2'] at key
    exact key

  obtain ⟨eP₁⟩ := VertTriv.nonempty_invModule_mul_pow_iso hP hΦ hΦtriv an
  obtain ⟨eP₂⟩ := VertTriv.nonempty_invModule_mul_pow_iso (hP.mul (hΦ.pow an)) hΨ hΨtriv dn
  obtain ⟨eN₁⟩ := VertTriv.nonempty_invModule_mul_pow_iso hN hΦ hΦtriv ap
  obtain ⟨eN₂⟩ := VertTriv.nonempty_invModule_mul_pow_iso (hN.mul (hΦ.pow ap)) hΨ hΨtriv dp
  have ePN : Nonempty ((∏ k, I k ^ vp k).invModule ≅ (∏ k, I k ^ vn k).invModule) := by
    refine ⟨eP₁.symm ≪≫ eP₂.symm ≪≫ ?_ ≪≫ eN₂ ≪≫ eN₁⟩
    rw [hideal]
  obtain ⟨ePN⟩ := ePN
  obtain ⟨ev⟩ := VertTriv.nonempty_invModule_tensor_module_iso hN
  exact ⟨(ePN ⊗ᵢ Iso.refl _) ≪≫ ev⟩

end S_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_invModule_prod_pow_tensor_module_prod_pow_iso_tensorUnit_of_arithProg
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_invModule_prod_pow_tensor_module_prod_pow_iso_tensorUnit_of_arithProg (solution)
