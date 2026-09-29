-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/18b5017e-763e-592b-8838-e43415ef21b5

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule.AlgebraicGeometry.RelPicard NeronModelInfra"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension Scheme.IdealSheafData.one_eq_top Scheme.Hom Spec Scheme IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.IdealSheafData RelEffCartierDiv graphOver graphOver_snd RelEffCartierDiv.ofPoint Scheme.IdealSheafData.IsInvertible prodKerGraph prodKerGraph_eq_prod prodKerGraph_zero Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso pointsSubBasepointModule pointsSubBasepointModule_nil pointsSubBasepointModule_cons"
namespace TensorList
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

p2m_open "AlgebraicGeometry.RelPicard.Scheme AlgebraicGeometry.Scheme"

variable {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
  [IsSeparated a] [SmoothOfRelativeDimension 1 a]

noncomputable def shuffle {X : Scheme.{u}} (X₁ X₂ Y₁ Y₂ : X.Modules) :
    (X₁ ⊗ X₂) ⊗ (Y₁ ⊗ Y₂) ≅ (X₁ ⊗ Y₁) ⊗ (X₂ ⊗ Y₂) :=
  (α_ X₁ X₂ (Y₁ ⊗ Y₂)) ≪≫
    whiskerLeftIso X₁ ((α_ X₂ Y₁ Y₂).symm ≪≫ whiskerRightIso (β_ X₂ Y₁) Y₂ ≪≫ α_ Y₁ X₂ Y₂) ≪≫
    (α_ X₁ Y₁ (X₂ ⊗ Y₂)).symm

lemma isInvertible_ker (P : Spec (CommRingCat.of k) ⟶ A) (hP : P ≫ a = 𝟙 _) :
    (graphOver a P hP).ker.IsInvertible :=
by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd a (𝟙 _)) (graphOver a P hP) (graphOver_snd a P hP)

lemma isInvertible_prodKerGraph {r : ℕ} (P : Fin r → (Spec (CommRingCat.of k) ⟶ A)) (hP : ∀ i, P i ≫ a = 𝟙 _) :
    (prodKerGraph a P hP).IsInvertible := by
  induction r with
  | zero => rw [prodKerGraph_zero]; exact IdealSheafData.isInvertible_top
  | succ r ih =>
    rw [prodKerGraph_eq_prod, Fin.prod_univ_succ]
    exact (isInvertible_ker (P 0) (hP 0)).mul (ih (fun i => P i.succ) (fun i => hP i.succ))

lemma isInvertible_pow {X : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsInvertible) (n : ℕ) :
    (I ^ n).IsInvertible := by
  induction n with
  | zero => rw [pow_zero, Scheme.IdealSheafData.one_eq_top]; exact IdealSheafData.isInvertible_top
  | succ n ih => rw [pow_succ]; exact ih.mul hI

theorem main (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) {r : ℕ}
    (P : Fin r → (Spec (CommRingCat.of k) ⟶ A)) (hP : ∀ i, P i ≫ a = 𝟙 _) :
    Nonempty ((prodKerGraph a P hP).invModule ⊗ ((RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^ r).module ≅
      pointsSubBasepointModule (a := a) ε
        (List.ofFn fun i => (⟨P i, hP i⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a))) := by
  induction r with
  | zero =>
    have h1 : prodKerGraph a P hP = ⊤ := prodKerGraph_zero a P hP
    have h2 : (RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^ 0 = ⊤ := by rw [pow_zero, Scheme.IdealSheafData.one_eq_top]
    rw [List.ofFn_zero, pointsSubBasepointModule_nil, h1, h2]
    exact Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso IdealSheafData.isInvertible_top
  | succ r ih =>

    let I₀ := (graphOver a (P 0) (hP 0)).ker
    let J := prodKerGraph a (fun i => P i.succ) (fun i => hP i.succ)
    let Iε := (RelEffCartierDiv.ofPoint a ε.1 ε.2).I
    have hprod : prodKerGraph a P hP = I₀ * J := by
      simp only [I₀, J, prodKerGraph_eq_prod]
      rw [Fin.prod_univ_succ]
    have hpow : Iε ^ (r + 1) = Iε * Iε ^ r := pow_succ' Iε r
    have hI₀ : I₀.IsInvertible := isInvertible_ker (P 0) (hP 0)
    have hJ : J.IsInvertible := isInvertible_prodKerGraph _ _
    have hIε : Iε.IsInvertible := isInvertible_ker ε.1 ε.2
    have hIεr : (Iε ^ r).IsInvertible := isInvertible_pow hIε r
    obtain ⟨e₁⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor hI₀ hJ
    obtain ⟨e₂⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor hIε hIεr
    obtain ⟨e₃⟩ := ih (fun i => P i.succ) (fun i => hP i.succ)
    rw [List.ofFn_succ, pointsSubBasepointModule_cons]
    have c₁ : (prodKerGraph a P hP).invModule ≅ (I₀ * J).invModule := eqToIso (by rw [hprod])
    have c₂ : ((RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^ (r + 1)).module ≅ (Iε * Iε ^ r).module :=
      eqToIso (by rw [show (RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^ (r + 1) = Iε * Iε ^ r from hpow])
    exact ⟨(c₁ ⊗ᵢ c₂) ≪≫ (e₁ ⊗ᵢ e₂) ≪≫ shuffle _ _ _ _ ≪≫ whiskerLeftIso _ e₃⟩

end AlgebraicGeometry.RelPicard.TensorList

theorem solution
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) {r : ℕ}
    (P : Fin r → (Spec (CommRingCat.of k) ⟶ A)) (hP : ∀ i, P i ≫ a = 𝟙 _) :
    Nonempty ((prodKerGraph a P hP).invModule ⊗ ((RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^ r).module ≅
      pointsSubBasepointModule (a := a) ε
        (List.ofFn fun i => (⟨P i, hP i⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a))) :=
  AlgebraicGeometry.RelPicard.TensorList.main ε P hP

end S_AlgebraicGeometry_RelPicard_nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule (solution)
