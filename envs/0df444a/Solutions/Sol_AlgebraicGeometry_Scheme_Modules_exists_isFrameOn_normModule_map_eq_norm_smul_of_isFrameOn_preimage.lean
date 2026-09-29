-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_normModule_map_eq_norm_smul_of_isFrameOn_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/bffa3138-adf0-531f-a964-4f096ed07fe3

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isFrameOn_normModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isFrameOn_sheafificationAdjunction_unit_iotaMulti
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_dual_eq_of_ihomEval_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_map_eq_norm_smul_of_isFrameOn_preimage

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_map_eq_norm_smul_of_isFrameOn_preimage.AlgebraicGeometry Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pushforward Scheme.Hom Scheme Scheme.Hom.preimage_mono Scheme.Modules Scheme.Modules.dual Scheme.Modules.tensorSections Scheme.Modules.tensorSections_smul_left Scheme.Modules.tensorSections_smul_right Scheme.Modules.map_homOfLE_tensorSections Scheme.Modules.unitSection Scheme.Modules.map_unitSection Scheme.Modules.IsFrameOn Scheme.Modules.ihomEval Scheme.Modules.map_ihomEval Scheme.Modules.ihomEval_smul_left Scheme.Modules.ihomEval_smul_right Scheme.Modules.presheafExteriorPower Scheme.Modules.det Scheme.Modules.normModule Scheme.Modules.IsFrameOn.exists_isFrameOn_normModule Scheme.Modules.sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul Scheme.Modules.isFrameOn_sheafificationAdjunction_unit_iotaMulti Scheme.Modules.IsFrameOn.dual_eq_of_ihomEval_eq"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pushforward Hom Γ Hom.preimage_mono Modules Opens PresheafOfModules Modules.dual Modules.tensorSections Modules.tensorSections_smul_left Modules.tensorSections_smul_right Modules.map_homOfLE_tensorSections Modules.unitSection Modules.map_unitSection Modules.IsFrameOn Modules.ihomEval Modules.map_ihomEval Modules.ihomEval_smul_left Modules.ihomEval_smul_right Modules.presheafExteriorPower Modules.det Modules.normModule TwoAffineOpenCover Modules.IsFrameOn.exists_isFrameOn_normModule Modules.sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul Modules.isFrameOn_sheafificationAdjunction_unit_iotaMulti Modules.IsFrameOn.dual_eq_of_ihomEval_eq"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pushforward presheaf Hom map_smul dual tensorSections tensorSections_smul_left tensorSections_smul_right map_homOfLE_tensorSections unitSection map_unitSection IsFrameOn ihomEval map_ihomEval ihomEval_smul_left ihomEval_smul_right presheafExteriorPower exteriorPower det normModule IsFrameOn.exists_isFrameOn_normModule sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul isFrameOn_sheafificationAdjunction_unit_iotaMulti IsFrameOn.dual_eq_of_ihomEval_eq"
namespace NormCocycle
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

noncomputable def wedge (M : X.Modules) (V : X.Opens) {d : ℕ} (f : Fin d → Γ(M, V)) :
    Γ(Scheme.Modules.det d M, V) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      ((Scheme.Modules.presheafExteriorPower X d).obj M.val)).app (op V)
    (show ((Scheme.Modules.presheafExteriorPower X d).obj M.val).obj (op V) from
      exteriorPower.ιMulti Γ(X, V) d f)

theorem map_wedge (M : X.Modules) {V W : X.Opens} (h : W ≤ V) {d : ℕ} (f : Fin d → Γ(M, V)) :
    (Scheme.Modules.det d M).presheaf.map (homOfLE h).op (wedge M V f) =
      wedge M W (fun i => M.presheaf.map (homOfLE h).op (f i)) := by
  unfold wedge
  have nat := PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      ((Scheme.Modules.presheafExteriorPower X d).obj M.val)) (homOfLE h).op
    (show ((Scheme.Modules.presheafExteriorPower X d).obj M.val).obj (op V) from
      exteriorPower.ιMulti Γ(X, V) d f)
  erw [← nat]
  congr 1
  exact PresheafOfModules.exteriorPower_map_ιMulti d M.val (homOfLE h).op f

end AlgebraicGeometry.Scheme.Modules.NormCocycle

open AlgebraicGeometry.Scheme.Modules.NormCocycle in
set_option maxHeartbeats 6400000 in
theorem solution
    {X Y : Scheme.{u}} (π : Y ⟶ X) (d : ℕ) (𝒰 : X.TwoAffineOpenCover)
    (e₀ : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), 𝒰.U0))
    (he₀ : ∀ (W : X.Opens) (hW : W ≤ 𝒰.U0),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e₀ i))
    (e₁ : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), 𝒰.U1))
    (he₁ : ∀ (W : X.Opens) (hW : W ≤ 𝒰.U1),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e₁ i))
    (L : Y.Modules) (s₀ : Γ(L, π ⁻¹ᵁ 𝒰.U0)) (s₁ : Γ(L, π ⁻¹ᵁ 𝒰.U1))
    (hs₀ : Scheme.Modules.IsFrameOn s₀ (π ⁻¹ᵁ 𝒰.U0)) (hs₁ : Scheme.Modules.IsFrameOn s₁ (π ⁻¹ᵁ 𝒰.U1))
    (u : Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)))
    (hs : L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π inf_le_right)).op s₁ =
      u • L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π inf_le_left)).op s₀) :
    letI : Algebra Γ(X, 𝒰.U0 ⊓ 𝒰.U1) Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) := (π.app (𝒰.U0 ⊓ 𝒰.U1)).hom.toAlgebra
    ∃ (Ω₀ : Γ(Scheme.Modules.normModule π d L, 𝒰.U0)) (Ω₁ : Γ(Scheme.Modules.normModule π d L, 𝒰.U1)),
      Scheme.Modules.IsFrameOn Ω₀ 𝒰.U0 ∧ Scheme.Modules.IsFrameOn Ω₁ 𝒰.U1 ∧
      (Scheme.Modules.normModule π d L).presheaf.map (homOfLE inf_le_right).op Ω₁ =
        (Algebra.norm Γ(X, 𝒰.U0 ⊓ 𝒰.U1) u) •
          (Scheme.Modules.normModule π d L).presheaf.map (homOfLE inf_le_left).op Ω₀ := by

  obtain ⟨q₀, hq₀, hq₀ev, hΩ₀⟩ :=
    Scheme.Modules.IsFrameOn.exists_isFrameOn_normModule π d (L := L) e₀ he₀ hs₀
  obtain ⟨q₁, hq₁, hq₁ev, hΩ₁⟩ :=
    Scheme.Modules.IsFrameOn.exists_isFrameOn_normModule π d (L := L) e₁ he₁ hs₁
  refine ⟨_, _, hΩ₀, hΩ₁, ?_⟩
  letI : Algebra Γ(X, 𝒰.U0 ⊓ 𝒰.U1) Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) := (π.app (𝒰.U0 ⊓ 𝒰.U1)).hom.toAlgebra

  let E : X.Modules := (Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)
  let P : X.Modules := (Scheme.Modules.pushforward π).obj L
  have hW0 : 𝒰.U0 ⊓ 𝒰.U1 ≤ 𝒰.U0 := inf_le_left
  have hW1 : 𝒰.U0 ⊓ 𝒰.U1 ≤ 𝒰.U1 := inf_le_right

  let e₀' : Fin d → Γ(E, 𝒰.U0 ⊓ 𝒰.U1) := fun i => E.presheaf.map (homOfLE hW0).op (e₀ i)
  let e₁' : Fin d → Γ(E, 𝒰.U0 ⊓ 𝒰.U1) := fun i => E.presheaf.map (homOfLE hW1).op (e₁ i)
  obtain ⟨b₀, hb₀⟩ := he₀ (𝒰.U0 ⊓ 𝒰.U1) hW0
  obtain ⟨b₁, hb₁⟩ := he₁ (𝒰.U0 ⊓ 𝒰.U1) hW1
  have hb₀' : ∀ i, b₀ i = e₀' i := hb₀
  have hb₁' : ∀ i, b₁ i = e₁' i := hb₁

  let a : Matrix (Fin d) (Fin d) Γ(X, 𝒰.U0 ⊓ 𝒰.U1) := fun i j => b₀.repr (e₁' j) i
  have ha : ∀ j, e₁' j = ∑ i, a i j • e₀' i := by
    intro j
    conv_lhs => rw [← b₀.sum_repr (e₁' j)]
    exact Finset.sum_congr rfl fun i _ => by rw [hb₀']
  have hadet : IsUnit a.det := by
    have hab : a = b₀.toMatrix b₁ := by
      ext i j
      simp only [a, Module.Basis.toMatrix_apply, hb₁']
    rw [hab, ← Module.Basis.det_apply]
    exact b₀.isUnit_det b₁
  obtain ⟨w, hw⟩ := hadet

  let s₀' : Γ(L, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) := L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π hW0)).op s₀
  let s₁' : Γ(L, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) := L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π hW1)).op s₁
  have hs' : s₁' = u • s₀' := hs
  let f₀ : Fin d → Γ(P, 𝒰.U0 ⊓ 𝒰.U1) := fun i =>
    (show Γ(P, 𝒰.U0 ⊓ 𝒰.U1) from (show Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) from e₀' i) • s₀')
  let f₁ : Fin d → Γ(P, 𝒰.U0 ⊓ 𝒰.U1) := fun i =>
    (show Γ(P, 𝒰.U0 ⊓ 𝒰.U1) from (show Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) from e₁' i) • s₁')

  let c : Matrix (Fin d) (Fin d) Γ(X, 𝒰.U0 ⊓ 𝒰.U1) := fun i j =>
    b₀.repr (show Γ(E, 𝒰.U0 ⊓ 𝒰.U1) from (show Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) from e₁' j) * u) i
  have hc : ∀ j, f₁ j = ∑ i, c i j • f₀ i := by
    intro j
    have hsum : (show Γ(E, 𝒰.U0 ⊓ 𝒰.U1) from (show Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) from e₁' j) * u) =
        ∑ i, c i j • e₀' i := by
      conv_lhs => rw [← b₀.sum_repr
        (show Γ(E, 𝒰.U0 ⊓ 𝒰.U1) from (show Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) from e₁' j) * u)]
      exact Finset.sum_congr rfl fun i _ => by rw [hb₀']
    have h1 : f₁ j = (show Γ(P, 𝒰.U0 ⊓ 𝒰.U1) from
        ((show Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) from e₁' j) * u) • s₀') := by
      change (show Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) from e₁' j) • s₁' = _
      rw [hs', smul_smul]
    rw [h1]
    have h2 : (show Γ(P, 𝒰.U0 ⊓ 𝒰.U1) from ((show Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) from e₁' j) * u) • s₀') =
        (show Γ(P, 𝒰.U0 ⊓ 𝒰.U1) from
          (show Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) from (∑ i, c i j • e₀' i : Γ(E, 𝒰.U0 ⊓ 𝒰.U1))) • s₀') := by
      rw [← hsum]
    rw [h2]
    change (show Γ(L, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) from
        (show Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) from (∑ i, c i j • e₀' i : Γ(E, 𝒰.U0 ⊓ 𝒰.U1))) • s₀') =
      ∑ i, (π.app (𝒰.U0 ⊓ 𝒰.U1)).hom (c i j) • ((show Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) from e₀' i) • s₀')
    have h3 : (show Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) from (∑ i, c i j • e₀' i : Γ(E, 𝒰.U0 ⊓ 𝒰.U1))) =
        ∑ i, (π.app (𝒰.U0 ⊓ 𝒰.U1)).hom (c i j) * (show Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) from e₀' i) := rfl
    rw [h3, Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => mul_smul _ _ _
  have hcdet : c.det = Algebra.norm Γ(X, 𝒰.U0 ⊓ 𝒰.U1) u * a.det := by
    let bY : Module.Basis (Fin d) Γ(X, 𝒰.U0 ⊓ 𝒰.U1) Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) := b₀
    have hcm : c = Algebra.leftMulMatrix bY u * a := by
      ext i j
      have hv := congrFun (Algebra.leftMulMatrix_mulVec_repr bY u
        (show Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) from e₁' j)) i
      rw [Matrix.mulVec, dotProduct] at hv
      change bY.repr ((show Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) from e₁' j) * u) i = _
      rw [mul_comm, ← hv, Matrix.mul_apply]
      rfl
    rw [hcm, Matrix.det_mul, Algebra.norm_eq_matrix_det bY]

  have hdetE : wedge E (𝒰.U0 ⊓ 𝒰.U1) e₁' = a.det • wedge E (𝒰.U0 ⊓ 𝒰.U1) e₀' :=
    Scheme.Modules.sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul e₀' e₁' a ha
  have hdetP : wedge P (𝒰.U0 ⊓ 𝒰.U1) f₁ = c.det • wedge P (𝒰.U0 ⊓ 𝒰.U1) f₀ :=
    Scheme.Modules.sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul f₀ f₁ c hc

  have hΩ₀res : (Scheme.Modules.normModule π d L).presheaf.map (homOfLE hW0).op
      (Scheme.Modules.tensorSections (wedge P 𝒰.U0 (fun i =>
        (show Γ(P, 𝒰.U0) from (show Γ(Y, π ⁻¹ᵁ 𝒰.U0) from e₀ i) • s₀))) q₀) =
      Scheme.Modules.tensorSections (wedge P (𝒰.U0 ⊓ 𝒰.U1) f₀)
        ((Scheme.Modules.dual (Scheme.Modules.det d E)).presheaf.map (homOfLE hW0).op q₀) := by
    change (Scheme.Modules.det d P ⊗ Scheme.Modules.dual (Scheme.Modules.det d E)).presheaf.map (homOfLE hW0).op
      (Scheme.Modules.tensorSections (wedge P 𝒰.U0 (fun i =>
        (show Γ(P, 𝒰.U0) from (show Γ(Y, π ⁻¹ᵁ 𝒰.U0) from e₀ i) • s₀))) q₀) = _
    rw [Scheme.Modules.map_homOfLE_tensorSections, map_wedge]
    congr 2
    funext i
    exact L.val.map_smul (homOfLE (Scheme.Hom.preimage_mono π hW0)).op
      (show Γ(Y, π ⁻¹ᵁ 𝒰.U0) from e₀ i) s₀
  have hΩ₁res : (Scheme.Modules.normModule π d L).presheaf.map (homOfLE hW1).op
      (Scheme.Modules.tensorSections (wedge P 𝒰.U1 (fun i =>
        (show Γ(P, 𝒰.U1) from (show Γ(Y, π ⁻¹ᵁ 𝒰.U1) from e₁ i) • s₁))) q₁) =
      Scheme.Modules.tensorSections (wedge P (𝒰.U0 ⊓ 𝒰.U1) f₁)
        ((Scheme.Modules.dual (Scheme.Modules.det d E)).presheaf.map (homOfLE hW1).op q₁) := by
    change (Scheme.Modules.det d P ⊗ Scheme.Modules.dual (Scheme.Modules.det d E)).presheaf.map (homOfLE hW1).op
      (Scheme.Modules.tensorSections (wedge P 𝒰.U1 (fun i =>
        (show Γ(P, 𝒰.U1) from (show Γ(Y, π ⁻¹ᵁ 𝒰.U1) from e₁ i) • s₁))) q₁) = _
    rw [Scheme.Modules.map_homOfLE_tensorSections, map_wedge]
    congr 2
    funext i
    exact L.val.map_smul (homOfLE (Scheme.Hom.preimage_mono π hW1)).op
      (show Γ(Y, π ⁻¹ᵁ 𝒰.U1) from e₁ i) s₁

  have hq : (Scheme.Modules.dual (Scheme.Modules.det d E)).presheaf.map (homOfLE hW1).op q₁ =
      ((↑w⁻¹ : Γ(X, 𝒰.U0 ⊓ 𝒰.U1))) •
        (Scheme.Modules.dual (Scheme.Modules.det d E)).presheaf.map (homOfLE hW0).op q₀ := by

    have hev₀ : Scheme.Modules.ihomEval (Scheme.Modules.det d E) (𝟙_ X.Modules) (𝒰.U0 ⊓ 𝒰.U1)
        (wedge E (𝒰.U0 ⊓ 𝒰.U1) e₀')
        ((Scheme.Modules.dual (Scheme.Modules.det d E)).presheaf.map (homOfLE hW0).op q₀) =
        Scheme.Modules.unitSection (𝒰.U0 ⊓ 𝒰.U1) := by
      have := congrArg ((𝟙_ X.Modules).presheaf.map (homOfLE hW0).op) hq₀ev
      erw [Scheme.Modules.map_ihomEval] at this
      rw [Scheme.Modules.map_unitSection] at this
      have hwd : (Scheme.Modules.det d E).presheaf.map (homOfLE hW0).op (wedge E 𝒰.U0 e₀) =
          wedge E (𝒰.U0 ⊓ 𝒰.U1) e₀' := map_wedge E hW0 e₀
      rw [← hwd]
      exact this
    have hev₁ : Scheme.Modules.ihomEval (Scheme.Modules.det d E) (𝟙_ X.Modules) (𝒰.U0 ⊓ 𝒰.U1)
        (wedge E (𝒰.U0 ⊓ 𝒰.U1) e₁')
        ((Scheme.Modules.dual (Scheme.Modules.det d E)).presheaf.map (homOfLE hW1).op q₁) =
        Scheme.Modules.unitSection (𝒰.U0 ⊓ 𝒰.U1) := by
      have := congrArg ((𝟙_ X.Modules).presheaf.map (homOfLE hW1).op) hq₁ev
      erw [Scheme.Modules.map_ihomEval] at this
      rw [Scheme.Modules.map_unitSection] at this
      have hwd : (Scheme.Modules.det d E).presheaf.map (homOfLE hW1).op (wedge E 𝒰.U1 e₁) =
          wedge E (𝒰.U0 ⊓ 𝒰.U1) e₁' := map_wedge E hW1 e₁
      rw [← hwd]
      exact this

    have he₁' : ∀ (W' : X.Opens) (hW' : W' ≤ 𝒰.U0 ⊓ 𝒰.U1),
        ∃ b : Module.Basis (Fin d) Γ(X, W') Γ(E, W'), ∀ i, b i = E.presheaf.map (homOfLE hW').op (e₁' i) := by
      intro W' hW'
      obtain ⟨b, hb⟩ := he₁ W' (hW'.trans hW1)
      refine ⟨b, fun i => ?_⟩
      rw [hb i]
      change _ = (E.presheaf.map (homOfLE hW1).op ≫ E.presheaf.map (homOfLE hW').op) (e₁ i)
      rw [← CategoryTheory.Functor.map_comp]
      rfl
    have hfr : Scheme.Modules.IsFrameOn (M := Scheme.Modules.det d E) (wedge E (𝒰.U0 ⊓ 𝒰.U1) e₁')
        (𝒰.U0 ⊓ 𝒰.U1) :=
      Scheme.Modules.isFrameOn_sheafificationAdjunction_unit_iotaMulti e₁' he₁'
    refine Scheme.Modules.IsFrameOn.dual_eq_of_ihomEval_eq hfr le_rfl ?_
    have hid : (Scheme.Modules.det d E).presheaf.map (homOfLE (le_rfl : 𝒰.U0 ⊓ 𝒰.U1 ≤ 𝒰.U0 ⊓ 𝒰.U1)).op
        (wedge E (𝒰.U0 ⊓ 𝒰.U1) e₁') = wedge E (𝒰.U0 ⊓ 𝒰.U1) e₁' := by
      change (Scheme.Modules.det d E).presheaf.map (𝟙 (op (𝒰.U0 ⊓ 𝒰.U1))) (wedge E (𝒰.U0 ⊓ 𝒰.U1) e₁') = _
      rw [CategoryTheory.Functor.map_id]
      rfl
    rw [hid, hev₁, Scheme.Modules.ihomEval_smul_right, hdetE, Scheme.Modules.ihomEval_smul_left, hev₀,
      smul_smul, ← hw, Units.inv_mul, one_smul]

  change (Scheme.Modules.normModule π d L).presheaf.map (homOfLE hW1).op
      (Scheme.Modules.tensorSections (wedge P 𝒰.U1 (fun i =>
        (show Γ(P, 𝒰.U1) from (show Γ(Y, π ⁻¹ᵁ 𝒰.U1) from e₁ i) • s₁))) q₁) =
    Algebra.norm Γ(X, 𝒰.U0 ⊓ 𝒰.U1) u •
      (Scheme.Modules.normModule π d L).presheaf.map (homOfLE hW0).op
        (Scheme.Modules.tensorSections (wedge P 𝒰.U0 (fun i =>
          (show Γ(P, 𝒰.U0) from (show Γ(Y, π ⁻¹ᵁ 𝒰.U0) from e₀ i) • s₀))) q₀)
  rw [hΩ₀res, hΩ₁res, hq, hdetP, Scheme.Modules.tensorSections_smul_left,
    Scheme.Modules.tensorSections_smul_right, smul_smul, hcdet, mul_assoc, hw.symm, Units.mul_inv, mul_one]
  rfl

end S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_map_eq_norm_smul_of_isFrameOn_preimage
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_map_eq_norm_smul_of_isFrameOn_preimage (solution)
