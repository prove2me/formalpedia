-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_normModule_forall_map_eq_norm_smul_of_isFrameOn_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/2eeee922-778d-5142-9efb-4afd72ccd611

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isFrameOn_normModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isFrameOn_sheafificationAdjunction_unit_iotaMulti
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_dual_eq_of_ihomEval_eq
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_forall_map_eq_norm_smul_of_isFrameOn_preimage

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_forall_map_eq_norm_smul_of_isFrameOn_preimage.AlgebraicGeometry Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pushforward Scheme.Hom Scheme Scheme.Hom.preimage_mono Scheme.Modules Scheme.Modules.IsFrameOn.exists_isFrameOn_normModule Scheme.Modules.dual Scheme.Modules.tensorSections Scheme.Modules.tensorSections_smul_left Scheme.Modules.tensorSections_smul_right Scheme.Modules.map_homOfLE_tensorSections Scheme.Modules.unitSection Scheme.Modules.map_unitSection Scheme.Modules.IsFrameOn Scheme.Modules.ihomEval Scheme.Modules.map_ihomEval Scheme.Modules.ihomEval_smul_left Scheme.Modules.ihomEval_smul_right Scheme.Modules.presheafExteriorPower Scheme.Modules.det Scheme.Modules.normModule Scheme.Modules.sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul Scheme.Modules.isFrameOn_sheafificationAdjunction_unit_iotaMulti Scheme.Modules.IsFrameOn.dual_eq_of_ihomEval_eq"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pushforward Hom Γ Hom.preimage_mono Modules Opens PresheafOfModules Modules.IsFrameOn.exists_isFrameOn_normModule Modules.dual Modules.tensorSections Modules.tensorSections_smul_left Modules.tensorSections_smul_right Modules.map_homOfLE_tensorSections Modules.unitSection Modules.map_unitSection Modules.IsFrameOn Modules.ihomEval Modules.map_ihomEval Modules.ihomEval_smul_left Modules.ihomEval_smul_right Modules.presheafExteriorPower Modules.det Modules.normModule Modules.sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul Modules.isFrameOn_sheafificationAdjunction_unit_iotaMulti Modules.IsFrameOn.dual_eq_of_ihomEval_eq"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pushforward presheaf Hom map_smul IsFrameOn.exists_isFrameOn_normModule dual tensorSections tensorSections_smul_left tensorSections_smul_right map_homOfLE_tensorSections unitSection map_unitSection IsFrameOn ihomEval map_ihomEval ihomEval_smul_left ihomEval_smul_right presheafExteriorPower exteriorPower det normModule sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul isFrameOn_sheafificationAdjunction_unit_iotaMulti IsFrameOn.dual_eq_of_ihomEval_eq"
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
    {X Y : Scheme.{u}} (π : Y ⟶ X) (d : ℕ) {ι : Type u} (U : ι → X.Opens)

    (e : ∀ i, Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), U i))
    (he : ∀ (i : ι) (W : X.Opens) (hW : W ≤ U i),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), W),
        ∀ k, b k = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e i k))

    (L : Y.Modules) (s : ∀ i, Γ(L, π ⁻¹ᵁ U i)) (hs : ∀ i, Scheme.Modules.IsFrameOn (s i) (π ⁻¹ᵁ U i))
    (u : ∀ i j, Γ(Y, π ⁻¹ᵁ (U i ⊓ U j)))
    (hu : ∀ i j, L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π inf_le_right)).op (s j) =
      u i j • L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π inf_le_left)).op (s i)) :
    ∃ Ω : ∀ i, Γ(Scheme.Modules.normModule π d L, U i),
      (∀ i, Scheme.Modules.IsFrameOn (Ω i) (U i)) ∧
      ∀ i j, letI : Algebra Γ(X, U i ⊓ U j) Γ(Y, π ⁻¹ᵁ (U i ⊓ U j)) := (π.app (U i ⊓ U j)).hom.toAlgebra
        (Scheme.Modules.normModule π d L).presheaf.map (homOfLE inf_le_right).op (Ω j) =
          (Algebra.norm Γ(X, U i ⊓ U j) (u i j)) •
            (Scheme.Modules.normModule π d L).presheaf.map (homOfLE inf_le_left).op (Ω i) := by

  choose q hq hqev hΩ using fun i =>
    Scheme.Modules.IsFrameOn.exists_isFrameOn_normModule π d (L := L) (e i) (he i) (hs i)
  refine ⟨_, hΩ, ?_⟩
  intro i0 j0
  letI : Algebra Γ(X, U i0 ⊓ U j0) Γ(Y, π ⁻¹ᵁ (U i0 ⊓ U j0)) := (π.app (U i0 ⊓ U j0)).hom.toAlgebra

  let E : X.Modules := (Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)
  let P : X.Modules := (Scheme.Modules.pushforward π).obj L
  have hW0 : (U i0) ⊓ (U j0) ≤ (U i0) := inf_le_left
  have hW1 : (U i0) ⊓ (U j0) ≤ (U j0) := inf_le_right

  let e₀' : Fin d → Γ(E, (U i0) ⊓ (U j0)) := fun i => E.presheaf.map (homOfLE hW0).op ((e i0) i)
  let e₁' : Fin d → Γ(E, (U i0) ⊓ (U j0)) := fun i => E.presheaf.map (homOfLE hW1).op ((e j0) i)
  obtain ⟨b₀, hb₀⟩ := (he i0) ((U i0) ⊓ (U j0)) hW0
  obtain ⟨b₁, hb₁⟩ := (he j0) ((U i0) ⊓ (U j0)) hW1
  have hb₀' : ∀ i, b₀ i = e₀' i := hb₀
  have hb₁' : ∀ i, b₁ i = e₁' i := hb₁

  let a : Matrix (Fin d) (Fin d) Γ(X, (U i0) ⊓ (U j0)) := fun i j => b₀.repr (e₁' j) i
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

  let s₀' : Γ(L, π ⁻¹ᵁ ((U i0) ⊓ (U j0))) := L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π hW0)).op (s i0)
  let s₁' : Γ(L, π ⁻¹ᵁ ((U i0) ⊓ (U j0))) := L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π hW1)).op (s j0)
  have hs' : s₁' = (u i0 j0) • s₀' := (hu i0 j0)
  let f₀ : Fin d → Γ(P, (U i0) ⊓ (U j0)) := fun i =>
    (show Γ(P, (U i0) ⊓ (U j0)) from (show Γ(Y, π ⁻¹ᵁ ((U i0) ⊓ (U j0))) from e₀' i) • s₀')
  let f₁ : Fin d → Γ(P, (U i0) ⊓ (U j0)) := fun i =>
    (show Γ(P, (U i0) ⊓ (U j0)) from (show Γ(Y, π ⁻¹ᵁ ((U i0) ⊓ (U j0))) from e₁' i) • s₁')

  let c : Matrix (Fin d) (Fin d) Γ(X, (U i0) ⊓ (U j0)) := fun i j =>
    b₀.repr (show Γ(E, (U i0) ⊓ (U j0)) from (show Γ(Y, π ⁻¹ᵁ ((U i0) ⊓ (U j0))) from e₁' j) * (u i0 j0)) i
  have hc : ∀ j, f₁ j = ∑ i, c i j • f₀ i := by
    intro j
    have hsum : (show Γ(E, (U i0) ⊓ (U j0)) from (show Γ(Y, π ⁻¹ᵁ ((U i0) ⊓ (U j0))) from e₁' j) * (u i0 j0)) =
        ∑ i, c i j • e₀' i := by
      conv_lhs => rw [← b₀.sum_repr
        (show Γ(E, (U i0) ⊓ (U j0)) from (show Γ(Y, π ⁻¹ᵁ ((U i0) ⊓ (U j0))) from e₁' j) * (u i0 j0))]
      exact Finset.sum_congr rfl fun i _ => by rw [hb₀']
    have h1 : f₁ j = (show Γ(P, (U i0) ⊓ (U j0)) from
        ((show Γ(Y, π ⁻¹ᵁ ((U i0) ⊓ (U j0))) from e₁' j) * (u i0 j0)) • s₀') := by
      change (show Γ(Y, π ⁻¹ᵁ ((U i0) ⊓ (U j0))) from e₁' j) • s₁' = _
      rw [hs', smul_smul]
    rw [h1]
    have h2 : (show Γ(P, (U i0) ⊓ (U j0)) from ((show Γ(Y, π ⁻¹ᵁ ((U i0) ⊓ (U j0))) from e₁' j) * (u i0 j0)) • s₀') =
        (show Γ(P, (U i0) ⊓ (U j0)) from
          (show Γ(Y, π ⁻¹ᵁ ((U i0) ⊓ (U j0))) from (∑ i, c i j • e₀' i : Γ(E, (U i0) ⊓ (U j0)))) • s₀') := by
      rw [← hsum]
    rw [h2]
    change (show Γ(L, π ⁻¹ᵁ ((U i0) ⊓ (U j0))) from
        (show Γ(Y, π ⁻¹ᵁ ((U i0) ⊓ (U j0))) from (∑ i, c i j • e₀' i : Γ(E, (U i0) ⊓ (U j0)))) • s₀') =
      ∑ i, (π.app ((U i0) ⊓ (U j0))).hom (c i j) • ((show Γ(Y, π ⁻¹ᵁ ((U i0) ⊓ (U j0))) from e₀' i) • s₀')
    have h3 : (show Γ(Y, π ⁻¹ᵁ ((U i0) ⊓ (U j0))) from (∑ i, c i j • e₀' i : Γ(E, (U i0) ⊓ (U j0)))) =
        ∑ i, (π.app ((U i0) ⊓ (U j0))).hom (c i j) * (show Γ(Y, π ⁻¹ᵁ ((U i0) ⊓ (U j0))) from e₀' i) := rfl
    rw [h3, Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => mul_smul _ _ _
  have hcdet : c.det = Algebra.norm Γ(X, (U i0) ⊓ (U j0)) (u i0 j0) * a.det := by
    let bY : Module.Basis (Fin d) Γ(X, (U i0) ⊓ (U j0)) Γ(Y, π ⁻¹ᵁ ((U i0) ⊓ (U j0))) := b₀
    have hcm : c = Algebra.leftMulMatrix bY (u i0 j0) * a := by
      ext i j
      have hv := congrFun (Algebra.leftMulMatrix_mulVec_repr bY (u i0 j0)
        (show Γ(Y, π ⁻¹ᵁ ((U i0) ⊓ (U j0))) from e₁' j)) i
      rw [Matrix.mulVec, dotProduct] at hv
      change bY.repr ((show Γ(Y, π ⁻¹ᵁ ((U i0) ⊓ (U j0))) from e₁' j) * (u i0 j0)) i = _
      rw [mul_comm, ← hv, Matrix.mul_apply]
      rfl
    rw [hcm, Matrix.det_mul, Algebra.norm_eq_matrix_det bY]

  have hdetE : wedge E ((U i0) ⊓ (U j0)) e₁' = a.det • wedge E ((U i0) ⊓ (U j0)) e₀' :=
    Scheme.Modules.sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul e₀' e₁' a ha
  have hdetP : wedge P ((U i0) ⊓ (U j0)) f₁ = c.det • wedge P ((U i0) ⊓ (U j0)) f₀ :=
    Scheme.Modules.sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul f₀ f₁ c hc

  have hΩires : (Scheme.Modules.normModule π d L).presheaf.map (homOfLE hW0).op
      (Scheme.Modules.tensorSections (wedge P (U i0) (fun i =>
        (show Γ(P, (U i0)) from (show Γ(Y, π ⁻¹ᵁ (U i0)) from (e i0) i) • (s i0)))) (q i0)) =
      Scheme.Modules.tensorSections (wedge P ((U i0) ⊓ (U j0)) f₀)
        ((Scheme.Modules.dual (Scheme.Modules.det d E)).presheaf.map (homOfLE hW0).op (q i0)) := by
    change (Scheme.Modules.det d P ⊗ Scheme.Modules.dual (Scheme.Modules.det d E)).presheaf.map (homOfLE hW0).op
      (Scheme.Modules.tensorSections (wedge P (U i0) (fun i =>
        (show Γ(P, (U i0)) from (show Γ(Y, π ⁻¹ᵁ (U i0)) from (e i0) i) • (s i0)))) (q i0)) = _
    rw [Scheme.Modules.map_homOfLE_tensorSections, map_wedge]
    congr 2
    funext i
    exact L.val.map_smul (homOfLE (Scheme.Hom.preimage_mono π hW0)).op
      (show Γ(Y, π ⁻¹ᵁ (U i0)) from (e i0) i) (s i0)
  have hΩjres : (Scheme.Modules.normModule π d L).presheaf.map (homOfLE hW1).op
      (Scheme.Modules.tensorSections (wedge P (U j0) (fun i =>
        (show Γ(P, (U j0)) from (show Γ(Y, π ⁻¹ᵁ (U j0)) from (e j0) i) • (s j0)))) (q j0)) =
      Scheme.Modules.tensorSections (wedge P ((U i0) ⊓ (U j0)) f₁)
        ((Scheme.Modules.dual (Scheme.Modules.det d E)).presheaf.map (homOfLE hW1).op (q j0)) := by
    change (Scheme.Modules.det d P ⊗ Scheme.Modules.dual (Scheme.Modules.det d E)).presheaf.map (homOfLE hW1).op
      (Scheme.Modules.tensorSections (wedge P (U j0) (fun i =>
        (show Γ(P, (U j0)) from (show Γ(Y, π ⁻¹ᵁ (U j0)) from (e j0) i) • (s j0)))) (q j0)) = _
    rw [Scheme.Modules.map_homOfLE_tensorSections, map_wedge]
    congr 2
    funext i
    exact L.val.map_smul (homOfLE (Scheme.Hom.preimage_mono π hW1)).op
      (show Γ(Y, π ⁻¹ᵁ (U j0)) from (e j0) i) (s j0)

  have hq : (Scheme.Modules.dual (Scheme.Modules.det d E)).presheaf.map (homOfLE hW1).op (q j0) =
      ((↑w⁻¹ : Γ(X, (U i0) ⊓ (U j0)))) •
        (Scheme.Modules.dual (Scheme.Modules.det d E)).presheaf.map (homOfLE hW0).op (q i0) := by

    have hev₀ : Scheme.Modules.ihomEval (Scheme.Modules.det d E) (𝟙_ X.Modules) ((U i0) ⊓ (U j0))
        (wedge E ((U i0) ⊓ (U j0)) e₀')
        ((Scheme.Modules.dual (Scheme.Modules.det d E)).presheaf.map (homOfLE hW0).op (q i0)) =
        Scheme.Modules.unitSection ((U i0) ⊓ (U j0)) := by
      have := congrArg ((𝟙_ X.Modules).presheaf.map (homOfLE hW0).op) (hqev i0)
      erw [Scheme.Modules.map_ihomEval] at this
      rw [Scheme.Modules.map_unitSection] at this
      have hwd : (Scheme.Modules.det d E).presheaf.map (homOfLE hW0).op (wedge E (U i0) (e i0)) =
          wedge E ((U i0) ⊓ (U j0)) e₀' := map_wedge E hW0 (e i0)
      rw [← hwd]
      exact this
    have hev₁ : Scheme.Modules.ihomEval (Scheme.Modules.det d E) (𝟙_ X.Modules) ((U i0) ⊓ (U j0))
        (wedge E ((U i0) ⊓ (U j0)) e₁')
        ((Scheme.Modules.dual (Scheme.Modules.det d E)).presheaf.map (homOfLE hW1).op (q j0)) =
        Scheme.Modules.unitSection ((U i0) ⊓ (U j0)) := by
      have := congrArg ((𝟙_ X.Modules).presheaf.map (homOfLE hW1).op) (hqev j0)
      erw [Scheme.Modules.map_ihomEval] at this
      rw [Scheme.Modules.map_unitSection] at this
      have hwd : (Scheme.Modules.det d E).presheaf.map (homOfLE hW1).op (wedge E (U j0) (e j0)) =
          wedge E ((U i0) ⊓ (U j0)) e₁' := map_wedge E hW1 (e j0)
      rw [← hwd]
      exact this

    have he₁' : ∀ (W' : X.Opens) (hW' : W' ≤ (U i0) ⊓ (U j0)),
        ∃ b : Module.Basis (Fin d) Γ(X, W') Γ(E, W'), ∀ i, b i = E.presheaf.map (homOfLE hW').op (e₁' i) := by
      intro W' hW'
      obtain ⟨b, hb⟩ := (he j0) W' (hW'.trans hW1)
      refine ⟨b, fun i => ?_⟩
      rw [hb i]
      change _ = (E.presheaf.map (homOfLE hW1).op ≫ E.presheaf.map (homOfLE hW').op) ((e j0) i)
      rw [← CategoryTheory.Functor.map_comp]
      rfl
    have hfr : Scheme.Modules.IsFrameOn (M := Scheme.Modules.det d E) (wedge E ((U i0) ⊓ (U j0)) e₁')
        ((U i0) ⊓ (U j0)) :=
      Scheme.Modules.isFrameOn_sheafificationAdjunction_unit_iotaMulti e₁' he₁'
    refine Scheme.Modules.IsFrameOn.dual_eq_of_ihomEval_eq hfr le_rfl ?_
    have hid : (Scheme.Modules.det d E).presheaf.map (homOfLE (le_rfl : (U i0) ⊓ (U j0) ≤ (U i0) ⊓ (U j0))).op
        (wedge E ((U i0) ⊓ (U j0)) e₁') = wedge E ((U i0) ⊓ (U j0)) e₁' := by
      change (Scheme.Modules.det d E).presheaf.map (𝟙 (op ((U i0) ⊓ (U j0)))) (wedge E ((U i0) ⊓ (U j0)) e₁') = _
      rw [CategoryTheory.Functor.map_id]
      rfl
    rw [hid, hev₁, Scheme.Modules.ihomEval_smul_right, hdetE, Scheme.Modules.ihomEval_smul_left, hev₀,
      smul_smul, ← hw, Units.inv_mul, one_smul]

  change (Scheme.Modules.normModule π d L).presheaf.map (homOfLE hW1).op
      (Scheme.Modules.tensorSections (wedge P (U j0) (fun i =>
        (show Γ(P, (U j0)) from (show Γ(Y, π ⁻¹ᵁ (U j0)) from (e j0) i) • (s j0)))) (q j0)) =
    Algebra.norm Γ(X, (U i0) ⊓ (U j0)) (u i0 j0) •
      (Scheme.Modules.normModule π d L).presheaf.map (homOfLE hW0).op
        (Scheme.Modules.tensorSections (wedge P (U i0) (fun i =>
          (show Γ(P, (U i0)) from (show Γ(Y, π ⁻¹ᵁ (U i0)) from (e i0) i) • (s i0)))) (q i0))
  rw [hΩires, hΩjres, hq, hdetP, Scheme.Modules.tensorSections_smul_left,
    Scheme.Modules.tensorSections_smul_right, smul_smul, hcdet, mul_assoc, hw.symm, Units.mul_inv, mul_one]
  rfl

end S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_forall_map_eq_norm_smul_of_isFrameOn_preimage
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_forall_map_eq_norm_smul_of_isFrameOn_preimage (solution)
