-- Prove2me | Definitions.Def_Esgk_BridgeIdentity
-- name    : Esgk_BridgeIdentity
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:49:33.540994+00:00
-- url     : https://prove2.me/theorems/be636f9b-3dda-40b8-a25d-2c2c9a75547f
-- title:
--   Uniqueness of direct isometries with prescribed data
-- statement:
--   This records uniqueness of a direct linear isometry once its value on a nonzero vector is fixed, and of a direct affine isometry once its values at two distinct points are fixed. It also supplies the associated basis and coordinate identities.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_Energy
import Definitions.Def_Esgk_Foundation
import Definitions.Def_Esgk_PlanarGeneralPosition
import Definitions.Def_Esgk_RichnessLevels
import Definitions.Def_LeanFormalizations_Geometry_Euclidean_IsometryClassification
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Nat.Log
import Mathlib.Topology.MetricSpace.Isometry

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry
open Filter Topology
open scoped Pointwise Real InnerProductSpace EuclideanSpace

variable {n : ℕ}


local notation "o" => (positiveOrientation : Orientation ℝ ℝ² (Fin 2))

 
local notation "J" => Orientation.rightAngleRotation o


lemma direct_linearIsometryEquiv_eq_of_send_eq {u : ℝ²} (hu : u ≠ 0)
    {T₁ T₂ : ℝ² ≃ₗᵢ[ℝ] ℝ²}
    (h₁ : 0 < LinearMap.det (T₁.toLinearEquiv : ℝ² →ₗ[ℝ] ℝ²))
    (h₂ : 0 < LinearMap.det (T₂.toLinearEquiv : ℝ² →ₗ[ℝ] ℝ²))
    (huv : T₁ u = T₂ u) :
    T₁ = T₂ := by
  apply (o.basisRightAngleRotation u hu).ext_linearIsometryEquiv
  intro i
  have hcoe : ⇑(o.basisRightAngleRotation u hu) = ![u, J u] :=
    o.coe_basisRightAngleRotation u hu
   
   
  have hJ₁ : T₁ (J u) = J (T₁ u) :=
    o.linearIsometryEquiv_comp_rightAngleRotation T₁ h₁ u
  have hJ₂ : T₂ (J u) = J (T₂ u) :=
    o.linearIsometryEquiv_comp_rightAngleRotation T₂ h₂ u
  fin_cases i
  · change T₁ ((o.basisRightAngleRotation u hu) 0) =
      T₂ ((o.basisRightAngleRotation u hu) 0)
    rw [hcoe]
    simp [huv]
  · change T₁ ((o.basisRightAngleRotation u hu) 1) =
      T₂ ((o.basisRightAngleRotation u hu) 1)
    rw [hcoe]
    simp [hJ₁, hJ₂, huv]


lemma direct_isometryEquiv_eq_of_send_pair {a b : ℝ²} (hab : a ≠ b)
    {g₁ g₂ : ℝ² ≃ᵢ ℝ²}
    (hd₁ : IsDirect g₁) (hd₂ : IsDirect g₂)
    (ha : g₁ a = g₂ a) (hb : g₁ b = g₂ b) :
    g₁ = g₂ := by
  set u : ℝ² := b - a with hu_def
  have hu : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  set T₁ := g₁.toRealAffineIsometryEquiv.linearIsometryEquiv with hT₁_def
  set T₂ := g₂.toRealAffineIsometryEquiv.linearIsometryEquiv with hT₂_def
   
  have h₁ : 0 < LinearMap.det (T₁.toLinearEquiv : ℝ² →ₗ[ℝ] ℝ²) := hd₁
  have h₂ : 0 < LinearMap.det (T₂.toLinearEquiv : ℝ² →ₗ[ℝ] ℝ²) := hd₂
   
  have hT₁_vsub : T₁ u = g₁ b - g₁ a := by
    rw [hu_def]
    have := g₁.toRealAffineIsometryEquiv.map_vsub b a
    rw [IsometryEquiv.coeFn_toRealAffineIsometryEquiv] at this
    simpa [hT₁_def] using this
  have hT₂_vsub : T₂ u = g₂ b - g₂ a := by
    rw [hu_def]
    have := g₂.toRealAffineIsometryEquiv.map_vsub b a
    rw [IsometryEquiv.coeFn_toRealAffineIsometryEquiv] at this
    simpa [hT₂_def] using this
  have hTeq : T₁ u = T₂ u := by rw [hT₁_vsub, hT₂_vsub, ha, hb]
   
  have hT : T₁ = T₂ := direct_linearIsometryEquiv_eq_of_send_eq hu h₁ h₂ hTeq
   
  apply IsometryEquiv.ext
  intro x
  have h1 := g₁.toRealAffineIsometryEquiv.map_vsub x a
  have h2 := g₂.toRealAffineIsometryEquiv.map_vsub x a
  rw [IsometryEquiv.coeFn_toRealAffineIsometryEquiv] at h1 h2
  rw [← hT₁_def] at h1
  rw [← hT₂_def] at h2
  rw [hT] at h1
  rw [ha] at h1
  have h12 := h1.symm.trans h2
  rwa [vsub_left_cancel_iff] at h12


lemma bundle_Esgk_BridgeIdentity_ne_zero_of_norm_eq {u v : ℝ²} (hu : u ≠ 0) (huv : ‖u‖ = ‖v‖) : v ≠ 0 := fun hv0 ↦ hu <| by rw [← norm_eq_zero (E := ℝ²), huv, hv0, norm_zero]


lemma bundle_Esgk_BridgeIdentity_inner_basisRightAngleRotation {u : ℝ²} (hu : u ≠ 0) (i j : Fin 2) :
    ⟪(o.basisRightAngleRotation u hu) i, (o.basisRightAngleRotation u hu) j⟫_ℝ =
      if i = j then ‖u‖ ^ 2 else 0 := by
  rw [o.coe_basisRightAngleRotation u hu]
  fin_cases i <;> fin_cases j <;>
    set_option linter.unusedSimpArgs false in simp [real_inner_self_eq_norm_sq]


lemma bundle_Esgk_BridgeIdentity_inner_preservation_basis_equiv {u v : ℝ²} (hu : u ≠ 0) (huv : ‖u‖ = ‖v‖) (x y : ℝ²) :
    ⟪((o.basisRightAngleRotation u hu).equiv
        (o.basisRightAngleRotation v (bundle_Esgk_BridgeIdentity_ne_zero_of_norm_eq hu huv))
        (Equiv.refl (Fin 2))) x,
      ((o.basisRightAngleRotation u hu).equiv
        (o.basisRightAngleRotation v (bundle_Esgk_BridgeIdentity_ne_zero_of_norm_eq hu huv))
        (Equiv.refl (Fin 2))) y⟫_ℝ = ⟪x, y⟫_ℝ := by
  set hv : v ≠ 0 := bundle_Esgk_BridgeIdentity_ne_zero_of_norm_eq hu huv
  set bᵤ : Module.Basis (Fin 2) ℝ ℝ² := o.basisRightAngleRotation u hu with hbu_def
  set bᵥ : Module.Basis (Fin 2) ℝ ℝ² := o.basisRightAngleRotation v hv with hbv_def
  set f : ℝ² ≃ₗ[ℝ] ℝ² := bᵤ.equiv bᵥ (Equiv.refl (Fin 2)) with hf_def
  change ⟪f x, f y⟫_ℝ = ⟪x, y⟫_ℝ
  have hf_basis : ∀ i : Fin 2, f (bᵤ i) = bᵥ i := fun i ↦ by
    simp [hf_def, Module.Basis.equiv_apply]
  have hx := bᵤ.sum_repr x
  have hy := bᵤ.sum_repr y
  have hfx : f x = ∑ i, bᵤ.repr x i • bᵥ i := by
    conv_lhs => rw [← hx]
    simp only [map_sum, map_smul, hf_basis]
  have hfy : f y = ∑ i, bᵤ.repr y i • bᵥ i := by
    conv_lhs => rw [← hy]
    simp only [map_sum, map_smul, hf_basis]
  rw [hfx, hfy]
   
   
  simp only [inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right]
   
  conv_rhs => rw [← hx, ← hy]
  simp only [inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
   
   
  congr 1
  congr 1
  rw [bundle_Esgk_BridgeIdentity_inner_basisRightAngleRotation hu j i,
      bundle_Esgk_BridgeIdentity_inner_basisRightAngleRotation hv j i, huv]


noncomputable def directLinearIsometryEquivOfSend (u v : ℝ²) (hu : u ≠ 0) (huv : ‖u‖ = ‖v‖) : ℝ² ≃ₗᵢ[ℝ] ℝ² := LinearEquiv.isometryOfInner
    ((o.basisRightAngleRotation u hu).equiv
      (o.basisRightAngleRotation v (bundle_Esgk_BridgeIdentity_ne_zero_of_norm_eq hu huv))
      (Equiv.refl (Fin 2)))
    (bundle_Esgk_BridgeIdentity_inner_preservation_basis_equiv hu huv)


noncomputable def directAffineIsometryEquivOfSendPair (a b c d : ℝ²) (hab : a ≠ b) (hdist : dist a b = dist c d) :
    ℝ² ≃ᵃⁱ[ℝ] ℝ² := let u : ℝ² := b - a
  let v : ℝ² := d - c
  have hu : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have huv : ‖u‖ = ‖v‖ := by
    change ‖b - a‖ = ‖d - c‖
    rw [← dist_eq_norm, ← dist_eq_norm, dist_comm b a, dist_comm d c, hdist]
  AffineIsometryEquiv.mk' (fun x : ℝ² ↦ directLinearIsometryEquivOfSend u v hu huv (x - a) + c)
    (directLinearIsometryEquivOfSend u v hu huv) a (fun p' ↦ by
      change directLinearIsometryEquivOfSend u v hu huv (p' - a) + c =
        directLinearIsometryEquivOfSend u v hu huv (p' -ᵥ a) +ᵥ
          (directLinearIsometryEquivOfSend u v hu huv (a - a) + c)
      simp)


end Esgk


