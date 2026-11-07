-- Prove2me | solution 1 for AaronsonAmbainis.wing_of_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:26:03.345854+00:00
-- url     : https://prove2.me/submissions/fcce552a-19e5-4824-bf7d-c37eacc135dd

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Antipodal

set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution {g : Cube ι → Bool} {u : Cube ι} {x y w : ι → ℝ} (hu : g u = true)
    (hw : ∀ j, 0 < w j) (hx : IsRow g u x) (hy : ∀ j, 0 ≤ y j)
    (hpos : 0 < ∑ j, w j * x j * y j) :
    IsWing g u (univ.filter fun j => (w j)⁻¹ < (∑ j, w j * x j * y j)⁻¹ * y j) := by
  intro T hT
  by_contra hne
  have hne' : g (flipSet u T) ≠ g u := by rw [hu]; exact hne
  have h1 : 1 ≤ ∑ j ∈ T, x j := hx.2 T hne'
  set Sm := ∑ j, w j * x j * y j with hSm
  have hD : 0 < Sm⁻¹ := inv_pos.mpr hpos
  -- every `j ∈ T` has `1 < w j * (Sm⁻¹ * y j)`
  have hA : ∀ j ∈ T, 1 < w j * (Sm⁻¹ * y j) := by
    intro j hj
    have hj' := (Finset.mem_filter.mp (hT hj)).2
    have h2 := mul_lt_mul_of_pos_left hj' (hw j)
    rwa [mul_inv_cancel₀ (hw j).ne'] at h2
  have hle : ∀ j ∈ T, x j ≤ x j * (w j * (Sm⁻¹ * y j)) := by
    intro j hj
    have h3 := hA j hj
    nlinarith [hx.1 j]
  obtain ⟨j0, hj0T, hj0⟩ : ∃ j ∈ T, 0 < x j := by
    by_contra hcon
    have h4 : ∑ j ∈ T, x j ≤ 0 :=
      Finset.sum_nonpos fun j hj => not_lt.mp fun hp => hcon ⟨j, hj, hp⟩
    linarith
  have hlt : ∑ j ∈ T, x j < ∑ j ∈ T, x j * (w j * (Sm⁻¹ * y j)) := by
    apply Finset.sum_lt_sum hle
    refine ⟨j0, hj0T, ?_⟩
    have h5 := hA j0 hj0T
    nlinarith
  have hsub : ∑ j ∈ T, x j * (w j * (Sm⁻¹ * y j)) ≤ ∑ j, x j * (w j * (Sm⁻¹ * y j)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    intro j _ _
    exact mul_nonneg (hx.1 j) (mul_nonneg (hw j).le (mul_nonneg hD.le (hy j)))
  have htot : ∑ j, x j * (w j * (Sm⁻¹ * y j)) = 1 := by
    have h6 : ∑ j, x j * (w j * (Sm⁻¹ * y j)) = Sm⁻¹ * Sm := by
      rw [hSm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h6, inv_mul_cancel₀ hpos.ne']
  linarith
end AaronsonAmbainis
