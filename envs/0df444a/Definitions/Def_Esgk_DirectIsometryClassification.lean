-- Prove2me | Definitions.Def_Esgk_DirectIsometryClassification
-- name    : Esgk_DirectIsometryClassification
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:50:36.818667+00:00
-- url     : https://prove2.me/theorems/5b104dfa-6cea-4365-a19c-c2e4b8f85b4b
-- title:
--   Classification data for direct plane isometries
-- statement:
--   This decomposes a plane isometry into its linear part and displacement, and records rotation, fixed-point, injectivity, surjectivity, and uniqueness properties for direct isometries.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_BridgeIdentity
import Definitions.Def_Esgk_RichnessLevels
import Definitions.Def_LeanFormalizations_Geometry_Euclidean_IsometryClassification
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry

noncomputable section

 
local instance : Fact (Module.finrank ℝ ℝ² = 2) := ⟨by simp⟩

 
local notation "o" => (positiveOrientation : Orientation ℝ ℝ² (Fin 2))

 
def planeIsometryLinearPart (g : IsometryEquiv ℝ² ℝ²) : ℝ² ≃ₗᵢ[ℝ] ℝ² :=
  g.toRealAffineIsometryEquiv.linearIsometryEquiv


def planeIsometryLinearDisplacement (g : IsometryEquiv ℝ² ℝ²) :
    ℝ² →ₗ[ℝ] ℝ² :=
  (planeIsometryLinearPart g).toLinearEquiv.toLinearMap - LinearMap.id


theorem planeIsometry_apply_eq_linearPart_add (g : IsometryEquiv ℝ² ℝ²)
    (x : ℝ²) :
    g x = planeIsometryLinearPart g x + g 0 := by
  have h := g.toRealAffineIsometryEquiv.map_vsub x 0
  rw [IsometryEquiv.coeFn_toRealAffineIsometryEquiv] at h
  have hlinear : planeIsometryLinearPart g x = g x - g 0 := by
    simpa [planeIsometryLinearPart] using h
  exact (eq_sub_iff_add_eq.mp hlinear).symm


theorem direct_planeIsometryLinearPart_exists_rotation
    {g : IsometryEquiv ℝ² ℝ²} (hdirect : IsDirect g) :
    ∃ θ : Real.Angle, planeIsometryLinearPart g = o.rotation θ := by
  exact o.exists_linearIsometryEquiv_eq_of_det_pos
    (f := planeIsometryLinearPart g)
    (by simpa [IsDirect, planeIsometryLinearPart] using hdirect)


theorem planeIsometryLinearPart_eq_one_of_fixedVector
    {g : IsometryEquiv ℝ² ℝ²} (hdirect : IsDirect g)
    {v : ℝ²} (hv : v ≠ 0)
    (hfixed : planeIsometryLinearPart g v = v) :
    planeIsometryLinearPart g = 1 := by
  apply direct_linearIsometryEquiv_eq_of_send_eq hv
  · simpa [IsDirect, planeIsometryLinearPart] using hdirect
  · change 0 < LinearMap.det (LinearMap.id : ℝ² →ₗ[ℝ] ℝ²)
    rw [LinearMap.det_id]
    norm_num
  · simpa using hfixed


theorem planeIsometryLinearDisplacement_injective
    {g : IsometryEquiv ℝ² ℝ²} (hdirect : IsDirect g)
    (hlinear : planeIsometryLinearPart g ≠ 1) :
    Function.Injective (planeIsometryLinearDisplacement g) := by
  intro x y hxy
  by_contra hne
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hxy' :
      planeIsometryLinearPart g x - x =
        planeIsometryLinearPart g y - y := by
    simpa [planeIsometryLinearDisplacement, LinearMap.sub_apply] using hxy
  have hfixed : planeIsometryLinearPart g (x - y) = x - y := by
    rw [map_sub]
    calc
      planeIsometryLinearPart g x - planeIsometryLinearPart g y =
          (planeIsometryLinearPart g x - x) -
            (planeIsometryLinearPart g y - y) + (x - y) := by
              abel
      _ = x - y := by rw [hxy']; simp
  exact hlinear
    (planeIsometryLinearPart_eq_one_of_fixedVector hdirect hsub hfixed)


theorem planeIsometryLinearDisplacement_surjective
    {g : IsometryEquiv ℝ² ℝ²} (hdirect : IsDirect g)
    (hlinear : planeIsometryLinearPart g ≠ 1) :
    Function.Surjective (planeIsometryLinearDisplacement g) := by
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
    (planeIsometryLinearDisplacement_injective hdirect hlinear)

 
theorem planeIsometryLinearDisplacement_eq_neg_zero_of_fixedPoint
    {g : IsometryEquiv ℝ² ℝ²} {x : ℝ²} (hfixed : g x = x) :
    planeIsometryLinearDisplacement g x = -g 0 := by
  have hform := planeIsometry_apply_eq_linearPart_add g x
  have hsum : planeIsometryLinearPart g x + g 0 = x :=
    hform.symm.trans hfixed
  change planeIsometryLinearPart g x - x = -g 0
  calc
    planeIsometryLinearPart g x - x =
        planeIsometryLinearPart g x -
          (planeIsometryLinearPart g x + g 0) := by rw [hsum]
    _ = -g 0 := by abel


theorem direct_isometry_existsUnique_fixedPoint_of_linearPart_ne_one
    {g : IsometryEquiv ℝ² ℝ²} (hdirect : IsDirect g)
    (hlinear : planeIsometryLinearPart g ≠ 1) :
    ∃! center : ℝ², g center = center := by
  have hinjective :=
    planeIsometryLinearDisplacement_injective hdirect hlinear
  have hsurjective :=
    planeIsometryLinearDisplacement_surjective hdirect hlinear
  obtain ⟨center, hcenter⟩ := hsurjective (-g 0)
  refine ⟨center, ?_, ?_⟩
  · change g center = center
    rw [planeIsometry_apply_eq_linearPart_add]
    have hdisplacement :
        planeIsometryLinearPart g center - center = -g 0 := by
      simpa [planeIsometryLinearDisplacement, LinearMap.sub_apply] using hcenter
    calc
      planeIsometryLinearPart g center + g 0 =
          (planeIsometryLinearPart g center - center) + center + g 0 := by
            abel
      _ = -g 0 + center + g 0 := by rw [hdisplacement]
      _ = center := by abel
  · intro other hother
    apply hinjective
    exact (planeIsometryLinearDisplacement_eq_neg_zero_of_fixedPoint hother).trans
      hcenter.symm

 
theorem planeIsometry_apply_eq_add_zero_of_linearPart_eq_one
    {g : IsometryEquiv ℝ² ℝ²}
    (hlinear : planeIsometryLinearPart g = 1) (x : ℝ²) :
    g x = x + g 0 := by
  rw [planeIsometry_apply_eq_linearPart_add, hlinear]
  simp


theorem planeIsometry_zero_ne_zero_of_ne_one_of_linearPart_eq_one
    {g : IsometryEquiv ℝ² ℝ²} (hne : g ≠ 1)
    (hlinear : planeIsometryLinearPart g = 1) :
    g 0 ≠ 0 := by
  intro hzero
  apply hne
  apply IsometryEquiv.ext
  intro x
  rw [planeIsometry_apply_eq_add_zero_of_linearPart_eq_one hlinear, hzero]
  simp


theorem planeIsometry_dist_fixedPoint
    {g : IsometryEquiv ℝ² ℝ²} {center : ℝ²}
    (hcenter : g center = center) (x : ℝ²) :
    dist (g x) center = dist x center := by
  calc
    dist (g x) center = dist (g x) (g center) := by rw [hcenter]
    _ = dist x center := g.dist_eq x center


end

end Esgk


