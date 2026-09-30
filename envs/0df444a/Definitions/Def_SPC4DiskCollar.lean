-- Prove2me | Definitions.Def_SPC4DiskCollar
-- name    : SPC4DiskCollar
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-05T19:25:44.088234+00:00
-- url     : https://prove2.me/theorems/9b07efbc-5069-4b3e-98d4-b097e512c23f
-- title:
--   Explicit radial collar and boundary identification of the disk
-- statement:
--   For every nonnegative integer m, construct the specified map from the unit m-sphere times [0,1] to the closed unit ball, (u,t) ↦ (1−t/2)u, and the point-preserving homeomorphism from the boundary of the concrete disk atlas to the unit sphere. The latter constructor carries the proved norm-one boundary characterization. Its three boundary proof helpers are retained internally under SPC4Disk.CollarData with no admitted dependencies; the existing SPC4DiskCharts bundle is imported unchanged. No arbitrary-manifold collar theorem or transported annulus structure is defined.
-- source:
--   Ryan Shin, unpublished Disk.lean, boundary identification and explicit collar constructions (original lines 857–921 and 1018–1028); source SHA-256 889a9eccf9d2350aee7051ab7b6895e565f9f1a0c84e7120fb45c15acae0097e. Exact declaration extraction, source refactor, namespace-reference edits and commentary-only cleanup are recorded in the accompanying provenance.

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_SPC4DiskCharts

set_option autoImplicit false

namespace SPC4Disk.CollarData

open Set Metric

open scoped ContDiff Manifold

noncomputable section

variable {n : ℕ} [NeZero n]

section BoundaryChart

variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

lemma _root_.SPC4Disk.CollarData.disk_isInteriorPoint
    {z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (h : ‖z.val‖ < 1) : (𝓡∂ (m + 1)).IsInteriorPoint z := by
  have hchart : chartAt (EuclideanHalfSpace (m + 1)) z =
      if ‖z.val‖ < 1 then SPC4Disk.DiskInteriorChart
      else SPC4Disk.DiskBoundaryChart (SPC4Disk.unitOr SPC4Disk.diskNorth z.val) := rfl
  rw [ModelWithCorners.IsInteriorPoint,
    interior_range_modelWithCornersEuclideanHalfSpace, extChartAt, hchart,
    if_pos h]
  show (0 : ℝ) < (z.val + SPC4Disk.diskShift (m + 1)) 0
  have hco : (z.val + SPC4Disk.diskShift (m + 1)) 0 = z.val 0 + 2 := by simp [SPC4Disk.diskShift]
  rw [hco]
  have h2 := abs_le.mp (le_trans (SPC4Disk.EuclideanSpace.abs_coord_le_norm _ 0) h.le)
  linarith [h2.1]

lemma _root_.SPC4Disk.CollarData.disk_isBoundaryPoint
    {z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (h : ‖z.val‖ = 1) : (𝓡∂ (m + 1)).IsBoundaryPoint z := by
  have hchart : chartAt (EuclideanHalfSpace (m + 1)) z =
      if ‖z.val‖ < 1 then SPC4Disk.DiskInteriorChart
      else SPC4Disk.DiskBoundaryChart (SPC4Disk.unitOr SPC4Disk.diskNorth z.val) := rfl
  rw [ModelWithCorners.IsBoundaryPoint,
    frontier_range_modelWithCornersEuclideanHalfSpace, extChartAt, hchart,
    if_neg (by rw [h]; exact lt_irrefl 1)]
  show (0 : ℝ) =
    (SPC4Disk.DiskBoundaryChartFun (SPC4Disk.unitOr SPC4Disk.diskNorth z.val) z).val 0
  rw [SPC4Disk.DiskBoundaryChartFun_val_zero, h, sub_self]

/-- **Milestone 4(a): the boundary of the closed ball is the unit sphere**
(as subsets of the ball, via Mathlib's `InteriorBoundary` machinery). -/
lemma _root_.SPC4Disk.CollarData.diskBoundary_eq :
    (𝓡∂ (m + 1)).boundary
      (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) =
      { z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
        ‖z.val‖ = 1 } := by
  ext z
  rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp z.2) with h | h
  · apply iff_of_false
    · rw [← mem_compl_iff, ModelWithCorners.compl_boundary]
      exact SPC4Disk.CollarData.disk_isInteriorPoint h
    · exact fun h1 => absurd h1 (ne_of_lt h)
  · exact iff_of_true (SPC4Disk.CollarData.disk_isBoundaryPoint h) h

/-- **Milestone 4(b): the boundary of the disk is homeomorphic to the
sphere.** The homeomorphism is transport of the underlying point, with
membership carried across `diskBoundary_eq`. -/
noncomputable def _root_.SPC4Disk.diskBoundaryHomeoSphere :
    ((𝓡∂ (m + 1)).boundary
      (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)) ≃ₜ
    sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 where
  toFun z := ⟨z.val.val, mem_sphere_zero_iff_norm.mpr
    ((Set.ext_iff.mp SPC4Disk.CollarData.diskBoundary_eq z.val).mp z.2)⟩
  invFun s := ⟨⟨s.val, mem_closedBall_zero_iff.mpr
      (le_of_eq (mem_sphere_zero_iff_norm.mp s.2))⟩, by
    rw [SPC4Disk.CollarData.diskBoundary_eq]
    exact mem_sphere_zero_iff_norm.mp s.2⟩
  left_inv z := Subtype.ext (Subtype.ext rfl)
  right_inv s := Subtype.ext rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val

end BoundaryChart

section BoundarySmooth

variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

end BoundarySmooth

section Collar

variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The collar map of the disk: `(u, t) ↦ (1 - t/2) • u`, radii in
`[1/2, 1]`. -/
def _root_.SPC4Disk.diskCollar (p : (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) ×
    (Set.Icc (0 : ℝ) 1)) :
    closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
  ⟨(1 - p.2.val / 2) • p.1.val, by
    have h1 : ‖p.1.val‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
    have h2 : (0 : ℝ) ≤ 1 - p.2.val / 2 := by linarith [p.2.2.2]
    rw [mem_closedBall_zero_iff, norm_smul, h1, mul_one, Real.norm_eq_abs,
      abs_of_nonneg h2]
    linarith [p.2.2.1]⟩

end Collar

section ValSmooth

variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

end ValSmooth

section Annulus

variable {m : ℕ}

end Annulus

end
end SPC4Disk.CollarData


