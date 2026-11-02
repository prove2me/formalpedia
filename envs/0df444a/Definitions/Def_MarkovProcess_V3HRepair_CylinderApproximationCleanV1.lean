-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_CylinderApproximationCleanV1
-- name    : MarkovProcess_V3HRepair_CylinderApproximationCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T09:48:42.18053+00:00
-- url     : https://prove2.me/theorems/5a6f054e-b111-439e-a7d9-a70cc886d206
-- title:
--   Verified MarkovProcess source repair: CylinderApproximationCleanV1
-- statement:
--   Bounded cylinder functionals on continuous paths form an algebra separating points, and bounded continuous path functionals admit compact-set cylinder approximations.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream commit 1f8060caa137731fa08029592019eeaf9d997fe5; source-faithful adapted proof module V3HRepaired.CylinderApproximationCleanV1, archived SHA-256 a1ade3d84c99d50de769de9c0793cd84d251e8c3202e6b5fe8b65045780b37b8.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Trajectory_CylinderAlgebra_cdb093fb
open scoped BoundedContinuousFunction NNReal ZeroAtInfty

namespace MarkovProcess

namespace ContinuousPath

section Cylinder

variable {alpha : Type*} [TopologicalSpace alpha]

theorem isBoundedCylinder_const (c : ℝ) :
    IsBoundedCylinder (alpha := alpha) fun _ ↦ c :=
  ⟨∅, BoundedContinuousFunction.const _ c, fun _ ↦ rfl⟩

theorem IsBoundedCylinder.add {G H : ContinuousPath alpha → ℝ} (hG : IsBoundedCylinder G)
    (hH : IsBoundedCylinder H) : IsBoundedCylinder fun omega ↦ G omega + H omega := by
  obtain ⟨I, g, hg⟩ := hG
  obtain ⟨J, h, hh⟩ := hH
  refine ⟨I ∪ J,
    g.compContinuous (finsetRestrict (alpha := alpha) Finset.subset_union_left) +
      h.compContinuous (finsetRestrict (alpha := alpha) Finset.subset_union_right),
    fun omega ↦ ?_⟩
  simp only [BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.compContinuous_apply, p2m_embedded_099d1679a309679e]
  rw [hg, hh]

theorem IsBoundedCylinder.mul {G H : ContinuousPath alpha → ℝ} (hG : IsBoundedCylinder G)
    (hH : IsBoundedCylinder H) : IsBoundedCylinder fun omega ↦ G omega * H omega := by
  obtain ⟨I, g, hg⟩ := hG
  obtain ⟨J, h, hh⟩ := hH
  refine ⟨I ∪ J,
    g.compContinuous (finsetRestrict (alpha := alpha) Finset.subset_union_left) *
      h.compContinuous (finsetRestrict (alpha := alpha) Finset.subset_union_right),
    fun omega ↦ ?_⟩
  simp only [BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.compContinuous_apply, p2m_embedded_099d1679a309679e]
  rw [hg, hh]

theorem isBoundedCylinder_coordinate (t : ℝ≥0) (f : C₀(alpha, ℝ)) :
    IsBoundedCylinder fun omega : ContinuousPath alpha ↦ f (omega t) :=
  ⟨{t}, f.toBCF.compContinuous
      ⟨fun path ↦ path ⟨t, Finset.mem_singleton_self t⟩, continuous_apply _⟩, fun _ ↦ rfl⟩

theorem isBoundedCylinder_of_mem_coordinateSubalgebra {G : C(ContinuousPath alpha, ℝ)}
    (hG : G ∈ coordinateSubalgebra alpha) :
    IsBoundedCylinder fun omega ↦ G omega := by
  induction hG using Algebra.adjoin_induction with
  | mem G hGmem =>
      obtain ⟨t, f, rfl⟩ := hGmem
      exact isBoundedCylinder_coordinate t f
  | algebraMap r =>
      have hconst : (fun omega : ContinuousPath alpha ↦
          (algebraMap ℝ C(ContinuousPath alpha, ℝ) r) omega) = fun _ ↦ r := by
        funext omega
        simp
      rw [hconst]
      exact isBoundedCylinder_const r
  | add G H _ _ ihG ihH => exact ihG.add ihH
  | mul G H _ _ ihG ihH => exact ihG.mul ihH

/-- The coordinate algebra separates points of path space: two distinct continuous paths differ
at some time, and a function vanishing at infinity separates the two values there. -/
theorem coordinateSubalgebra_separatesPoints [T3Space alpha] [LocallyCompactSpace alpha] :
    (coordinateSubalgebra alpha).SeparatesPoints := by
  intro omega eta homega
  have hexists : ∃ t : ℝ≥0, omega t ≠ eta t := by
    by_contra hcon
    exact homega (ContinuousPath.ext fun t ↦ not_ne_iff.mp (not_exists.mp hcon t))
  obtain ⟨t, ht⟩ := hexists
  obtain ⟨f, hfone, hfzero, hfcompact, -⟩ :=
    exists_continuous_one_zero_of_isCompact (isCompact_singleton : IsCompact ({omega t} : Set alpha))
      (isClosed_singleton : IsClosed ({eta t} : Set alpha)) (Set.disjoint_singleton.mpr ht)
  let f0 : C₀(alpha, ℝ) := ⟨f, HasCompactSupport.is_zero_at_infty hfcompact⟩
  let G : C(ContinuousPath alpha, ℝ) :=
    (f0 : C(alpha, ℝ)).comp ⟨fun path ↦ path t, continuous_eval t⟩
  refine ⟨G, ⟨G, ⟨Algebra.subset_adjoin ⟨t, f0, rfl⟩, rfl⟩⟩, ?_⟩
  show f (omega t) ≠ f (eta t)
  rw [hfone (Set.mem_singleton _), hfzero (Set.mem_singleton _)]
  exact one_ne_zero

end Cylinder

section Approximation

variable {alpha : Type*} [MetricSpace alpha] [LocallyCompactSpace alpha]

/-- **Cylinder approximation on a compact set of paths.**  A bounded continuous functional `F` of
the path is, on any compact set of paths, uniformly `eps`-close to a bounded cylinder functional
whose norm is at most `‖F‖ + eps`.

Density comes from Stone--Weierstrass applied to `coordinateSubalgebra`; the norm bound comes from
truncating the approximant at height `‖F‖ + eps`, which changes nothing on the compact set. -/
theorem exists_boundedCylinder_approx (F : ContinuousPath alpha →ᵇ ℝ)
    {K : Set (ContinuousPath alpha)} (hK : IsCompact K) {eps : ℝ} (heps : 0 < eps) :
    ∃ G : ContinuousPath alpha →ᵇ ℝ, IsBoundedCylinder (fun omega ↦ G omega) ∧
      ‖G‖ ≤ ‖F‖ + eps ∧ ∀ omega ∈ K, |G omega - F omega| ≤ eps := by
  obtain ⟨G0, hG0mem, hG0approx⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      (coordinateSubalgebra_separatesPoints (alpha := alpha)) F.toContinuousMap hK heps
  obtain ⟨I, g0, hg0⟩ := isBoundedCylinder_of_mem_coordinateSubalgebra hG0mem
  set C : ℝ := ‖F‖ + eps with hCdef
  have hC0 : 0 ≤ C := by positivity
  set clampC : ℝ → ℝ := fun y ↦ max (-C) (min C y) with hclampdef
  have hclampcont : Continuous clampC :=
    continuous_const.max (continuous_const.min continuous_id)
  have hclampabs : ∀ y, |clampC y| ≤ C := by
    intro y
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hclampeq : ∀ y, |y| ≤ C → clampC y = y := by
    intro y hy
    rw [abs_le] at hy
    simp only [hclampdef, min_eq_right hy.2, max_eq_right hy.1]
  set g : (I → alpha) →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun path ↦ clampC (g0 path))
      (hclampcont.comp g0.continuous) C (fun path ↦ by
        rw [Real.norm_eq_abs]; exact hclampabs _) with hgdef
  set G : ContinuousPath alpha →ᵇ ℝ :=
    g.compContinuous ⟨finsetEvaluation (alpha := alpha) I, continuous_finiteEvaluation _⟩ with hGdef
  have hGapply : ∀ omega : ContinuousPath alpha, G omega = clampC (G0 omega) := by
    intro omega
    rw [hGdef]
    show clampC (g0 (finsetEvaluation I omega)) = clampC (G0 omega)
    congr 1
    exact (hg0 omega).symm
  refine ⟨G, ⟨I, g, fun omega ↦ rfl⟩, ?_, ?_⟩
  · refine (BoundedContinuousFunction.norm_le hC0).mpr fun omega ↦ ?_
    rw [Real.norm_eq_abs, hGapply omega]
    exact hclampabs _
  · intro omega homega
    have hnear : |G0 omega - F omega| < eps := by
      simpa only [Real.norm_eq_abs] using! hG0approx omega homega
    have hFbound : |F omega| ≤ ‖F‖ := by
      simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm omega
    have hG0bound : |G0 omega| ≤ C := by
      have habs : |G0 omega| - |F omega| ≤ |G0 omega - F omega| :=
        abs_sub_abs_le_abs_sub _ _
      rw [hCdef]
      linarith
    rw [hGapply omega, hclampeq _ hG0bound]
    exact hnear.le

end Approximation

end ContinuousPath

end MarkovProcess

#print axioms MarkovProcess.ContinuousPath.exists_boundedCylinder_approx


