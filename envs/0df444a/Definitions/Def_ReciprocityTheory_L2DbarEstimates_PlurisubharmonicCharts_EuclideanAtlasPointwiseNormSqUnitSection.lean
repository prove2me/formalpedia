-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_EuclideanAtlasPointwiseNormSqUnitSection
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_EuclideanAtlasPointwiseNormSqUnitSection
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:11:34.211318+00:00
-- url     : https://prove2.me/theorems/e95bd5fe-3e30-51a2-a955-323ed6de6bef
-- title:
--   Euclidean Atlas Pointwise Norm Sq Unit Section
-- statement:
--   Definitions and structural lemmas for Euclidean Atlas Pointwise Norm Sq Unit Section, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/EuclideanAtlasPointwiseNormSqUnitSection.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Matrix
noncomputable section
namespace ExponentialProfileBounds
variable {n : ℕ}
def wv (n : ℕ) (y : V n) : Fin (n + 1) → ℂ := Fin.cons 1 (fun j => y j)
theorem pos_one_add (y : V n) : 0 < 1 + ‖y‖ ^ 2 := by
  positivity
theorem contDiff_ph (la : ℤ) : ContDiff ℝ ∞ (fun y : V n => (la : ℝ) * Real.log (1 + ‖y‖ ^ 2)) := (contDiff_const.mul ((contDiff_const.add (contDiff_norm_sq ℂ)).log fun y => (pos_one_add y).ne'))
def atlas (n : ℕ) : WeightedAtlas n (V n) Unit ℤ where
  chart _ := OpenPartialHomeomorph.refl (V n)
  pick _ := ()
  mem_pick _ := by simp
  holo_trans _ _ := differentiableOn_id.congr fun _ _ => rfl
  g _ _ _ _ := 1
  holo_g _ _ _ := differentiableOn_const _
  g_ne _ _ _ _ _ _ := one_ne_zero
  g_cocycle _ _ _ _ _ _ _ _ := by simp
  g_add _ _ _ _ _ _ _ := by simp
  ph la _ y := (la : ℝ) * Real.log (1 + ‖y‖ ^ 2)
  smooth_ph la _ := (contDiff_ph la).contDiffOn.congr fun _ _ => rfl
  ph_add la mu _ y _ := by push_cast; ring
  ph_trans _ _ _ _ _ _ := by simp
  kap := 0
  g_kap _ _ y _ _ := by
    rw [show ((OpenPartialHomeomorph.refl (V n)) ∘ (OpenPartialHomeomorph.refl (V n)).symm) = id
      from rfl, fderiv_id]
    exact LinearMap.det_id.symm
  mu := volume
  mu_chart _ A _ _ := by simp
def wI (n : ℕ) : Fin (n + 1) → Unit → V n → ℂ := fun k _ y => wv n y k
def w0I (n : ℕ) : Unit → V n → ℂ := fun _ _ => 1
def sI (n : ℕ) : Fin n → Unit → V n → ℂ := fun k _ y => y k
def gv (n : ℕ) : Fin (n + 1) → V n → ℂ := fun k y => wv n y k
end ExponentialProfileBounds
end
end ReciprocityTheory.L2DbarEstimates.Y


