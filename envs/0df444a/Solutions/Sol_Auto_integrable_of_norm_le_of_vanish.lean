-- Prove2me | solution 1 for Auto.integrable_of_norm_le_of_vanish
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:58:32.555907+00:00
-- url     : https://prove2.me/submissions/d7f42090-113f-4b4e-bc87-d97838cfd73b

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] {h : ℝ → E} {A B : ℝ}
    (hm : AEStronglyMeasurable h volume) (hB : ∀ x, ‖h x‖ ≤ B)
    (hs : ∀ x, A < |x| → h x = 0) : Integrable h := by
  have he : h = (Icc (-A) A).indicator h := by
    ext x
    by_cases hx : x ∈ Icc (-A) A
    · simp [hx]
    · rw [indicator_of_notMem hx, hs x (lt_of_not_ge fun h' => hx (abs_le.mp h'))]
  rw [he, integrable_indicator_iff measurableSet_Icc]
  exact Measure.integrableOn_of_bounded (by simp [Real.volume_Icc]) hm (ae_of_all _ hB)
end Auto
