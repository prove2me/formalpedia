-- Prove2me | solution 1 for Auto.aux_ErgodicBox.realErgodicAverage_sub_aestronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:55:03.582303+00:00
-- url     : https://prove2.me/submissions/e35fcd0f-97b1-4aee-886c-dd538eb0353e

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_ErgodicBox_realErgodicAverage_aestronglyMeasurable

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Auto.aux_ErgodicBox
theorem _root_.solution {X : Type*}
    [MeasurableSpace X] {μ : Measure X} {n : ℕ}
    (S : ErgodicSystem X μ n) (N M : ℕ) (f : Fin n → X → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun x ↦ realErgodicAverage S N f x -
      realErgodicAverage S M f x) μ := by
  exact (realErgodicAverage_aestronglyMeasurable S N f hf).sub
    (realErgodicAverage_aestronglyMeasurable S M f hf)
end Auto.aux_ErgodicBox
