-- Prove2me | solution 1 for Auto.aux_ErgodicBox.aemeasurable_enorm_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:38:04.894877+00:00
-- url     : https://prove2.me/submissions/690ef543-84f7-4efd-94bf-d1ea83b53f06

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference

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
theorem _root_.solution {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (f : X → ℝ) (hf : AEStronglyMeasurable f μ) (p : ℝ) :
    AEMeasurable (fun x ↦ ‖f x‖ₑ ^ p) μ := by
  exact ENNReal.continuous_rpow_const.aemeasurable.comp_aemeasurable hf.enorm
end Auto.aux_ErgodicBox
