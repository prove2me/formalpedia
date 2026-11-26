-- Prove2me | solution 1 for Auto.aux_ErgodicBox.realErgodicAverage_aestronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:53:44.245673+00:00
-- url     : https://prove2.me/submissions/4891732e-5d4e-4f64-a801-52785ebc878b

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
theorem _root_.solution {X : Type*}
    [MeasurableSpace X] {μ : Measure X} {n : ℕ}
    (S : ErgodicSystem X μ n) (N : ℕ) (f : Fin n → X → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (realErgodicAverage S N f) μ := by
  unfold realErgodicAverage
  change AEStronglyMeasurable ((N : ℝ)⁻¹ • fun x ↦
    ∑ m ∈ Finset.range N, ∏ i, f i ((S.transformation i)^[m] x)) μ
  apply (Finset.aestronglyMeasurable_fun_sum (Finset.range N) ?_).const_smul
  intro m _
  apply Finset.aestronglyMeasurable_fun_prod Finset.univ
  intro i _
  change AEStronglyMeasurable (f i ∘ (S.transformation i)^[m]) μ
  exact (hf i).comp_quasiMeasurePreserving
    ((S.measurePreserving i).iterate m).quasiMeasurePreserving
end Auto.aux_ErgodicBox
