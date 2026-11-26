-- Prove2me | solution 1 for Auto.aux_continuous_fintype_tensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:55:00.195021+00:00
-- url     : https://prove2.me/submissions/35e166b2-4c60-43c2-b2d0-7e52ebe80658

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {ι : Type*} [Fintype ι]
    {d : ι → ℕ} {𝕜 : Type*} [NormedField 𝕜]
    {f : ∀ i, EuclideanSpace ℝ (Fin (d i)) → 𝕜} (hf : ∀ i, Continuous (f i)) :
    Continuous (fun x : ∀ i, EuclideanSpace ℝ (Fin (d i)) ↦ ∏ i, f i (x i)) := by
  classical
  exact continuous_finsetProd Finset.univ fun i _ ↦ (hf i).comp (continuous_apply i)
end Auto
