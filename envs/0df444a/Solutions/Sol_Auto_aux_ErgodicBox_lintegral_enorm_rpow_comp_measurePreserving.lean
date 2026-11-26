-- Prove2me | solution 1 for Auto.aux_ErgodicBox.lintegral_enorm_rpow_comp_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:51:09.910247+00:00
-- url     : https://prove2.me/submissions/b077a973-b3e1-468f-84b6-0100184d6be5

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_ErgodicBox_aemeasurable_enorm_rpow
section
@[expose] public section
namespace Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
@[simp] private theorem aux_orbit_zero {X : Type*} (S : Fin 0 → X → X)
    (k : Fin 0 → ℕ) : aux_orbit S k = id :=
  rfl
@[simp] private theorem aux_orbit_succ {X : Type*} {n : ℕ}
    (S : Fin (n + 1) → X → X) (k : Fin (n + 1) → ℕ) :
    aux_orbit S k = (S 0)^[k 0] ∘
      aux_orbit (fun i ↦ S i.succ) (fun i ↦ k i.succ) :=
  rfl
section
universe v
end
namespace aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
end aux_CuboidNorm
namespace aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
end aux_ErgodicBox
end
end Auto
end
end

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
theorem _root_.solution
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (T : X → X) (hT : MeasurePreserving T μ μ)
    (f : X → ℝ) (hf : AEStronglyMeasurable f μ) (p : ℝ) :
    ∫⁻ x, ‖f (T x)‖ₑ ^ p ∂μ = ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  change ∫⁻ x, ((fun y ↦ ‖f y‖ₑ ^ p) ∘ T) x ∂μ = _
  rw [lintegral_comp'
    (by simpa only [hT.map_eq] using aemeasurable_enorm_rpow f hf p)
    hT.aemeasurable, hT.map_eq]
end Auto.aux_ErgodicBox
