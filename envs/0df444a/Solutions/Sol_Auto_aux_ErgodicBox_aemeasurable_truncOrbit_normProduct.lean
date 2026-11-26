-- Prove2me | solution 1 for Auto.aux_ErgodicBox.aemeasurable_truncOrbit_normProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:53:42.394724+00:00
-- url     : https://prove2.me/submissions/f53a0f1c-2cba-4cfc-a55f-973e8e488c60

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_ErgodicBox_aemeasurable_orbitPowerSum
public import Theorems.Thm_Auto_aux_ErgodicBox_eLpNorm_truncOrbit_sq
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
    {X κ : Type*} [MeasurableSpace X] [MeasurableSpace κ]
    [Countable κ] [MeasurableSingletonClass κ] {μ : Measure X}
    {n : ℕ} (B : Finset κ) (T : κ → X → X)
    (hT : ∀ k ∈ B, MeasurePreserving (T k) μ μ)
    (f : Fin n → X → ℝ) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (p : Fin n → ℝ≥0∞) (hp0 : ∀ i, p i ≠ 0) (hptop : ∀ i, p i ≠ ∞)
    (hpreal : ∀ i, 0 < (p i).toReal) :
    AEMeasurable (fun x ↦
      ∏ i, eLpNorm (truncOrbit B T (f i) x) (p i) Measure.count ^ 2) μ := by
  simpa only [Finset.prod_fn] using Finset.aemeasurable_prod Finset.univ
    (fun i _ ↦ by
      let q : ℝ := 2 / (p i).toReal
      have heq : (fun x ↦ eLpNorm (truncOrbit B T (f i) x) (p i)
          Measure.count ^ 2) =
          fun x ↦ orbitPowerSum B T (f i) (p i).toReal x ^ q := by
        funext x
        dsimp [q]
        exact eLpNorm_truncOrbit_sq B T (f i) x (p i) (hp0 i) (hptop i) (hpreal i)
      rw [heq]
      exact ENNReal.continuous_rpow_const.aemeasurable.comp_aemeasurable
        (aemeasurable_orbitPowerSum B T hT (f i) (hf i) (p i).toReal))
end Auto.aux_ErgodicBox
