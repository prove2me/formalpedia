-- Prove2me | solution 1 for Auto.aux_ErgodicBox.eLpNorm_truncOrbit_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:52:43.290919+00:00
-- url     : https://prove2.me/submissions/c0c1b059-f342-499f-904b-1dbb4187030c

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_ErgodicBox_eLpNorm_count_sq_eq_finset_sum_rpow
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
    [Countable κ] [MeasurableSingletonClass κ]
    (B : Finset κ) (T : κ → X → X) (f : X → ℝ) (x : X)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (hpreal : 0 < p.toReal) :
    eLpNorm (truncOrbit B T f x) p Measure.count ^ 2 =
      orbitPowerSum B T f p.toReal x ^ (2 / p.toReal) := by
  rw [eLpNorm_count_sq_eq_finset_sum_rpow B (truncOrbit B T f x) p hp0 hptop hpreal]
  · congr 1
    unfold orbitPowerSum truncOrbit
    apply Finset.sum_congr rfl
    intro k hk
    rw [Set.indicator_of_mem (by simpa using hk)]
  · intro k hk
    unfold truncOrbit
    rw [Set.indicator_of_notMem (by simpa using hk)]
end Auto.aux_ErgodicBox
