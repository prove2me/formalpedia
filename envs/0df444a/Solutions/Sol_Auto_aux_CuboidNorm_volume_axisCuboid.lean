-- Prove2me | solution 1 for Auto.aux_CuboidNorm.volume_axisCuboid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:47:35.135682+00:00
-- url     : https://prove2.me/submissions/90256300-d020-4ba6-b198-d46be6d21eda

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_volume_cuboid
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
open Auto.aux_CuboidNorm
namespace Auto.aux_CuboidNorm
theorem _root_.solution {n : ℕ} {ε δ : ℝ} (i : Fin n)
    (k : RVector n) :
    volume (axisCuboid ε δ i k) =
      ∏ j, ENNReal.ofReal (if j = i then δ else ε) := by
  rw [axisCuboid, volume_cuboid]
  apply Finset.prod_congr rfl
  intro j _
  simp only [axisUpper, axisLower]
  by_cases hji : j = i <;> simp [hji]
end Auto.aux_CuboidNorm
