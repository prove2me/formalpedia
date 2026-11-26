-- Prove2me | solution 1 for Auto.aux_toLp_translateAxis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:45:21.166215+00:00
-- url     : https://prove2.me/submissions/d9d136f4-a0b6-41af-908a-88430c08845b

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
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
namespace Auto
theorem _root_.solution {n : ℕ} (x : aux_RVector n)
    (i : Fin n) (s : ℝ) :
    WithLp.toLp 2 (aux_translateAxis x i s) =
      WithLp.toLp 2 x + s • ctCoordinateAxis i := by
  ext j
  simp [aux_translateAxis, ctCoordinateAxis]
end Auto
