-- Prove2me | solution 1 for Auto.aux_CuboidNorm.lintegral_count_enorm_rpow_eq_finset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:36:20.423884+00:00
-- url     : https://prove2.me/submissions/8948b783-a628-4d32-9eae-1febd5f77c09

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
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
namespace Auto.aux_CuboidNorm
theorem _root_.solution {κ : Type*}
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (A : Finset κ) (a : κ → ℝ) (q : ℝ) (hq : 0 < q)
    (hsupport : ∀ k, k ∉ A → a k = 0) :
    (∫⁻ k, ‖a k‖ₑ ^ q ∂Measure.count) = ∑ k ∈ A, ‖a k‖ₑ ^ q := by
  classical
  rw [lintegral_count]
  exact tsum_eq_sum fun k hk ↦ by
    rw [hsupport k hk]
    simp [ENNReal.zero_rpow_of_pos hq]
end Auto.aux_CuboidNorm
