-- Prove2me | solution 1 for Auto.aux_overlapUpper_eq_add_overlapUpper_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:46:29.883893+00:00
-- url     : https://prove2.me/submissions/ffcd92e6-bcb9-4994-8999-e56f32239ba9

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_fin_univ_nonempty
public import Theorems.Thm_P2M_Auto_aux_add_inf__657294d4941d
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
theorem _root_.solution {n : ℕ}
    (hn : 0 < n) (ε δ : ℝ) (u : aux_RVector n) (m : ℕ) :
    aux_overlapUpper hn ε δ u m = (m : ℝ) + aux_overlapUpper hn ε δ u 0 := by
  let hne : (Finset.univ : Finset (Fin n)).Nonempty := aux_fin_univ_nonempty hn
  unfold aux_overlapUpper
  dsimp
  simpa [sub_eq_add_neg, add_assoc] using
    (aux_add_inf' Finset.univ hne (fun i ↦ ε + δ - u i) (m : ℝ)).symm
end Auto
