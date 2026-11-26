-- Prove2me | solution 1 for Auto.aux_overlapLower_eq_add_overlapLower_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:45:39.374248+00:00
-- url     : https://prove2.me/submissions/8849a843-fb43-49bd-85d6-3ee9269863b4

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_fin_univ_nonempty
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
    (hn : 0 < n) (ε : ℝ) (u : aux_RVector n) (m : ℕ) :
    aux_overlapLower hn ε u m = (m : ℝ) + aux_overlapLower hn ε u 0 := by
  let hne : (Finset.univ : Finset (Fin n)).Nonempty := aux_fin_univ_nonempty hn
  unfold aux_overlapLower
  dsimp
  simpa [sub_eq_add_neg, add_assoc] using
    (Finset.add_sup' Finset.univ (fun i ↦ ε - u i) (m : ℝ) hne).symm
end Auto
