-- Prove2me | solution 1 for Auto.aux_CuboidNorm.endpointJump_cube_dom_of_overlap_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:49:33.39461+00:00
-- url     : https://prove2.me/submissions/558ae615-48f3-4c8c-9aca-6fc0cffcb54f

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_enorm_mul_le_enorm_mul_of_nonneg_le
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
theorem _root_.solution {n J : ℕ}
    {ε δ : ℝ} (hεδ : ε ≤ δ)
    (N : Fin (J + 1) → ℕ) (T : ℕ → RVector n → ℝ)
    (D : ℕ → ZVector n → ℝ) (W : RVector n → ℝ)
    (hW : ∀ u, (∀ i, 0 ≤ u i ∧ u i ≤ ε) → δ - ε ≤ W u)
    (hT : ∀ (M : ℕ) (k : ZVector n) (u : RVector n),
      (∀ i, 0 ≤ u i ∧ u i < ε) →
      0 < M →
      T M (fun i ↦ (k i : ℝ) + u i) = W u * D M k)
    (hNpos : ∀ q, 0 < N q)
    (j : Fin J) (k : ZVector n) (x : RVector n)
    (hx : x ∈ latticeCuboid ε k) :
    ‖(δ - ε) * (D (N j.succ) k - D (N j.castSucc) k)‖ₑ ≤
      ‖(T (N j.succ) x - T (N j.castSucc) x)‖ₑ := by
  let u : RVector n := fun i ↦ x i - (k i : ℝ)
  have hu : ∀ i, 0 ≤ u i ∧ u i < ε := by
    intro i
    have hxi : x i ∈ Ico ((k i : ℝ)) ((k i : ℝ) + ε) := by
      simpa [latticeCuboid, cuboid] using hx i (by simp)
    exact ⟨by dsimp [u]; linarith [hxi.1], by dsimp [u]; linarith [hxi.2]⟩
  have hx_eq : x = fun i ↦ (k i : ℝ) + u i := by
    funext i
    dsimp [u]
    ring
  have hTsucc := hT (N j.succ) k u hu (hNpos j.succ)
  have hTprev := hT (N j.castSucc) k u hu (hNpos j.castSucc)
  rw [hx_eq, hTsucc, hTprev]
  rw [← mul_sub]
  exact enorm_mul_le_enorm_mul_of_nonneg_le (sub_nonneg.mpr hεδ)
    (hW u (fun i ↦ ⟨(hu i).1, (hu i).2.le⟩))
end Auto.aux_CuboidNorm
