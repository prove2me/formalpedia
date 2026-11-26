-- Prove2me | solution 1 for Auto.aux_finite_continuous_to_discrete_constant_bridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:51:45.269785+00:00
-- url     : https://prove2.me/submissions/378593e5-72b9-41a8-aef4-bcb4513dadcf

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_cuboid_factor_mul_dyadic
public import Theorems.Thm_Auto_aux_ofReal_dyadic_power
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
    (C g : ℝ) (D E : ℝ≥0∞) (L F : Fin n → ℝ≥0∞)
    (hlower :
      (ENNReal.ofReal ((1 : ℝ) / 8) ^ (2 : ℝ) *
        ENNReal.ofReal ((1 : ℝ) / 8) ^ n) * D ≤ E)
    (hupper : E ≤ ENNReal.ofReal C * ENNReal.ofReal g *
      ∏ i, L i ^ (2 : ℕ))
    (hL : ∀ i, L i ≤ F i) :
    D ≤ ENNReal.ofReal (((2 : ℝ) ^ (3 * n + 6)) * C) *
      ENNReal.ofReal g * ∏ i, F i ^ (2 : ℕ) := by
  let K : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (3 * n + 6)
  have hK :
      (ENNReal.ofReal ((1 : ℝ) / 8) ^ (2 : ℝ) *
        ENNReal.ofReal ((1 : ℝ) / 8) ^ n) * K = 1 := by
    exact aux_cuboid_factor_mul_dyadic n
  have hDE : D ≤ K * E := by
    calc
      D =
          ((ENNReal.ofReal ((1 : ℝ) / 8) ^ (2 : ℝ) *
            ENNReal.ofReal ((1 : ℝ) / 8) ^ n) * K) * D := by
              rw [hK, one_mul]
      _ = K *
          ((ENNReal.ofReal ((1 : ℝ) / 8) ^ (2 : ℝ) *
            ENNReal.ofReal ((1 : ℝ) / 8) ^ n) * D) := by
              ac_rfl
      _ ≤ K * E := mul_le_mul_right hlower K
  have hprod : ∏ i, L i ^ (2 : ℕ) ≤ ∏ i, F i ^ (2 : ℕ) := by
    apply Finset.prod_le_prod'
    intro i hi
    exact pow_le_pow_left' (hL i) 2
  calc
    D ≤ K * E := hDE
    _ ≤ K * (ENNReal.ofReal C * ENNReal.ofReal g *
        ∏ i, L i ^ (2 : ℕ)) := mul_le_mul_right hupper K
    _ = ENNReal.ofReal (((2 : ℝ) ^ (3 * n + 6)) * C) *
        ENNReal.ofReal g * ∏ i, L i ^ (2 : ℕ) := by
          have hp : 0 ≤ (2 : ℝ) ^ (3 * n + 6) := by positivity
          have hcast : ENNReal.ofReal ((2 : ℝ) ^ (3 * n + 6)) *
              ENNReal.ofReal C =
              ENNReal.ofReal (((2 : ℝ) ^ (3 * n + 6) * C)) :=
            (ENNReal.ofReal_mul hp).symm
          dsimp [K]
          rw [← aux_ofReal_dyadic_power n]
          rw [show ENNReal.ofReal ((2 : ℝ) ^ (3 * n + 6)) *
              (ENNReal.ofReal C * ENNReal.ofReal g *
                ∏ i, L i ^ (2 : ℕ)) =
              (ENNReal.ofReal ((2 : ℝ) ^ (3 * n + 6)) * ENNReal.ofReal C) *
                ENNReal.ofReal g * ∏ i, L i ^ (2 : ℕ) by ac_rfl,
            hcast]
    _ ≤ ENNReal.ofReal (((2 : ℝ) ^ (3 * n + 6)) * C) *
        ENNReal.ofReal g * ∏ i, F i ^ (2 : ℕ) :=
      mul_le_mul_right hprod _
end Auto
