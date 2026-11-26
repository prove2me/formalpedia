-- Prove2me | solution 1 for Auto.aux_CuboidNorm.eLpNorm_liftedCuboidEmbed_le_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:55:09.581239+00:00
-- url     : https://prove2.me/submissions/9efcd49e-fde0-439f-a0d7-f9287dfc23e6

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_eLpNorm_liftedCuboidEmbed_eq_count_mul
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
theorem _root_.solution {n : ℕ}
    {ε δ : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1) (hεδ : ε + δ < 1)
    (i : Fin n) (A : Finset (ZVector n)) (a : ZVector n → ℝ)
    (hsupport : ∀ k, k ∉ A → a k = 0) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (hvolume : ∏ j, ENNReal.ofReal (if j = i then δ else ε) ≤ 1) :
    eLpNorm (aux_liftRaw (aux_cuboidEmbed ε δ i a)) p volume ≤
      eLpNorm a p Measure.count := by
  rw [eLpNorm_liftedCuboidEmbed_eq_count_mul hε0 hε hεδ i A a hsupport
    p hp0 hptop]
  calc
    eLpNorm a p Measure.count *
        (∏ j, ENNReal.ofReal (if j = i then δ else ε)) ^ (1 / p.toReal) ≤
        eLpNorm a p Measure.count * 1 :=
      by
        simpa [mul_comm] using mul_le_mul_left
          (ENNReal.rpow_le_one hvolume (by positivity)) (eLpNorm a p Measure.count)
    _ = eLpNorm a p Measure.count := mul_one _
end Auto.aux_CuboidNorm
