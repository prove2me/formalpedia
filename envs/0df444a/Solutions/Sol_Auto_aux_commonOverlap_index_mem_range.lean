-- Prove2me | solution 1 for Auto.aux_commonOverlap_index_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:46:48.218901+00:00
-- url     : https://prove2.me/submissions/15b0c756-ef45-4fc3-abce-642521833a4e

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
theorem _root_.solution {n : ℕ} (hn : 0 < n)
    {ε δ : ℝ} (hwidth : ε + δ < 1) (u : aux_RVector n)
    (hu : ∀ i, 0 ≤ u i ∧ u i < ε) (N : ℕ) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) N) (m : ℤ)
    (hm : ∀ i, ε - u i ≤ s - (m : ℝ) ∧
      s - (m : ℝ) < ε + δ - u i) :
    ∃ q : Fin N, (q.val : ℤ) = m := by
  let i₀ : Fin n := ⟨0, hn⟩
  have hmnonneg : 0 ≤ m := by
    by_contra hneg
    have hmle : m ≤ -1 := by omega
    have hupper := (hm i₀).2
    have hge : 1 ≤ s - (m : ℝ) := by
      have hmle' : (m : ℝ) ≤ -1 := by exact_mod_cast hmle
      linarith [hs.1]
    linarith [hupper, hwidth, (hu i₀).1]
  have hmlts : (m : ℝ) < s := by
    have hlower := (hm i₀).1
    have hpos : 0 < ε - u i₀ := by linarith [(hu i₀).2]
    linarith
  have hmltNreal : (m : ℝ) < (N : ℝ) := lt_trans hmlts hs.2
  have hmltN : m < (N : ℤ) := by
    exact_mod_cast hmltNreal
  have htoNat : m.toNat < N := by
    have hcast : (m.toNat : ℤ) < (N : ℤ) := by
      simpa only [Int.toNat_of_nonneg hmnonneg] using hmltN
    exact_mod_cast hcast
  refine ⟨⟨m.toNat, htoNat⟩, ?_⟩
  simp only [Int.toNat_of_nonneg hmnonneg]
end Auto
