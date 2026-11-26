-- Prove2me | solution 1 for Auto.aux_cuboidEmbed_product_eq_zero_of_no_common_overlap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:46:36.911666+00:00
-- url     : https://prove2.me/submissions/83b73e0d-9135-4b40-bc9d-1a3fa23908a4

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_cuboidEmbed_translateAxis_exists_or_eq_zero
public import Theorems.Thm_Auto_aux_overlap_index_eq
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
theorem _root_.solution
    {n : ℕ} (hn : 0 < n) {ε δ : ℝ} (hε : ε < 1)
    (hwidth : ε + δ < 1) (a : Fin n → aux_ZVector n → ℝ)
    (k : aux_ZVector n) (u : aux_RVector n) (s : ℝ)
    (hu : ∀ j, 0 ≤ u j ∧ u j < ε)
    (hno : ¬ ∃ m : ℤ, ∀ i, ε - u i ≤ s - (m : ℝ) ∧
      s - (m : ℝ) < ε + δ - u i) :
    (∏ i, aux_cuboidEmbed ε δ i (a i)
      (aux_translateAxis (fun j ↦ (k j : ℝ) + u j) i s)) = 0 := by
  classical
  have hmissing : ∃ i : Fin n, ¬ ∃ m : ℤ,
      ε - u i ≤ s - (m : ℝ) ∧ s - (m : ℝ) < ε + δ - u i := by
    by_contra hmissing
    push Not at hmissing
    choose M hM using hmissing
    let i₀ : Fin n := ⟨0, hn⟩
    apply hno
    refine ⟨M i₀, ?_⟩
    intro i
    have hEq : M i = M i₀ :=
      aux_overlap_index_eq hwidth u hu i i₀ s (M i) (M i₀) (hM i) (hM i₀)
    simpa [hEq] using hM i
  obtain ⟨i, hi⟩ := hmissing
  have hzero : aux_cuboidEmbed ε δ i (a i)
      (aux_translateAxis (fun j ↦ (k j : ℝ) + u j) i s) = 0 := by
    rcases aux_cuboidEmbed_translateAxis_exists_or_eq_zero hε hwidth i
      (a i) k u s hu with hyes | hno
    · exact False.elim
        (hi ⟨hyes.choose, hyes.choose_spec.1, hyes.choose_spec.2.1⟩)
    · exact hno.2
  exact Finset.prod_eq_zero_iff.mpr ⟨i, Finset.mem_univ i, hzero⟩
end Auto
