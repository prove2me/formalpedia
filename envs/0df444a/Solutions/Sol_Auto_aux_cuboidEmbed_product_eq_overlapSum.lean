-- Prove2me | solution 1 for Auto.aux_cuboidEmbed_product_eq_overlapSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:47:57.678349+00:00
-- url     : https://prove2.me/submissions/e1cb244f-6d5e-49f0-b23b-090f531afc30

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_cuboidEmbed_product_translateAxis_eq
public import Theorems.Thm_Auto_aux_overlap_index_eq
public import Theorems.Thm_Auto_aux_cuboidEmbed_product_eq_zero_of_no_common_overlap
public import Theorems.Thm_Auto_aux_commonOverlap_index_mem_range
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
    (hn : 0 < n) {ε δ : ℝ} (hε : ε < 1)
    (hwidth : ε + δ < 1) (a : Fin n → aux_ZVector n → ℝ)
    (k : aux_ZVector n) (u : aux_RVector n)
    (hu : ∀ i, 0 ≤ u i ∧ u i < ε) (N : ℕ) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) N) :
    (∏ i, aux_cuboidEmbed ε δ i (a i)
      (aux_translateAxis (fun j ↦ (k j : ℝ) + u j) i s)) =
      ∑ q : Fin N, aux_overlapContribution ε δ a k u q.val s := by
  classical
  by_cases hcommon : ∃ m : ℤ, ∀ i,
      ε - u i ≤ s - (m : ℝ) ∧ s - (m : ℝ) < ε + δ - u i
  · obtain ⟨m, hm⟩ := hcommon
    obtain ⟨q, hq⟩ :=
      aux_commonOverlap_index_mem_range hn hwidth u hu N hs m hm
    have hqreal : (q.val : ℝ) = (m : ℝ) := by
      exact_mod_cast hq
    have hqcommon : aux_commonOverlap ε δ u q.val s := by
      intro i
      simpa only [hqreal] using hm i
    have hleft : (∏ i, aux_cuboidEmbed ε δ i (a i)
        (aux_translateAxis (fun j ↦ (k j : ℝ) + u j) i s)) =
        ∏ i, a i (aux_translateAxisInt k i m) :=
      aux_cuboidEmbed_product_translateAxis_eq hε hwidth a k u m s hu hm
    rw [hleft]
    symm
    change (∑ q' : Fin N, aux_overlapContribution ε δ a k u q'.val s) =
      ∏ i, a i (aux_translateAxisInt k i m)
    let i₀ : Fin n := ⟨0, hn⟩
    refine (Fintype.sum_eq_single
      (f := fun q' : Fin N ↦ aux_overlapContribution ε δ a k u q'.val s)
      q ?_).trans ?_
    · intro q' hqne
      have hnot : ¬ aux_commonOverlap ε δ u q'.val s := by
        intro hq'
        have hq'int : ∀ i,
            ε - u i ≤ s - ((q'.val : ℤ) : ℝ) ∧
              s - ((q'.val : ℤ) : ℝ) < ε + δ - u i := by
          intro i
          simpa only [Int.cast_natCast] using hq' i
        have hqint : ∀ i,
            ε - u i ≤ s - ((q.val : ℤ) : ℝ) ∧
              s - ((q.val : ℤ) : ℝ) < ε + δ - u i := by
          intro i
          simpa only [Int.cast_natCast] using hqcommon i
        have heq : (q'.val : ℤ) = (q.val : ℤ) :=
          aux_overlap_index_eq hwidth u hu i₀ i₀ s
            (q'.val : ℤ) (q.val : ℤ) (hq'int i₀) (hqint i₀)
        have hval : q'.val = q.val := by
          exact_mod_cast heq
        exact hqne (Fin.ext hval)
      simp only [aux_overlapContribution, hnot, if_false]
    · simp only [aux_overlapContribution, hqcommon, if_true, hq]
  · have hzero : (∏ i, aux_cuboidEmbed ε δ i (a i)
        (aux_translateAxis (fun j ↦ (k j : ℝ) + u j) i s)) = 0 :=
      aux_cuboidEmbed_product_eq_zero_of_no_common_overlap hn hε hwidth
        a k u s hu hcommon
    rw [hzero]
    symm
    apply Fintype.sum_eq_zero
      (f := fun q : Fin N ↦ aux_overlapContribution ε δ a k u q.val s)
    intro q
    rw [aux_overlapContribution, if_neg]
    intro hq
    apply hcommon
    refine ⟨(q.val : ℤ), ?_⟩
    intro i
    simpa only [Int.cast_natCast] using hq i
end Auto
