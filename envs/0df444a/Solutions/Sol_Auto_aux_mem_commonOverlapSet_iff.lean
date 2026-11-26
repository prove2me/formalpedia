-- Prove2me | solution 1 for Auto.aux_mem_commonOverlapSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:39:19.766099+00:00
-- url     : https://prove2.me/submissions/175b9dd5-5656-4e65-8fda-57cd9e50458a

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
theorem _root_.solution {n : ℕ} (hn : 0 < n)
    {ε δ s : ℝ} (u : aux_RVector n) (m : ℕ) :
    s ∈ aux_commonOverlapSet ε δ u m ↔
      s ∈ Ico (aux_overlapLower hn ε u m) (aux_overlapUpper hn ε δ u m) := by
  let hne : (Finset.univ : Finset (Fin n)).Nonempty := aux_fin_univ_nonempty hn
  simp only [aux_commonOverlapSet, Set.mem_ofPred_eq, mem_Ico]
  change (∀ i, ε - u i ≤ s - (m : ℝ) ∧
      s - (m : ℝ) < ε + δ - u i) ↔
    Finset.univ.sup' hne (fun i ↦ (m : ℝ) + ε - u i) ≤ s ∧
      s < Finset.univ.inf' hne (fun i ↦ (m : ℝ) + ε + δ - u i)
  constructor
  · intro hs
    constructor
    · apply Finset.sup'_le hne
      intro i hi
      linarith [(hs i).1]
    · exact (Finset.lt_inf'_iff _).2 fun i hi ↦ by
        linarith [(hs i).2]
  · rintro ⟨hl, hu⟩ i
    constructor
    · have hli := Finset.le_sup' (s := Finset.univ)
        (fun i ↦ (m : ℝ) + ε - u i) (Finset.mem_univ i)
      linarith
    · have hui := Finset.inf'_le (s := Finset.univ)
        (fun i ↦ (m : ℝ) + ε + δ - u i) (Finset.mem_univ i)
      linarith
end Auto
