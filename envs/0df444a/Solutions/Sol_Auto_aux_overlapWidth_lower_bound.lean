-- Prove2me | solution 1 for Auto.aux_overlapWidth_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:46:22.13528+00:00
-- url     : https://prove2.me/submissions/1055fcb6-0146-4365-99ae-df264bdc42ab

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
    {ε δ : ℝ} (u : aux_RVector n) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ ε) :
    δ - ε ≤ aux_overlapWidth hn ε δ u := by
  let hne : (Finset.univ : Finset (Fin n)).Nonempty := aux_fin_univ_nonempty hn
  unfold aux_overlapWidth aux_overlapLower aux_overlapUpper
  dsimp
  have hsup : Finset.univ.sup' hne (fun i ↦ (0 : ℝ) + ε - u i) ≤ ε := by
    apply Finset.sup'_le hne
    intro i hi
    linarith [(hu i).1]
  have hinf : δ ≤ Finset.univ.inf' hne
      (fun i ↦ (0 : ℝ) + ε + δ - u i) := by
    apply Finset.le_inf' hne
    intro i hi
    linarith [(hu i).2]
  norm_num only [Nat.cast_zero, zero_add] at hsup hinf ⊢
  linarith
end Auto
