-- Prove2me | solution 1 for Auto.aux_CuboidNorm.cuboidEmbed_eq_finiteLatticeStep_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:48:35.268602+00:00
-- url     : https://prove2.me/submissions/ab8edf93-58af-48b9-b405-54607efcf04e

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_mem_latticeAxisCuboid_iff
public import Theorems.Thm_Auto_aux_CuboidNorm_latticeAxisCuboid_pairwise_disjoint
public import Theorems.Thm_Auto_aux_CuboidNorm_finiteStep_apply_of_mem
public import Theorems.Thm_Auto_aux_CuboidNorm_finiteStep_apply_eq_zero

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
    (hsupport : ∀ k, k ∉ A → a k = 0) (y : RVector n) :
    aux_cuboidEmbed ε δ i a y = finiteLatticeStep ε δ i A a y := by
  classical
  have hεle : ε ≤ 1 := hε.le
  have hδle : δ ≤ 1 := by linarith
  by_cases hactive : ∃ k ∈ A, y ∈ latticeAxisCuboid ε δ i k
  · obtain ⟨k, hk, hy⟩ := hactive
    have hmem := (mem_latticeAxisCuboid_iff hε0 hε hεδ i k y).mp hy
    calc
      aux_cuboidEmbed ε δ i a y = a k := by
        unfold aux_cuboidEmbed
        rw [if_pos hmem.1]
        exact congrArg a hmem.2
      _ = finiteLatticeStep ε δ i A a y := by
        unfold finiteLatticeStep
        exact (finiteStep_apply_of_mem A (latticeAxisCuboid ε δ i) a
          (fun k hk l hl hkl ↦ latticeAxisCuboid_pairwise_disjoint hεle hδle i hkl)
          hk hy).symm
  · have hstepzero : finiteLatticeStep ε δ i A a y = 0 := by
      unfold finiteLatticeStep
      apply finiteStep_apply_eq_zero
      intro k hk hy
      exact hactive ⟨k, hk, hy⟩
    unfold aux_cuboidEmbed
    split_ifs with hcond
    · have hy : y ∈ latticeAxisCuboid ε δ i (fun j ↦ ⌊y j⌋) :=
        (mem_latticeAxisCuboid_iff hε0 hε hεδ i (fun j ↦ ⌊y j⌋) y).mpr
          ⟨hcond, rfl⟩
      have hnot : (fun j ↦ ⌊y j⌋) ∉ A := by
        intro hk
        exact hactive ⟨_, hk, hy⟩
      rw [hstepzero]
      exact hsupport _ hnot
    · exact hstepzero.symm
end Auto.aux_CuboidNorm
