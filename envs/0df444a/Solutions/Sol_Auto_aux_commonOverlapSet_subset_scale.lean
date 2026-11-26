-- Prove2me | solution 1 for Auto.aux_commonOverlapSet_subset_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:46:32.790793+00:00
-- url     : https://prove2.me/submissions/55fa2b44-6c4c-4e2a-9b26-0fb4cf5c766e

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference

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
    (hu : ∀ i, 0 ≤ u i ∧ u i < ε) (N : ℕ) (q : Fin N) :
    aux_commonOverlapSet ε δ u q.val ⊆ Ico (0 : ℝ) N := by
  intro s hs
  let i₀ : Fin n := ⟨0, hn⟩
  have hqnonneg : 0 ≤ (q.val : ℝ) := Nat.cast_nonneg q.val
  have hqsucc : q.val + 1 ≤ N := Nat.succ_le_iff.mpr q.isLt
  have hqsuccReal : (q.val : ℝ) + 1 ≤ (N : ℝ) := by
    exact_mod_cast hqsucc
  have hlower := hs i₀ |>.1
  have hupper := hs i₀ |>.2
  rw [mem_Ico]
  constructor
  · have hpositive : 0 < ε - u i₀ := sub_pos.mpr (hu i₀).2
    linarith
  · linarith [hwidth, (hu i₀).1]
end Auto
