-- Prove2me | Definitions.Def_FD1D_UniformArrival
-- name    : FD1D_UniformArrival
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:17:25.903107+00:00
-- url     : https://prove2.me/theorems/2b4d0c73-dcfd-49b8-a841-f37b6431b535
-- title:
--   Uniform Arrival
-- statement:
--   Definitions and structural lemmas for Uniform Arrival, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/UniformArrival.lean

import Definitions.Def_FD1D_Spatial
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_SupplyConfiguration_countState_apply
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.SupplyConfiguration.countState_apply
attribute [local simp] FD1D.weightedLevel_zero


set_option autoImplicit true
namespace FD1D
noncomputable section
open Set MeasureTheory
namespace DyadicMass
def constantLeafMass : (L : ℕ) → ℝ → DyadicMass L
  | 0, c => .leaf c
  | L + 1, c => .branch (constantLeafMass L c) (constantLeafMass L c)
@[simp]
theorem leafMass_constantLeafMass (L : ℕ) (c : ℝ) (i : DyadicNode L) :
    (constantLeafMass L c).leafMass i = c := by
  induction L with
  | zero =>
      simp [constantLeafMass, leafMass]
  | succ L ih =>
      obtain ⟨i | i, rfl⟩ := (dyadicLeafSumEquiv L).surjective i
      · simp [constantLeafMass, ih]
      · simp [constantLeafMass, ih]
@[simp]
theorem total_constantLeafMass (L : ℕ) (c : ℝ) :
    (constantLeafMass L c).total = ((2 ^ L : ℕ) : ℝ) * c := by
  induction L with
  | zero =>
      simp [constantLeafMass, total]
  | succ L ih =>
      simp only [constantLeafMass, total, ih]
      rw [pow_succ]
      push_cast
      ring
theorem allNonneg_constantLeafMass (L : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    (constantLeafMass L c).allNonneg := by
  induction L with
  | zero =>
      simpa [constantLeafMass, allNonneg] using hc
  | succ L ih =>
      simpa [constantLeafMass, allNonneg] using And.intro ih ih
def uniformArrivalMass (L : ℕ) : DyadicMass L :=
  constantLeafMass L (1 / ((2 ^ L : ℕ) : ℝ))
@[simp]
theorem uniformArrivalMass_leafMass (L : ℕ) (i : DyadicNode L) :
    (uniformArrivalMass L).leafMass i = 1 / ((2 ^ L : ℕ) : ℝ) := by
  simp [uniformArrivalMass]
theorem uniformArrivalMass_isProbability (L : ℕ) :
    (uniformArrivalMass L).IsProbability := by
  constructor
  · exact allNonneg_constantLeafMass L (by positivity)
  · simp only [uniformArrivalMass, total_constantLeafMass]
    have hpow : (((2 ^ L : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp
def uniformArrivalLeaf (L : ℕ) (u : ℝ) : DyadicNode L :=
  (uniformArrivalMass L).selectedIndex u
def uniformArrivalLeafLaw (L : ℕ) : FiniteLaw (DyadicNode L) :=
  (uniformArrivalMass L).selectedIndexLaw
    (uniformArrivalMass_isProbability L)
end DyadicMass
end
end FD1D


