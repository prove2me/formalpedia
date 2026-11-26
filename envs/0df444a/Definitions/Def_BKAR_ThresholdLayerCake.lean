-- Prove2me | Definitions.Def_BKAR_ThresholdLayerCake
-- name    : BKAR_ThresholdLayerCake
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:19:40.398799+00:00
-- url     : https://prove2.me/theorems/dc803dc0-7a28-55de-9bc3-0be28c04fa48
-- title:
--   Threshold Layer Cake
-- statement:
--   Definitions and structural lemmas for Threshold Layer Cake, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean

import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_BKAR_ThresholdComponents
import Theorems.Thm_BKAR_Forest_mem_thresholdComponent
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_Forest_self_mem_thresholdComponent
attribute [local simp] BKAR.Forest.mem_thresholdComponent
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil
attribute [local simp] BKAR.Forest.self_mem_thresholdComponent


set_option autoImplicit false
namespace BKAR
open scoped BigOperators
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
def interpolationLevels (F : Forest V) (u : F.EdgeParam → ℝ) : Finset ℝ :=
  insert 0
    (insert 1
      ((Finset.univ : Finset (Edge V)).image fun e => F.standardInterp u e))
@[simp]
theorem zero_mem_interpolationLevels (F : Forest V) (u : F.EdgeParam → ℝ) :
    0 ∈ F.interpolationLevels u := by
  simp [interpolationLevels]
@[simp]
theorem one_mem_interpolationLevels (F : Forest V) (u : F.EdgeParam → ℝ) :
    1 ∈ F.interpolationLevels u := by
  simp [interpolationLevels]
theorem one_lt_interpolationLevels_card
    (F : Forest V) (u : F.EdgeParam → ℝ) :
    1 < (F.interpolationLevels u).card := by
  rw [Finset.one_lt_card]
  exact ⟨0, F.zero_mem_interpolationLevels u, 1,
    F.one_mem_interpolationLevels u, zero_ne_one⟩
theorem interpolationLevels_card_pos
    (F : Forest V) (u : F.EdgeParam → ℝ) :
    0 < (F.interpolationLevels u).card :=
  Nat.lt_trans Nat.zero_lt_one (F.one_lt_interpolationLevels_card u)
def interpolationLevel (F : Forest V) (u : F.EdgeParam → ℝ)
    (i : Fin (F.interpolationLevels u).card) : ℝ :=
  (F.interpolationLevels u).orderEmbOfFin rfl i
def interpolationLayerThreshold
    (F : Forest V) (u : F.EdgeParam → ℝ) (i : ℕ) : ℝ :=
  if hi : i < (F.interpolationLevels u).card - 1 then
    F.interpolationLevel u
      ⟨i + 1, by
        omega⟩
  else
    0
def interpolationGap
    (F : Forest V) (u : F.EdgeParam → ℝ) (i : ℕ) : ℝ :=
  if hi : i < (F.interpolationLevels u).card - 1 then
    F.interpolationLayerThreshold u i -
      F.interpolationLevel u
        ⟨i, by
          omega⟩
  else
    0
def interpolationLevelAux
    (F : Forest V) (u : F.EdgeParam → ℝ) (i : ℕ) : ℝ :=
  if hi : i < (F.interpolationLevels u).card then
    F.interpolationLevel u ⟨i, hi⟩
  else
    0
end
end Forest
end BKAR


