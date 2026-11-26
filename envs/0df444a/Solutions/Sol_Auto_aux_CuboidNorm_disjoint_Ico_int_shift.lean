-- Prove2me | solution 1 for Auto.aux_CuboidNorm.disjoint_Ico_int_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:40:40.179819+00:00
-- url     : https://prove2.me/submissions/38598f38-6810-418b-b74c-1930d3525904

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
open Auto.aux_CuboidNorm
namespace Auto.aux_CuboidNorm
theorem _root_.solution {c w : ℝ} (hw : w ≤ 1)
    {k l : ℤ} (hkl : k ≠ l) :
    Disjoint (Ico ((k : ℝ) + c) ((k : ℝ) + c + w))
      (Ico ((l : ℝ) + c) ((l : ℝ) + c + w)) := by
  apply Set.disjoint_left.2
  intro x hxk hxl
  rcases hxk with ⟨hxk₁, hxk₂⟩
  rcases hxl with ⟨hxl₁, hxl₂⟩
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hgapZ : k + 1 ≤ l := by omega
    have hgap : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hgapZ
    linarith
  · have hgapZ : l + 1 ≤ k := by omega
    have hgap : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hgapZ
    linarith
end Auto.aux_CuboidNorm
