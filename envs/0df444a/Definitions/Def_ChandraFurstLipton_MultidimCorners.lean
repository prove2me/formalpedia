-- Prove2me | Definitions.Def_ChandraFurstLipton_MultidimCorners
-- name    : ChandraFurstLipton_MultidimCorners
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T18:13:15.002851+00:00
-- url     : https://prove2.me/theorems/41a89f5f-56a5-48a8-83d2-d928530547eb
-- title:
--   Multidim Corners
-- statement:
--   Definitions and structural lemmas for Multidim Corners, from Yaël Dillies and Isabel Dahlgren's pinned Chandra–Furst–Lipton: number-on-the-forehead protocols development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/MultidimCorners.lean

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace NOF
variable {ι G : Type*} {a : ι → ι → G} {v : ι → G}
def forget (i : ι) (x : ι → G) (j : {j : ι // j ≠ i}) : G := x j
def IsForbiddenPatternWithTip (a : ι → ι → G) (v : ι → G) : Prop := ∀ ⦃i j⦄, i ≠ j → a i j = v j
def IsForbiddenPattern (a : ι → ι → G) : Prop := ∃ v, IsForbiddenPatternWithTip a v
lemma isForbiddenPatternWithTip_iff_forget :
    IsForbiddenPatternWithTip a v ↔ ∀ i, forget i v = forget i (a i) := by
  simp [funext_iff, IsForbiddenPatternWithTip, eq_comm, forget]
protected lemma IsForbiddenPatternWithTip.forget (h : IsForbiddenPatternWithTip a v) :
    ∀ i, forget i v = forget i (a i) := isForbiddenPatternWithTip_iff_forget.mp h
variable [Fintype ι] [AddCommGroup G]
structure IsMultidimCorner (a : ι → ι → G) (b : ι → G) : Prop where
  sum_eq_sum : ∀ i j, ∑ k, a i k = ∑ k, a j k
  isForbiddenPatternWithTip : IsForbiddenPatternWithTip a b
variable [DecidableEq ι]
end NOF


