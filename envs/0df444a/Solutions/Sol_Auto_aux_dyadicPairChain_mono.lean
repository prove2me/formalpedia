-- Prove2me | solution 1 for Auto.aux_dyadicPairChain_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:40:55.424433+00:00
-- url     : https://prove2.me/submissions/9fa6e8d6-346b-4ba3-829a-795cca60b315

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {J : ℕ} {k : ℤ} (x : aux_dyadicInterval k) :
    Monotone (aux_dyadicPairChain J k x) := by
  intro i j hij
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      rfl
    · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hj
      change (2 : ℝ) ^ k ≤ (x : ℝ)
      exact x.2.1
  · obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hi
    have hjpos : (0 : Fin (J + 1)) < j := lt_of_lt_of_le (Fin.succ_pos i) hij
    have hj : j ≠ 0 := Fin.ne_of_gt hjpos
    obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hj
    simp [aux_dyadicPairChain]
end Auto
