-- Prove2me | solution 1 for Auto.carlesonLin_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:53:19.838569+00:00
-- url     : https://prove2.me/submissions/21968dda-17e5-405f-a4b4-54cd18b25911

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real
namespace Auto
theorem _root_.solution (T : ℕ → ℝ → ℂ) (M : ℕ → ℝ) (lam : ℝ) (n : ℕ) (x : ℝ) :
    ∃ m ≤ n, carlesonLin T M lam n x = M m := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
    simp only [carlesonLin]
    split_ifs
    · exact ⟨n + 1, le_rfl, rfl⟩
    · obtain ⟨m, hm, he⟩ := ih
      exact ⟨m, hm.trans (Nat.le_succ n), he⟩
end Auto
