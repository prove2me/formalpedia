-- Prove2me | solution 1 for Auto.lt_norm_carlesonLin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:54:16.554122+00:00
-- url     : https://prove2.me/submissions/7130c8e9-28c2-4fa8-9d8a-ab6ffe3ceadf

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
theorem _root_.solution {h : ℝ → ℂ} {M : ℕ → ℝ} {lam : ℝ} (n : ℕ) {x : ℝ}
    (hx : ∃ m ≤ n, lam < ‖carlesonOp h (fun _ => M m) x‖) :
    lam < ‖carlesonOp h (carlesonLin (fun m => carlesonOp h fun _ => M m) M lam n) x‖ := by
  induction n with
  | zero =>
    obtain ⟨m, hm, hl⟩ := hx
    obtain rfl := Nat.le_zero.mp hm
    exact hl
  | succ n ih =>
    by_cases hn : lam < ‖carlesonOp h (fun _ => M (n + 1)) x‖
    · have : carlesonLin (fun m => carlesonOp h fun _ => M m) M lam (n + 1) x = M (n + 1) := by
        simp [carlesonLin, hn]
      simpa [carlesonOp, this] using hn
    · have he : carlesonLin (fun m => carlesonOp h fun _ => M m) M lam (n + 1) x =
          carlesonLin (fun m => carlesonOp h fun _ => M m) M lam n x := by
        simp [carlesonLin, hn]
      obtain ⟨m, hm, hl⟩ := hx
      have hm' : m ≤ n := by
        rcases Nat.lt_or_ge m (n + 1) with h' | h'
        · exact Nat.lt_succ_iff.mp h'
        · exact absurd (le_antisymm hm h' ▸ hl) hn
      have := ih ⟨m, hm', hl⟩
      simpa [carlesonOp, he] using this
end Auto
