-- Prove2me | solution 1 for Auto.measurable_carlesonLin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:53:26.813741+00:00
-- url     : https://prove2.me/submissions/532c94b0-48ed-4057-9736-f9d37335c0c5

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real
namespace Auto
theorem _root_.solution {T : ℕ → ℝ → ℂ} (hT : ∀ n, Measurable (T n)) (M : ℕ → ℝ)
    (lam : ℝ) (n : ℕ) : Measurable (carlesonLin T M lam n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact Measurable.ite (measurableSet_lt measurable_const (hT (n + 1)).norm)
      measurable_const ih
end Auto
