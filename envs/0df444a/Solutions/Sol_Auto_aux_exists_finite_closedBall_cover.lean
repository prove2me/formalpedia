-- Prove2me | solution 1 for Auto.aux_exists_finite_closedBall_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:43:53.692127+00:00
-- url     : https://prove2.me/submissions/c85462c4-3818-4bf3-9d0f-c1abbbc7c286

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (r : ℝ) (hr : 0 < r) (s : ℝ) :
    ∃ t : Finset E, ∀ y ∈ closedBall (0 : E) s, ∃ z ∈ t, y ∈ closedBall z r := by
  classical
  obtain ⟨u, -, hu, hcover⟩ :=
    (isCompact_closedBall (0 : E) s).finite_cover_balls (half_pos hr)
  refine ⟨hu.toFinset, ?_⟩
  intro y hy
  rcases Set.mem_iUnion₂.mp (hcover hy) with ⟨z, hzu, hyz⟩
  refine ⟨z, by simpa using hzu, ?_⟩
  exact Metric.mem_closedBall.mpr
    ((Metric.mem_ball.mp hyz).le.trans (by linarith))
end Auto
