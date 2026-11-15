-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.fpk_pointwise_of_weak_distribution_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:37:27.691891+00:00
-- url     : https://prove2.me/submissions/e697cc59-55c6-4291-9829-482de0e3c093

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AppliedSDE_SarkkaSolin_fpk_fixed_time_weak_to_pointwise
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped Topology
set_option autoImplicit false
theorem solution
    (b a : ℝ → ℝ) (ρ : ℝ → ℝ → ℝ)
    (hb : ContDiff ℝ 2 b) (ha : ContDiff ℝ 2 a)
    (hρ : ∀ t : ℝ, ContDiff ℝ 2 (ρ t))
    (hdtcont : ∀ t : ℝ,
      Continuous (fun x : ℝ => deriv (fun s : ℝ => ρ s x) t))
    (hweak : ∀ (t : ℝ) (φ : ℝ → ℝ),
      ContDiff ℝ 2 φ → HasCompactSupport φ →
        (∫ x : ℝ, φ x *
          (deriv (fun s : ℝ => ρ s x) t +
            deriv (fun y : ℝ => b y * ρ t y) x -
            (1 / 2 : ℝ) *
              deriv (fun y : ℝ =>
                deriv (fun z : ℝ => a z * ρ t z) y) x)) = 0) :
    ∀ (t x : ℝ),
      deriv (fun s : ℝ => ρ s x) t =
        -deriv (fun y : ℝ => b y * ρ t y) x +
          (1 / 2 : ℝ) *
            deriv (fun y : ℝ => deriv (fun z : ℝ => a z * ρ t z) y) x := by
  intro t x
  exact AppliedSDE.SarkkaSolin.fpk_fixed_time_weak_to_pointwise
    b a (ρ t)
    (fun z => deriv (fun s => ρ s z) t)
    hb ha (hρ t) (hdtcont t) (hweak t) x
