-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.compact_second_ibp_one_dim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:25:59.862197+00:00
-- url     : https://prove2.me/submissions/5232d138-dbbd-4ce4-8502-02c823ac3b4a

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AppliedSDE_SarkkaSolin_compact_ibp_one_dim
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped Topology
set_option autoImplicit false
theorem solution
    (u v : ℝ -> ℝ) (hu : ContDiff ℝ 2 u)
    (hv : ContDiff ℝ 2 v) (hcompact : HasCompactSupport u) :
    (∫ x : ℝ, u x * deriv (deriv v) x) =
      (∫ x : ℝ, deriv (deriv u) x * v x) := by
  have hfirst :=
    AppliedSDE.SarkkaSolin.compact_ibp_one_dim
      u (deriv v) (hu.of_le (by norm_num)) hv.deriv' hcompact
  have hsecond :=
    AppliedSDE.SarkkaSolin.compact_ibp_one_dim
      (deriv u) v hu.deriv' (hv.of_le (by norm_num)) hcompact.deriv
  calc
    _ = -(∫ x : ℝ, deriv u x * deriv v x) := hfirst
    _ = (∫ x : ℝ, deriv (deriv u) x * v x) := by
      rw [hsecond]
      ring
