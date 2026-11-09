-- Prove2me | Definitions.Def_MatchingGFT_TightE_Regularity
-- name    : MatchingGFT_TightE_Regularity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:59.400194+00:00
-- url     : https://prove2.me/theorems/372de863-f10d-4520-b217-a60650bf9043
-- title:
--   Regularity with atom interpolation, supports, disjoint edges, knapsack
-- statement:
--   A buyer law is regular if $R^{\mathrm{lin}}$ is concave and a seller law if $K^{\mathrm{lin}}$ is convex, where the curve is linearly interpolated across the quantile interval of each atom. Also: support in $[0,1]$, pairwise disjoint trading edges, and a single knapsack constraint with nonnegative weights and capacity.
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), §4, Appendix A, PDF pp. 18, 24

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_MatchingGFT_TightE_Quantile

open MeasureTheory Set

namespace MatchingGFT.TightE

variable {B S : Type*}

open Classical in
/-- `R^lin` (PDF p. 24): on the interior of the quantile interval `[P(v > a), P(v ≥ a)]` of an atom
at `a`, the linear interpolation of `R` between the endpoints; `R` elsewhere. These open intervals
are pairwise disjoint, so the atom is unique. -/
noncomputable def revCurveLin (F : Measure ℝ) (x : ℝ) : ℝ :=
  if h : ∃ a : ℝ, 0 < F.real {a} ∧ x ∈ Ioo (F.real (Ioi a)) (F.real (Ici a)) then
    let a := h.choose
    revCurve F (F.real (Ioi a)) +
      (x - F.real (Ioi a)) / (F.real (Ici a) - F.real (Ioi a)) *
        (revCurve F (F.real (Ici a)) - revCurve F (F.real (Ioi a)))
  else revCurve F x

open Classical in
/-- `K^lin` (PDF p. 24): on the interior of the quantile interval `[P(c < a), P(c ≤ a)]` of an atom at
`a`, the linear interpolation of `K` between the endpoints; `K` elsewhere. An endpoint value is
finite: an atom whose interval ends at `1` is the top of a bounded law, so `K(1) = a`. -/
noncomputable def costCurveLin (G : Measure ℝ) (x : ℝ) : ℝ :=
  if h : ∃ a : ℝ, 0 < G.real {a} ∧ x ∈ Ioo (G.real (Iio a)) (G.real (Iic a)) then
    let a := h.choose
    (costCurve G (G.real (Iio a))).toReal +
      (x - G.real (Iio a)) / (G.real (Iic a) - G.real (Iio a)) *
        ((costCurve G (G.real (Iic a))).toReal - (costCurve G (G.real (Iio a))).toReal)
  else (costCurve G x).toReal

/-- A buyer law is regular if `R^lin` is concave (PDF pp. 18, 24). -/
def IsRegularBuyerLaw (F : Measure ℝ) : Prop :=
  ConcaveOn ℝ (Icc 0 1) (revCurveLin F)

/-- A seller law is regular if `K^lin` is convex (PDF pp. 18, 24). The curve may tend to `+∞` at
`1`, so convexity is stated on `[0, 1)`; with `K(1)` the left limit, this is convexity on `[0, 1]`. -/
def IsRegularSellerLaw (G : Measure ℝ) : Prop :=
  ConvexOn ℝ (Ico 0 1) (costCurveLin G)

/-- The law gives mass one to `[0, 1]` (Theorem 4.1 (i), PDF p. 18). -/
def IsSupportedOnUnit (F : Measure ℝ) : Prop := F (Icc 0 1) = 1

/-- Theorem 4.1 (ii): all trading edges have pairwise disjoint endpoints. -/
def HasDisjointEdges (m : Market B S) : Prop :=
  ∀ e ∈ m.edges, ∀ e' ∈ m.edges, e ≠ e' → e.1 ≠ e'.1 ∧ e.2 ≠ e'.2

/-- Theorem 4.1 (iii): feasibility is a single knapsack constraint over the matchings of `E`, with
nonnegative weights and capacity. -/
def IsKnapsackFeasibility (m : Market B S) : Prop :=
  ∃ (w : B × S → ℝ) (C : ℝ), (∀ e, 0 ≤ w e) ∧ 0 ≤ C ∧
    ∀ M : Finset (B × S), M ∈ m.family ↔ IsMatching m.edges M ∧ ∑ e ∈ M, w e ≤ C

end MatchingGFT.TightE


