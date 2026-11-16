-- Prove2me | Definitions.Def_OnlinePerceptronIsolation_Binary_Supplement_WellSeparated
-- name    : OnlinePerceptronIsolation_Binary_Supplement_WellSeparated
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:06:20.874303+00:00
-- url     : https://prove2.me/theorems/314511c9-9c1a-4a78-a135-b6dfeb4abfb2
-- title:
--   Definition 2.4 — well-separated unions of intervals
-- statement:
--   A set $K\subseteq\mathbb R$ is well-separated if there are a real number $\Delta>0$ and a family $\mathcal I$ of real intervals such that
--   $$K=\bigcup_{I\in\mathcal I}I,\qquad |x-y|\ge\Delta\quad(I,J\in\mathcal I,\ I\ne J,\ x\in I,\ y\in J).$$
--   Intervals are order-connected subsets: their endpoints may be included or excluded, and single points, empty intervals and unbounded intervals are allowed. The family can be infinite. No maximality or extra measurability assumption is imposed. This is precisely the input class of the general-perceptron companion theorem.
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Definition 2.4, printed p. 6, PDF p. 8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary.Supplement

/-- Definition 2.4: an arbitrary family of intervals with a single positive gap.
No finiteness, endpoint closure, boundedness or nonemptiness is imposed. -/
def WellSeparated (K : Set ℝ) : Prop :=
  ∃ Δ : ℝ, 0 < Δ ∧ ∃ intervals : Set (Set ℝ),
    K = ⋃₀ intervals ∧
    (∀ I ∈ intervals, Set.OrdConnected I) ∧
    ∀ I ∈ intervals, ∀ J ∈ intervals, I ≠ J →
      ∀ x ∈ I, ∀ y ∈ J, Δ ≤ |x - y|

end OnlinePerceptronIsolation.Binary.Supplement


