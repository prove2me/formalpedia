-- Prove2me | Definitions.Def_GenEmpLik_Consistency_inclDist
-- name    : GenEmpLik_Consistency_inclDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:52:48.8344+00:00
-- url     : https://prove2.me/theorems/94410a56-a8ab-438b-94a7-060367d1b2e0
-- title:
--   Inclusion distance $d_\subset(A,B)=\sup_{x\in A}\operatorname{dist}(x,B)$
-- statement:
--   For subsets $A,B$ of a metric space, the **inclusion distance** (or **deviation**) from $A$ to $B$ is
--
--   $$
--   d_\subset(A,B)=\sup_{x\in A}\operatorname{dist}(x,B)=\inf\{\epsilon\ge0 : A\subset\{y:\operatorname{dist}(y,B)\le\epsilon\}\},
--   $$
--
--   where $\operatorname{dist}(x,B)=\inf_{y\in B}\|x-y\|$. It is zero exactly when every point of $A$ lies in the closure of $B$, and it measures how far a set of approximate solutions can stray from the true solution set; it is not symmetric.
--
--   **Formalization Note** The value lies in $[0,\infty]$ (Mathlib's extended infimum distance `Metric.infEDist`). Hence $\operatorname{dist}(x,\emptyset)=+\infty$, a supremum over an unbounded family is $+\infty$ rather than a junk value, and $d_\subset(\emptyset,B)=0$, in agreement with the infimum form above.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 5, (6)

import Mathlib

open scoped ENNReal

namespace GenEmpLik.Consistency

/-- The inclusion distance, or deviation, from a set `A` to a set `B` (arXiv:1610.03425v3,
(6), p. 5): `d_⊂(A, B) = sup_{x ∈ A} dist(x, B)`. It is valued in `[0, ∞]`: `dist(x, ∅) = ∞`
(the infimum over the empty set), the supremum over an unbounded family is `∞` rather than a
junk value, and `d_⊂(∅, B) = 0`, matching the form `inf {ε ≥ 0 : A ⊂ {y : dist(y, B) ≤ ε}}`. -/
noncomputable def inclDist {E : Type*} [PseudoMetricSpace E] (A B : Set E) : ℝ≥0∞ :=
  ⨆ x ∈ A, Metric.infEDist x B

end GenEmpLik.Consistency


