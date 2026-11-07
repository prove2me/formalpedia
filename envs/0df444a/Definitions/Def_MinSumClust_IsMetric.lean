-- Prove2me | Definitions.Def_MinSumClust_IsMetric
-- name    : MinSumClust_IsMetric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:46:37.479494+00:00
-- url     : https://prove2.me/theorems/20921742-1346-49c1-8d88-15956b357ee2
-- title:
--   Pseudometrics and metrics on the clients
-- statement:
--   A function $d : D\times D\to\mathbb R$ is a **pseudometric** if $d(i,i)=0$, $d(i,j)\ge 0$, $d(i,j)=d(j,i)$ and $d(i,l)\le d(i,j)+d(j,l)$ for all clients $i,j,l$. It is a **metric** if moreover $d(i,j)>0$ whenever $i\ne j$.
--
--   The paper's input is a finite metric ("metric distances $d(u,v)\ge 0$", p.1); positivity of distinct points is used in Lemma 14 (p.22) and at the end of §4.5.4 (p.42). The bipoint rounding of §5 and Observation 39 only use the pseudometric axioms, and those milestones are stated for pseudometrics.
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), §1, p.1 (PDF p.3); Lemma 14, p.22; §4.5.4, p.42

import Mathlib

namespace MinSumClust

/-- **Pseudometric**: `d(i,i) = 0`, `d ≥ 0`, symmetry and the triangle inequality.

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), §1, p.1 ("metric distances d(u, v) ≥ 0").

**Formalization Note.** The rounding milestones of §5 and Observation 39 are stated for
pseudometrics (distinct points may be at distance 0), which contain the paper's metrics. -/
def IsPseudometric {D : Type*} (d : D → D → ℝ) : Prop :=
  (∀ i, d i i = 0) ∧ (∀ i j, 0 ≤ d i j) ∧ (∀ i j, d i j = d j i) ∧
    (∀ i j l, d i l ≤ d i j + d j l)

/-- **Metric**: a pseudometric with `d(i, j) > 0` for `i ≠ j`, §1, p.1 (Anand et al., STOC 2027
submission).

**Formalization Note.** Positivity of distinct points is used by the paper (Lemma 14, p.22:
"Because we assume that d is a metric, we have cost(S) > 0 if |S| ≥ 2"; end of §4.5.4, p.42), so
the goal, Theorem 2 and the Algorithm 3 milestones assume it. -/
def IsMetric {D : Type*} (d : D → D → ℝ) : Prop :=
  IsPseudometric d ∧ ∀ i j, i ≠ j → 0 < d i j

end MinSumClust


