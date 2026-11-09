-- Prove2me | Definitions.Def_ListReplicableBias_LowerBound_ListReplicability
-- name    : ListReplicableBias_LowerBound_ListReplicability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:49.283842+00:00
-- url     : https://prove2.me/theorems/a76967bd-dc35-4ac7-bbb3-611c68c9c818
-- title:
--   List replicability for coin-bias estimation
-- statement:
--   Let $k,d,N\in\mathbb N$, let $\varepsilon,\delta>0$, and let $A$ be an $N$-toss sampling algorithm. It is $(k,\varepsilon,\delta)$-list replicable if for every bias vector $p\in[0,1]^d$ there exists a finite set $L_p\subseteq\mathbb R^d$ such that
--   $$|L_p|\le k,\qquad \forall y\in L_p,\ \|y-p\|_\infty\le\varepsilon,\qquad \Pr_p(Y\in L_p)\ge1-\delta.$$
--   The set is chosen for $p$, independently of the realized seed and tosses; failure is excluded from it.
--
--   This is Definition 3.3, including all three clauses. The predicate supplies the subject of the sample lower bound and imposes no allocation restriction on the algorithm. Finite sets are represented by `Finset`; vector closeness is non-strict. The formula is defined for all real parameters for convenience, and all theorem uses retain the source's positive parameter domain.
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Definition 3.3, PDF p. 3

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_Geometry
import Definitions.Def_ListReplicableBias_LowerBound_Sampling

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound

/-- Definition 3.3, PDF p. 3. The finite list is chosen for each bias vector,
before any seed or samples. Failure (none) is never a list entry. The predicate
is used with ε,δ > 0, as required by the definition's stated domain. -/
def IsListReplicable {d N : ℕ} (A : SamplingAlgorithm d N)
    (k : ℕ) (ε δ : ℝ) : Prop :=
  ∀ p ∈ cube d 0 1, ∃ L : Finset (Fin d → ℝ),
    L.card ≤ k ∧ (∀ y ∈ L, ‖y - p‖ ≤ ε) ∧
      1 - δ ≤ outputProb A p (some '' (L : Set (Fin d → ℝ)))

end ListReplicableBias.LowerBound


