-- Prove2me | Definitions.Def_VertexSampleCSP_Supplement_SampleAlgorithm
-- name    : VertexSampleCSP_Supplement_SampleAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:58:51.432122+00:00
-- url     : https://prove2.me/theorems/9fab0fd0-0ded-43a6-9a3f-4a32b0bdeb57
-- title:
--   Algorithms with sample size $k$ and their failure probability
-- statement:
--   **The observation model of Appendix E.** An algorithm with sample size $k$ receives a uniformly random set $S$ of $k$ distinct variables together with the subinstance $\mathcal I[S]$, labeled by the names of the variables, and outputs a real number, possibly using additional randomness. Since this extra randomness is independent of everything else, such an algorithm is described by the law $A(S,\mathcal I[S])$ of its output, a probability measure on $\mathbb R$ for each observation; deterministic algorithms are the Dirac laws.
--
--   The **failure probability** of $A$ on an instance $\mathcal I$ at threshold $\tau$ is
--
--   $$\mathrm{fail}_k(A,\mathcal I,\tau)=\binom{|V|}{k}^{-1}\sum_{|S|=k} A(S,\mathcal I[S])\big(\{y\in\mathbb R:|y-\mathrm{OPT}(\mathcal I)|>\tau\}\big),$$
--
--   the probability, over the sample and the algorithm's randomness, that the output differs from $\mathrm{OPT}(\mathcal I)$ by more than $\tau$.
--
--   These are the objects quantified in the lower bounds (Theorems E.1 and E.4).
--
--   **Formalization Note** The uniform average is the published `unifAvg`, which returns $0$ for $k>|V|$; the theorems using it either imply $k\le|V|$ or let the prover choose $n$ large. The failure event is open, hence measurable.
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix E, "The observation model", p.20 (PDF p.22)

import Mathlib
import Definitions.Def_VertexSampleCSP_Instance
import Definitions.Def_VertexSampleCSP_OPT
import Definitions.Def_VertexSampleCSP_Instance_sub
import Definitions.Def_VertexSampleCSP_unifAvg

namespace VertexSampleCSP.Supplement

open MeasureTheory

/-- **Algorithm with sample size `k` (the observation model of Appendix E).** Chang, *Optimal Vertex
Sampling for Constraint Satisfaction Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…),
Appendix E, "The observation model", p.20 (PDF p.22): "An algorithm with sample size k receives a
uniformly random set S of k distinct variables together with the subinstance I[S], labeled by the
names of the variables, and outputs a number, possibly using additional randomness."

A `SampleAlgorithm V r q` maps a set `S` of variables (with their names) and a subinstance on `S` to
the law of its real output, a probability measure on `ℝ`.

**Formalization Note.** The algorithm's additional randomness is independent of everything else, so
an algorithm is the same as its output law given the observation `(S, I[S])`; a deterministic
algorithm is the case of a Dirac law. The sample size `k` is not part of the type: it enters through
the uniform average over `k`-subsets in `failProb`. -/
abbrev SampleAlgorithm (V : Type*) [Fintype V] [DecidableEq V] (r q : ℕ) :=
  (S : Finset V) → Instance S r q → ProbabilityMeasure ℝ

/-- **Failure probability of an algorithm with sample size `k`.** Chang, STOC 2027 submission
(manuscript sha256 1e0edd23…), Appendix E, p.20 (PDF p.22), Theorems E.1 and E.4: the probability
that "the output differs from OPT(I) by more than τ".

`failProb k A I τ` is the probability, over the uniformly random `k`-subset `S` of the variables and
the algorithm's own randomness, that the output of `A` on `(S, I[S])` lies at distance more than `τ`
from `OPT(I)`:
`failProb k A I τ = C(|V|, k)⁻¹ Σ_{|S| = k} A(S, I[S]) {y : |y − OPT(I)| > τ}`.

**Formalization Note.** The uniform average is the published `unifAvg`, which is the junk value `0`
when `k > |V|`; the statements using `failProb` either assume or imply `k ≤ |V|`. The event
`{y : τ < |y − OPT(I)|}` is open, hence measurable. -/
noncomputable def failProb {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ} (k : ℕ)
    (A : SampleAlgorithm V r q) (I : Instance V r q) (τ : ℝ) : ℝ :=
  unifAvg k (fun S => ((A S (I.sub S)) {y : ℝ | τ < |y - OPT I|} : ℝ))

end VertexSampleCSP.Supplement


