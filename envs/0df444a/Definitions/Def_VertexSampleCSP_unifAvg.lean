-- Prove2me | Definitions.Def_VertexSampleCSP_unifAvg
-- name    : VertexSampleCSP_unifAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:28.863976+00:00
-- url     : https://prove2.me/theorems/37a2154e-04e1-485a-8167-d580c0b2aaeb
-- title:
--   Expectation and probability over a uniformly random $k$-subset
-- statement:
--   For a finite set $V$ and $k\in\mathbb N$, the expectation of $X(S)$ for $S$ uniform over the $k$-subsets of $V$ is
--
--   $$\frac{1}{\binom{|V|}{k}}\sum_{S\subseteq V,\ |S|=k}X(S),$$
--
--   and the probability of an event is the number of $k$-subsets in it divided by $\binom{|V|}{k}$.
--
--   **Formalization Note** For $k>|V|$ there is no $k$-subset and the formula gives $0/0=0$; every statement using these averages assumes $k\le|V|$.
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Theorem 1.1, p.2 (PDF p.4); Corollary D.2, p.18 (PDF p.20)

import Mathlib

namespace VertexSampleCSP

/-- **Expectation over a uniformly random `k`-subset.** Chang, *Optimal Vertex Sampling for
Constraint Satisfaction Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), Theorem 1.1,
p.2 (PDF p.4): "let S be a uniformly random set of k variables".

`unifAvg k X = (Σ_{S ⊆ V, |S| = k} X(S)) / C(|V|, k)`, the expectation of `X(S)` when `S` is uniform
over the `k`-subsets of `V`.

**Formalization Note.** For `k > |V|` there is no `k`-subset, the binomial is `0` and the value is the
junk `0 / 0 = 0`; every statement using it assumes `k ≤ |V|`. -/
noncomputable def unifAvg {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ) (X : Finset V → ℝ) : ℝ :=
  (∑ S ∈ Finset.powersetCard k Finset.univ, X S) / ((Fintype.card V).choose k : ℝ)

open Classical in
/-- **Probability over a uniformly random `k`-subset.** Chang, STOC 2027 submission (manuscript
sha256 1e0edd23…), Theorem 1.1, p.2 and Corollary D.2, p.18: `P(S satisfies P)` for `S` uniform over
the `k`-subsets of `V`, i.e. the number of `k`-subsets satisfying `P` divided by `C(|V|, k)`. -/
noncomputable def unifProb {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ) (P : Finset V → Prop) :
    ℝ :=
  (((Finset.powersetCard k Finset.univ).filter P).card : ℝ) / ((Fintype.card V).choose k : ℝ)

end VertexSampleCSP


