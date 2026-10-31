-- Prove2me | Definitions.Def_SuperPareto_IsWNA
-- name    : SuperPareto_IsWNA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:15:19.424835+00:00
-- url     : https://prove2.me/theorems/86018eba-9acd-4010-a6cc-8a72ef6d20b3
-- title:
--   Definition 2, p.5 — weakly negatively associated random variables
-- statement:
--   A set $S\subseteq\mathbb R^k$ is **decreasing** if $\mathbf x\in S$ and $\mathbf y\le\mathbf x$ (componentwise) imply $\mathbf y\in S$. Real random variables $X_1,\dots,X_n$ on $(\Omega,\mathcal F,P)$ are **weakly negatively associated** if for every index $i$, every measurable decreasing set $S\subseteq\mathbb R^{n-1}$ and every $x\in\mathbb R$,
--
--   $$
--   P(\mathbf X_{-i}\in S,\ X_i\le x)\ \le\ P(\mathbf X_{-i}\in S)\,P(X_i\le x),
--   $$
--
--   where $\mathbf X_{-i}=(X_1,\dots,X_{i-1},X_{i+1},\dots,X_n)$. When $P(X_i\le x)>0$ this is the paper's display (2), $P(\mathbf X_{-i}\in S\mid X_i\le x)\le P(\mathbf X_{-i}\in S)$: learning that $X_i$ is small makes the other variables less likely to be jointly small.
--
--   Independence is a special case, and negative association and negative regression dependence imply it. It is the dependence assumption of the main theorem.
--
--   **Formalization Note** The family is indexed by an arbitrary type $\iota$, and $\mathbf X_{-i}$ takes values in $\{j\,//\,j\ne i\}\to\mathbb R$ with the componentwise order, so "decreasing" is `IsLowerSet`. Only measurable decreasing sets are quantified over: a decreasing subset of $\mathbb R^k$, $k\ge2$, need not be Borel, and then $P(\mathbf X_{-i}\in S)$ has no meaning. The product form needs no positivity condition on $P(X_i\le x)$, since it reads $0\le0$ when that probability vanishes. Probabilities are the $[0,\infty]$-valued measure.
-- source:
--   Chen, Embrechts, Wang, An unexpected stochastic dominance: Pareto distributions, dependence, and diversification, arXiv:2208.08471v4, Definition 2 and display (2), p.5

import Mathlib

open MeasureTheory

namespace SuperPareto

/-- **Weak negative association.** Chen, Embrechts, Wang, *An unexpected stochastic dominance*,
arXiv:2208.08471v4, Definition 2, p.5: random variables `X₁, …, Xₙ` are weakly negatively
associated if for every `i`, every decreasing set `S ⊆ ℝ^{n−1}` and every `x ∈ ℝ` with
`P(Xᵢ ≤ x) > 0`,
`P(X₋ᵢ ∈ S | Xᵢ ≤ x) ≤ P(X₋ᵢ ∈ S)`  (2),
where `X₋ᵢ = (X₁, …, X_{i−1}, X_{i+1}, …, Xₙ)`. A set is decreasing if `x ∈ S` and `y ≤ x`
(componentwise) imply `y ∈ S`.

Here the family is `X : ι → Ω → ℝ`, the vector `X₋ᵢ` takes values in `{j // j ≠ i} → ℝ` (ordered
componentwise, so "decreasing" is `IsLowerSet`), and (2) is written in product form
`P(X₋ᵢ ∈ S, Xᵢ ≤ x) ≤ P(X₋ᵢ ∈ S) · P(Xᵢ ≤ x)`.

**Formalization Note.** (a) The product form is equivalent to (2) when `P(Xᵢ ≤ x) > 0` and holds
trivially (`0 ≤ 0`) when `P(Xᵢ ≤ x) = 0`, so no positivity condition on `x` is needed.
(b) Only measurable (Borel) decreasing sets are quantified over: a decreasing subset of `ℝ^k`,
`k ≥ 2`, need not be Borel, and then `P(X₋ᵢ ∈ S)` is undefined. Quantifying over fewer sets makes
the condition weaker, so every theorem assuming it is at least as strong as with the paper's
wording. (c) The index type is arbitrary; the paper's `[n]` is a `Fintype` index in the theorems
that use this notion. -/
def IsWNA {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ι → Ω → ℝ) : Prop :=
  ∀ (i : ι) (S : Set ({j // j ≠ i} → ℝ)), MeasurableSet S → IsLowerSet S → ∀ x : ℝ,
    P {ω | (fun j : {j // j ≠ i} => X j ω) ∈ S ∧ X i ω ≤ x} ≤
      P {ω | (fun j : {j // j ≠ i} => X j ω) ∈ S} * P {ω | X i ω ≤ x}

end SuperPareto


