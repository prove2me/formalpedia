-- Prove2me | Definitions.Def_TTTSampling_prefixMass
-- name    : TTTSampling_prefixMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:36:13.672545+00:00
-- url     : https://prove2.me/theorems/033d77e6-074a-43ed-8469-5ff07abfc2ee
-- title:
--   Prefix marginal $\mu(x)$ of a distribution on $\Sigma^n$
-- statement:
--   Let $\Sigma$ be a finite alphabet and $n\in\mathbb N$. For a probability distribution $\mu$ on $\Sigma^n$ and a finite string $x$, the **prefix marginal** is
--
--   $$
--   \mu(x)\;=\;\mu\bigl(\{v\in\Sigma^n : x \text{ is a prefix of } v\}\bigr),
--   $$
--
--   so that for $x\in\Sigma^i$, $i<n$, $\mu(x)=\mu(\{x\circ x' \mid x'\in\Sigma^{n-i}\})$, and for $x\in\Sigma^n$ it is the probability of $x$. In particular $\mu(\emptyset)=1$.
--
--   The paper uses one symbol $\mu(\cdot)$ for the distribution on $\Sigma^n$ and for its marginals on $\Sigma^{<n}$; every statement of this mission reads $\mu(x)$ through this definition.
--
--   **Formalization Note** Full strings are functions $\mathrm{Fin}\,n\to\Sigma$ and prefixes are lists; the value is $0$ for lists longer than $n$, which are not nodes of the paper's tree.
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), §3, p.17 (PDF p.19)

import Mathlib

namespace TTTSampling

/-- **Prefix marginal** `µ(x)` of a distribution `µ ∈ ∆(Σⁿ)` at a finite string `x`.

Golowich, Moitra, Rohatgi, *The Power of Test-Time Training for Approximate Sampling*,
arXiv:2606.11437 (version of November 3, 2026), §3, printed p.17 (PDF p.19): "we write, for any
µ ∈ ∆(Σⁿ) and x ∈ Σⁱ, i < n, µ(x) = µ({x∘x′ | x′ ∈ Σ^{n−i}})".

`prefixMass µ x` is the total mass of the full strings `v ∈ Σⁿ` whose list form `List.ofFn v` has
`x` as a prefix.

**Formalization Note**
* The alphabet `Σ` is a finite type `α`; full strings are `Fin n → α`; prefixes are `List α`.
* At `x = []` the value is `1` (the convention `µ(∅) = 1` of p.18 holds automatically); at a full
  string `x = List.ofFn v` it is `µ(v)`; for `x.length > n` it is `0` (no such string is a node of
  the paper's tree, and no statement of the mission evaluates it there). -/
noncomputable def prefixMass {α : Type} [Fintype α] [DecidableEq α] {n : ℕ}
    (μ : PMF (Fin n → α)) (x : List α) : ℝ :=
  ∑ v : Fin n → α, if x <+: List.ofFn v then (μ v).toReal else 0

end TTTSampling


