-- Prove2me | Definitions.Def_RiskAverseConsistency_EpiConvergesOn
-- name    : RiskAverseConsistency_EpiConvergesOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:21:13.031555+00:00
-- url     : https://prove2.me/theorems/7b9b935a-9d31-4a9b-a65e-ac64077d76b9
-- title:
--   Epiconvergence (Definition 2)
-- statement:
--   Let $V$ be a metric space and $S\subseteq V$. A sequence $\phi_k:S\to(-\infty,\infty]$ **epiconverges** to $\phi:S\to(-\infty,\infty]$ if for each $v\in S$
--
--   1. for each sequence $(v_k)\subset S$ with $v_k\to v$, $\liminf_{k\to\infty}\phi_k(v_k)\ge\phi(v)$, and
--   2. there exists $(v_k)\subset S$ with $v_k\to v$ such that $\limsup_{k\to\infty}\phi_k(v_k)\le\phi(v)$.
--
--   **Formalization Note** The paper states the definition on a complete metric space $V$; here it is relative to a subset $S$ of a metric space ($S=V$ gives the paper's definition, and a closed subset of a Banach space is the complete metric space to which Proposition 9 and Corollary 22 apply it). Values are in `EReal`; exclusion of $-\infty$ is a hypothesis of the theorems.
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.5, Definition 2

import Mathlib

open Filter Topology

namespace RiskAverseConsistency

/-- **Epiconvergence** (Definition 2) of `φₖ` to `φ` on a set `S` of a metric space: for each
`v ∈ S`,
1. for each sequence `(vₖ) ⊂ S` with `vₖ → v`, `liminf φₖ(vₖ) ≥ φ(v)`, and
2. there exists `(vₖ) ⊂ S` with `vₖ → v` such that `limsup φₖ(vₖ) ≤ φ(v)`.

Milz, Surowiec, arXiv:2207.14756v2, Definition 2, p.5.

Formalization Note: the paper's functions are `V → (−∞, ∞]` on a complete metric space `V`. Here
they are `EReal`-valued on the ambient metric space and every point and sequence is restricted to
`S`; with `S = univ` this is Definition 2 verbatim, and with `S` a closed subset of a Banach space
it is Definition 2 for the complete metric space `S` (the use made of it in Proposition 9 and
Corollary 22). The exclusion of the value `−∞` is a hypothesis of the theorems that use this. -/
def EpiConvergesOn {V : Type*} [MetricSpace V] (S : Set V) (φk : ℕ → V → EReal)
    (φ : V → EReal) : Prop :=
  ∀ v ∈ S,
    (∀ u : ℕ → V, (∀ k, u k ∈ S) → Tendsto u atTop (𝓝 v) →
      φ v ≤ liminf (fun k => φk k (u k)) atTop) ∧
    (∃ u : ℕ → V, (∀ k, u k ∈ S) ∧ Tendsto u atTop (𝓝 v) ∧
      limsup (fun k => φk k (u k)) atTop ≤ φ v)

end RiskAverseConsistency


