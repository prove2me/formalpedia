-- Prove2me | Definitions.Def_GhostPenalty_InnerSemicontWithinAt
-- name    : GhostPenalty_InnerSemicontWithinAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:00.610542+00:00
-- url     : https://prove2.me/theorems/7b91653e-54bb-4fbf-b18c-5c32dec6b9af
-- title:
--   Inner semicontinuity of a set-valued map relative to a set
-- statement:
--   A set-valued map $S$ is **inner semicontinuous at $\bar x$ relative to $A$** if for every $z\in S(\bar x)$ and every sequence $x_k\to\bar x$ with $x_k\in A$ there are $z_k\in S(x_k)$, for all large $k$, with $z_k\to z$. Equivalently, the inner limit of $S$ at $\bar x$ relative to $A$ contains $S(\bar x)$ (Rockafellar–Wets, Def. 5.4). $S$ is **continuous** at $\bar x$ relative to $A$ when it is both outer and inner semicontinuous there.
--
--   **Formalization Note** Sequential form, as in the finite-dimensional setting of [54].
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, Lemma 1 (ii), p.9; proof of (iii), p.10 (via Rockafellar–Wets, Def. 5.4)

import Mathlib

namespace GhostPenalty

open Filter Topology

/-- **Inner semicontinuity of a set-valued mapping at `x̄` relative to a set `A`.**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, Lemma 1 (ii), p.9, and the proof of Lemma 1 (iii), p.10: "By the inner semicontinuity
relative to K (see [54] for the definition of inner semicontinuity) of `βBⁿ∞ ∩ (K − •)` at `x̄`,
`z^ν` exists such that `z^ν → z̄` and `z^ν ∈ βBⁿ∞ ∩ (K − x^ν)`."

`S` is inner semicontinuous at `x̄` relative to `A` if for every `z ∈ S(x̄)` and every sequence
`x_k → x̄` with `x_k ∈ A` there are `z_k ∈ S(x_k)` (for all large `k`) with `z_k → z` (the inner
limit of `S` at `x̄` relative to `A` contains `S(x̄)`, Rockafellar & Wets, Def. 5.4).

**Formalization Note.** Sequential definition, as in the finite-dimensional setting of [54]. A
set-valued mapping is *continuous* at `x̄` relative to `A` when it is both outer and inner
semicontinuous there. -/
def InnerSemicontWithinAt {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (S : α → Set β) (A : Set α) (xbar : α) : Prop :=
  ∀ z ∈ S xbar, ∀ xk : ℕ → α, (∀ k, xk k ∈ A) → Tendsto xk atTop (𝓝 xbar) →
    ∃ zk : ℕ → β, (∀ᶠ k in atTop, zk k ∈ S (xk k)) ∧ Tendsto zk atTop (𝓝 z)

end GhostPenalty


