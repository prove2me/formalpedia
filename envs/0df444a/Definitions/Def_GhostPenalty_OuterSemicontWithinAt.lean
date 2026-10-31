-- Prove2me | Definitions.Def_GhostPenalty_OuterSemicontWithinAt
-- name    : GhostPenalty_OuterSemicontWithinAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:02.903416+00:00
-- url     : https://prove2.me/theorems/60ad5aa0-e9ec-4e12-a0f6-a32918a16a8c
-- title:
--   Outer semicontinuity of a set-valued map relative to a set
-- statement:
--   A set-valued map $S$ is **outer semicontinuous at $\bar x$ relative to $A$** if
--   $$x_k\to\bar x,\ x_k\in A,\quad z_k\in S(x_k),\quad z_k\to z\quad\Longrightarrow\quad z\in S(\bar x).$$
--   Equivalently, the outer limit of $S$ at $\bar x$ relative to $A$ is contained in $S(\bar x)$ (Rockafellar–Wets, *Variational Analysis*, Def. 5.4).
--
--   **Formalization Note** The sequential form, which is the definition of [54] in the finite-dimensional spaces where it is used.
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, Lemma 1 (iii), p.9, proof p.10 (via Rockafellar–Wets, Def. 5.4)

import Mathlib

namespace GhostPenalty

open Filter Topology

/-- **Outer semicontinuity of a set-valued mapping at `x̄` relative to a set `A`.**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, Lemma 1 (iii), p.9, and its proof, p.10, which refer to [54] (Rockafellar & Wets,
*Variational Analysis*, Def. 5.4) "for the definition of outer semicontinuity".

`S` is outer semicontinuous at `x̄` relative to `A` if whenever `x_k → x̄` with `x_k ∈ A`,
`z_k ∈ S(x_k)` and `z_k → z`, then `z ∈ S(x̄)` (the outer limit of `S` at `x̄` relative to `A`
is contained in `S(x̄)`).

**Formalization Note.** The sequential definition, which is Rockafellar–Wets' definition in the
finite-dimensional (metric) spaces where it is used; the proof of Lemma 1 (iii) uses exactly this
form. -/
def OuterSemicontWithinAt {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (S : α → Set β) (A : Set α) (xbar : α) : Prop :=
  ∀ (xk : ℕ → α) (zk : ℕ → β) (z : β), (∀ k, xk k ∈ A) → Tendsto xk atTop (𝓝 xbar) →
    (∀ k, zk k ∈ S (xk k)) → Tendsto zk atTop (𝓝 z) → z ∈ S xbar

end GhostPenalty


