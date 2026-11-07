-- Prove2me | Definitions.Def_MonoTestDAG_copyEdge
-- name    : MonoTestDAG_copyEdge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:58.813382+00:00
-- url     : https://prove2.me/theorems/6c22f3e9-fae0-457a-bb2a-8aebee6db429
-- title:
--   Disjoint unions: $G^{(T)}$ and padding
-- statement:
--   $G^{(T)}$ is the disjoint union of $T$ copies of a directed graph $G_0=(V_0,E_0)$: its vertex set is $[T]\times V_0$, with an edge $(j,u)\to(j,v)$ for every edge $u\to v$ of $G_0$ and every $j$, and no edges between copies. The module also defines the disjoint union of two directed graphs (`unionEdge`).
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Lemma 5.4, pp.28–29 and Lemma 5.5, p.29

import Mathlib

namespace MonoTestDAG

/-- The disjoint union `G^{(T)}` of `T` copies of a directed graph `G₀ = (V₀, E₀)`: vertex set
`[T] × V₀`, and an edge `(j, u) → (j, v)` for every edge `u → v` of `G₀` and every copy `j`; no
edges between distinct copies.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Lemma 5.4, pp.28–29. -/
def copyEdge {V : Type} (E₀ : V → V → Prop) (T : ℕ) : Fin T × V → Fin T × V → Prop :=
  fun a b => a.1 = b.1 ∧ E₀ a.2 b.2

/-- The disjoint union of two directed graphs `(α, E₁)` and `(β, E₂)`: vertex set `α ⊔ β`, the
edges of each component, and no edges between the components.
Yoshida, arXiv:2602.15341 (sha256 454609db…), Lemma 5.5, p.29. -/
def unionEdge {α β : Type} (E₁ : α → α → Prop) (E₂ : β → β → Prop) : α ⊕ β → α ⊕ β → Prop
  | .inl a, .inl b => E₁ a b
  | .inr a, .inr b => E₂ a b
  | _, _ => False

end MonoTestDAG


