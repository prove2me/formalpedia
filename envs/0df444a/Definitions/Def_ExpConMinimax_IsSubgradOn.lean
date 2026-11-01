-- Prove2me | Definitions.Def_ExpConMinimax_IsSubgradOn
-- name    : ExpConMinimax_IsSubgradOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:46.08847+00:00
-- url     : https://prove2.me/theorems/b0554d10-e54f-4430-bfb6-1fb429b4948f
-- title:
--   Subgradient and supergradient relative to a set
-- statement:
--   Let $\varphi:E\to\mathbb R$ be a function on a real inner-product space, $S\subseteq E$ and $x\in E$.
--
--   1. A vector $g$ is a **subgradient of $\varphi$ at $x$ relative to $S$** if
--   $$\varphi(x)+\langle g,u-x\rangle\le\varphi(u)\qquad\text{for all }u\in S.$$
--   2. A vector $g$ is a **supergradient of $\varphi$ at $x$ relative to $S$** if
--   $$\varphi(u)\le\varphi(x)+\langle g,u-x\rangle\qquad\text{for all }u\in S.$$
--
--   These are the inequalities behind the paper's memberships $\widetilde\nabla_xF(x,y)\in\partial_xF(x,y)$, $\widetilde\nabla H(x)\in\partial H(x)$ (subgradients of convex functions) and $\widetilde\nabla_yF(x,y)\in\partial_yF(x,y)$ (a supergradient of the concave function $F(x,\cdot)$).
--
--   **Formalization Note** The inequalities are required only at points of $S$ (the feasible regions $\mathcal X$, $\mathcal Y$), where the paper uses them.
-- source:
--   Yang, Li, Lan, Data-Driven Minimax Optimization with Expectation Constraints, arXiv:2202.07868v2, Assumptions 2.1–2.2, p.9

import Mathlib

namespace ExpConMinimax

/-- **Subgradient relative to a set.**
arXiv:2202.07868v2, Assumptions 2.1–2.2, p.9: "`∇̃ₓF(x,y) ∈ ∂ₓF(x,y)`", "`∇̃H(x) ∈ ∂H(x)`",
"`∇̃G(y) ∈ ∂G(y)`".

`g` is a subgradient of `φ` at `x` relative to `S` iff
`φ x + ⟨g, u − x⟩ ≤ φ u` for every `u ∈ S`.

**Formalization Note.** The paper's subdifferentials are used only through this inequality at
points of the feasible sets `X`, `Y` (proof of Lemma 2, App. B.2). Requiring it only on `S`
(rather than on the whole space) is a weaker hypothesis. -/
def IsSubgradOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : E → ℝ) (S : Set E) (x g : E) : Prop :=
  ∀ u ∈ S, φ x + inner ℝ g (u - x) ≤ φ u

/-- **Supergradient relative to a set** (the subdifferential of a concave function).
arXiv:2202.07868v2, Assumption 2.1, p.9: "`∇̃_yF(x,y) ∈ ∂_yF(x,y)`" for the concave function
`F(x,·)`.

`g` is a supergradient of `φ` at `x` relative to `S` iff `φ u ≤ φ x + ⟨g, u − x⟩` for every
`u ∈ S`. -/
def IsSupergradOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : E → ℝ) (S : Set E) (x g : E) : Prop :=
  ∀ u ∈ S, φ u ≤ φ x + inner ℝ g (u - x)

end ExpConMinimax


