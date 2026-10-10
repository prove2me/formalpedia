-- Prove2me | Definitions.Def_ShortestGCS_MICP_Perspective
-- name    : ShortestGCS_MICP_Perspective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:42.403282+00:00
-- url     : https://prove2.me/theorems/8f8fb6eb-3287-43e6-ace4-35759f4dce7c
-- title:
--   Definition 4.1, p. 5 — the perspective 𝒳̃ = cl{(x, λ) : λ ≥ 0, x ∈ λ𝒳} of a set
-- statement:
--   Let $E$ be a real topological vector space and $\mathcal X \subseteq E$. The **perspective** of $\mathcal X$ is the closed cone
--
--   $$
--   \tilde{\mathcal X} := \operatorname{cl}\{(x,\lambda) \in E \times \mathbb R : \lambda \ge 0,\ x \in \lambda \mathcal X\},
--   $$
--
--   where $\lambda\mathcal X = \{\lambda x : x \in \mathcal X\}$ and $\operatorname{cl}$ is the topological closure in $E \times \mathbb R$. Before the closure is taken, the slice at height $\lambda > 0$ is the scaled copy $\lambda\mathcal X$, and the slice at $\lambda = 0$ is $0\cdot\mathcal X$, which is $\{0\}$ when $\mathcal X$ is nonempty and empty otherwise. The closure adds the limit points; for a nonempty closed convex $\mathcal X$ it leaves the slices at $\lambda > 0$ unchanged and adds at $\lambda = 0$ the recession directions of $\mathcal X$, which are only $\{0\}$ when $\mathcal X$ is bounded (Remark 4.2).
--
--   This homogenization of a convex set is the basic device of the paper: it turns the bilinear constraints $z = y x$, $x \in \mathcal X$ into the convex conic constraint $(z, y) \in \tilde{\mathcal X}$, and it is used to define the perspective of a function.
--
--   **Formalization Note** The definition is stated for an arbitrary set in any real topological vector space; the paper states it for closed convex $\mathcal X \subseteq \mathbb R^n$, and those hypotheses are put on the theorems that use it. In the mission, $\mathbb R^n$ is `Fin n → ℝ`.
-- source:
--   Marcucci, Umenberger, Parrilo & Tedrake, Shortest Paths in Graphs of Convex Sets, arXiv:2101.11565v5, Definition 4.1, p. 5

import Mathlib

namespace ShortestGCS.MICP

open Pointwise

/-- The perspective of a set `𝒳` (Definition 4.1, arXiv:2101.11565v5, p. 5):
`𝒳̃ := cl{(x, λ) : λ ≥ 0, x ∈ λ𝒳}`. For `λ = 0` the pointwise multiple `0 • 𝒳` is `{0}` when `𝒳` is
nonempty (`Set.zero_smul_set`) and `∅` when it is empty. -/
def perspectiveSet {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (X : Set E) : Set (E × ℝ) :=
  closure {q : E × ℝ | 0 ≤ q.2 ∧ q.1 ∈ q.2 • X}

end ShortestGCS.MICP


