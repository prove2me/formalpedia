-- Prove2me | Definitions.Def_ShortestGCS_MICP_PerspectiveFun
-- name    : ShortestGCS_MICP_PerspectiveFun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:10:17.367997+00:00
-- url     : https://prove2.me/theorems/3da3fdab-eb49-4741-aecf-9e90e55adfc7
-- title:
--   Definition 4.4, p. 6 — epigraph, proper closed convex functions, and the perspective f̃(x, λ) = inf{σ : (x, σ, λ) ∈ (epi f)~}
-- statement:
--   Let $E$ be a real topological vector space and $f : E \to \mathbb R \cup \{\pm\infty\}$.
--
--   1. The **epigraph** of $f$ is $\operatorname{epi} f := \{(x,\sigma) \in E \times \mathbb R : f(x) \le \sigma\}$.
--   2. $f$ is **proper, closed and convex** if $\operatorname{epi} f$ is convex and closed, $f(x) < +\infty$ for some $x$, and $f(x) > -\infty$ for every $x$.
--   3. The **perspective** of $f$ is the function $\tilde f : E \times \mathbb R \to \mathbb R \cup \{\pm\infty\}$ whose epigraph is the perspective (Definition 4.1) of the epigraph of $f$:
--
--   $$
--   \tilde f(x,\lambda) := \inf\{\sigma \in \mathbb R : (x,\sigma,\lambda) \in \widetilde{\operatorname{epi} f}\},
--   $$
--
--   with $\inf \emptyset = +\infty$.
--
--   For $\lambda > 0$ and closed $f$ this is $\lambda f(x/\lambda)$, for $\lambda < 0$ it is $+\infty$, and at $\lambda = 0$ it is the closure of that formula (Remark 4.5). The perspective of an edge length $\ell_e$ is the cost term $\tilde\ell_e(z_e, z'_e, y_e)$ of the mixed-integer program (5.5): it switches the length of an edge off when its flow $y_e$ is zero.
--
--   **Formalization Note** Values are in `EReal`. The point $(x,\sigma,\lambda)$ is encoded as `((x, σ), λ)`, so that $\widetilde{\operatorname{epi} f}$ is literally the perspective of the set $\operatorname{epi} f \subseteq E\times\mathbb R$. The perspective is defined by the infimum of Definition 4.4, not by the formula $\lambda f(x/\lambda)$, which in Lean would give $0$ at $\lambda = 0$ for every $x$. Definition 4.4 is stated for closed convex $f$; that hypothesis is carried by the theorems.
-- source:
--   Marcucci, Umenberger, Parrilo & Tedrake, Shortest Paths in Graphs of Convex Sets, arXiv:2101.11565v5, Definition 4.4 and footnote 2, p. 6; §2, p. 4 (proper, closed, convex)

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective

namespace ShortestGCS.MICP

/-- The epigraph `epi f := {(x, σ) : f(x) ≤ σ}` of an extended-real-valued function
(Definition 4.4, arXiv:2101.11565v5, p. 6). Only real heights `σ` are used. -/
def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p | f p.1 ≤ (p.2 : EReal)}

/-- `f : E → ℝ ∪ {∞}` is proper, closed and convex (§2, p. 4; Definition 4.4, p. 6): its epigraph
is convex and closed, `f` is finite somewhere, and `f` never takes the value `-∞`. -/
def IsProperClosedConvex {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f) ∧ IsClosed (epigraph f) ∧ (∃ x, f x ≠ ⊤) ∧ ∀ x, f x ≠ ⊥

/-- The perspective of a function (Definition 4.4, arXiv:2101.11565v5, p. 6):
`f̃(x, λ) := inf{σ : (x, σ, λ) ∈ (epi f)~}`, where `(epi f)~` is the perspective
(Definition 4.1) of the epigraph. The point `(x, σ, λ)` is encoded as `((x, σ), λ)`.
The infimum is taken in `EReal`, so it is `⊤` when no `σ` qualifies. -/
noncomputable def perspectiveFun {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (f : E → EReal) (x : E) (lam : ℝ) : EReal :=
  sInf ((fun σ : ℝ => (σ : EReal)) '' {σ : ℝ | ((x, σ), lam) ∈ perspectiveSet (epigraph f)})

end ShortestGCS.MICP


