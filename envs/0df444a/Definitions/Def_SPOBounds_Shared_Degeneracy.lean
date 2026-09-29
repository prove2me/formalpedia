-- Prove2me | Definitions.Def_SPOBounds_Shared_Degeneracy
-- name    : SPOBounds_Shared_Degeneracy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:36:11.126989+00:00
-- url     : https://prove2.me/theorems/a4cc6f05-0928-44cb-ac29-705a77dcc34c
-- title:
--   Degenerate cost vectors $\mathcal C^\circ$, distance to degeneracy $\nu_S$, and the strength property
-- statement:
--   Let $E$ be a real normed space (the paper's $\mathbb R^d$ with a generic norm $\|\cdot\|$) and let $S\subseteq E$ be a feasible region. A cost vector is a continuous linear functional $\hat c$ on $E$; $\hat c^\top w$ denotes its value $\hat c(w)$, and the operator norm $\|\hat c\|$ is the dual norm $\|\hat c\|_*=\max_{\|w\|\le1}\hat c^\top w$. Write $P(\hat c)$ for the linear optimization problem $\min_{w\in S}\hat c^\top w$.
--
--   1. **Degenerate cost vectors.** A cost vector is *degenerate* when $P(\hat c)$ has more than one optimal solution:
--   $$\mathcal C^\circ := \{\hat c : \text{there are } u\ne v \text{ in } S \text{ both minimizing } \hat c^\top w \text{ over } S\}.$$
--   2. **Distance to degeneracy.** $$\nu_S(\hat c) := \inf_{c\in\mathcal C^\circ}\|c-\hat c\|_*.$$
--   3. **Strength property.** Given an optimization oracle $w^*$ (a map with $w^*(\hat c)\in\arg\min_{w\in S}\hat c^\top w$) and a constant $\mu$, the region $S$ satisfies the strength property with parameter $\mu$ if
--   $$\hat c^\top\big(w-w^*(\hat c)\big)\ \ge\ \Big(\frac{\mu\,\nu_S(\hat c)}{2}\Big)\,\|w-w^*(\hat c)\|^2\qquad\text{for all } w\in S \text{ and all cost vectors } \hat c.$$
--
--   The strength property is a quantitative optimality condition: the farther a prediction $\hat c$ is from the degenerate set, the more sharply the optimal solution $w^*(\hat c)$ is separated from the rest of $S$. It is the hypothesis under which the margin-based generalization bounds of the paper hold.
--
--   Used by two missions of this paper: 03-strongly-convex (Theorem 7, §5.1, pp. 23–24, and App. D; the definitions of Definition 2, p. 13, and Definition 3, p. 14) and 04-polyhedral (Proposition 2 and Theorem 8, §5.2, pp. 24–25; the same definitions, p. 13 and p. 14).
--
--   **Formalization Note** Cost vectors are elements of `StrongDual ℝ E`, whose operator norm is the dual norm. $\nu_S$ is `Metric.infDist` to $\mathcal C^\circ$, which returns $0$ when $\mathcal C^\circ$ is empty; every theorem that uses it assumes $S$ has two distinct points, and then $0\in\mathcal C^\circ$. The requirement $\mu>0$ of Definition 3 is not part of the predicate; every theorem states it as a separate hypothesis. The oracle is a parameter of the predicate, exactly as $w^*(\hat c)$ appears in (5).
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 5 (§2, eq. (2), oracle), p. 8 (§2.1, dual norm), p. 13 (Definition 2), p. 14 (Definition 3, eq. (5))

import Mathlib

namespace SPOBounds.Shared

/-- The set of degenerate cost vector predictions (arXiv:1905.11488v3, Definition 2, p. 13):
`𝒞° = {ĉ : P(ĉ) has multiple optimal solutions}`, where `P(ĉ)` is `min_{v ∈ S} ĉᵀv`.
A cost vector is a continuous linear functional `ĉ`, so `ĉᵀv` is `ĉ v`; `ĉ` is degenerate when
`v ↦ ĉ v` has two distinct minimizers over `S`. -/
def degenerate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) : Set (StrongDual ℝ E) :=
  {chat | ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ IsMinOn (fun x => chat x) S u ∧
    IsMinOn (fun x => chat x) S v}

/-- The distance to degeneracy `ν_S(ĉ) = inf_{c ∈ 𝒞°} ‖c − ĉ‖_*` (Definition 2, p. 13),
measured in the operator norm of `StrongDual ℝ E`, which is the dual norm `‖·‖_*`.
(`Metric.infDist` is `0` on the empty set; when `S` has two distinct points, `0 ∈ 𝒞°`.) -/
noncomputable def nu {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (chat : StrongDual ℝ E) : ℝ :=
  Metric.infDist chat (degenerate S)

/-- The strength property (Definition 3, p. 14, eq. (5)) with parameter `μ` for the
optimization oracle `w`:
`ĉᵀ(v − w*(ĉ)) ≥ (μ ν_S(ĉ) / 2) ‖v − w*(ĉ)‖²` for all `v ∈ S` and all cost vectors `ĉ`.
The requirement `μ > 0` of Definition 3 is carried separately by every theorem. -/
def StrengthProperty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (μ : ℝ) (w : StrongDual ℝ E → E) : Prop :=
  ∀ chat : StrongDual ℝ E, ∀ v ∈ S,
    μ * nu S chat / 2 * ‖v - w chat‖ ^ 2 ≤ chat (v - w chat)

end SPOBounds.Shared


