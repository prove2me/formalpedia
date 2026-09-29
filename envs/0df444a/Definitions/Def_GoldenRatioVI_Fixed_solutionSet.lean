-- Prove2me | Definitions.Def_GoldenRatioVI_Fixed_solutionSet
-- name    : GoldenRatioVI_Fixed_solutionSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:54:53.305892+00:00
-- url     : https://prove2.me/theorems/e1beb8c8-2be2-453c-945b-0dfb9abc45b6
-- title:
--   Monotone variational inequality (1): domain, conditions (C2)–(C3), solution set $S$
-- statement:
--   Let $\mathcal E$ be a finite-dimensional real inner product space with norm $\|\cdot\| = \sqrt{\langle\cdot,\cdot\rangle}$, let $g:\mathcal E\to(-\infty,+\infty]$ and $F:\mathcal E\to\mathcal E$. This file fixes the objects of the variational inequality problem
--   $$\text{find } z^*\in\mathcal E \quad\text{s.t.}\quad \langle F(z^*), z-z^*\rangle + g(z) - g(z^*) \ge 0 \qquad \forall z\in\mathcal E. \tag{1}$$
--
--   1. The **domain** of $g$ is $\operatorname{dom} g = \{x : g(x) < +\infty\}$.
--   2. Condition **(C2)**: $g$ is **proper** (it never takes the value $-\infty$ and is finite at some point), **convex** (its epigraph $\{(x,t)\in\mathcal E\times\mathbb R : g(x)\le t\}$ is a convex set) and **lower semicontinuous** on $\mathcal E$.
--   3. Condition **(C3)**: $F$ is **monotone** on a set $D$ if $\langle F(u)-F(v), u-v\rangle\ge 0$ for all $u,v\in D$; the paper requires this for $D = \operatorname{dom} g$.
--   4. The **solution set** $S$ of (1) is the set of $z^*\in\operatorname{dom} g$ satisfying the inequality in (1) for every $z\in\mathcal E$. Condition **(C1)** is $S\neq\emptyset$.
--
--   These are the objects in terms of which Eq. (4), Eq. (14) and Theorem 1 are stated.
--
--   **Formalization Note** $g$ is a function `E → EReal`; properness excludes the value $\bot$. The inequality in (1) is evaluated in `EReal`; since $z^*\in\operatorname{dom} g$ and $g$ is proper in every theorem that uses $S$, $g(z)-g(z^*)$ is never of the form $\infty-\infty$, and it equals $+\infty$ when $g(z)=+\infty$. The operator $F$ is a total function `E → E`; the paper defines $F$ on $\operatorname{dom} g$ only, so every hypothesis on $F$ is restricted to $\operatorname{dom} g$ and values of $F$ outside it play no role in the conditions.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (Optimization Online 6598, 2018), p. 1, Eq. (1) and (C1)–(C3); p. 3, Preliminaries (dom g)

import Mathlib

namespace GoldenRatioVI.Fixed

/-- The effective domain `dom g = {x | g x < +∞}` of an extended-real-valued function. -/
def effDom {E : Type*} (g : E → EReal) : Set E :=
  {x | g x ≠ ⊤}

/-- Condition (C2): `g : 𝓔 → (-∞, +∞]` is proper, convex and lower semicontinuous.
Proper: `g` never takes the value `-∞` and is finite somewhere. Convex: its epigraph
`{(x, t) | g x ≤ t}` is convex. Lower semicontinuous on all of `E`. -/
def IsProperConvexLSC {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → EReal) : Prop :=
  (∀ x, g x ≠ ⊥) ∧ (∃ x, g x ≠ ⊤) ∧
    Convex ℝ {p : E × ℝ | g p.1 ≤ (p.2 : EReal)} ∧ LowerSemicontinuous g

/-- Condition (C3): `F` is monotone on the set `D`:
`⟪F u - F v, u - v⟫ ≥ 0` for all `u, v ∈ D`. -/
def IsMonotoneOperatorOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → E) (D : Set E) : Prop :=
  ∀ u ∈ D, ∀ v ∈ D, 0 ≤ inner ℝ (F u - F v) (u - v)

/-- The solution set `S` of the variational inequality (1):
`z* ∈ dom g` with `⟪F z*, z - z*⟫ + g z - g z* ≥ 0` for every `z ∈ E`
(computed in `EReal`; since `z* ∈ dom g`, no `⊤ - ⊤` occurs for proper `g`). -/
def solutionSet {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → EReal) (F : E → E) : Set E :=
  {zs | zs ∈ effDom g ∧ ∀ z : E, (0 : EReal) ≤ ((inner ℝ (F zs) (z - zs) : ℝ) : EReal) + g z - g zs}

end GoldenRatioVI.Fixed


