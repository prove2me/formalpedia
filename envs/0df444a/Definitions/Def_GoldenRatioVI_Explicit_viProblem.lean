-- Prove2me | Definitions.Def_GoldenRatioVI_Explicit_viProblem
-- name    : GoldenRatioVI_Explicit_viProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:27:54.238181+00:00
-- url     : https://prove2.me/theorems/9b9bfe9a-f2d9-4e3e-b607-214d4b5d3438
-- title:
--   Monotone variational inequality (1): dom g, conditions (C2)–(C3), solution set S, bifunction Ψ
-- statement:
--   Let $\mathcal E$ be a finite-dimensional real inner product space with norm $\|\cdot\| = \sqrt{\langle\cdot,\cdot\rangle}$, let $g:\mathcal E\to(-\infty,+\infty]$ and let $F:\operatorname{dom} g\to\mathcal E$. This file fixes the objects of the monotone variational inequality studied by Malitsky.
--
--   1. The **domain** of $g$ is $\operatorname{dom} g = \{x\in\mathcal E : g(x) < +\infty\}$.
--   2. **Condition (C2):** $g$ is proper (it never takes the value $-\infty$ and is finite at some point), convex (its epigraph $\{(x,t)\in\mathcal E\times\mathbb R : g(x)\le t\}$ is convex) and lower semicontinuous on $\mathcal E$.
--   3. **Condition (C3):** $F$ is monotone on $\operatorname{dom} g$: $\langle F(u)-F(v),u-v\rangle\ge 0$ for all $u,v\in\operatorname{dom} g$.
--   4. The **solution set** $S$ of the variational inequality
--   $$\text{find } z^*\in\mathcal E \text{ such that } \langle F(z^*), z - z^*\rangle + g(z) - g(z^*) \ge 0 \quad \forall z\in\mathcal E, \tag{1}$$
--   consists of the points $z^*\in\operatorname{dom} g$ satisfying (1). Condition (C1) of the paper is $S\neq\emptyset$.
--   5. The **bifunction** $\Psi(u,v) = \langle F(u), v-u\rangle + g(v) - g(u)$, a real number for $u,v\in\operatorname{dom} g$.
--   6. The **Lipschitz hypothesis** of §2.1: for every bounded set $B\subseteq\operatorname{dom} g$ there is $L\ge 0$ with $\|F(u)-F(v)\|\le L\|u-v\|$ for all $u,v\in B$.
--
--   These are the standing objects of every statement of the mission.
--
--   **Formalization Note** $g$ is a map `E → EReal`; $F$ is a total map `E → E` whose values off $\operatorname{dom} g$ are never used. Since $g(z^*)$ is finite for $z^*\in\operatorname{dom} g$, inequality (1) is stored without extended-real subtraction as $g(z^*)\le\langle F(z^*),z-z^*\rangle+g(z)$. $\Psi$ is real-valued via `EReal.toReal`, which returns $0$ at $+\infty$; this junk value only arises off $\operatorname{dom} g$. The paper assumes $F$ "locally Lipschitz"; item 6 is the property its proof of Lemma 2 uses, and it coincides with local Lipschitz continuity on $\operatorname{dom} g$ when $\operatorname{dom} g$ is closed (for instance $g=\delta_C$ with $C$ closed, or $g$ finite everywhere).
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (Optimization Online 6598, 2018), p. 1, Eq. (1) and (C1)–(C3); p. 3, Preliminaries (dom g); p. 5, §2.1 (locally Lipschitz F); p. 6, bifunction Ψ

import Mathlib

namespace GoldenRatioVI.Explicit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The effective domain of an extended-real-valued function `g : E → (−∞, +∞]`
(Malitsky, p. 3): `dom g = {x : g(x) < +∞}`. -/
def dom (g : E → EReal) : Set E := {x | g x ≠ ⊤}

/-- Condition (C2) of Malitsky (p. 1): `g : E → (−∞, +∞]` is proper, convex and lower
semicontinuous. Proper: `g` never takes the value `−∞` and is finite somewhere. Convex: its
epigraph `{(x, t) : g(x) ≤ t}` is a convex subset of `E × ℝ`. Lower semicontinuous on all of
`E` (as a map into `EReal`). -/
structure IsProperConvexLSC (g : E → EReal) : Prop where
  ne_bot : ∀ x, g x ≠ ⊥
  exists_ne_top : ∃ x, g x ≠ ⊤
  convex_epigraph : Convex ℝ {p : E × ℝ | g p.1 ≤ (p.2 : EReal)}
  lsc : LowerSemicontinuous g

/-- Condition (C3) of Malitsky (p. 1): `F` is monotone on `dom g`,
`⟨F(u) − F(v), u − v⟩ ≥ 0` for all `u, v ∈ dom g`. Values of `F` off `dom g` play no role. -/
def IsMonotoneOnDom (g : E → EReal) (F : E → E) : Prop :=
  ∀ u ∈ dom g, ∀ v ∈ dom g, 0 ≤ inner ℝ (F u - F v) (u - v)

/-- The solution set `S` of the variational inequality (1) of Malitsky (p. 1):
`z* ∈ dom g` with `⟨F(z*), z − z*⟩ + g(z) − g(z*) ≥ 0` for every `z ∈ E`. Since `g(z*)` is
finite, the inequality is written without subtraction as `g(z*) ≤ ⟨F(z*), z − z*⟩ + g(z)`
in `EReal`. -/
def solutionSet (g : E → EReal) (F : E → E) : Set E :=
  {zs | zs ∈ dom g ∧ ∀ z, g zs ≤ ((inner ℝ (F zs) (z - zs) : ℝ) : EReal) + g z}

/-- The bifunction of Malitsky (p. 6), `Ψ(u, v) = ⟨F(u), v − u⟩ + g(v) − g(u)`, as a real
number. It is meaningful for `u, v ∈ dom g` (where `g` is finite); `EReal.toReal` sends `⊤` to
`0`, a junk value that is only reached off `dom g`. -/
noncomputable def psi (g : E → EReal) (F : E → E) (u v : E) : ℝ :=
  inner ℝ (F u) (v - u) + (g v).toReal - (g u).toReal

/-- The Lipschitz hypothesis on `F` used for Lemma 2 and Theorem 2 of Malitsky (pp. 5–6):
on every bounded subset `B` of `dom g`, `F` is Lipschitz with some constant `L` (depending
on `B`). For closed `dom g` this is equivalent to local Lipschitz continuity of `F` on `dom g`. -/
def IsLipschitzOnBoundedDom (g : E → EReal) (F : E → E) : Prop :=
  ∀ B ⊆ dom g, Bornology.IsBounded B → ∃ L : NNReal, LipschitzOnWith L F B

end GoldenRatioVI.Explicit


