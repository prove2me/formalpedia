-- Prove2me | Definitions.Def_EkelandVP_General_IsGateauxDiff
-- name    : EkelandVP_General_IsGateauxDiff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T10:25:58.380605+00:00
-- url     : https://prove2.me/theorems/db5fdd65-7362-42cb-9d44-1dff6c4eae93
-- title:
--   Gâteaux differentiability (2.1) of $F: V \to \mathbb{R} \cup \{+\infty\}$ with derivative $F': V \to V^*$
-- statement:
--   Let $V$ be a real normed space with topological dual $V^*$, let $F : V \to \mathbb{R} \cup \{+\infty\}$, and let $F' : V \to V^*$. We say that $F$ is **Gâteaux-differentiable with derivative $F'$** if, at every point $u_0$ with $F(u_0) < +\infty$ and for every direction $v \in V$,
--
--   $$
--   \frac{d}{dt} F(u_0 + t v)\Big|_{t=0} = \langle F'(u_0), v \rangle .
--   $$
--
--   Here the left-hand side is an ordinary derivative of a real function of $t$: the map $t \mapsto F(u_0+tv)$ is finite for all $t$ near $0$ and differentiable at $t=0$. The values of $F'$ at points where $F = +\infty$ play no role.
--
--   This is the notion of differentiability under which Ekeland's §2 states that approximate critical points exist: Corollary 2.3 produces points with $\|F'(v)\|_* \le \varepsilon$.
--
--   **Formalization Note** $F$ takes values in `EReal`. A real derivative at $t=0$ presupposes that $F(u_0+tv)$ is finite for $t$ near $0$; the definition states this explicitly ("eventually $\ne +\infty$ and $\ne -\infty$"), because Lean's `EReal.toReal` sends $\pm\infty$ to $0$ and would otherwise let an infinite function have a junk derivative. The value $-\infty$ is excluded because the paper's $F$ never takes it.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 326, §2, (2.1)

import Mathlib

namespace EkelandVP.General

/-- Gâteaux differentiability (2.1) of Ekeland (1974), p. 326, for `F : V → ℝ ∪ {+∞}` (encoded in
`EReal`) on a real normed space `V`, with derivative map `F' : V → V*`: at every point `u₀` with
`F u₀ < +∞`, for every direction `v`, the function `t ↦ F (u₀ + t v)` is finite for `t` near `0`
and its (real) derivative at `t = 0` equals `⟨F'(u₀), v⟩`. -/
def IsGateauxDiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : V → EReal) (F' : V → V →L[ℝ] ℝ) : Prop :=
  ∀ u₀ : V, F u₀ ≠ ⊤ → ∀ v : V,
    (∀ᶠ t in nhds (0 : ℝ), F (u₀ + t • v) ≠ ⊤ ∧ F (u₀ + t • v) ≠ ⊥) ∧
    HasDerivAt (fun t : ℝ => (F (u₀ + t • v)).toReal) (F' u₀ v) 0

end EkelandVP.General


