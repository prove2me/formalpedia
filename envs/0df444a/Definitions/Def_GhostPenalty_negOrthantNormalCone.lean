-- Prove2me | Definitions.Def_GhostPenalty_negOrthantNormalCone
-- name    : GhostPenalty_negOrthantNormalCone
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:33:59.109748+00:00
-- url     : https://prove2.me/theorems/66656fd1-454f-4e1c-baef-c2431bd6dd70
-- title:
--   Normal cone $N_{\mathbb R^m_-}(y)$ of the nonpositive orthant
-- statement:
--   For $y\in\mathbb R^m$, the classical normal cone of the convex set $\mathbb R^m_-=\{y:\ y\le 0\}$ at $y$ is empty if $y\not\le 0$, and for $y\le 0$
--   $$N_{\mathbb R^m_-}(y)=\{\xi\in\mathbb R^m:\ \xi\ge 0,\ \xi_i y_i=0\ \text{for all } i\}.$$
--   It encodes the sign and complementarity conditions on multipliers of inequality constraints.
--
--   **Formalization Note** The emptiness off $\mathbb R^m_-$ is the clause "$y_i\le 0$ for all $i$"; multipliers are functions `Fin m → ℝ`.
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, §2, p.5

import Mathlib

namespace GhostPenalty

/-- **Normal cone `N_{ℝᵐ₋}(y)` of the nonpositive orthant.**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, §2, p.5: "`N_{ℝᵐ₋}(y)` … [is] the classical normal cone to the
convex set `ℝᵐ₋` at `y` … If `g(x) ≤ 0`, the condition `ξ ∈ N_{ℝᵐ₋}(g(x))` can be more familiarly
rewritten as `ξ_i ≥ 0, ξ_i g_i(x) = 0` for all `i`."

For `y ∈ ℝᵐ`, `negOrthantNormalCone y` is empty unless `y ≤ 0`, and for `y ≤ 0` it is
`{ξ ∈ ℝᵐ : ξ ≥ 0, ξ_i y_i = 0 for all i}`.

**Formalization Note.** The classical normal cone of a convex set is empty at points outside
the set; this convention is built in through the clause `∀ i, y i ≤ 0`. Vectors of `ℝᵐ`
(multipliers) are functions `Fin m → ℝ`. -/
def negOrthantNormalCone {m : ℕ} (y : Fin m → ℝ) : Set (Fin m → ℝ) :=
  {ξ | (∀ i, y i ≤ 0) ∧ (∀ i, 0 ≤ ξ i) ∧ ∀ i, ξ i * y i = 0}

end GhostPenalty


