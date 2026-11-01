-- Prove2me | Definitions.Def_GPHigherGauge_Flatness_SurfaceCondition
-- name    : GPHigherGauge_Flatness_SurfaceCondition
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:55:42.957068+00:00
-- url     : https://prove2.me/theorems/dfbf6575-953c-4706-907c-11b570461a8b
-- title:
--   The surface condition (2.10), $t(h)=g_2g_1^{-1}$, on every small square near $(x_0,0)$
-- statement:
--   Let $G$ be a group, $t:H\to G$ a map, $g_\mu(x,a)$ edge labels and $h_{\mu\nu}(x,a)$ square labels on $\mathbb R^n$, and $x_0\in\mathbb R^n$. The labels satisfy the **surface condition near $(x_0,0)$** when for all $\mu\neq\nu$ and all $(x,a)$ in a neighbourhood of $(x_0,0)$,
--   $$t\big(h_{\mu\nu}(x,a)\big)=\big(g_\nu(x,a)\,g_\mu(x+ae_\nu,a)\big)\big(g_\mu(x,a)\,g_\nu(x+ae_\mu,a)\big)^{-1}.$$
--
--   This is the condition $t(h)=g_2\cdot g_1^{-1}$ of the integral formulation of 2-gauge theory for the square of Figure 1(c): $g_1$ is the label of its source curve (through $x+ae_\mu$) and $g_2$ the label of its target curve (through $x+ae_\nu$), so $t(h)$ is the inverse holonomy along the boundary.
--
--   **Formalization Note** Only the squares are constrained; the relation $h_{\mu\nu}=h_{\nu\mu}^{-1}$ is not assumed. The side $a$ takes both signs.
-- source:
--   Girelli, Pfeiffer, Higher gauge theory — differential versus integral formulation, arXiv:hep-th/0309173v2, §2.2, Eq. (2.10), p. 6; Figure 1(c), p. 15

import Mathlib

open scoped Topology
open Filter

namespace GPHigherGauge.Flatness

/-- The surface condition (2.10) on every small square near `(x₀, 0)`.

Girelli, Pfeiffer, *Higher gauge theory — differential versus integral formulation*,
arXiv:hep-th/0309173v2, §2.2, Eq. (2.10), p. 6:
"The label h of the surface is required to satisfy, t(h) = g2 · g1^{-1}, (2.10) i.e. t(h) is the
(inverse) holonomy along the boundary curve."

For the square at `x` with side `a` in the `(μν)`-plane (Figure 1(c), p. 15) the source curve is
`0 → μ → μ + ν` with label `g₁ = g_μ(x, a) · g_ν(x + a e_μ, a)` and the target curve is
`0 → ν → ν + μ` with label `g₂ = g_ν(x, a) · g_μ(x + a e_ν, a)` (labels multiply in traversal
order). The condition is `t(h_μν(x, a)) = g₂ · g₁⁻¹` for all `μ ≠ ν` and all `(x, a)` near
`(x₀, 0)`.

**Formalization Note** Only the squares are constrained, for `μ ≠ ν` (Readings 3 and 4);
`h_μν = h_νμ⁻¹` (p. 15) is not assumed. `a` ranges over a neighbourhood of `0`, both signs.
`e_μ = EuclideanSpace.single μ 1`. -/
def SurfaceCondition {G : Type*} [Group G] {H : Type*} {n : ℕ} (t : H → G)
    (g : Fin n → EuclideanSpace ℝ (Fin n) → ℝ → G)
    (h : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ → H) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  ∀ μ ν : Fin n, μ ≠ ν → ∀ᶠ p in 𝓝 (x₀, (0 : ℝ)),
    t (h μ ν p.1 p.2) =
      (g ν p.1 p.2 * g μ (p.1 + p.2 • EuclideanSpace.single ν (1 : ℝ)) p.2) *
        (g μ p.1 p.2 * g ν (p.1 + p.2 • EuclideanSpace.single μ (1 : ℝ)) p.2)⁻¹

end GPHigherGauge.Flatness


