-- Prove2me | Definitions.Def_GPHigherGauge_Flatness_generalizedHolonomy
-- name    : GPHigherGauge_Flatness_generalizedHolonomy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:55:42.411718+00:00
-- url     : https://prove2.me/theorems/56f13ec9-8f02-45eb-9fda-e9f46c7cc018
-- title:
--   The generalized holonomy $\mathcal F_{\mu\nu}$ of a square of side $a$
-- statement:
--   Let $G$ be a group, $t:H\to G$ a map, $g_\mu(x,a)$ edge labels and $h_{\mu\nu}(x,a)$ square labels. For the square at $x$ with side $a$ in the $(\mu\nu)$-plane, the **generalized holonomy** is
--   $$\mathcal F_{\mu\nu}(x,a)=g_\mu(x+ae_\nu,a)^{-1}\,g_\nu(x,a)^{-1}\,t\big(h_{\mu\nu}(x,a)\big)\,g_\mu(x,a)\,g_\nu(x+ae_\mu,a).$$
--
--   In the notation $\mathcal F=g_2^{-1}t(h)g_1$ of the integral picture, the source curve $x\to x+ae_\mu\to x+ae_\mu+ae_\nu$ has label $g_1=g_\mu(x,a)\,g_\nu(x+ae_\mu,a)$ and the target curve $x\to x+ae_\nu\to x+ae_\nu+ae_\mu$ has label $g_2=g_\nu(x,a)\,g_\mu(x+ae_\nu,a)$; labels multiply in traversal order. It is the holonomy around the square corrected by the transport through its surface.
-- source:
--   Girelli, Pfeiffer, Higher gauge theory — differential versus integral formulation, arXiv:hep-th/0309173v2, §3.3, Eq. (3.22) and Figure 1(c), pp. 15–16; §2.6, Eq. (2.37), p. 13

import Mathlib

namespace GPHigherGauge.Flatness

/-- The generalized holonomy `𝓕_μν` of the square of side `a` at `x`.

Girelli, Pfeiffer, *Higher gauge theory — differential versus integral formulation*,
arXiv:hep-th/0309173v2, §3.3, Eq. (3.22) and Figure 1(c), pp. 15–16:
"The expression 𝓕 of (2.37) reads for the square of Figure 1(c),
e^{a²F̃_µν} ∼ 𝓕_µν = g_µ^{-1}(ν) g_ν(0)^{-1} t(h_µν(0)) g_µ(0) g_ν(µ)."

With "(0)" = `x`, "(μ)" = `x + a • e_μ` and "(ν)" = `x + a • e_ν`:
`𝓕_μν(x, a) = g_μ(x + a e_ν, a)⁻¹ · g_ν(x, a)⁻¹ · t(h_μν(x, a)) · g_μ(x, a) · g_ν(x + a e_μ, a)`.
In the notation of (2.37), `𝓕 = g₂⁻¹ t(h) g₁` with source `g₁ = g_μ(0) g_ν(μ)` and target
`g₂ = g_ν(0) g_μ(ν)` (labels multiply in traversal order).

**Formalization Note** `e_μ = EuclideanSpace.single μ 1`; `t` is any map `H → G`. -/
noncomputable def generalizedHolonomy {G : Type*} [Group G] {H : Type*} {n : ℕ} (t : H → G)
    (g : Fin n → EuclideanSpace ℝ (Fin n) → ℝ → G)
    (h : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ → H) (μ ν : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (a : ℝ) : G :=
  (g μ (x + a • EuclideanSpace.single ν (1 : ℝ)) a)⁻¹ * (g ν x a)⁻¹ * t (h μ ν x a) * g μ x a *
    g ν (x + a • EuclideanSpace.single μ (1 : ℝ)) a

end GPHigherGauge.Flatness


