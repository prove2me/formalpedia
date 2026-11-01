-- Prove2me | Definitions.Def_GPHigherGauge_Flatness_tau
-- name    : GPHigherGauge_Flatness_tau
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:55:44.287491+00:00
-- url     : https://prove2.me/theorems/e4398bf5-41e9-4bfd-ad5a-063bac5f3ca2
-- title:
--   The infinitesimal map $\tau = dt:\mathfrak h\to\mathfrak g$
-- statement:
--   Let $G$ and $H$ be real Lie groups with Lie algebras $\mathfrak g$ and $\mathfrak h$, and let $t:H\to G$ be a map with $t(1)=1$ (for example the homomorphism of a crossed module). Its **infinitesimal version** is the derivative at the unit,
--   $$\tau=dt_1:\mathfrak h\to\mathfrak g .$$
--
--   In the paper's differential picture, $\tau$ is the map through which the 2-form $B$ enters the curvature of the 2-connection.
--
--   **Formalization Note** $\tau$ is Mathlib's `mfderiv` of $t$ at $1\in H$; both tangent spaces are definitionally the model spaces, so it is typed $\mathfrak h\to\mathfrak g$.
-- source:
--   Girelli, Pfeiffer, Higher gauge theory — differential versus integral formulation, arXiv:hep-th/0309173v2, §3.1, p. 14 (τ = dt); §3.3, Eq. (3.21), p. 16

import Mathlib

open scoped Manifold ContDiff

namespace GPHigherGauge.Flatness

/-- The infinitesimal map `τ = dt : 𝔥 → 𝔤` of the crossed-module homomorphism `t : H → G`.

Girelli, Pfeiffer, *Higher gauge theory — differential versus integral formulation*,
arXiv:hep-th/0309173v2, §3.1, p. 14 ("the derivative τ = dt") and §3.3, Eq. (3.21), p. 16:
"The map τ: 𝔥 → 𝔤 is the infinitesimal version of the map t: H → G, t(h_µν) ∼ e^{a²τ(B_µν)}."

`τ` is the manifold derivative of `t` at the unit `1 ∈ H`.

**Formalization Note** When `t 1 = 1` (part of every crossed module) the codomain
`T_{t 1}G` is `T₁G = 𝔤`; both are definitionally the model space, so the map is typed
`𝔥 →L[ℝ] 𝔤` throughout. -/
noncomputable def tau {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] [ChartedSpace F H] [Group H] (t : H → G) :
    GroupLieAlgebra 𝓘(ℝ, F) H →L[ℝ] GroupLieAlgebra 𝓘(ℝ, E) G :=
  mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) t 1

end GPHigherGauge.Flatness


