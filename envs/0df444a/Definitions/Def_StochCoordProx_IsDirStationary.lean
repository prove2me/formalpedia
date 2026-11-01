-- Prove2me | Definitions.Def_StochCoordProx_IsDirStationary
-- name    : StochCoordProx_IsDirStationary
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:50.378488+00:00
-- url     : https://prove2.me/theorems/8e9c355c-15fc-496c-9368-4179f9e74eb1
-- title:
--   Directional stationary point on a convex set
-- statement:
--   Let $\Phi$ be a real function on a real vector space, $D$ a set and $y^*\in D$. The point $y^*$ is a **(first-order) stationary point of $\Phi$ on $D$** if no feasible direction is a first-order descent direction:
--
--   $$
--   \liminf_{t\downarrow0}\frac{\Phi(y^*+t(y-y^*))-\Phi(y^*)}{t}\ge0\qquad\text{for every }y\in D .
--   $$
--
--   This is the notion used in Lemma 3. The paper cites [32] for it and does not define it.
--
--   **Formalization Note** The $\liminf$ is written out: for every $\varepsilon>0$ the difference quotient is at least $-\varepsilon$ for all sufficiently small $t>0$. It is deliberately not the optimality condition (15) itself, so that Lemma 3 is an equivalence with content.
-- source:
--   Necoara & Chorobura, Efficiency of stochastic coordinate proximal gradient methods on nonseparable composite optimization, arXiv:2104.13370v3, Lemma 3, p.9 (the notion of stationary point, cited from [32])

import Mathlib

open Filter Topology

namespace StochCoordProx

/-- **Stationary point of `Φ` on a convex set `D`** (the notion of Lemma 3): `y* ∈ D` is a
first-order (directional) stationary point of `Φ` on `D` if no feasible direction is a
first-order descent direction: for every `y ∈ D`,
`liminf_{t ↓ 0} (Φ(y* + t (y − y*)) − Φ(y*)) / t ≥ 0`.

Necoara & Chorobura, arXiv:2104.13370v3, Lemma 3, p.9 (the paper cites [32] for the notion and
does not define it).

**Formalization Note.** The `liminf ≥ 0` is written out: for every `ε > 0`, the difference
quotient is `≥ −ε` for all sufficiently small `t > 0` (`∀ᶠ t in 𝓝[>] 0`). This is a reading of
the undefined term; it is deliberately not the optimality condition (15) itself, so that
Lemma 3 is a genuine equivalence. -/
def IsDirStationary {V : Type*} [AddCommGroup V] [Module ℝ V] (Φ : V → ℝ) (D : Set V)
    (ystar : V) : Prop :=
  ∀ y ∈ D, ∀ ε > 0, ∀ᶠ t in 𝓝[>] (0 : ℝ), -ε ≤ (Φ (ystar + t • (y - ystar)) - Φ ystar) / t

end StochCoordProx


