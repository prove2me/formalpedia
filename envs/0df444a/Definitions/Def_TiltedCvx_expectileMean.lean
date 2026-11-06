-- Prove2me | Definitions.Def_TiltedCvx_expectileMean
-- name    : TiltedCvx_expectileMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:16.671109+00:00
-- url     : https://prove2.me/theorems/e441475a-9309-4c39-8ee8-abc134c3e24d
-- title:
--   The $m$-point mean $M^{(m)}_{\gamma,\lambda}$ (upper expectile)
-- statement:
--   Fix $m\ge2$, a probability vector $\lambda\in\Delta_m$ and $\gamma\in(0,1]$. For $a=(a_1,\dots,a_m)\in\mathbb R^m$,
--
--   $$
--   M^{(m)}_{\gamma,\lambda}(a):=\max_{S\subseteq\{1,\dots,m\}}\frac{\sum_{i\in S}\lambda_i a_i+\gamma\sum_{i\notin S}\lambda_i a_i}{\sum_{i\in S}\lambda_i+\gamma\sum_{i\notin S}\lambda_i}.
--   $$
--
--   It is the expectile at level $1/(1+\gamma)$ of the distribution putting mass $\lambda_i$ on $a_i$; $M^{(m)}_{1,\lambda}$ is the weighted mean. It replaces the arithmetic mean in the Jensen form of tilted secant convexity.
--
--   **Formalization Note** Indices are `Fin m` and $S$ ranges over all finite subsets. Only formula (17) for $\gamma\in(0,1]$ is encoded (the denominator is then at least $\gamma>0$); the separate convention (18) for $\gamma=0$ is used by no statement of the mission.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Definition 13, (17), p.26

import Mathlib

namespace TiltedCvx

/-- **The `m`-point mean `M^{(m)}_{γ,λ}` (upper expectile).** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Definition 13, (17), p.26: for `m ≥ 2`, `λ ∈ Δm`, `γ ∈ (0, 1]` and
`a ∈ ℝ^m`,
`M^{(m)}_{γ,λ}(a) := max_{S ⊆ {1,…,m}} (Σ_{i∈S} λᵢaᵢ + γ Σ_{i∉S} λᵢaᵢ)/(Σ_{i∈S} λᵢ + γ Σ_{i∉S} λᵢ)`.

**Formalization Note** Indices are `Fin m`, and the maximum runs over all `S : Finset (Fin m)`.
This is formula (17), used only for `γ ∈ (0, 1]`, where the denominator is at least
`γ Σ λᵢ = γ > 0`. The separate convention (18) for `γ = 0` is not needed by any statement of
this mission and is not encoded. -/
noncomputable def expectileMean {m : ℕ} (γ : ℝ) (lam a : Fin m → ℝ) : ℝ :=
  (Finset.univ : Finset (Finset (Fin m))).sup' Finset.univ_nonempty fun S =>
    (∑ i ∈ S, lam i * a i + γ * ∑ i ∈ Sᶜ, lam i * a i) /
      (∑ i ∈ S, lam i + γ * ∑ i ∈ Sᶜ, lam i)

end TiltedCvx


