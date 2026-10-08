-- Prove2me | Definitions.Def_RobustDP_ChiSquare_Moments
-- name    : RobustDP_ChiSquare_Moments
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:36:20.812197+00:00
-- url     : https://prove2.me/theorems/c45be0b7-bba7-481c-8b5f-f3731799f7a2
-- title:
--   Expectation $E^q[x]$ and variance $\mathrm{Var}^q[x]$ of a function on a finite set
-- statement:
--   Let $\mathcal S$ be a finite set and $q:\mathcal S\to\mathbb R$ a weight vector (in every use below, $q$ is a probability measure on $\mathcal S$). For a function $x:\mathcal S\to\mathbb R$ define the **expectation** and the **variance** of $x$ under $q$ by
--
--   $$
--   \mathbf E^q[x]=\sum_{s\in\mathcal S}q(s)\,x(s),\qquad
--   \mathbf{Var}^q[x]=\sum_{s\in\mathcal S}q(s)\,\big(x(s)-\mathbf E^q[x]\big)^2 .
--   $$
--
--   For a probability measure $p$ this is the expectation $\mathbf E^p[v]=p^{T}v$ of Section 4 of Iyengar's paper, and $\mathbf{Var}^q$ is the variance appearing in the dual problem (48).
--
--   These are the two moments in terms of which every value identity of this mission is stated.
--
--   **Formalization Note** Both are plain finite sums over a `Fintype`; no measure theory is used. The definitions make sense for any weight vector, and the theorems add the hypothesis that $q$ is a probability vector where the paper has it.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 15 (E^p[v] = p^T v) and p. 18, eq. (48) (Var^q)

import Mathlib

namespace RobustDP.ChiSquare

/-- The expectation `E^q[x] = ∑_{s ∈ S} q(s) x(s)` of a function `x : S → ℝ` under a weight
vector `q` on a finite set `S` (Iyengar, TR-2002-07, p. 15: `Eᵖ[v] = pᵀv`). -/
noncomputable def expect {S : Type*} [Fintype S] (q x : S → ℝ) : ℝ :=
  ∑ s, q s * x s

/-- The variance `Var^q[x] = ∑_{s ∈ S} q(s) (x(s) − E^q[x])²` of `x : S → ℝ` under `q`
(the quantity `Var^q` of (48), Iyengar, TR-2002-07, p. 18). -/
noncomputable def variance {S : Type*} [Fintype S] (q x : S → ℝ) : ℝ :=
  ∑ s, q s * (x s - expect q x) ^ 2

end RobustDP.ChiSquare


