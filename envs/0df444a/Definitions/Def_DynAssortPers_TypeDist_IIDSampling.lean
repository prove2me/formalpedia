-- Prove2me | Definitions.Def_DynAssortPers_TypeDist_IIDSampling
-- name    : DynAssortPers_TypeDist_IIDSampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:14:52.260318+00:00
-- url     : https://prove2.me/theorems/b3f3ba31-920d-4d0d-821f-9e2f93654365
-- title:
--   The law of an i.i.d. sample from a distribution on a finite set, the $\ell_q$ norm on $\mathbb R^m$, and the exponent $1/q$ with $1/\infty=0$
-- statement:
--   This module fixes three general objects used throughout the mission.
--
--   1. **The i.i.d. sample law.** Let $\mu=(\mu_1,\dots,\mu_m)$ be a probability vector on the finite set of types $\{1,\dots,m\}$, i.e. a point of the simplex $\Delta^m=\{\mu\in\mathbb R^m:\mu_i\ge 0,\ \sum_i\mu_i=1\}$. A sample of size $N$ is a sequence $x=(x_1,\dots,x_N)$ of types; under the i.i.d. law it has probability $\prod_{t=1}^N\mu_{x_t}$. For an event $E$ (a set of samples),
--   $$\mathbb P_\mu(E)=\sum_{x\in E}\ \prod_{t=1}^N\mu_{x_t}.$$
--   2. **The $\ell_q$ norm.** For $v\in\mathbb R^m$ and $q\in[1,\infty]$,
--   $$\|v\|_q=\Big(\sum_{i=1}^m|v_i|^q\Big)^{1/q}\quad(q<\infty),\qquad \|v\|_\infty=\max_i|v_i|.$$
--   3. **The exponent $1/q$** for $q\in[1,\infty]$, with the convention $1/\infty=0$, so that $m^{1/q}$ and $m^{2/q}$ both equal $1$ at $q=\infty$.
--
--   These are the probability space and the norms in which the concentration of the empirical type frequencies is stated.
--
--   **Formalization Note** The types are `Fin m` and the draws `Fin N`, both 0-based. The probability is a finite sum of products over the finite set of samples `Fin N → Fin m`; no measure theory is involved. The simplex hypothesis on $\mu$ is not part of this definition; theorems assume `μ ∈ stdSimplex ℝ (Fin m)` (Mathlib's $\Delta^m$). The $\ell_q$ norm is Mathlib's `PiLp` norm, which for $q=\infty$ is the supremum of the absolute coordinates. The exponent is defined by cases, `if q = ∞ then 0 else 1 / q.toReal`, rather than relying on `ENNReal.toReal ∞ = 0`.
-- source:
--   Kallus, Udell, Dynamic Assortment Personalization in High Dimensions, arXiv:1610.05604 (PDF sha256 2b010481…216a), Sec. 2, p. 5 (μ⋆ ∈ Δ^m); Sec. 3, p. 11 (P(I = i) = μ⋆_i); Sec. 3.2, p. 13 (i_t iid); Theorem 4, p. 18 (q ∈ [1, ∞])

import Mathlib

namespace DynAssortPers.TypeDist

open Finset
open scoped ENNReal

/-- The probability of an event `E` about an i.i.d. sample of size `N` from a law `μ` on the finite
set `Fin m`: a sample is a map `x : Fin N → Fin m` (draw `t` is `x t`), it has weight
`∏_t μ (x t)` under the product law, and `iidProb μ E = ∑_{x ∈ E} ∏_t μ (x t)`. This is a finite
sum, no measure theory; it is a probability when `μ` lies in the simplex `stdSimplex ℝ (Fin m)`. -/
noncomputable def iidProb {m N : ℕ} (μ : Fin m → ℝ) (E : (Fin N → Fin m) → Prop) : ℝ := by
  classical
  exact ∑ x ∈ univ.filter E, ∏ t, μ (x t)

/-- The `ℓ_q` norm of `v ∈ ℝ^m` for `q ∈ [0, ∞]`, taken from Mathlib's `PiLp`:
`(∑_i |v_i|^q)^{1/q}` for `0 < q < ∞` and `max_i |v_i|` for `q = ∞`. -/
noncomputable def lqNorm {m : ℕ} (q : ℝ≥0∞) (v : Fin m → ℝ) : ℝ :=
  ‖(WithLp.toLp q v : PiLp q (fun _ : Fin m => ℝ))‖

/-- The real exponent `1/q` for `q ∈ [1, ∞]`, with the convention `1/∞ = 0`; so `m ^ invQ q` is
`m^{1/q}` and equals `1` at `q = ∞`. -/
noncomputable def invQ (q : ℝ≥0∞) : ℝ :=
  if q = ∞ then 0 else 1 / q.toReal

end DynAssortPers.TypeDist


