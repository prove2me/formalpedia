-- Prove2me | Definitions.Def_MomentSearch_Supplement_cdf
-- name    : MomentSearch_Supplement_cdf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:29:31.425391+00:00
-- url     : https://prove2.me/theorems/2c1affe6-3ad2-4070-864a-1cc47402cdd2
-- title:
--   CDF, Kolmogorov distance $d_K$, Kolmogorov balls $B_K(\pi,\delta)$ and the collection $\mathcal U_{K,\delta}$
-- statement:
--   Let $p=(p_0,\dots,p_{n-1})$ be a vector on the path $[n]_0=\{0,\dots,n-1\}$. Its **cumulative distribution function** is
--   $$P(t)=\sum_{j=0}^{t}p_j,\qquad t\in[n]_0 .$$
--   For two distributions $p,\pi$ with CDFs $P,\Pi$, the **Kolmogorov distance** is
--   $$d_K(p,\pi)=\|P-\Pi\|_\infty=\max_{0\le t\le n-1}|P(t)-\Pi(t)|.$$
--   For a nominal distribution $\pi\in\Delta_n$ and a radius $\delta$, the **Kolmogorov ball** is $B_K(\pi,\delta)=\{p\in\Delta_n: d_K(p,\pi)\le\delta\}$, and $\mathcal U_{K,\delta}=\{B_K(\pi,\delta):\pi\in\Delta_n\}$ is the uncertainty collection of all such balls.
--
--   These objects state the Coarse Greedy guarantee (Theorem 5), the quantile bound (Theorem 8), the characterization of Kolmogorov balls (Theorem 9), moment recovery (Theorem 18) and the dyadic sketch (Theorem 27).
--
--   **Formalization Note** The CDF is evaluated at natural numbers; the paper's convention $P(-1)=0$ is never needed. The maximum is a real supremum over the finite index set $[n]_0$, which is attained for $n\ge1$; all statements assume $n\ge2$. $\Delta_n$ is Mathlib's standard simplex.
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43350dfaea073a9c0a9a0850a9955ea82082a7163a2db90cc48b9339e3), §2.2, p.6 (PDF p.8): CDF, Kolmogorov distance, Kolmogorov ball, U_K,δ

import Mathlib

namespace MomentSearch.Supplement

/-- The cumulative distribution function `P(t) := ∑_{j=0}^{t} p_j` of a vector `p` on
`[n]₀ = {0, …, n − 1}`, evaluated at a natural number `t` (Megow, Stein, Verschae,
*Distributionally Robust Search: The Power of Information and the Limits of Moments*,
arXiv:2611.04559 (held version, sha256 fbfa4b43…), §2.2, p.6 (PDF p.8)).

**Formalization Note.** `t` is a natural number; for `t ≥ n − 1` the value is `∑_j p_j`
(`= 1` on the simplex). The paper's convention `P(−1) := 0` is never needed, because all
statements evaluate the CDF at `t ∈ [n]₀`. -/
def cdf {n : ℕ} (p : Fin n → ℝ) (t : ℕ) : ℝ :=
  ∑ s : Fin n, if (s : ℕ) ≤ t then p s else 0

/-- The Kolmogorov distance `d_K(p, π) := ‖P − Π‖_∞ = max_{0 ≤ t ≤ n−1} |P(t) − Π(t)|`
(arXiv:2611.04559, held version, §2.2, p.6 (PDF p.8)).

**Formalization Note.** Written as a real `⨆` over the finite index type `Fin n`; for `n ≥ 1`
it is the maximum of finitely many reals (attained), as in the paper. Every statement assumes
`n ≥ 2`, so the junk value `0` of an empty supremum never arises. -/
noncomputable def kolDist {n : ℕ} (p π : Fin n → ℝ) : ℝ :=
  ⨆ t : Fin n, |cdf p (t : ℕ) - cdf π (t : ℕ)|

/-- The Kolmogorov ball `B_K(π, δ) := {p ∈ Δ_n : d_K(p, π) ≤ δ}`
(arXiv:2611.04559, held version, §2.2, p.6 (PDF p.8)); `Δ_n` is `stdSimplex ℝ (Fin n)`. -/
def kolBall {n : ℕ} (π : Fin n → ℝ) (δ : ℝ) : Set (Fin n → ℝ) :=
  {p | p ∈ stdSimplex ℝ (Fin n) ∧ kolDist p π ≤ δ}

/-- The uncertainty collection `𝒰_{K,δ} := {B_K(π, δ) : π ∈ Δ_n}` of all Kolmogorov balls of
radius `δ` around a nominal distribution in the simplex
(arXiv:2611.04559, held version, §2.2, p.6 (PDF p.8)). -/
def kolCollection (n : ℕ) (δ : ℝ) : Set (Set (Fin n → ℝ)) :=
  {U | ∃ π ∈ stdSimplex ℝ (Fin n), U = kolBall π δ}

end MomentSearch.Supplement


