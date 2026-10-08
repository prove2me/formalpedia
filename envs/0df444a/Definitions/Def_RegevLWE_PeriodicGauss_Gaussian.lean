-- Prove2me | Definitions.Def_RegevLWE_PeriodicGauss_Gaussian
-- name    : RegevLWE_PeriodicGauss_Gaussian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:55.14942+00:00
-- url     : https://prove2.me/theorems/b36efedb-ae85-4083-8dba-729e401a27cb
-- title:
--   Eqs. (5), (7) and p. 34:14 — the normal density ν_β, the periodic normal density Ψ_β on 𝕋, and the statistical distance Δ
-- statement:
--   Write $\mathbb{T} = \mathbb{R}/\mathbb{Z}$, identified with the segment $[0,1)$ with addition modulo $1$.
--
--   1. **Normal density** (Eq. (5) with $n = 1$). For $\beta > 0$ and $x \in \mathbb{R}$,
--   $$\nu_\beta(x) := \frac{1}{\beta}\exp\Bigl(-\pi\Bigl(\frac{x}{\beta}\Bigr)^2\Bigr),$$
--   the density of a normal variable with mean $0$ and standard deviation $\beta/\sqrt{2\pi}$.
--   2. **Periodic normal density** (Eq. (7)). For $\beta > 0$ and $r \in [0,1)$,
--   $$\Psi_\beta(r) := \sum_{k=-\infty}^{\infty} \frac{1}{\beta}\exp\Bigl(-\pi\Bigl(\frac{r-k}{\beta}\Bigr)^2\Bigr),$$
--   the density on $\mathbb{T}$ of a normal variable with mean $0$ and standard deviation $\beta/\sqrt{2\pi}$ reduced modulo $1$.
--   3. **Statistical distance** (p. 34:14). For densities $\varphi_1, \varphi_2$ on $\mathbb{R}$, $\Delta(\varphi_1,\varphi_2) := \int_{\mathbb{R}} |\varphi_1(x) - \varphi_2(x)|\,dx$, and for densities on $\mathbb{T}$, $\Delta(\varphi_1,\varphi_2) := \int_0^1 |\varphi_1(r) - \varphi_2(r)|\,dr$. There is no factor $\tfrac12$: on probability densities the distance ranges in $[0,2]$.
--
--   The periodic normal distribution $\Psi_\beta$ is the error distribution of the Learning with Errors problem in Regev's paper; these objects are the vocabulary of Claim 2.2.
--
--   **Formalization Note** The two distances are lower Lebesgue integrals of $|\varphi_1 - \varphi_2|$ with values in $[0,\infty]$ (`statDist` over $\mathbb{R}$, `statDistT` over `Set.Ico 0 1`), so they cannot collapse to $0$ on a non-integrable difference. $\Psi_\beta$ is a real `tsum` over $k \in \mathbb{Z}$; the series converges absolutely for $\beta \neq 0$, so the value is the true one. The formulas are evaluated for every real argument; the paper (and every theorem of the mission) uses them for $\beta > 0$ and, for $\Psi_\beta$, only on $[0,1)$.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:14 (𝕋 and statistical distance), p. 34:15 Eq. (5), p. 34:16 Eq. (7)

import Mathlib

open MeasureTheory

namespace RegevLWE.PeriodicGauss

/-- The one-dimensional normal density with mean `0` and standard deviation `β / √(2π)`,
`ν_β(x) = (1/β) · exp(-π (x/β)²)` (Regev, J. ACM 2009, p. 34:15, Eq. (5) with `n = 1`, and
p. 34:16, Eq. (7)); the paper uses it for `β > 0`. -/
noncomputable def nu (β : ℝ) (x : ℝ) : ℝ :=
  (1 / β) * Real.exp (-Real.pi * (x / β) ^ 2)

/-- The periodic normal density `Ψ_β(r) = ∑_{k ∈ ℤ} (1/β) · exp(-π ((r - k)/β)²)`
(p. 34:16, Eq. (7)): the density on `𝕋 = [0, 1)` of a normal variable with mean `0` and standard
deviation `β / √(2π)` reduced modulo `1`. The formula is evaluated for every real `r`; only its
values on `[0, 1)` are used. -/
noncomputable def Psi (β : ℝ) (r : ℝ) : ℝ :=
  ∑' k : ℤ, (1 / β) * Real.exp (-Real.pi * ((r - k) / β) ^ 2)

/-- The statistical distance `Δ(φ₁, φ₂) = ∫_ℝ |φ₁(x) - φ₂(x)| dx` of two densities on `ℝ`
(p. 34:14), with **no** factor `1/2`; a lower Lebesgue integral with values in `ℝ≥0∞`. -/
noncomputable def statDist (φ₁ φ₂ : ℝ → ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal |φ₁ x - φ₂ x|

/-- The statistical distance `Δ(φ₁, φ₂) = ∫_{[0,1)} |φ₁(r) - φ₂(r)| dr` of two densities on
`𝕋 = ℝ/ℤ`, identified with the segment `[0, 1)` (p. 34:14), with **no** factor `1/2`; a lower
Lebesgue integral with values in `ℝ≥0∞`. -/
noncomputable def statDistT (φ₁ φ₂ : ℝ → ℝ) : ENNReal :=
  ∫⁻ r in Set.Ico (0 : ℝ) 1, ENNReal.ofReal |φ₁ r - φ₂ r|

end RegevLWE.PeriodicGauss


