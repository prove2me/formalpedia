-- Prove2me | Definitions.Def_PlugInRisk_avar
-- name    : PlugInRisk_avar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:30.511044+00:00
-- url     : https://prove2.me/theorems/df4fcd50-6f54-477f-97c4-c7246a797929
-- title:
--   Average value at risk of a law, display (1.1)
-- statement:
--   For a probability law $\nu$ on $\mathbb R$ with finite mean and a level $u\in[0,1)$, the **average value at risk** is
--
--   $$
--   \mathrm{AVaR}_u(\nu)=\inf_{m\in\mathbb R}\Bigl(\frac{1}{1-u}\int(x-m)^+\,\nu(dx)+m\Bigr).
--   $$
--
--   For a random variable $X$, $\mathrm{AVaR}_u(X)=\mathrm{AVaR}_u(\text{law of }X)$, and $\mathrm{AVaR}^\mu_u(F)=\mathrm{AVaR}_u(\mu\circ F^{-1})$. At $u=0$ it is the mean; as $u\to1$ it tends to the essential supremum. AVaR is the building block of the spectral representation of every law-invariant risk measure.
--
--   **Formalization Note** The infimum is a real infimum; for an integrable law the family is bounded below by the mean. Levels $u\ge1$ are not used.
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, display (1.1), p.2

import Mathlib

open MeasureTheory

namespace PlugInRisk

/-- **Average value at risk of a law** (Bartl & Tangpi, arXiv:2003.10479v2, display (1.1), p.2):
`AVaR_u(F(S)) = inf_{m∈ℝ} ( (1/(1−u)) E[(F(S) − m)⁺] + m )`.

`avar ν u` is this quantity for a random variable with law `ν`, so `AVaR_u(X) = avar (law X) u`
and `AVaR^μ_u(F) = avar (μ.map F) u`.

**Formalization Note** The level `u` ranges over `[0, 1)` in the paper (from §4 on, with
`AVaR₀ = E`); for `u ≥ 1` the value is meaningless and no statement uses it. For an integrable
law the family is bounded below by the mean, so the real infimum is the paper's; every statement
applies `avar` only to integrable laws. -/
noncomputable def avar (ν : Measure ℝ) (u : ℝ) : ℝ :=
  ⨅ m : ℝ, ((1 - u)⁻¹ * ∫ x, max (x - m) 0 ∂ν + m)

end PlugInRisk


