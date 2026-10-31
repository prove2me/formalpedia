-- Prove2me | Definitions.Def_MFCLiquidation_IsItoIntegral
-- name    : MFCLiquidation_IsItoIntegral
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:23:46.318213+00:00
-- url     : https://prove2.me/theorems/d975f94b-8e2b-48bc-a4e0-fbb84c6f4a2c
-- title:
--   The Itô integral $\int_0^\cdot H\,dW$ of a progressive square-integrable integrand, by its brackets
-- statement:
--   Let $W$ be a Brownian motion and $H$ a progressively measurable process with $\int_0^T H_s^2\,ds<\infty$ a.s. A process $N$ is the **Itô integral** $N=\int_0^{\cdot\wedge T}H\,dW$ if
--
--   1. $N$ has continuous paths and $N_0=0$;
--   2. $N$ is a (true) martingale for the filtration $\mathbb F$;
--   3. its quadratic variation is $[N,N]_s=\int_0^{s\wedge T}H_r^2\,dr$ and its covariation with $W$ is $[N,W]_s=\int_0^{s\wedge T}H_r\,dr$.
--
--   The brackets give $[N-\int H\,dW]=0$, so $N$ coincides with the stochastic integral. This characterization is needed because the volatility $\sigma$ and the BSDE integrand $Z^F$ of the paper are only progressively measurable: left-point Riemann sums define $\int H\,dW$ only for càdlàg $H$.
--
--   **Formalization Note** Brackets are the dyadic limits in probability of `EthierKurtz.HasCrossVariation`. Time is $\mathbb R_{\ge0}$ and only $[0,T]$ matters.
-- source:
--   Fu, Horst & Xia, A Mean-Field Control Problem of Optimal Portfolio Liquidation with Semimartingale Strategies, arXiv:2207.00446v3, (2.10) and (2.17), pp.8–10 (σ_s dW_s and Z^F_t dW_t with σ, Z^F progressively measurable); standing assumption item 3, p.10

import Mathlib
import Definitions.Def_EthierKurtz_HasCrossVariation

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MFCLiquidation

/-- `N = ∫₀^· H dW` on the horizon `[0, T]`, for an integrand `H` that is only progressively
measurable, with `∫₀ᵀ H² ds < ∞` almost surely.

The left-point Riemann sums of `KurtzProtter91.Integrals.HasStochIntegral` are correct for cadlag
integrands only, so the integral is pinned down by its characterization (Kunita–Watanabe): `N` is
a continuous `𝔽`-martingale started at `0`, constant after `T`, with
`[N, N] = ∫₀^· H² ds` and `[N, W] = ∫₀^· H ds`. Then `[N − ∫H dW] = 0`, so `N = ∫H dW`.

Formalization Note: this is a true martingale, not merely a local one, which is what makes the
BSDE (2.17) well posed. Progressive measurability and square-integrability are asked of `H` on
`[0, T]` only (through the process stopped at `T`), and the second clause excludes the
default-zero Bochner integral of a non-integrable `H²`. Time integrals run over `ℝ`, with
`r.toNNReal` the corresponding point of the time index `ℝ≥0`. -/
def IsItoIntegral {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 m) (W : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (H N : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive 𝓕 (fun s ω => H (min s T) ω) ∧
  (∀ᵐ ω ∂P, IntervalIntegrable (fun r : ℝ => H r.toNNReal ω ^ 2) volume 0 (T : ℝ)) ∧
  (∀ ω, Continuous fun s => N s ω) ∧
  (∀ ω, N 0 ω = 0) ∧
  Martingale N 𝓕 P ∧
  EthierKurtz.HasCrossVariation P N N
    (fun s ω => ∫ r in (0 : ℝ)..(min s T : ℝ≥0), H r.toNNReal ω ^ 2) ∧
  EthierKurtz.HasCrossVariation P N W
    (fun s ω => ∫ r in (0 : ℝ)..(min s T : ℝ≥0), H r.toNNReal ω)

end MFCLiquidation


