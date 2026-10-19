-- Prove2me | Definitions.Def_LogMeanVar_Complete_LogReturn
-- name    : LogMeanVar_Complete_LogReturn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:12.509114+00:00
-- url     : https://prove2.me/theorems/b92dff99-273d-4dc5-a0a1-32c19a8a41d5
-- title:
--   (6) and A_t, p. 8 — the log-return SDE started at (t, y), driven by B_{t+·} − B_t, and admissible feedback strategies
-- statement:
--   This file builds the log-return equation (6) and the admissible set $\mathcal A_t$ of p. 8 in the complete market of §3.
--
--   Fix a probability space $(\Omega,\mathcal F,\mathbb P)$ carrying a standard Brownian motion $B$. A **feedback strategy** is a function $\pi(\tau,y)$: the fraction of wealth held in the stock at time $\tau$ when the log-wealth is $y$. For a start $(t,y)$, write $B^{(t)}_u = B_{t+u}-B_t$ for the Brownian increments after $t$, and $\mathcal F^{(t)}_u$ for their natural filtration.
--
--   A process $R$ is a **solution of (6) on $[t,T]$ started at $R_t=y$** if
--
--   1. each $R_s$, $s\in[t,T]$, is (up to a null set) $\mathcal F^{(t)}_{s-t}$-measurable;
--   2. its paths are almost surely continuous on $[t,T]$;
--   3. almost surely $\tau\mapsto\pi(\tau,R_\tau)$ is integrable and square integrable on $[t,T]$;
--   4. there is an Itô integral $I$ of $u\mapsto\sigma\pi(t+u,R_{t+u})$ (set to $0$ after the horizon) against $B^{(t)}$, and for every $s\in[t,T]$, almost surely,
--   $$R_s = y+\int_t^s\Big(r+(\mu-r)\pi(\tau,R_\tau)-\tfrac12\sigma^2\pi(\tau,R_\tau)^2\Big)d\tau + I_{s-t}.$$
--
--   This is the integral form of $dR_s=[r+(\mu-r)\pi_s-\tfrac12\sigma^2\pi_s^2]\,ds+\sigma\pi_s\,dB_s$.
--
--   A strategy $\pi$ is **admissible** if for every $t\in[0,T)$ and every $y\in\mathbb R$:
--
--   1. (6) has a solution started at $(t,y)$;
--   2. any two such solutions agree almost surely on all of $[t,T]$;
--   3. every solution satisfies $\mathbb E\big[\int_t^T|\sigma\pi(s,R_s)|^2ds\big]<+\infty$ (the printed condition defining $\mathcal A_t$);
--   4. every solution has $R_T\in L^2(\mathbb P)$.
--
--   The reward function and the equilibrium notion of the mission are defined on these solutions.
--
--   **Formalization Note** The complete market has no state variable $X$, so strategies are functions of $(\tau,y)$ only. The Itô integral is the published relation `EthierKurtz.HasBrownianItoIntegral` (adapted bounded step integrands converging in integrated squared error, and their Itô sums converging in probability), in elapsed time from $t$; the integrand is also set to $0$ on the null set of paths where it is not square integrable, as that relation requires square integrability on every path. Conditions 1, 2 and 4 of admissibility are not printed in the definition of $\mathcal A_t$: they are added so that the mean and variance of $R_T$ are well-defined real numbers.
-- source:
--   Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), pp. 7–8, (1), (3), (6), definition of A_t; p. 11, §3

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_LogMeanVar_Complete_Market
import Definitions.Def_LogMeanVar_Complete_BrownianShift

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace LogMeanVar.Complete

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A feedback trading strategy of the complete market (p. 8, "we restrict attention to
feedback strategy πt = π(t,Rt,Xt)"): `π τ y` is the fraction of wealth held in the stock at
time `τ` when the log-wealth is `y`.

**Formalization Note** The complete market of §3 has no state variable `X`, so the argument
`x` of `π(t, y, x)` is dropped. -/
abbrev Strategy := ℝ → ℝ → ℝ

open Classical in
/-- The diffusion integrand `σ π(t+u, R_{t+u})` of (6), p. 8, in elapsed time `u`, cut off to
`0` after the horizon (`t + u > T`) and on the null set of paths on which
`τ ↦ π(τ, R_τ)` is not square integrable on `[t, T]`. -/
noncomputable def logReturnIntegrand (M : Market) (π : Strategy) (t : ℝ) (R : ℝ → Ω → ℝ) :
    ℝ≥0 → Ω → ℝ :=
  fun u ω =>
    if t + (u : ℝ) ≤ M.T ∧
        IntervalIntegrable (fun τ => (π τ (R τ ω)) ^ 2) volume t M.T then
      M.σ * π (t + u) (R (t + u) ω)
    else 0

/-- `R` is a solution on `[t, T]` of the log-return equation (6), p. 8, with constant market
parameters (§3, p. 11),
`dR_s = [r + (μ - r)π_s - ½σ²π_s²] ds + σπ_s dB_s`, `π_s = π(s, R_s)`,
started at `R_t = y`:
1. each `R_s`, `s ∈ [t, T]`, is (up to a null set) measurable for the natural filtration of
   `B_{t+·} - B_t` at elapsed time `s - t`;
2. the paths `s ↦ R_s` are a.s. continuous on `[t, T]`;
3. `τ ↦ π(τ, R_τ)` is a.s. integrable and square integrable on `[t, T]`;
4. there is an Itô integral `I` of `σπ(t+·, R_{t+·})` against `B_{t+·} - B_t`
   (`EthierKurtz.HasBrownianItoIntegral`) such that for every `s ∈ [t, T]`, a.s.,
   `R_s = y + ∫_t^s (r + (μ - r)π(τ, R_τ) - σ²π(τ, R_τ)²/2) dτ + I_{s-t}`. -/
def IsLogReturn (M : Market) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (π : Strategy) (t y : ℝ)
    (R : ℝ → Ω → ℝ) : Prop :=
  (∀ s ∈ Icc t M.T, AEStronglyMeasurable[shiftFiltration B t (s - t).toNNReal] (R s) P) ∧
  (∀ᵐ ω ∂P, ContinuousOn (fun s => R s ω) (Icc t M.T)) ∧
  (∀ᵐ ω ∂P, IntervalIntegrable (fun τ => π τ (R τ ω)) volume t M.T ∧
    IntervalIntegrable (fun τ => (π τ (R τ ω)) ^ 2) volume t M.T) ∧
  ∃ I : ℝ≥0 → Ω → ℝ,
    EthierKurtz.HasBrownianItoIntegral P (shiftFiltration B t) (shiftBM B t)
      (logReturnIntegrand M π t R) I ∧
    ∀ s ∈ Icc t M.T, ∀ᵐ ω ∂P,
      R s ω = y + (∫ τ in t..s,
          (M.r + (M.μ - M.r) * π τ (R τ ω) - M.σ ^ 2 * (π τ (R τ ω)) ^ 2 / 2))
        + I (s - t).toNNReal ω

/-- The admissible strategies `A_t` of p. 8,
`A_t = {π : E_t[∫_t^T |σ π(s, R^π_s)|² ds] < +∞}`, required at every `t ∈ [0, T)` and every
starting log-wealth `y`, together with what makes `J` a real number (`paper.md` slip 8):
1. (6) has a solution started at `(t, y)`;
2. any two solutions agree a.s. on `[t, T]`;
3. every solution satisfies `E[∫_t^T |σ π(s, R_s)|² ds] < ∞` (the printed condition);
4. every solution has `R_T ∈ L²`.

**Formalization Note** Conditions 1, 2 and 4 are not printed in the definition of `A_t`; they
are added so that `E_t[R^π_T]` and `Var_t[R^π_T]` are well-defined real numbers. -/
def Admissible (M : Market) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (π : Strategy) : Prop :=
  ∀ t ∈ Ico 0 M.T, ∀ y : ℝ,
    (∃ R, IsLogReturn M P B π t y R) ∧
    (∀ R R', IsLogReturn M P B π t y R → IsLogReturn M P B π t y R' →
      ∀ᵐ ω ∂P, ∀ s ∈ Icc t M.T, R s ω = R' s ω) ∧
    (∀ R, IsLogReturn M P B π t y R →
      (∫⁻ ω, (∫⁻ s in Icc t M.T, ‖M.σ * π s (R s ω)‖ₑ ^ 2) ∂P) < ∞) ∧
    (∀ R, IsLogReturn M P B π t y R → MemLp (R M.T) 2 P)

end LogMeanVar.Complete


