-- Prove2me | Definitions.Def_SmithRenewal_Elementary_RenewalProcess
-- name    : SmithRenewal_Elementary_RenewalProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:26:56.995028+00:00
-- url     : https://prove2.me/theorems/598a5f5f-0c07-44a1-8bb4-d2e27d33e015
-- title:
--   Renewal process (§1.2): i.i.d. non-negative lifetimes, not a.s. zero; S_n, N_t, H(t) = EN_t, μ₁ = EX_i, ζ_t, truncation X_i†
-- statement:
--   This file fixes the objects of §1.2 of Smith (1958).
--
--   1. **Renewal process.** On a probability space $(\Omega,\mathcal F,P)$, a renewal process is a sequence $X_1, X_2, \dots$ of mutually independent, identically distributed, non-negative random variables which "do not vanish with probability one", that is, $P(X_i = 0) < 1$. The $X_i$ are the lifetimes of successive articles; $X_i = 0$ with positive probability is allowed.
--   2. **Renewal epochs.** $S_0 = 0$ and $S_n = X_1 + \dots + X_n$ is the time of the $n$-th renewal.
--   3. **Counting variable.** $N_t$ is the number of renewals in $[0,t]$, the number of indices $n \ge 1$ with $S_n \le t$. For $t \ge 0$ this is the largest $n$ with $S_n \le t$; it takes values in $\{0,1,2,\dots\}\cup\{\infty\}$, the value $\infty$ occurring only on an event of probability zero.
--   4. **Renewal function and mean lifetime.**
--   $$H(t) = \mathbb E N_t \in [0,\infty], \qquad \mu_1 = \mathbb E X_i \in (0,\infty].$$
--   5. **Residual lifetime.** $\zeta_t$ is defined by $S_{N_t+1} = t + \zeta_t$, the residual useful life of the article in use at time $t$.
--   6. **Truncation.** For $\Delta > 0$, $X_i^\dagger = \min(X_i, \Delta)$, i.e. $X_i^\dagger = X_i$ if $X_i \le \Delta$ and $X_i^\dagger = \Delta$ otherwise. The quantities $S_n^\dagger, N_t^\dagger, H^\dagger(t), \mu_1^\dagger, \zeta_t^\dagger$ are the same constructions applied to $(X_i^\dagger)$.
--
--   These are the objects of the elementary renewal theorem and of Doob's proof as presented by Smith.
--
--   **Formalization Note** The lifetimes $X_1, X_2, \dots$ are indexed from $0$ in Lean (`X 0, X 1, …`). Non-negativity is required at every sample point, measurability is part of "random variable", and independence is mutual (`iIndepFun`). $N_t$ is a count in `ℕ∞`; $H$ and $\mu_1$ are lower Lebesgue integrals in $[0,\infty]$, so no finiteness is presupposed. $\zeta_t$ reads $N_t$ through `ENat.toNat`, so on the null event $N_t = \infty$ it equals $S_1 - t$; this never affects an expectation.
-- source:
--   Smith, Renewal Theory and Its Ramifications, J. R. Statist. Soc. B 20(2):243–283 (1958), DOI 10.1111/j.2517-6161.1958.tb00294.x, §1.2, pp. 245–246

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SmithRenewal.Elementary

/-- **Renewal process** (Smith, *Renewal Theory and Its Ramifications*, J. R. Statist. Soc. B
20(2):243–283 (1958), §1.2, p. 245, unnumbered): "a sequence {X_i} of independent, non-negative,
identically distributed random variables, and to avoid triviality we suppose the X_i do not vanish
with probability one."

Formalization Note: the paper's lifetimes `X₁, X₂, …` are `X 0, X 1, …`. "Random variable" is read
as a measurable real function; "independent" is mutual independence (`iIndepFun`); "identically
distributed" is `IdentDistrib (X i) (X 0)` for every `i`; non-negativity is required at every
sample point; "do not vanish with probability one" is `P {X 0 = 0} < 1`. Strict positivity of the
`X i` is **not** assumed. -/
structure IsRenewalProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ) :
    Prop where
  measurable : ∀ i, Measurable (X i)
  indep : iIndepFun X P
  identDistrib : ∀ i, IdentDistrib (X i) (X 0) P P
  nonneg : ∀ i ω, 0 ≤ X i ω
  not_ae_zero : P {ω | X 0 ω = 0} < 1

/-- Partial sums (§1.2, p. 245): `S X n ω = X₁ + ⋯ + X_n` in the paper's indexing, i.e.
`X 0 ω + ⋯ + X (n-1) ω`; `S X 0 = 0`. It is the time of the `n`-th renewal. -/
def S {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, X i ω

/-- Counting variable `N_t` (§1.2, p. 245): "the biggest value of n for which S_n ≤ t; in other
words N_t is the number of renewals that will have occurred by the time t (including any made at
t)".

Formalization Note: `N X t ω` is the number of indices `n ≥ 1` with `S_n ≤ t`, as an element of
`ℕ∞`. For non-negative lifetimes and `t ≥ 0` this set is `{1, …, m}`, so the count is the biggest
`n` with `S_n ≤ t` (and `0` when `S_1 > t`); for `t < 0` it is `0`. It equals `⊤` exactly when every
`S_n ≤ t`, an event of probability zero for a renewal process. -/
noncomputable def N {Ω : Type*} (X : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℕ∞ :=
  {n : ℕ | 1 ≤ n ∧ S X n ω ≤ t}.encard

/-- Renewal function (§1.2, p. 246): "H(t) ≡ EN_t", the expected number of renewals in `[0, t]`,
as a lower Lebesgue integral with values in `[0, ∞]` (it is not assumed finite). -/
noncomputable def H {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ) (P : Measure Ω) (t : ℝ) :
    ℝ≥0∞ :=
  ∫⁻ ω, (N X t ω : ℝ≥0∞) ∂P

/-- Mean lifetime (§1.2, p. 246): "μ₁ = EX_i ≤ ∞", as a lower Lebesgue integral in `[0, ∞]`; the
value `∞` is allowed. -/
noncomputable def mu1 {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ) (P : Measure Ω) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (X 0 ω) ∂P

/-- Residual lifetime `ζ_t` (§1.2, p. 246): defined by "S_{N_t+1} = t + ζ_t", the residual useful
life of the article in use at time `t`.

Formalization Note: `zeta X t ω = S_{N_t(ω)+1}(ω) − t`, where `N_t(ω)` is read through
`ENat.toNat`. On the probability-zero event `N_t = ⊤` this gives `S_1 − t`; that value never
affects an expectation. -/
noncomputable def zeta {Ω : Type*} (X : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  S X ((N X t ω).toNat + 1) ω - t

/-- Truncated process (§1.2, p. 246): "X_i† = X_i for X_i ≤ Δ, and X_i† = Δ for X_i > Δ", i.e.
`X_i† = min (X_i, Δ)`. The related quantities `S†, N†, H†, μ₁†, ζ†` are `S, N, H, mu1, zeta`
applied to `trunc Δ X`. -/
def trunc {Ω : Type*} (Δ : ℝ) (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun i ω => min (X i ω) Δ

end SmithRenewal.Elementary


