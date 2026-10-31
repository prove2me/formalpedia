-- Prove2me | Definitions.Def_RelPerfMFG_Centralized
-- name    : RelPerfMFG_Centralized
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:27:36.444231+00:00
-- url     : https://prove2.me/theorems/2f051fb9-15eb-4555-8151-5c9b410990f2
-- title:
--   Centralized problem (3.4), the ratio-based RPC payoff $F(a^i,a;f)$ (3.12) and optimal RPCs (Definition 3.3)
-- statement:
--   This module defines the objects of §3.1–§3.2.
--
--   1. **Centralized payoff** (3.4), p.10: for a control $a$, the random variable $R(\sum_k a_k,Y)-\sum_k C_k(a_k)$; $V=\sup_{a\in\mathcal A}\mathbb E[\cdot]$.
--   2. **Optimal solution** (`IsOptimalSolution`): $a^*\in\mathcal A$ whose payoff is integrable (so $V<\infty$) and such that every $a\in\mathcal A$ has expected payoff at most $\mathbb E[\text{payoff}(a^*)]$ (in the extended sense).
--   3. **The conditional-finiteness assumption of Lemma 3.1** (`CondFiniteDeriv`): almost surely, $\mathbb E\big[|R'(a^*_0+\dots+a^*_{k-1}+a+a^*_{k+1}+\dots+a^*_{N-1})|\,\big|\,\mathcal F^Y_k\big]<\infty$ for all $a$ close to $a^*_k$.
--   4. **Aggregates** $\bar a_k=\mathbb E[a_k\mid\mathcal F^Y_k]$ (p.13), and the mean $m_D$ of the conditional law $D$ of the cumulative performance $\sum_k\phi_k(a_k,X_{k+1})$ given $Y$.
--   5. **Ratio-based RPC** (3.12), p.13: $f(x,D,y)=(1-\beta(y))+\beta(y)\,x/m_D$, and the payoff of a player using $a^i$ while all others use $a$,
--   $$F(a^i,a;f)=\mathbb E\Big[f\Big(\sum_k\phi_k(a^i_k,X^i_{k+1}),D,Y\Big)R\Big(\sum_k\bar a_k\Big)-\sum_kC_k(a^i_k)\Big].$$
--   6. **Definition 3.3**, p.14: $\hat a\in\tilde{\mathcal A}$ is an equilibrium w.r.t. $f$ if $\hat a\in\arg\max_{a\in\tilde{\mathcal A}}F(a,\hat a;f)$; $f$ is an optimal RPC if some equilibrium has $F(\hat a,\hat a;f)=V$.
--
--   **Formalization Note** Conditional expectations of nonnegative or possibly non-integrable quantities (items 3–4) are integrals against regular conditional distributions, so they are meaningful for every outcome and never collapse to Mathlib's value $0$ for non-integrable functions; for $a\in\mathcal A$, $\bar a_k=a_k$ a.s. Payoff comparisons and the equilibrium value are expectations in the extended sense (`ExpLE`, `ExpEq`). Representative-player form: the player's own noise is $X$. Lean's $x/0=0$.
-- source:
--   Zhou, Optimal relative performance criteria in mean field contribution games, SSRN 3742584 (Nov. 13, 2022), Section 3.1, p.10 ((3.4), Lemma 3.1 assumptions); Section 3.2, pp.13–14 ((3.12), F(a^i, a; f), Definition 3.3)

import Mathlib
import Definitions.Def_RelPerfMFG_Setup

open MeasureTheory ProbabilityTheory

namespace RelPerfMFG

variable {Ω : Type*} [MeasurableSpace Ω] {N d e : ℕ}

/-- **The centralized payoff** inside (3.4), Zhou, *Optimal relative performance criteria in
mean field contribution games*, SSRN 3742584 (Nov. 13, 2022), §3.1, p.10:
`R(Σ_{k=0}^{N−1} a_k, Y) − Σ_{k=0}^{N−1} C_k(a_k)`, a random variable. -/
noncomputable def centralPayoff (Y : Ω → NoisePath N e) (C : Fin N → ℝ → ℝ)
    (R : ℝ → NoisePath N e → ℝ) (a : Fin N → Ω → ℝ) (ω : Ω) : ℝ :=
  R (∑ k, a k ω) (Y ω) - ∑ k, C k (a k ω)

/-- **An optimal solution for `V`** in (3.4), SSRN 3742584 (Nov. 13, 2022), §3.1, p.10:
`a* ∈ 𝒜` attains `V = sup_{a∈𝒜} E[R(Σ a_k) − Σ C_k(a_k)]`, and `V < ∞`.

**Formalization Note.** The payoff of `a*` is integrable (so `V = E[payoff(a*)]` is finite) and
every `a ∈ 𝒜` has `E[payoff(a)] ≤ V` in the extended sense (`ExpLE`), so no control with an
infinite or non-integrable payoff is discarded. -/
def IsOptimalSolution (μ : Measure Ω) (Y : Ω → NoisePath N e) (C : Fin N → ℝ → ℝ)
    (R : ℝ → NoisePath N e → ℝ) (a : Fin N → Ω → ℝ) : Prop :=
  IsCtrlA Y a ∧ Integrable (centralPayoff Y C R a) μ ∧
    ∀ b : Fin N → Ω → ℝ, IsCtrlA Y b →
      ExpLE μ (centralPayoff Y C R b) (∫ ω, centralPayoff Y C R a ω ∂μ)

/-- The regular conditional distribution of `(a, Y) = ((a₀, …, a_{N−1}), Y)` given
`F^Y_k = σ(Y₁, …, Y_k)`: a kernel from the `k`-prefix of the common-noise path. Integrating
against `ctrlNoiseKernel μ Y a k (truncPath k (Y ω))` is a version of `E[· | F^Y_k](ω)`, defined
also for nonnegative integrands that are not integrable. Used for Lemma 3.1, SSRN 3742584
(Nov. 13, 2022), p.10. -/
noncomputable def ctrlNoiseKernel (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → NoisePath N e)
    (a : Fin N → Ω → ℝ) (k : ℕ) : ProbabilityTheory.Kernel (NoisePath N e) ((Fin N → ℝ) × NoisePath N e) :=
  condDistrib (fun ω => ((fun j => a j ω), Y ω)) (fun ω => truncPath k (Y ω)) μ

/-- **The conditional finiteness assumption of Lemma 3.1**, SSRN 3742584 (Nov. 13, 2022), p.10,
for period `k`: almost surely,
`E[|R′(a*₀ + … + a*_{k−1} + a + a*_{k+1} + … + a*_{N−1})| | F^Y_k] < ∞` for all `a` close to `a*_k`.

**Formalization Note.** The conditional expectation is the integral against the regular
conditional distribution `ctrlNoiseKernel` (a `[0, ∞]`-valued integral, so "`< ∞`" is not
vacuous); "close to `a*_k`" is an open interval around `a*_k(ω)` whose radius may depend on `ω`.
`R′ = rderiv (R · y)`. -/
def CondFiniteDeriv (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → NoisePath N e)
    (R : ℝ → NoisePath N e → ℝ) (a : Fin N → Ω → ℝ) (k : Fin N) : Prop :=
  ∀ᵐ ω ∂μ, ∃ δ : ℝ, 0 < δ ∧ ∀ b : ℝ, |b - a k ω| < δ →
    ∫⁻ p, ENNReal.ofReal |rderiv (fun x => R x p.2)
        (∑ j, if j = k then b else p.1 j)| ∂(ctrlNoiseKernel μ Y a k (truncPath k (Y ω))) < ⊤

/-- The population aggregate `ā_k = E[a_k | F^Y_k]`, SSRN 3742584 (Nov. 13, 2022), §3.2, p.13
(and (4.2)–(4.3), p.19), a random variable.

**Formalization Note.** The conditional expectation of the nonnegative `a_k` is taken through
the regular conditional distribution of `a_k` given the first `k` common noises, as a
`[0, ∞]`-valued integral converted to a real number. For `a ∈ 𝒜` it equals `a_k` a.s. whether or
not `a_k` is integrable; where it is `+∞` the real value is `0`. -/
noncomputable def aggregate (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → NoisePath N e)
    (a : Fin N → Ω → ℝ) : Fin N → Ω → ℝ :=
  fun k ω => (∫⁻ v, ENNReal.ofReal v ∂(condDistrib (a k) (fun ω' => truncPath k (Y ω')) μ
    (truncPath k (Y ω)))).toReal

/-- The mean `m_D` of `D = D(Σ_{k=0}^{N−1} φ_k(a_k, X_{k+1}))`, the distribution of the cumulative
performance of all players conditioned on `Y`, SSRN 3742584 (Nov. 13, 2022), §3.2, p.13.

**Formalization Note.** `D` is the regular conditional distribution of
`Σ_k φ_k(a_k, X_{k+1})` given `Y`, evaluated at `Y(ω)`, and `m_D = ∫ s D(ds)`. Representative
form: the population's noise is `X`. 0-based periods: `φ k (a k ω) (X ω k)` is paper
`φ_k(a_k, X_{k+1})`. -/
noncomputable def perfMean (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → NoisePath N d)
    (Y : Ω → NoisePath N e) (φ : Fin N → ℝ → (Fin d → ℝ) → ℝ) (a : Fin N → Ω → ℝ) (ω : Ω) : ℝ :=
  ∫ s, s ∂(condDistrib (fun ω' => ∑ k, φ k (a k ω') (X ω' k)) Y μ (Y ω))

/-- **The payoff `F(aⁱ, a; f)` under the ratio-based RPC** (3.12), SSRN 3742584 (Nov. 13, 2022),
§3.2, p.13, as a random variable (the integrand of the expectation):
`f(Σ_k φ_k(aⁱ_k, Xⁱ_{k+1}), D, Y) · R(Σ_k ā_k) − Σ_k C_k(aⁱ_k)` with
`f(x, D, y) = (1 − β(y)) + β(y) · x / m_D` (3.12). Here `aⁱ = a'` is the representative player's
control, `a` the control of all the other players.

**Formalization Note.** `β` is a random variable (the paper's `β(Y)`); `f` depends on `D` only
through `m_D = perfMean`. Representative form: the player's own noise is `X`. Lean's `x / 0 = 0`. -/
noncomputable def ratioPayoff (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → NoisePath N d)
    (Y : Ω → NoisePath N e) (φ : Fin N → ℝ → (Fin d → ℝ) → ℝ) (C : Fin N → ℝ → ℝ)
    (R : ℝ → NoisePath N e → ℝ) (β : Ω → ℝ) (a' a : Fin N → Ω → ℝ) (ω : Ω) : ℝ :=
  ((1 - β ω) + β ω * (∑ k, φ k (a' k ω) (X ω k)) / perfMean μ X Y φ a ω) *
      R (∑ k, aggregate μ Y a k ω) (Y ω) - ∑ k, C k (a' k ω)

/-- **Equilibrium w.r.t. the ratio-based RPC, with payoff `v`**, SSRN 3742584 (Nov. 13, 2022),
Definition 3.3, p.14: `â ∈ 𝒜̃`, `F(â, â; f) = v`, and `â ∈ argmax_{a ∈ 𝒜̃} F(a, â; f)`, i.e.
`F(a, â; f) ≤ v` for every `a ∈ 𝒜̃`.

**Formalization Note.** Both the value and the comparisons are expectations in the extended
sense (`ExpEq`, `ExpLE`), so no deviation is discarded and no claim is made about an expectation
that is undefined. -/
def IsRatioRPCEquilibriumVal (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → NoisePath N d)
    (Y : Ω → NoisePath N e) (φ : Fin N → ℝ → (Fin d → ℝ) → ℝ) (C : Fin N → ℝ → ℝ)
    (R : ℝ → NoisePath N e → ℝ) (β : Ω → ℝ) (â : Fin N → Ω → ℝ) (v : ℝ) : Prop :=
  IsCtrlTilde X Y â ∧ ExpEq μ (ratioPayoff μ X Y φ C R β â â) v ∧
    ∀ a : Fin N → Ω → ℝ, IsCtrlTilde X Y a → ExpLE μ (ratioPayoff μ X Y φ C R β a â) v

/-- **Optimal RPC (ratio-based)**, SSRN 3742584 (Nov. 13, 2022), Definition 3.3, p.14: the
ratio-based RPC with weight `β` is optimal if some equilibrium `â ∈ 𝒜̃` w.r.t. it has
`F(â, â; f) = V`, where `V` is the centralized value (3.4). -/
def IsOptimalRatioRPC (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → NoisePath N d)
    (Y : Ω → NoisePath N e) (φ : Fin N → ℝ → (Fin d → ℝ) → ℝ) (C : Fin N → ℝ → ℝ)
    (R : ℝ → NoisePath N e → ℝ) (β : Ω → ℝ) (V : ℝ) : Prop :=
  ∃ â : Fin N → Ω → ℝ, IsRatioRPCEquilibriumVal μ X Y φ C R β â V

end RelPerfMFG


