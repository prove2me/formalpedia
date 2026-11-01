-- Prove2me | Definitions.Def_RandomRateMSQ_StandingData
-- name    : RandomRateMSQ_StandingData
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:24:31.089434+00:00
-- url     : https://prove2.me/theorems/265dfa88-9aba-45a1-8a61-7d821e8d5a63
-- title:
--   Data of the random-rate many-server model: $\bar\mu$, $\mathrm{var}(\tilde\mu)$, $\mathrm{var}(u)$, the corrected noise coefficient, $\langle\!\langle\iota,\nu\rangle\!\rangle$, Assumption 1
-- statement:
--   The fixed data of the model of Büke and Qin. The interarrival law $F_u$ is a probability measure on $\mathbb R$, concentrated on $[0,\infty)$, with mean $1$ and finite second moment; write $\mathrm{var}\,u=\int u^2\,dF_u-1$. The rate law $F$ is a probability measure on $\mathbb R_+$ with no atom at $0$ and finite second moment; write
--
--   $$
--   \bar\mu=\int\mu\,dF(\mu),\qquad \mathrm{var}(\tilde\mu)=\int\mu^2\,dF(\mu)-\bar\mu^2 .
--   $$
--
--   For a probability measure $\nu$ on $\mathbb R_+$, $\langle\!\langle\iota,\nu\rangle\!\rangle=\int\mu\,d\nu(\mu)\in[0,\infty]$ is its mean. The cumulative integral of a path $f$ on $[0,\infty)$ is $\int_0^t f(s)\,ds$. The diffusion coefficient of the limit equation is
--
--   $$
--   \sqrt{\bar\mu\,(1+\mathrm{var}\,u)} .
--   $$
--
--   **Assumption 1.** With arrival rates $\lambda_n$, $n^{-1/2}(\lambda_n-n\bar\mu)\to\hat\lambda\in\mathbb R$ as $n\to\infty$.
--
--   These are the parameters of every statement of the mission.
--
--   **Formalization Note** The paper prints the coefficient $\bar\mu\sqrt{c_a^2+1}$ with $c_a^2=\mathrm{var}(u)/\bar\mu^2$; that constant is false (with all rates equal to $2$ and Poisson arrivals the system is Erlang-A, whose Halfin–Whitt limit has coefficient $\sqrt{2\mu}=2$, against the printed $\sqrt5$). The mean is a lower Lebesgue integral in $[0,\infty]$, so an infinite mean is never a junk $0$.
-- source:
--   Büke and Qin, Many-Server Queues with Random Service Rates in the Halfin-Whitt Regime, arXiv:1905.04198v1, §3, pp.5 and 17 (Assumption 1, p.5; Theorem 5, p.17; ⟨⟨ι, ζ⟩⟩, p.3)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace RandomRateMSQ

/-- The cumulative integral `∫₀ᵗ f(s) ds` of a path `f : ℝ≥0 → ℝ` (Büke–Qin, arXiv:1905.04198v1,
§3, pp.5–19, used in every integral of the model).

**Formalization Note.** Time is `ℝ≥0`; the integral is the interval integral over `[0, t] ⊂ ℝ`
of `s ↦ f (max s 0)`. It is the Bochner integral, so it is `0` when `f` is not integrable on
`[0, t]`; every path it is applied to in this mission is càdlàg (hence bounded and measurable on
`[0, t]`) or is required to be measurable and locally bounded. -/
noncomputable def cumInt (f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  ∫ s in (0 : ℝ)..(t : ℝ), f (Real.toNNReal s)

/-- The mean service rate `µ̄ = E[µ̃] = ∫ µ dF(µ)` of the rate law `F` (arXiv:1905.04198v1, p.5:
"We assume that µ̄ = E[µ̃ⁿₖ]"). -/
noncomputable def muBar (F : Measure ℝ≥0) : ℝ := ∫ x, (x : ℝ) ∂F

/-- The variance `var(µ̃) = ∫ µ² dF − µ̄²` of the rate law `F` (arXiv:1905.04198v1, Theorem 5,
p.17: "σ̃ is distributed normally with mean 0 and variance var(µ̃)"). -/
noncomputable def varMu (F : Measure ℝ≥0) : ℝ := ∫ x, (x : ℝ) ^ 2 ∂F - muBar F ^ 2

/-- The variance `var u = ∫ u² dF_u − 1` of the interarrival law `F_u`, which has mean `1`
(arXiv:1905.04198v1, p.5: "uⁿₖs are i.i.d. random variables with mean 1"; Theorem 5, p.17:
"c²ₐ := var(uⁿₖ)/µ̄²"). -/
noncomputable def varU (Fu : Measure ℝ) : ℝ := ∫ x, x ^ 2 ∂Fu - 1

/-- The diffusion coefficient of the limit equation (3.7), **corrected**:
`√(µ̄ (1 + var u))` (arXiv:1905.04198v1, Theorem 5, p.17, which prints `µ̄ √(c²ₐ + 1)` with
`c²ₐ = var(u)/µ̄²`).

**Formalization Note (correction).** The printed constant is false. With every rate equal to `2`
and Poisson arrivals (`var u = 1`) the system is the Erlang-A queue, whose Halfin–Whitt limit has
diffusion coefficient `√(2µ) = 2` (Garnett–Mandelbaum–Reiman 2002), while the printed formula
gives `√5`. The paper's own computations on p.18 give `⟨M̂ⁿ₁⟩ₜ → µ̄ t` (so `√µ̄ W₂`) and the renewal
FCLT gives `Âⁿ ⇒ √(µ̄ var u) W₁`, independent; their sum has coefficient `√(µ̄(1 + var u))`. -/
noncomputable def noiseCoeff (mubar vu : ℝ) : ℝ := Real.sqrt (mubar * (1 + vu))

/-- The mean `⟨⟨ι, ν⟩⟩ = ∫ µ dν(µ)` of a probability measure `ν` on `ℝ₊` (arXiv:1905.04198v1,
§1.1, p.3: "the expected value of a random variable following the distribution ζ ∈ P can be
denoted as ⟨⟨ι, ζ⟩⟩").

**Formalization Note.** Computed as a lower Lebesgue integral in `[0, ∞]`, so an infinite mean is
`∞`, never a junk `0`. -/
noncomputable def meanRate (ν : ProbabilityMeasure ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ x, (x : ℝ≥0∞) ∂(ν : Measure ℝ≥0)

/-- The **standing assumptions on the data** (arXiv:1905.04198v1, §3, p.5):
1. the interarrival law `F_u` is a probability measure on `ℝ`, concentrated on `[0, ∞)`, with
   mean `1` and finite second moment ("uⁿₖs are i.i.d. random variables with mean 1"; its
   variance enters Theorem 5 through `c²ₐ`);
2. the rate law `F` is a probability measure on `ℝ₊` with no atom at `0` (the rates are
   "positive i.i.d. random variables with a general distribution F(µ)") and finite second moment
   ("E[(µ̃ⁿₖ)²] < ∞").

**Formalization Note.** One law `F_u` and one law `F` serve every system `n` (the paper's
`var(uⁿₖ)` and `F(µ)` carry no `n`). -/
def StandingData (Fu : Measure ℝ) (F : Measure ℝ≥0) : Prop :=
  IsProbabilityMeasure Fu ∧ Fu (Set.Iio 0) = 0 ∧ Integrable (fun x : ℝ => x ^ 2) Fu ∧
    ∫ x, x ∂Fu = 1 ∧
  IsProbabilityMeasure F ∧ F {0} = 0 ∧ Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 2) F

/-- **Assumption 1** (arXiv:1905.04198v1, p.5): "As n → ∞, n^{−1/2}(λₙ − nµ̄) → λ̂, where
λ̂ ∈ ℝ." -/
def Assumption1 (F : Measure ℝ≥0) (lam : ℕ → ℝ) (lamHat : ℝ) : Prop :=
  Tendsto (fun n : ℕ => (lam n - n * muBar F) / Real.sqrt n) atTop (𝓝 lamHat)

end RandomRateMSQ


