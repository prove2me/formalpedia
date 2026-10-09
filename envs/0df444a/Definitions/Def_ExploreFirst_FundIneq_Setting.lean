-- Prove2me | Definitions.Def_ExploreFirst_FundIneq_Setting
-- name    : ExploreFirst_FundIneq_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:04.596535+00:00
-- url     : https://prove2.me/theorems/79fca2e7-f899-4b0c-b729-0e54d969f849
-- title:
--   §1.1–§2, pp. 3–6 — the Bernoulli law, the binary divergence kl of (5) in [0, ∞], and expected pull counts
-- statement:
--   This file fixes the three objects that the fundamental inequality (6) of Garivier, Ménard and Stoltz is written in, on top of the canonical stochastic bandit model (the published definitions `StochasticBandit` and `BanditPolicy`).
--
--   1. **Bernoulli law.** For a real number $p$, $\mathcal B(p)$ is the measure on $\mathbb R$ putting mass $p$ at $1$ and mass $1-p$ at $0$. It is a probability measure whenever $p\in[0,1]$, which is the only case used.
--
--   2. **Binary Kullback–Leibler divergence.** For $p,q\in[0,1]$,
--   $$
--   \mathrm{kl}(p,q)=\mathrm{KL}\big(\mathcal B(p),\mathcal B(q)\big)\in[0,+\infty].
--   $$
--   For $q\in(0,1)$ this is the formula (5) of the paper, $\mathrm{kl}(p,q)=p\ln\frac pq+(1-p)\ln\frac{1-p}{1-q}$, with $0\ln 0=0$; for $q\in\{0,1\}$ and $p\neq q$ it is $+\infty$, the limiting value of (5); and $\mathrm{kl}(p,p)=0$.
--
--   3. **Expected number of draws.** For a $K$-armed bandit problem $\underline\nu=(\nu_a)_{a}$, a strategy $\psi$, a horizon $T\in\mathbb N$ and an arm $a$,
--   $$
--   \mathbb E_{\underline\nu}\big[N_{\psi,a}(T)\big]=\int N_{\psi,a}(T)\,\mathrm d\mathbb P_{\underline\nu},
--   $$
--   where $N_{\psi,a}(T)=\sum_{t=1}^T\mathbb I\{A_t=a\}$ counts the rounds among the first $T$ in which arm $a$ is pulled and $\mathbb P_{\underline\nu}$ is the law of the history $(A_1,Y_1,\dots,A_T,Y_T)$ when $\psi$ interacts with $\underline\nu$.
--
--   These are the binary divergence and the weights of the fundamental inequality (6), the tool from which every lower bound of the paper is derived.
--
--   **Formalization Note.** The binary divergence takes values in $[0,+\infty]$ and is defined as a Kullback–Leibler divergence of two measures, rather than by the real formula (5), so that it is $+\infty$ exactly where the paper's convention makes it so; a real formula would return a finite junk value at $q\in\{0,1\}$. Arms are indexed by $\{0,\dots,K-1\}$ instead of $\{1,\dots,K\}$. Strategies are the Markov-kernel policies of the published `BanditPolicy` (the arm in round $t+1$ is drawn from a kernel applied to the observed history), which generate the same joint laws of arms and rewards as the paper's strategies with auxiliary uniform randomisation. The pull count is integrated as a real-valued function bounded by $T$, hence integrable.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, pp. 2–3, §1.1 (N_{ψ,a}(T)); p. 6, §2, (5)

import Mathlib
import Definitions.Def_BanditPolicy

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace ExploreFirst.FundIneq

/-- The Bernoulli law of parameter `p` as a measure on `ℝ`: mass `p` at `1` and mass `1 - p` at `0`
(Garivier, Ménard, Stoltz, arXiv:1602.07182v3, §2, p. 6, the distributions underlying (5)).
It is a probability measure for `p ∈ [0, 1]`; every use below has `p ∈ [0, 1]`. -/
noncomputable def bernoulliLaw (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac 1 + ENNReal.ofReal (1 - p) • Measure.dirac 0

/-- The Bernoulli Kullback–Leibler divergence `kl(p, q)` of (5), p. 6, valued in `[0, ∞]`:
the Kullback–Leibler divergence between the Bernoulli laws of parameters `p` and `q`.
For `p ∈ [0, 1]`, `q ∈ (0, 1)` it equals `p ln(p/q) + (1 - p) ln((1 - p)/(1 - q))` with `0 ln 0 = 0`;
for `q ∈ {0, 1}` and `p ≠ q` it is `+∞`, the limit value of (5). -/
noncomputable def klBer (p q : ℝ) : ℝ≥0∞ :=
  klDiv (bernoulliLaw p) (bernoulliLaw q)

/-- The expected number of pulls `𝔼_ν[N_{ψ,a}(T)]` of arm `a` up to round `T` (§1.1, p. 3), when the
strategy `π` interacts with the bandit problem `ν`, under the canonical bandit measure on histories of
length `T`. The integrand is bounded by `T`, hence integrable. -/
noncomputable def expPulls {K : ℕ} (ν : BanditAlgorithm.StochasticBandit K)
    (π : BanditAlgorithm.BanditPolicy K) (T : ℕ) (a : Fin K) : ℝ :=
  ∫ h, (BanditAlgorithm.armPullCount a h : ℝ) ∂(BanditAlgorithm.banditMeasure ν π T)

end ExploreFirst.FundIneq


