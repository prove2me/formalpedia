-- Prove2me | Definitions.Def_You2015_Shared_Basis
-- name    : You2015_Shared_Basis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T01:31:06.783382+00:00
-- url     : https://prove2.me/theorems/8ca865c3-0dd5-4ea2-82bd-ce8ae5e92434
-- title:
--   The stochastic basis of (2.1): filtration under the usual conditions, 𝓕-Brownian motion w, right-continuous 𝓕-Markov chain r with generator Γ, independent of w
-- statement:
--   This file fixes the probabilistic setting of Section 2 of the paper. Time runs over $\mathbb R_+=[0,\infty)$.
--
--   1. **Usual conditions.** A filtration $\{\mathcal F_t\}_{t\ge0}$ on a probability space $(\Omega,\mathcal F,\mathbb P)$ satisfies the usual conditions when it is increasing, right-continuous,
--   $$\mathcal F_t=\bigcap_{s>t}\mathcal F_s\qquad(t\ge0),$$
--   and $\mathcal F_0$ contains every $\mathbb P$-null set. Since $\mathcal F_0\subseteq\mathcal F$, this also makes the probability space complete.
--
--   2. **$\{\mathcal F_t\}$-Brownian motion.** $w(t)=(w_1(t),\dots,w_m(t))^T$ is an $m$-dimensional $\{\mathcal F_t\}$-Brownian motion when every coordinate $w_k$ is a standard real Brownian motion ($w_k(0)=0$ a.s., independent Gaussian increments with variance equal to the elapsed time, a.s. continuous paths), the $m$ coordinate processes are mutually independent, $w(t)$ is $\mathcal F_t$-measurable, and every increment $w(s+t)-w(s)$ is independent of $\mathcal F_s$.
--
--   3. **Generator.** $\Gamma=(\gamma_{ij})_{N\times N}$ is a generator on $S=\{1,\dots,N\}$ when $\gamma_{ij}\ge0$ for $i\ne j$ and $\gamma_{ii}=-\sum_{j\ne i}\gamma_{ij}$.
--
--   4. **$\{\mathcal F_t\}$-Markov chain with generator $\Gamma$.** $r(t)$, $t\ge0$, with values in $S$, is a right-continuous $\{\mathcal F_t\}$-Markov chain with generator $\Gamma$ when every path is right-continuous (for a finite state space: constant on some interval $[t,t+\varepsilon)$ after every $t$), $r(t)$ is $\mathcal F_t$-measurable, and for all $s,t\ge0$ and $j\in S$,
--   $$\mathbb P\{r(s+t)=j\mid\mathcal F_s\}=\big(e^{t\Gamma}\big)_{r(s),\,j}\quad\text{a.s.}$$
--
--   5. **Hybrid setup.** The stochastic basis of the controlled system (2.1) consists of a filtration under the usual conditions, an $m$-dimensional $\{\mathcal F_t\}$-Brownian motion $w$ and a right-continuous $\{\mathcal F_t\}$-Markov chain $r$ with generator $\Gamma$ and $r(0)=r_0$ a.s., such that the chain $r(\cdot)$ is independent of the Brownian motion $w(\cdot)$ (as random paths).
--
--   These objects are the standard framework of hybrid stochastic differential equations (SDEs with Markovian switching) and are reusable by any mission on such systems.
--
--   Used by both missions of this paper: 01-asymptotic-stability (Theorem 3.4 series; p. 907, Section 2) and 02-exponential-stability (Theorem 4.2 series; p. 907, Section 2).
--
--   **Formalization Note** Modes are `Fin N`, so $S$ is $\{0,\dots,N-1\}$ in Lean. The paper says "an $m$-dimensional Brownian motion defined on the probability space" and a Markov chain "with generator $\Gamma$ given by $\mathbb P\{r(t+\Delta)=j\mid r(t)=i\}=\gamma_{ij}\Delta+o(\Delta)$"; we read these, as in the framework of Mao–Yuan (the paper's reference [23], cited for existence and for the Itô formula), as a Brownian motion and a Markov chain relative to $\{\mathcal F_t\}$, the chain being time-homogeneous with transition matrix $P(t)=e^{t\Gamma}$ (equivalently $P(\Delta)=I+\Gamma\Delta+o(\Delta)$). The time-$0$ state is fixed almost surely. Right-continuity of the filtration is written as the equality with the infimum of the σ-algebras $\mathcal F_s$, $s>t$.
-- source:
--   You, Liu, Lu, Mao, Qiu, Stabilization of Hybrid Systems by Feedback Control Based on Discrete-Time State Observations, SIAM J. Control Optim. 53(2), 2015, https://doi.org/10.1137/140985779, p. 907, Section 2 (usual conditions, Brownian motion w, Markov chain r with generator Γ, independence of r and w)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace You2015.Shared

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The **usual conditions** on a filtration `{𝓕_t}_{t ≥ 0}` of `(Ω, 𝓕, P)`: the filtration is
increasing (built into `Filtration`), right-continuous, `𝓕_t = ⋂_{s > t} 𝓕_s` for every `t ≥ 0`
(the infimum of σ-algebras), and `𝓕_0` contains every `P`-null set. Because `𝓕_0 ⊆ 𝓕`, the
second clause also makes `(Ω, 𝓕, P)` complete. -/
def UsualConditions (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) : Prop :=
  (∀ t : ℝ≥0, 𝓕 t = ⨅ s ∈ Set.Ioi t, 𝓕 s) ∧
    ∀ A : Set Ω, P A = 0 → MeasurableSet[𝓕 0] A

/-- `w = (w_1, …, w_m)ᵀ` is an `m`-dimensional `{𝓕_t}`-Brownian motion: each coordinate is a
standard real Brownian motion (Mathlib's `IsBrownianReal`: Gaussian increments with variance
the elapsed time, independent increments, `w(0) = 0` a.s., a.s. continuous paths), the `m`
coordinate processes are mutually independent, `w(t)` is `𝓕_t`-measurable for each `t`, and
every increment `w(s + t) − w(s)` is independent of `𝓕_s`. -/
structure IsFBrownian {m : ℕ} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (w : ℝ≥0 → Ω → (Fin m → ℝ)) : Prop where
  brownian : ∀ k : Fin m, IsBrownianReal (fun t ω => w t ω k) P
  indep_coord : iIndepFun (fun (k : Fin m) (ω : Ω) (t : ℝ≥0) => w t ω k) P
  adapted : ∀ t : ℝ≥0, Measurable[𝓕 t] (w t)
  indep_incr : ∀ s t : ℝ≥0,
    Indep (MeasurableSpace.comap (fun ω => w (s + t) ω - w s ω) inferInstance) (𝓕 s) P

/-- `Γ = (γ_ij)_{N × N}` is a generator (Q-matrix) on `S = {0, …, N − 1}`: the off-diagonal
transition rates are nonnegative and `γ_ii = −∑_{j ≠ i} γ_ij` (zero row sums). -/
def IsGenerator {N : ℕ} (Γ : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  (∀ i j, i ≠ j → 0 ≤ Γ i j) ∧ ∀ i, Γ i i = -∑ j ∈ Finset.univ.erase i, Γ i j

/-- `r` is a right-continuous `{𝓕_t}`-Markov chain on `S = Fin N` with generator `Γ`:
every path is right-continuous (for a finite state space: constant on some `[t, t + ε)`),
`r(t)` is `𝓕_t`-measurable, and for all `s, t ≥ 0` and every state `j`,
`P(r(s + t) = j | 𝓕_s) = (e^{tΓ})_{r(s), j}` almost surely (time-homogeneous transition matrix
`P(t) = e^{tΓ}`, i.e. `P(Δ) = I + ΓΔ + o(Δ)`). -/
structure IsFMarkovChain {N : ℕ} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (Γ : Matrix (Fin N) (Fin N) ℝ) (r : ℝ≥0 → Ω → Fin N) : Prop where
  right_cont : ∀ ω t, ∃ ε > 0, ∀ s, t ≤ s → s < t + ε → r s ω = r t ω
  adapted : ∀ t : ℝ≥0, Measurable[𝓕 t] (r t)
  markov : ∀ s t : ℝ≥0, ∀ j : Fin N,
    P[(fun ω => if r (s + t) ω = j then (1 : ℝ) else 0) | 𝓕 s]
      =ᵐ[P] fun ω => NormedSpace.exp ((t : ℝ) • Γ) (r s ω) j

/-- The stochastic basis of the controlled hybrid SDE (2.1): a filtration `{𝓕_t}` satisfying
the usual conditions, an `m`-dimensional `{𝓕_t}`-Brownian motion `w`, and a right-continuous
`{𝓕_t}`-Markov chain `r` on `Fin N` with generator `Γ`, started at `r(0) = r₀` (a.s.), with the
chain `r(·)` independent of the Brownian motion `w(·)` (as path-valued random variables). -/
structure HybridSetup (P : Measure Ω) (m N : ℕ) (Γ : Matrix (Fin N) (Fin N) ℝ)
    (r₀ : Fin N) where
  𝓕 : Filtration ℝ≥0 mΩ
  w : ℝ≥0 → Ω → (Fin m → ℝ)
  r : ℝ≥0 → Ω → Fin N
  usual : UsualConditions P 𝓕
  brownian : IsFBrownian P 𝓕 w
  markov : IsFMarkovChain P 𝓕 Γ r
  init : ∀ᵐ ω ∂P, r 0 ω = r₀
  indep : IndepFun (fun ω t => r t ω) (fun ω t => w t ω) P

end You2015.Shared


