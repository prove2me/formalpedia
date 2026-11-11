-- Prove2me | Definitions.Def_TensorPCAGlauber_OddK_Glauber
-- name    : TensorPCAGlauber_OddK_Glauber
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:53:30.49135+00:00
-- url     : https://prove2.me/theorems/011ab3f8-81de-498c-897f-9fdb27f76888
-- title:
--   Continuous-time Glauber dynamics on $\{\pm1\}^N$ as a path built from a rate-$N$ Poisson clock (Algorithm 3, §3.3), its generator, Dynkin martingale, ergodic averages and hitting times
-- statement:
--   Given a Hamiltonian $V:\Omega_N\to\mathbb R$, an inverse temperature $\beta\ge0$ and $X_0\in\Omega_N$, continuous-time Glauber dynamics (Algorithm 3) is driven by i.i.d. triples $(E_n,I_n,U_n)$ with $E_n\sim\mathrm{Exp}(N)$, $I_n\sim\mathrm{Uniform}([N])$, $U_n\sim\mathrm{Uniform}[0,1]$. The arrival times are $T_n=E_0+\dots+E_{n-1}$ (a rate-$N$ Poisson process). At the $n$-th arrival the site $I$ is resampled from the heat-bath kernel
--   $$q(+1\mid i,x)=\frac{e^{\beta V(x_{\neg i},x_i=+1)}}{\sum_{b\in\{\pm1\}}e^{\beta V(x_{\neg i},x_i=b)}}=\tfrac12\big(1+\tanh(\beta\,\partial_iV(x))\big),$$
--   the new spin being $+1$ iff $U\le q(+1\mid I,X_{T_n-})$; other coordinates are unchanged, and the path $(X_t)_{t\ge0}$ is constant between arrivals and right-continuous. The generator is $L_{V,\beta}f(x)=\sum_ic_i(x)[f(x^{\sim i})-f(x)]$ with flip rates $c_i(x)=\frac12[1-x_i\tanh(\beta\partial_iV(x))]$ (eq. (13)); the Dynkin martingale of $f$ is $M^f_t=f(X_t)-f(X_0)-\int_0^tL_{V,\beta}f(X_s)\,ds$ (Lemma 3.9). The ergodic average is $\bar X_T=T^{-1}\int_0^TX_t\,dt$ and the ergodic second moment $\bar\Sigma_T=T^{-1}\int_0^TX_tX_t^\top dt$; the hitting time of level $a$ by an observable $g$ is $\inf\{t\ge0:g(X_t)\ge a\}\in[0,\infty]$.
--
--   **Formalization Note.** The noise space is `ℕ → ℝ × Fin N × ℝ` with `Measure.infinitePi` of `expMeasure N ⊗ uniformOn univ ⊗ volume|[0,1]`. Arrival epochs and the counting process $N_t=\#\{n\ge1:T_n\le t\}$ are the published `QueueingFundamentals.Foundations.arrivalTime` / `countingProcess` (the latter is `Set.ncard`, $0$ on the null event of infinitely many arrivals). The path is `glauberState` evaluated at $N_t$. Hitting times are `ENNReal`-valued, so a level never reached gives $\infty$, not $0$.
-- source:
--   Das & Schramm, Averaged Annealed Markov Chains Achieve the Algorithmic Threshold for Tensor PCA, Part I: Glauber Dynamics, arXiv:2610.16705 (PDF of 2026-11-03, sha256 b1d9d241…), pp. 18–20 (PDF 21–23), §3.3, Algorithm 3, eq. (13), Lemma 3.9; p. 30 (PDF 33), eq. (30)

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_ArrivalProcess
import Definitions.Def_TensorPCAGlauber_OddK_Hypercube

open MeasureTheory ProbabilityTheory

namespace TensorPCAGlauber.OddK

/-- The driving noise of continuous-time Glauber dynamics on `Ω_N` (Algorithm 3, §3.3): a sequence
of triples `(E_n, I_n, U_n)`, `n = 0, 1, 2, …`, where `E_n` is the `n`-th interarrival time of the
rate-`N` Poisson clock, `I_n ∈ [N]` the site updated at the `(n+1)`-st arrival, and `U_n ∈ [0,1]` the
uniform mark with which the new spin is drawn. -/
abbrev Noise (N : ℕ) := ℕ → ℝ × Fin N × ℝ

/-- The law of one triple: `E ∼ Exp(N)`, `I ∼ Uniform([N])`, `U ∼ Uniform[0,1]`, independent. -/
noncomputable def markLaw (N : ℕ) : Measure (ℝ × Fin N × ℝ) :=
  (expMeasure (N : ℝ)).prod ((uniformOn (Set.univ : Set (Fin N))).prod
    (volume.restrict (Set.Icc (0 : ℝ) 1)))

/-- The law of the driving noise: the triples are i.i.d. with law `markLaw N`. -/
noncomputable def noiseMeasure (N : ℕ) : Measure (Noise N) :=
  Measure.infinitePi fun _ : ℕ => markLaw N

instance (N : ℕ) : IsFiniteMeasure (noiseMeasure N) := by
  by_cases h : ∀ _ : ℕ, IsProbabilityMeasure (markLaw N)
  · have : ∀ i : ℕ, IsProbabilityMeasure ((fun _ : ℕ => markLaw N) i) := h
    unfold noiseMeasure
    infer_instance
  · unfold noiseMeasure Measure.infinitePi
    rw [dif_neg h]
    infer_instance

/-- The interarrival times `E_n(ω)` of the driving noise. -/
def interarrival {N : ℕ} (n : ℕ) (ω : Noise N) : ℝ := (ω n).1

/-- The heat-bath probability of the spin `+1` at site `i` (Algorithm 3, line 8):
`q(+1 | i, x) = exp(βV(x_{¬i}, x_i = +1)) / ∑_{b ∈ {±1}} exp(βV(x_{¬i}, x_i = b))`
`= ½(1 + tanh(β ∂_i V(x)))`. -/
noncomputable def heatBathPlus {N : ℕ} (V : Cube N → ℝ) (β : ℝ) (x : Cube N) (i : Fin N) : ℝ :=
  Real.exp (β * V (Function.update x i true)) /
    (Real.exp (β * V (Function.update x i true)) + Real.exp (β * V (Function.update x i false)))

/-- One Glauber update at site `i` with uniform mark `u`: the new spin `Z` is `+1` iff
`u ≤ q(+1 | i, x)` (so `P[Z = +1] = q(+1 | i, x)` for `u ∼ Uniform[0,1]`); the other coordinates
are unchanged. -/
noncomputable def glauberStep {N : ℕ} (V : Cube N → ℝ) (β : ℝ) (x : Cube N) (i : Fin N)
    (u : ℝ) : Cube N :=
  Function.update x i (decide (u ≤ heatBathPlus V β x i))

/-- The embedded jump chain: the state after the first `n` updates, started at `x₀`. -/
noncomputable def glauberState {N : ℕ} (V : Cube N → ℝ) (β : ℝ) (x₀ : Cube N) (ω : Noise N) :
    ℕ → Cube N
  | 0 => x₀
  | n + 1 => glauberStep V β (glauberState V β x₀ ω n) (ω n).2.1 (ω n).2.2

/-- The number of arrivals of the rate-`N` clock in `[0, t]`, `N_t = #{n ≥ 1 : T_n ≤ t}` with
`T_n = E_0 + ⋯ + E_{n−1}` (the published Poisson-clock definitions). -/
noncomputable def numArrivals {N : ℕ} (t : ℝ) (ω : Noise N) : ℕ :=
  QueueingFundamentals.Foundations.countingProcess interarrival t ω

/-- The `n`-th arrival time `T_n = E_0 + ⋯ + E_{n−1}`. -/
noncomputable def arrivalAt {N : ℕ} (n : ℕ) (ω : Noise N) : ℝ :=
  QueueingFundamentals.Foundations.arrivalTime interarrival n ω

/-- The trajectory of continuous-time Glauber dynamics (Algorithm 3) for the Hamiltonian `V` at
inverse temperature `β`, started at `X_0 = x₀`, as a deterministic function of the driving noise:
`X_t` is the state after the `N_t` updates made at the arrival times `T_1 ≤ ⋯ ≤ T_{N_t} ≤ t`. The
path is constant between arrivals and right-continuous; `X_t = x₀` for `t < T_1`. -/
noncomputable def glauberPath {N : ℕ} (V : Cube N → ℝ) (β : ℝ) (x₀ : Cube N) (ω : Noise N)
    (t : ℝ) : Cube N :=
  glauberState V β x₀ ω (numArrivals t ω)

/-- The flip rate of coordinate `i` (eq. (13)): `c_i(x) = ½[1 − x_i tanh(β ∂_i V(x))]`. -/
noncomputable def flipRate {N : ℕ} (V : Cube N → ℝ) (β : ℝ) (x : Cube N) (i : Fin N) : ℝ :=
  (1 - vec x i * Real.tanh (β * pderiv i V x)) / 2

/-- The generator of Glauber dynamics (eq. (13)): `L_{V,β} f(x) = ∑_i c_i(x)[f(x^{∼i}) − f(x)]`. -/
noncomputable def generator {N : ℕ} (V : Cube N → ℝ) (β : ℝ) (f : Cube N → ℝ) (x : Cube N) : ℝ :=
  ∑ i, flipRate V β x i * (f (flipAt x i) - f x)

/-- The Dynkin martingale (Lemma 3.9): `M^f_t = f(X_t) − f(X_0) − ∫_0^t L_{V,β} f(X_s) ds`. -/
noncomputable def dynkinMart {N : ℕ} (V : Cube N → ℝ) (β : ℝ) (f : Cube N → ℝ) (x₀ : Cube N)
    (ω : Noise N) (t : ℝ) : ℝ :=
  f (glauberPath V β x₀ ω t) - f x₀ - ∫ s in (0 : ℝ)..t, generator V β f (glauberPath V β x₀ ω s)

/-- The ergodic average (eq. (30), Algorithm 1 line 2): `X̄_T = T^{−1} ∫_0^T X_t dt ∈ ℝ^N`. -/
noncomputable def ergodicAvg {N : ℕ} (V : Cube N → ℝ) (β : ℝ) (x₀ : Cube N) (T : ℝ)
    (ω : Noise N) : Fin N → ℝ :=
  fun i => T⁻¹ * ∫ t in (0 : ℝ)..T, vec (glauberPath V β x₀ ω t) i

/-- The ergodic second moment (Theorem 5.1): `Σ̄_T = T^{−1} ∫_0^T X_t X_tᵀ dt`. -/
noncomputable def ergodicSecondMoment {N : ℕ} (V : Cube N → ℝ) (β : ℝ) (x₀ : Cube N) (T : ℝ)
    (ω : Noise N) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => T⁻¹ * ∫ t in (0 : ℝ)..T,
    vec (glauberPath V β x₀ ω t) i * vec (glauberPath V β x₀ ω t) j

/-- The hitting time `inf{t ≥ 0 : a ≤ g(X_t)}` of the level `a` by the observable `g` along the
Glauber path, in `[0, ∞]` (`= ∞` when the level is never reached). -/
noncomputable def hitTime {N : ℕ} (V : Cube N → ℝ) (β : ℝ) (x₀ : Cube N) (ω : Noise N)
    (g : Cube N → ℝ) (a : ℝ) : ENNReal :=
  ⨅ (t : NNReal) (_ : a ≤ g (glauberPath V β x₀ ω t)), (t : ENNReal)

end TensorPCAGlauber.OddK


