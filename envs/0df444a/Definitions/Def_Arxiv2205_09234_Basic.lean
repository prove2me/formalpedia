-- Prove2me | Definitions.Def_Arxiv2205_09234_Basic
-- name    : Arxiv2205_09234_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T15:42:17.191373+00:00
-- url     : https://prove2.me/theorems/3e690754-c21e-4dc0-88df-09dd4cffdc6b
-- title:
--   Fourier-based metric $\mathcal L_{p,\alpha}$, DFT matrix and weight $\mathrm W_\alpha$ of $\omega$-FWI
-- statement:
--   Objects of Section 2.1 of Izzatullah and Alkhalifah (2022).
--
--   1. **Fourier transform.** For a waveform $d:\mathbb{R}\to\mathbb{R}$, $\hat d(\omega)=\int_{\mathbb{R}}d(t)\,e^{-i\omega t}\,dt$, where $\omega$ is the angular frequency.
--   2. **Fourier-based metric (eq. 1).** For real $p,\alpha$ and a modelled trace $d_m$ and an observed trace $d_o$,
--   $$\mathcal L_{p,\alpha}(d_m,d_o)=\Big(\int_{\mathbb{R}}|\omega|^\alpha\,|\hat d_m(\omega)-\hat d_o(\omega)|^p\,d\omega\Big)^{1/p}.$$
--   3. **DFT matrix.** For $N=N_t$ samples, $\Omega\in\mathbb{C}^{N\times N}$, $\Omega_{kj}=e^{-2\pi ikj/N}$ (unnormalised), and $\hat{\mathbf d}=\Omega\mathbf d$ for a sampled trace $\mathbf d\in\mathbb{R}^N$.
--   4. **Sample frequencies.** For time step $\Delta t$, $\omega_k=2\pi k/(N\Delta t)$ if $2k<N$ and $\omega_k=2\pi(k-N)/(N\Delta t)$ otherwise, $k=0,\dots,N-1$.
--   5. **Weight matrix.** $\mathrm W_\alpha=\operatorname{diag}(w)$, where $w_k\ge0$ for all $k$ and $w_k=|\omega_k|^\alpha$ whenever $\omega_k\ne0$ or $\alpha\ge0$ (with $0^0=1$). For $\alpha<0$ the zero-frequency entry $w_0$ is left as an arbitrary nonnegative number, because the paper does not say how the infinite value $|0|^\alpha$ is replaced.
--   6. **Discrete metric.** $\mathcal L_{p,\alpha}(\mathbf d_m,\mathbf d_o)=\big(\sum_k w_k|\hat{\mathbf d}_{m,k}-\hat{\mathbf d}_{o,k}|^p\big)^{1/p}$, the integral of eq. (1) replaced by the sum over the DFT frequencies, as in eq. (2).
--
--   **Formalization Note** The paper's display integrates over $\mathbb{R}^{N_t}$; it is read as an integral over the time axis $\mathbb{R}$. The DFT normalisation, the quadrature factor between the integral of eq. (1) and the sum of eq. (2), and the zero-frequency weight for $\alpha<0$ are not stated in the paper; the choices above are recorded in the mission description.
-- source:
--   Izzatullah and Alkhalifah, omega-FWI: Robust full-waveform inversion with Fourier-based metric, arXiv:2205.09234v1 (2022), Section 2.1, eqs. (1)-(2), PDF p. 2

import Mathlib

/-!
Izzatullah and Alkhalifah, *ω-FWI: Robust full-waveform inversion with Fourier-based metric*,
arXiv:2205.09234v1 (2022): the angular-frequency Fourier transform and the Fourier-based metric
`L_{p,α}` of Section 2.1 (eq. (1)), and its discrete form on sampled traces with the DFT matrix
`Ω`, the sample frequencies `ω` and the weight matrix `W_α = diag(|ω|^α)` (eq. (2)).
-/

open MeasureTheory

noncomputable section

namespace Arxiv2205_09234

/-- Section 2.1, display before eq. (1), p. 2: the Fourier transform of a waveform `d(t)` in the
angular frequency `ω`, `d̂(ω) = ∫ d(t) exp(-i ω t) dt` (the time axis is the real line). -/
def angFourier (d : ℝ → ℝ) (ω : ℝ) : ℂ :=
  ∫ t : ℝ, (d t : ℂ) * Complex.exp (-(Complex.I * ((ω * t : ℝ) : ℂ)))

/-- Section 2.1, eq. (1), p. 2: the Fourier-based metric
`L_{p,α}(d_m, d_o) = (∫ |ω|^α |d̂_m(ω) - d̂_o(ω)|^p dω)^{1/p}` of a modelled trace `d_m` and an
observed trace `d_o`. -/
def fourierMetric (p α : ℝ) (dm dobs : ℝ → ℝ) : ℝ :=
  (∫ ω : ℝ, |ω| ^ α * ‖angFourier dm ω - angFourier dobs ω‖ ^ p) ^ (1 / p)

/-- Section 2.1, eq. (2), p. 2: the Discrete Fourier Transform matrix `Ω` of size `N = N_t`
(unnormalised), `Ω_{kj} = exp(-2π i k j / N)`. -/
def dftMat (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun k j => Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (j : ℂ) / (N : ℂ)))

/-- Section 2.1, eq. (2), p. 2: the DFT `d̂ = Ω d` of a sampled real trace `d ∈ ℝ^{N_t}`. -/
def dft (N : ℕ) (d : Fin N → ℝ) : Fin N → ℂ :=
  (dftMat N).mulVec (fun j => (d j : ℂ))

/-- Section 2.1, eq. (2), p. 2: the vector `ω` of the waveform's sample (angular) frequencies for
`N` samples at time step `dt`: `ω_k = 2πk/(N dt)` if `2k < N` and `ω_k = 2π(k - N)/(N dt)`
otherwise (the frequency ordering of the DFT). -/
def sampleFreq (N : ℕ) (dt : ℝ) (k : Fin N) : ℝ :=
  2 * Real.pi * (if 2 * (k : ℕ) < N then (k : ℝ) else (k : ℝ) - N) / (N * dt)

/-- Section 2.1, eq. (2), p. 2: `w` is the diagonal of `W_α = diag(|ω|^α)`. Every entry is
nonnegative and equals `|ω_k|^α` wherever this is a real number. The paper does not say what
`W_α` contains at the zero frequency when `α < 0` (where `|0|^α` is infinite), so that entry is
any nonnegative real number. -/
def IsFreqWeight (N : ℕ) (dt α : ℝ) (w : Fin N → ℝ) : Prop :=
  (∀ k, 0 ≤ w k) ∧ ∀ k, (sampleFreq N dt k ≠ 0 ∨ 0 ≤ α) → w k = |sampleFreq N dt k| ^ α

/-- Section 2.1, eq. (2), p. 2: the weight matrix `W_α = diag(w)` as a complex matrix. -/
def weightMat {N : ℕ} (w : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun k => (w k : ℂ))

/-- Section 2.1, eqs. (1)-(2), p. 2: the Fourier-based metric of eq. (1) on sampled traces, with the
integral over `ω` replaced by the sum over the DFT frequencies as in eq. (2):
`L_{p,α}(d_m, d_o) = (∑_k w_k |d̂_{m,k} - d̂_{o,k}|^p)^{1/p}`, where `w` is the diagonal of `W_α`. -/
def discreteMetric (N : ℕ) (p : ℝ) (w : Fin N → ℝ) (dm dobs : Fin N → ℝ) : ℝ :=
  (∑ k, w k * ‖dft N dm k - dft N dobs k‖ ^ p) ^ (1 / p)

end Arxiv2205_09234


