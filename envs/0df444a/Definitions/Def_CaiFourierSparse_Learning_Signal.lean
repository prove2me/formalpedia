-- Prove2me | Definitions.Def_CaiFourierSparse_Learning_Signal
-- name    : CaiFourierSparse_Learning_Signal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:11:19.378119+00:00
-- url     : https://prove2.me/theorems/1853d3c0-e2ef-4ce0-8ce1-87bb99011677
-- title:
--   Fourier-sparse signals, window energies and inner products, Fourier-series coefficients, noise, and probability conventions
-- statement:
--   A **$k$-Fourier-sparse signal** is $x(t)=\sum_{j<k}\alpha_j e^{2\pi i f_j t}$ with labelled terms $j\in\{0,\dots,k-1\}$, complex amplitudes $\alpha_j$ (zero allowed) and arbitrary real frequencies $f_j$ (repeated frequencies allowed) (`sparseSignal`); for a set $S$ of terms, $x_S=\sum_{j\in S}\alpha_je^{2\pi i f_jt}$ (`subSignal`). Its **Fourier support** $\operatorname{supp}(\hat x)$ is the set of frequencies whose total amplitude $\sum_{j:f_j=\xi}\alpha_j$ is nonzero (`specSupp`); the frequencies lie in the **bandlimit** $[-F,F]$ when $|f_j|\le F$ for all $j$.
--
--   The time window is $[-1,1]$. Energies are unnormalized integrals with values in $[0,\infty]$: $\|z\|^2_{[-1,1]}=\int_{-1}^1|z|^2$ (`wsq`), $\|z\|_2^2=\int_{\mathbb R}|z|^2$ (`lsq`), $\|z\|^2_{\mathbb R\setminus[-1,1]}$ (`osq`); a function that is not square integrable has energy $\infty$. $\|z\|_{[-1,1]}$ is the square root (`wnorm`). Inner products are linear in the first argument: $\langle z,w\rangle_{[-1,1]}=\int_{-1}^1 z\,\overline w$ (`winner`), $\langle z,w\rangle=\int_{\mathbb R}z\,\overline w$ (`linner`). The Fourier-series coefficient is $\hat z[n]=\frac1{\sqrt2}\int_{-1}^1 z(t)e^{-i\pi nt}\,dt$, eq. (6) (`fsc`), and the Fourier transform over $\mathbb R$ of an integrable $g$ is $\hat g(\xi)=\int g(t)e^{-2\pi i\xi t}\,dt$ (`ftR`).
--
--   **Noise** $\eta$ is any function whose restriction to the window is almost-everywhere measurable and has $\|\eta\|^2_{[-1,1]}<\infty$ (`IsNoise`); point queries read the function itself. $a=(1\pm c)b$ means $(1-c)b\le a\le(1+c)b$ (`ApproxEq`). "With probability at least $p$" means that some measurable event of probability at least $p$ is contained in the event (`ProbAtLeast`). The reading of "with high probability" for size parameter $n=kF/\varepsilon$ is: probability at least $1-(2+n)^{-a}$ when $n\ge n_0$ and at least $p_0$ otherwise (`whpBound`).
--
--   **Formalization Note.** Energies are lower Lebesgue integrals, so no bound holds vacuously because of a junk value $0$; the Fourier support excludes cancelling and zero amplitudes, as the paper's $\operatorname{supp}(\hat x)$ does.
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), §1 and §2, printed pp. 1, 6–7, eqs. (6)–(7) (PDF pp. 3, 8–9)

import Mathlib

namespace CaiFourierSparse.Learning

open MeasureTheory Complex
open scoped ENNReal

/-! # Fourier-sparse signals, window norms and inner products, Fourier-series coefficients,
noise, and probability conventions (Cai–Chen–Shao–Wang, §1, §2, eqs. (6)–(7))

A `k`-Fourier-sparse signal is `x(t) = ∑_{j<k} α_j e^{2π i f_j t}` with labelled terms
`j : Fin k`, complex amplitudes `α_j` (zero allowed) and arbitrary real frequencies `f_j`
(repeated frequencies allowed). Norms on the window `[-1,1]` are unnormalized integrals; they are
`ℝ≥0∞`-valued lower Lebesgue integrals, so a function that is not square integrable has norm `∞`
rather than a junk value. Inner products are linear in the first argument. -/

/-- The single exponential `e^{2π i f t}`. -/
noncomputable def expTerm (f t : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (f : ℂ) * (t : ℂ))

/-- The `k`-Fourier-sparse signal `x(t) = ∑_{j<k} α_j e^{2π i f_j t}`. -/
noncomputable def sparseSignal {k : ℕ} (α : Fin k → ℂ) (f : Fin k → ℝ) (t : ℝ) : ℂ :=
  ∑ j, α j * expTerm (f j) t

/-- The signal `x_S(t) = ∑_{j ∈ S} α_j e^{2π i f_j t}` of a set `S` of labelled terms
(a cluster of `x`). -/
noncomputable def subSignal {k : ℕ} (α : Fin k → ℂ) (f : Fin k → ℝ) (S : Finset (Fin k))
    (t : ℝ) : ℂ :=
  ∑ j ∈ S, α j * expTerm (f j) t

/-- The Fourier support `supp(x̂)` of `x`: the frequencies whose total amplitude
`∑_{j : f_j = ξ} α_j` is nonzero (so cancelling or zero amplitudes are not in the support). -/
def specSupp {k : ℕ} (α : Fin k → ℂ) (f : Fin k → ℝ) : Set ℝ :=
  {ξ | ∃ j, f j = ξ ∧ ∑ i ∈ Finset.univ.filter (fun i => f i = ξ), α i ≠ 0}

/-- All frequencies lie in the bandlimit `[-F, F]`. -/
def Bandlimited {k : ℕ} (F : ℝ) (f : Fin k → ℝ) : Prop := ∀ j, |f j| ≤ F

/-- The time window `[-1, 1]`. -/
def window : Set ℝ := Set.Icc (-1) 1

/-- `‖z‖²_{[-1,1]} = ∫_{-1}^{1} |z(t)|² dt` (unnormalized), as an extended nonnegative real. -/
noncomputable def wsq (z : ℝ → ℂ) : ℝ≥0∞ := ∫⁻ t in window, ‖z t‖ₑ ^ 2

/-- `‖z‖²₂ = ∫_ℝ |z(t)|² dt`. -/
noncomputable def lsq (z : ℝ → ℂ) : ℝ≥0∞ := ∫⁻ t, ‖z t‖ₑ ^ 2

/-- `‖z‖²_{ℝ \ [-1,1]}`: the energy outside the window. -/
noncomputable def osq (z : ℝ → ℂ) : ℝ≥0∞ := ∫⁻ t in windowᶜ, ‖z t‖ₑ ^ 2

/-- `‖z‖_{[-1,1]}` as a real number (used only for signals with finite window energy). -/
noncomputable def wnorm (z : ℝ → ℂ) : ℝ := Real.sqrt (wsq z).toReal

/-- `⟨z, w⟩_{[-1,1]} = ∫_{-1}^{1} z(t) · conj(w(t)) dt` (linear in the first argument). -/
noncomputable def winner (z w : ℝ → ℂ) : ℂ := ∫ t in window, z t * (starRingEnd ℂ) (w t)

/-- `⟨z, w⟩ = ∫_ℝ z(t) · conj(w(t)) dt`. -/
noncomputable def linner (z w : ℝ → ℂ) : ℂ := ∫ t, z t * (starRingEnd ℂ) (w t)

/-- Fourier-series coefficient on the grid, eq. (6):
`ẑ[n] = (1/√2) ∫_{-1}^{1} z(t) e^{-iπ n t} dt`. -/
noncomputable def fsc (z : ℝ → ℂ) (n : ℤ) : ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) *
    ∫ t in window, z t * Complex.exp (-((Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)))

/-- The continuous Fourier transform over `ℝ`, `ĝ(ξ) = ∫ g(t) e^{-2π i ξ t} dt`, for an
integrable `g` (Mathlib's `𝓕`, whose kernel is `e^{-2π i ξ t}`). -/
noncomputable def ftR (g : ℝ → ℂ) (ξ : ℝ) : ℂ := ∫ t : ℝ, Complex.exp (-(2 * (Real.pi : ℂ) *
  Complex.I * (ξ : ℂ) * (t : ℂ))) * g t

/-- Admissible noise: a function with an almost-everywhere measurable restriction to the window
and finite window energy `‖η‖²_{[-1,1]} < ∞`. Point queries read the function itself. -/
def IsNoise (η : ℝ → ℂ) : Prop :=
  AEStronglyMeasurable η (volume.restrict window) ∧ wsq η < ⊤

/-- `a = (1 ± c) · b` for extended nonnegative reals:
`(1 - c) b ≤ a ≤ (1 + c) b` (the lower bound is vacuous when `c ≥ 1`). -/
def ApproxEq (c : ℝ) (a b : ℝ≥0∞) : Prop :=
  ENNReal.ofReal (1 - c) * b ≤ a ∧ a ≤ ENNReal.ofReal (1 + c) * b

/-- "With probability at least `p`": some measurable event of probability at least `p` is
contained in `E` (inner probability, so a non-measurable `E` is not credited with outer
measure). -/
def ProbAtLeast {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (E : Set Ω) (p : ℝ) : Prop :=
  ∃ S, MeasurableSet S ∧ S ⊆ E ∧ ENNReal.ofReal p ≤ μ S

/-- The reading of "with high probability" for an instance of size parameter `n = kF/ε`:
success probability at least `1 - (2 + n)^{-a}` once `n ≥ n₀`, and at least `p₀` below that
threshold. -/
noncomputable def whpBound (a n₀ p₀ n : ℝ) : ℝ :=
  if n₀ ≤ n then 1 - (2 + n) ^ (-a) else p₀

end CaiFourierSparse.Learning


