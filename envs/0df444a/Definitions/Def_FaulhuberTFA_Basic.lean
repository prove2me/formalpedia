-- Prove2me | Definitions.Def_FaulhuberTFA_Basic
-- name    : FaulhuberTFA_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T10:59:25.478816+00:00
-- url     : https://prove2.me/theorems/b10f2469-1b9a-472f-873f-98579cd63f35
-- title:
--   Time-frequency analysis: translation, modulation, STFT, ambiguity function, $L^2$ Fourier transform
-- statement:
--   This file fixes the notation of the lecture notes.
--
--   1. $\mathbb{R}^d$ is the Euclidean space with dot product $x\cdot\omega$, and $e^{2\pi i s}$ is written $\mathrm{e}(s)$.
--   2. Translation and modulation of $f:\mathbb{R}^d\to\mathbb{C}$ are $(T_xf)(t)=f(t-x)$ and $(M_\omega f)(t)=e^{2\pi i\omega\cdot t}f(t)$.
--   3. The $L^2$ inner product is $\langle f,g\rangle=\int_{\mathbb{R}^d}f(t)\overline{g(t)}\,dt$, linear in the first argument.
--   4. **Definition 2.2.** The short-time Fourier transform of $f$ with window $g$ is
--   $$V_gf(x,\omega)=\int_{\mathbb{R}^d}f(t)\,\overline{g(t-x)}\,e^{-2\pi i\omega\cdot t}\,dt,\qquad (x,\omega)\in\mathbb{R}^{2d}.$$
--   5. **Definition 3.2.** The cross-ambiguity function and the (auto-)ambiguity function are
--   $$A(f,g)(x,\omega)=\int_{\mathbb{R}^d}f\big(t+\tfrac{x}{2}\big)\,\overline{g\big(t-\tfrac{x}{2}\big)}\,e^{-2\pi i\omega\cdot t}\,dt,\qquad Af=A(f,f).$$
--   6. **Definition 0.1.** The Fourier transform $\hat f(\omega)=\int f(x)e^{-2\pi i\omega\cdot x}\,dx$, extended from $L^1\cap L^2$ to all of $L^2(\mathbb{R}^d)$.
--   7. The standard Gaussian $g_0(t)=2^{d/4}e^{-\pi|t|^2}$ on $\mathbb{R}^d$ and the box function $b_0=\chi_{[-1/2,1/2]}$ on $\mathbb{R}$.
--
--   These are the objects of Chapters 2 and 3 of the notes; every theorem of this mission is stated in terms of them.
--
--   **Formalization Note** The Fourier transform is Mathlib's $L^2$ Fourier transform, which has exactly the normalisation above; it is applied to the $L^2$ class of $f$ and returned as a function (a representative), and is set to $0$ for $f\notin L^2$, a case no theorem uses. The box function is written on $\mathbb{R}^1$, with $t\in\mathbb{R}^1$ identified with its single coordinate.
-- source:
--   Faulhuber, Time-Frequency Analysis (Lecture Notes), arXiv:2204.01596 (2022), Recap p. 7, Definition 2.2 p. 17, Definition 3.2 p. 25, Section 2 pp. 15-17 (b0, g0)

import Mathlib

/-!
Faulhuber, *Time-Frequency Analysis (Lecture Notes)*, arXiv:2204.01596 (2022):
notation of the Recap (p. 7), Definition 2.2 (p. 17), Definition 3.2 (p. 25), and the
functions `b₀`, `g₀` of Section 2 (p. 15–17).
-/

open MeasureTheory Complex
open scoped InnerProductSpace FourierTransform

noncomputable section

namespace FaulhuberTFA

/-- The Euclidean space `ℝ^d`; `⟪x, ω⟫_ℝ` is the dot product `x · ω`. -/
abbrev Rd (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-- The phase `e^{2πi s}`. -/
def ePhase (s : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))

/-- Translation by `x`: `(T_x f)(t) = f(t - x)`. -/
def transl (x : Rd d) (f : Rd d → ℂ) : Rd d → ℂ := fun t => f (t - x)

/-- Modulation by `ω`: `(M_ω f)(t) = e^{2πi ω·t} f(t)`. -/
def modul (ω : Rd d) (f : Rd d → ℂ) : Rd d → ℂ := fun t => ePhase ⟪ω, t⟫_ℝ * f t

/-- The `L²` inner product `⟨f, g⟩ = ∫ f(t) \overline{g(t)} dt` (linear in the first slot). -/
def l2inner (f g : Rd d → ℂ) : ℂ := ∫ t, f t * starRingEnd ℂ (g t)

/-- Definition 2.2: the short-time Fourier transform of `f` with window `g`,
`V_g f(x, ω) = ∫ f(t) \overline{g(t - x)} e^{-2πi ω·t} dt`. -/
def stft (g f : Rd d → ℂ) (x ω : Rd d) : ℂ :=
  ∫ t, f t * starRingEnd ℂ (g (t - x)) * ePhase (-⟪ω, t⟫_ℝ)

/-- Definition 3.2: the cross-ambiguity function
`A(f, g)(x, ω) = ∫ f(t + x/2) \overline{g(t - x/2)} e^{-2πi ω·t} dt`. -/
def crossAmbiguity (f g : Rd d → ℂ) (x ω : Rd d) : ℂ :=
  ∫ t, f (t + (1 / 2 : ℝ) • x) * starRingEnd ℂ (g (t - (1 / 2 : ℝ) • x)) * ePhase (-⟪ω, t⟫_ℝ)

/-- Definition 3.2: the (auto-)ambiguity function `A f = A(f, f)`. -/
def ambiguity (f : Rd d → ℂ) (x ω : Rd d) : ℂ := crossAmbiguity f f x ω

open Classical in
/-- Definition 0.1: the Fourier transform `\hat f` of `f ∈ L²(ℝ^d)`, with the normalisation
`\hat f(ω) = ∫ f(x) e^{-2πi ω·x} dx`, extended to `L²` (Mathlib's `L²` Fourier transform);
returned as a function. Its value for `f ∉ L²` is irrelevant (set to `0`). -/
def fourierL2 (f : Rd d → ℂ) : Rd d → ℂ :=
  if h : MemLp f 2 volume then
    ⇑((𝓕 (h.toLp f : Lp ℂ 2 (volume : Measure (Rd d)))) : Lp ℂ 2 (volume : Measure (Rd d)))
  else 0

/-- The `d`-dimensional standard Gaussian `g₀(t) = 2^{d/4} e^{-π |t|²}` (Example 2.3). -/
def gauss0 (d : ℕ) : Rd d → ℂ := fun t => ((2 : ℝ) ^ ((d : ℝ) / 4) * Real.exp (-Real.pi * ‖t‖ ^ 2) : ℝ)

/-- The box function `b₀ = χ_{[-1/2, 1/2]}` on `ℝ` (p. 15), written on `ℝ^1`. -/
def box0 : Rd 1 → ℂ := fun t => if |t 0| ≤ 1 / 2 then 1 else 0

end FaulhuberTFA


