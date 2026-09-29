-- Prove2me | Definitions.Def_analise_de_fourier_core
-- name    : analise_de_fourier_core
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-22T20:32:19.867237+00:00
-- url     : https://prove2.me/theorems/3c4abff0-ff50-4ea9-9c0a-ca4c857bedcf
-- title:
--   Fourier series: angular frequencies, coefficients $a_n, b_n, C_n$, average power
-- statement:
--   This bundle fixes the notation of the book's chapters 3-5 for a period $T>0$.
--
--   1. The angular frequencies are $\omega_n = 2\pi n/T$ for $n\in\mathbb{Z}$.
--   2. For a real-valued $f$, the trigonometric Fourier coefficients (eq. 3.23) are
--   $$a_n = \frac{2}{T}\int_0^T f(t)\cos(\omega_n t)\,dt,\qquad b_n = \frac{2}{T}\int_0^T f(t)\sin(\omega_n t)\,dt .$$
--   3. For a complex-valued $f$, the exponential coefficients (eq. 4.8) are
--   $$C_n = \frac{1}{T}\int_0^T f(t)e^{-i\omega_n t}\,dt .$$
--   4. The average power of a periodic signal (Definição 5.1.1) is $P_f = \frac{1}{T}\int_0^T |f(t)|^2\,dt$.
--   5. The trigonometric polynomial of degree $N$ (Definição 3.2.1) is $\frac{a_0}{2}+\sum_{n=1}^{N}\bigl[a_n\cos(\omega_n t)+b_n\sin(\omega_n t)\bigr]$.
--
--   These five notions are shared by every statement of the mission, so the whole mission rests on this one model of the Fourier coefficients of a periodic signal.
--
--   **Formalization Note.** The coefficient indices range over $\mathbb{Z}$, matching the book's extension (4.7) of $a_n,b_n$ to negative indices. Integrals are interval integrals over $[0,T]$; when the integrand is not integrable, or when $T=0$, they take the default value $0$, so every statement of the mission carries the hypothesis $0<T$ together with whatever integrability the book assumes.
-- source:
--   Esequia Sauter, Fabio Souto de Azevedo (orgs.), Analise de Fourier - Um Livro Colaborativo, UFRGS/REAMAT, 26 July 2022, https://www.ufrgs.br/reamat/TransformadasIntegrais/livro-af/main.html, Definicao 3.2.1 (p. 17), Teorema 3.2.2 / eq. (3.23) (p. 19), eq. (4.8) (p. 30), Definicao 5.1.1 / eq. (5.1) (p. 36)

import Mathlib

namespace AnaliseDeFourier

open MeasureTheory

/-- The `n`-th angular frequency of a `T`-periodic signal: `ω n = 2 * π * n / T`. -/
noncomputable def angFreq (T : ℝ) (n : ℤ) : ℝ := 2 * Real.pi * n / T

/-- The cosine Fourier coefficient `a n = (2 / T) * ∫ t in 0..T, f t * cos (ω n * t)`. -/
noncomputable def coeffA (T : ℝ) (f : ℝ → ℝ) (n : ℤ) : ℝ :=
  (2 / T) * ∫ t in (0 : ℝ)..T, f t * Real.cos (angFreq T n * t)

/-- The sine Fourier coefficient `b n = (2 / T) * ∫ t in 0..T, f t * sin (ω n * t)`. -/
noncomputable def coeffB (T : ℝ) (f : ℝ → ℝ) (n : ℤ) : ℝ :=
  (2 / T) * ∫ t in (0 : ℝ)..T, f t * Real.sin (angFreq T n * t)

/-- The exponential Fourier coefficient
`C n = (1 / T) * ∫ t in 0..T, f t * exp (-I * ω n * t)`, for `n : ℤ`. -/
noncomputable def coeffC (T : ℝ) (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  (1 / T) * ∫ t in (0 : ℝ)..T, f t * Complex.exp (-(Complex.I * (angFreq T n * t)))

/-- The average power of a `T`-periodic signal: `P f = (1 / T) * ∫ t in 0..T, ‖f t‖ ^ 2`. -/
noncomputable def avgPower (T : ℝ) (f : ℝ → ℂ) : ℝ :=
  (1 / T) * ∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2

/-- The trigonometric polynomial of degree `N` with coefficients `a` and `b`:
`a 0 / 2 + ∑ n ∈ [1, N], (a n * cos (ω n * t) + b n * sin (ω n * t))`. -/
noncomputable def trigPoly (T : ℝ) (a b : ℤ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  a 0 / 2 + ∑ n ∈ Finset.Icc 1 N,
    (a (n : ℤ) * Real.cos (angFreq T (n : ℤ) * t) + b (n : ℤ) * Real.sin (angFreq T (n : ℤ) * t))

end AnaliseDeFourier


