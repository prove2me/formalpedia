-- Prove2me | Definitions.Def_QuasiPolyTrace_fourier
-- name    : QuasiPolyTrace_fourier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:57.076375+00:00
-- url     : https://prove2.me/theorems/0ace4b98-4668-49c6-a988-90d816083f3f
-- title:
--   Fourier transform $F(\xi)=\sum_j f(j)e^{ij\xi}$ of a sequence on $\mathbb Z$
-- statement:
--   For an absolutely summable sequence $f:\mathbb Z\to\mathbb C$, its **Fourier transform** is the function of an angle $\xi$
--
--   $$
--   F(\xi)=\sum_{j=-\infty}^{\infty} f(j)\,e^{ij\xi}.
--   $$
--
--   It is $2\pi$-periodic, and $|F(\xi)|\le\sum_j|f(j)|$. The paper measures smoothness of weight sequences by the decay of $|F(\xi)|$ away from $\xi=0$ (Lemmas 36, 46, Corollary 34), and, through $z=e^{i\theta}$, evaluates the generating function $\sum_j f(j)z^j$ on the unit circle (Lemma 14).
--
--   **Formalization Note** A real sequence is passed through the coercion into $\mathbb C$. The series is a `tsum`, which is $0$ for a non-summable sequence; every statement applies it to a finitely supported sequence or assumes absolute summability, as the paper's definition does. $\xi$ ranges over $\mathbb R$; each statement restricts it to the angles it concerns.
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), Definition 4, p.6

import Mathlib

namespace QuasiPolyTrace

/-- **The Fourier transform of a sequence on `ℤ`.** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), Definition 4, p.6: "Given a sequence
`f : Z → R` such that `∑_j |f(j)|` is finite, we define its Fourier transform `F : (−π, π] → C`, with
argument considered as an angle mod 2π, by `F(ξ) := ∑_{j=−∞}^{∞} f(j) · e^{ijξ}`".

**Formalization Note.**
* The sequence is complex valued so that the same definition serves Corollary 34 (`f : Z → C`); a real
  sequence is passed through the coercion `ℝ → ℂ`.
* `ξ` ranges over all of `ℝ`; every statement restricts it to the angles it is about.
* The sum is a `tsum`, which is 0 when the series is not summable. Every statement using `fourier`
  applies it to a finitely supported sequence or assumes absolute summability, as Definition 4 does. -/
noncomputable def fourier (f : ℤ → ℂ) (ξ : ℝ) : ℂ :=
  ∑' j : ℤ, f j * Complex.exp (Complex.I * (j : ℂ) * (ξ : ℂ))

end QuasiPolyTrace


