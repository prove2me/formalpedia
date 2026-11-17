-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
-- name    : QuantumLTF_Membership_Supplement_hermCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:37:02.682214+00:00
-- url     : https://prove2.me/theorems/7c03066e-7f8a-4f0a-b724-b77c89054cbd
-- title:
--   Hermite coefficient $\widehat f_w(\alpha)$
-- statement:
--   For $\alpha\in\mathbb N^n$ the Hermite coefficient of $f_w(x)=\mathrm{sign}(\langle w,x\rangle)$ is
--   $$\widehat f_w(\alpha)=\int_{\mathbb R^n} f_w(x)\,h_\alpha(x)\,d\gamma_n(x),\qquad h_\alpha(x)=\prod_{i=1}^n h_{\alpha_i}(x_i),\quad h_k=\frac{He_k}{\sqrt{k!}},$$
--   with $He_k$ the probabilists' Hermite polynomial. These coefficients are the amplitudes of the Hermite state $|F_w\rangle=\sum_\alpha \widehat f_w(\alpha)|\alpha\rangle$ (Eq. (159)).
--
--   **Formalization Note** $He_k$ is Mathlib's `Polynomial.hermite k`. The integrand is bounded times a polynomial, hence $\gamma_n$-integrable.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, §2.3, p. 16 (PDF p. 17); Eq. (153), p. 58 (PDF p. 59); Eq. (159), p. 60 (PDF p. 61)

import Mathlib
import Definitions.Def_QuantumLTF_Membership_ltf

namespace QuantumLTF.Membership.Supplement

open MeasureTheory QuantumLTF.Membership

/-- **The Hermite coefficient `f̂_w(α)`.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, §2.3, p. 16 (PDF p. 17), and Eq. (153), p. 58
(PDF p. 59): `f̂_w(α) := ∫_{ℝⁿ} f_w(x) h_α(x) γ_n(x) dx` with `f_w(x) = sign(⟨w, x⟩)`,
`h_α(x) = ∏_i h_{α_i}(x_i)`, `h_k := He_k/√(k!)` and `He_k` the probabilists' Hermite polynomial.

**Formalization Note.** `He_k` is Mathlib's `Polynomial.hermite k` (probabilists' convention,
`He_{k+1} = x He_k − He_k'`); `γ_n` is `stdGaussian`. The integrand is a bounded function times a
polynomial, integrable under `γ_n`, so the Bochner integral is never the junk `0` of a
non-integrable function. `f_w = ltf w 0` is `±1`, cast to `ℝ`. -/
noncomputable def hermCoeff {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (α : Fin n → ℕ) : ℝ :=
  ∫ x, (ltf w 0 x : ℝ) *
      ∏ i : Fin n, Polynomial.aeval (x i) (Polynomial.hermite (α i)) / Real.sqrt ((α i).factorial)
    ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n)))

end QuantumLTF.Membership.Supplement


