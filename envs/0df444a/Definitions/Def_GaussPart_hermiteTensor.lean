-- Prove2me | Definitions.Def_GaussPart_hermiteTensor
-- name    : GaussPart_hermiteTensor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:10.984196+00:00
-- url     : https://prove2.me/theorems/7a26d03c-4728-4020-aa60-1d0b0f0ea276
-- title:
--   Normalized Hermite polynomials and Hermite tensors
-- statement:
--   Let $\mathrm{He}_m$ be the probabilists' Hermite polynomial and $h_m=\mathrm{He}_m/\sqrt{m!}$. For a multi-index $\beta$, $H_\beta(x)=\prod_r h_{\beta_r}(x_r)$. The order-$m$ **Hermite tensor** has entries
--   $$(\mathcal H_m(x))_{j_1,\dots,j_m}=\sqrt{\beta!/m!}\;H_\beta(x),\qquad \beta_r=|\{s:j_s=r\}|.$$
--   The Frobenius norm of a tensor is the square root of the sum of its squared entries; $A_i=\mathbb E_{x\sim\mu}[\mathcal H_i(x)]$ is the Hermite moment tensor of $\mu$, and $\hat A_i=\frac1n\sum_s\mathcal H_i(x^{(s)})$ the empirical one.
--
--   These tensors carry the low-degree moments of $Q$ in the moment discrepancy finder.
--
--   **Formalization Note** Mathlib's `Polynomial.hermite` is the probabilists' $\mathrm{He}_m$ with integer coefficients. Tensors are functions on index tuples `Fin m → Fin d`.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Appendix A, p.69 (PDF p.71); Proposition 3.3, p.15; Algorithm 2, p.29

import Mathlib
import Definitions.Def_GaussPart_Cell

open MeasureTheory

namespace GaussPart

/-- `h_m(t) = He_m(t)/√(m!)`, the normalized probabilists' Hermite polynomial (Appendix A, p.69,
PDF p.71). Mathlib's `Polynomial.hermite` is the probabilists' `He_m` with integer coefficients. -/
noncomputable def hermiteOne (m : ℕ) (t : ℝ) : ℝ :=
  ((Polynomial.hermite m).map (Int.castRingHom ℝ)).eval t / Real.sqrt (m.factorial : ℝ)

/-- `H_β(x) = ∏_r h_{β_r}(x_r)`. -/
noncomputable def hermiteBeta {d : ℕ} (β : Fin d → ℕ) (x : Vec d) : ℝ :=
  ∏ r, hermiteOne (β r) (x r)

/-- The multi-index `β_r = |{s ∈ [m] : j_s = r}|` of a tensor index `(j₁, …, j_m)`. -/
def multiIndex {m d : ℕ} (J : Fin m → Fin d) (r : Fin d) : ℕ :=
  (Finset.univ.filter fun s => J s = r).card

/-- The order-`m` **Hermite tensor**, arXiv:2611.05264 (sha256 7e0ca6d4…), Appendix A, p.69
(PDF p.71): `(H_m(x))_{j₁,…,j_m} = √(β!/m!) · H_β(x)`, `β! = ∏_r β_r!`. This normalization gives
`⟨H_m(x), u^{⊗m}⟩ = h_m(u · x)` for every unit vector `u`. -/
noncomputable def hermiteTensor {d : ℕ} (m : ℕ) (x : Vec d) (J : Fin m → Fin d) : ℝ :=
  Real.sqrt (((∏ r, (multiIndex J r).factorial : ℕ) : ℝ) / (m.factorial : ℝ)) *
    hermiteBeta (multiIndex J) x

/-- The Frobenius norm: the square root of the sum of the squared entries (§2, p.13). -/
noncomputable def frobeniusNorm {m d : ℕ} (A : (Fin m → Fin d) → ℝ) : ℝ :=
  Real.sqrt (∑ J, A J ^ 2)

/-- The Hermite moment tensor `A_i = E_{x∼μ}[H_i(x)]`, entrywise (Proposition 3.3, p.15). -/
noncomputable def hermiteMoment {d : ℕ} (μ : Measure (Vec d)) (i : ℕ) (J : Fin i → Fin d) : ℝ :=
  ∫ x, hermiteTensor i x J ∂μ

/-- The empirical Hermite tensor `Â_i = (1/n) ∑_s H_i(x⁽ˢ⁾)` (Algorithm 2, line 6, p.29). -/
noncomputable def empiricalTensor {n d : ℕ} (xs : Fin n → Vec d) (i : ℕ) (J : Fin i → Fin d) : ℝ :=
  (1 / (n : ℝ)) * ∑ s, hermiteTensor i (xs s) J

end GaussPart


