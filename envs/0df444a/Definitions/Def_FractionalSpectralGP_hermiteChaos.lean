-- Prove2me | Definitions.Def_FractionalSpectralGP_hermiteChaos
-- name    : FractionalSpectralGP_hermiteChaos
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:02.972302+00:00
-- url     : https://prove2.me/theorems/974508e8-c9da-4207-b110-518e0d97f425
-- title:
--   The chaos basis $H_\alpha=\prod_kh_{\alpha_k}(\widetilde{h_k})$
-- statement:
--   Let $\ell$ be the set of finitely supported multi-indices $\alpha=(\alpha_1,\alpha_2,\dots)$ with entries in $\mathbb N_0$, and let $\mathbf h_0,\mathbf h_1,\dots$ be the (probabilists') Hermite polynomials. Then
--
--   $$
--   H_\alpha(\omega)=\prod_{k}\mathbf h_{\alpha_k}\big(\widetilde{h_k}(\omega)\big),\qquad\alpha\in\ell .
--   $$
--
--   These functions form an orthogonal basis of the white noise space with $\|H_\alpha\|^2=\alpha!$ (theorem `eq_4_3_chaos_basis`). They are the coordinates in which the Wick product and the Kondratiev spaces are defined.
--
--   **Formalization Note** $\ell$ is `ℕ →₀ ℕ`, and coordinate $n=0,1,\dots$ carries $Z_n=\widetilde{h_n}$ (it is the paper's coordinate $k=n+1$). The polynomials are Mathlib's `Polynomial.hermite`, the probabilists' $He_n$, which (4.3) requires. A real representative of $Z_n$ is used.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, §4, p.10

import Mathlib
import Definitions.Def_FractionalSpectralGP_Omega
import Definitions.Def_FractionalSpectralGP_Zn

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The Wiener–Itô chaos basis `H_α = ∏_k h_{α_k}(h̃_k)`, `α ∈ ℓ` (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, §4, p.10),
with `h_k` the Hermite polynomials.

**Formalization Note.** `ℓ` is `ℕ →₀ ℕ`. The polynomials are Mathlib's `Polynomial.hermite`, the
probabilists' Hermite polynomials (monic, `E[He_n(Z)²] = n!`), which is what (4.3) requires.
Coordinate `n` of `α` (`n = 0, 1, …`) carries `Z_n = h̃_n`; it is the paper's coordinate
`k = n + 1`. The real part of a representative of `Z_n` is used (`Z_n` is real a.e.). -/
noncomputable def hermiteChaos (P : Measure Omega) (ι : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 P) (h : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ)))
    (α : ℕ →₀ ℕ) (ω : Omega) : ℝ :=
  α.prod fun n k => Polynomial.aeval ((Zn P ι h n : Omega → ℂ) ω).re (Polynomial.hermite k)

end FractionalSpectralGP


