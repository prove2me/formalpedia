-- Prove2me | Definitions.Def_LCAntiConc_polyExpect
-- name    : LCAntiConc_polyExpect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:49.101663+00:00
-- url     : https://prove2.me/theorems/3a8b0d6c-9908-4f8c-baba-babf2eefc7e2
-- title:
--   Expectation polynomial $\mathbb E_\omega F(\omega)$ of a random polynomial
-- statement:
--   Let $(\Omega,\nu)$ be a measure space and $F:\Omega\to\mathbb R[v]$ a random polynomial. Its **expectation polynomial** $\mathbb E_\omega F(\omega)\in\mathbb R[v]$ is the polynomial whose coefficient at every monomial $v^\alpha$ is the expectation of the corresponding coefficient,
--
--   $$\big[\mathbb E_\omega F(\omega)\big]_\alpha=\int_\Omega [F(\omega)]_\alpha\,d\nu(\omega).$$
--
--   The paper's polynomials $\mathbb E\,q(\langle X,v\rangle)$ in (1.3), $\mathbb E_{X,G}\,q^{(r)}(\cdots)^2$ in Definition 4.1 and $\mathbb E_X[z^\top B^2z-(z^\top Bz)^2]$ in Lemmas 4.7–4.8 are of this form: polynomials in $v$ whose coefficients are moments.
--
--   **Formalization Note** The coefficientwise integral defines a polynomial when only finitely many coefficients have nonzero mean, which is the case in every use (bounded degree); the definition returns $0$ otherwise. Integrability of the coefficients is the separate predicate `PolyIntegrable`.
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), (1.3), p.2 (PDF p.4); Definition 4.1, p.17 (PDF p.19); Lemmas 4.7–4.8, pp.23–24 (PDF pp.25–26)

import Mathlib

namespace LCAntiConc

open MeasureTheory

/-- The expectation `𝔼_ω F(ω)` of a random polynomial `F : Ω → ℝ[v]`: the polynomial whose
coefficient at every monomial `α` is `∫ (F ω)_α dν(ω)`. Examples: `𝔼 q(⟨X, v⟩)` in (1.3),
`𝔼_{X,G} q^{(r)}(…)²` in Definition 4.1, and `𝔼_X[zᵀB²z - (zᵀBz)²]` in Lemmas 4.7–4.8.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), (1.3), p.2 (PDF p.4); Definition 4.1,
p.17 (PDF p.19); Lemmas 4.7–4.8, pp.23–24 (PDF pp.25–26).

**Formalization Note** The coefficientwise integral is a polynomial whenever only finitely many
coefficients have nonzero integral, which holds in every use of the paper (the random polynomial
has bounded degree). In that case the coefficient at `α` is exactly `∫ (F ω)_α dν`; otherwise the
definition returns `0`. Integrability of the coefficients is a separate predicate
(`PolyIntegrable`). -/
noncomputable def polyExpect {σ Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (F : Ω → MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  haveI := Classical.propDecidable
  if h : (Function.support fun α => ∫ ω, (F ω).coeff α ∂ν).Finite then
    ∑ α ∈ h.toFinset, MvPolynomial.monomial α (∫ ω, (F ω).coeff α ∂ν)
  else 0

end LCAntiConc


