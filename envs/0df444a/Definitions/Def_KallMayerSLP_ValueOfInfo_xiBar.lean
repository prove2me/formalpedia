-- Prove2me | Definitions.Def_KallMayerSLP_ValueOfInfo_xiBar
-- name    : KallMayerSLP_ValueOfInfo_xiBar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:12:36.973984+00:00
-- url     : https://prove2.me/theorems/5449ff58-e7f1-4e3c-b51a-9c0b130ec014
-- title:
--   Mean $\bar\xi=\mathbb E_\xi[\xi]$ of the random vector
-- statement:
--   For the law $\mu$ of $\xi$ on $\mathbb R^r$, the vector of coordinate means
--
--   $$
--   \bar\xi=\mathbb E_\xi[\xi]=\Big(\int \xi_j\,d\mu(\xi)\Big)_{j=1,\dots,r}.
--   $$
--
--   The expected value problem (2.67) replaces $\xi$ by $\bar\xi$.
--
--   **Formalization Note** Coordinates are Bochner integrals; they are the true means under the chapter's standing assumption $\xi\in L^2$ (Assumption 1.1), which every theorem using $\bar\xi$ states.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, §2.3, p.244 (PDF 253)

import Mathlib

open MeasureTheory

namespace KallMayerSLP.ValueOfInfo

/-- **The expectation `ξ̄ = 𝔼_ξ[ξ]` of the random vector.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, p.244 (PDF 253): "the random vector
`ξ` would be replaced by its expectation `ξ̄ = 𝔼_ξ[ξ]`".

**Formalization Note.** `μ` is the law `ℙ_ξ` on `ℝʳ` and `ξ̄` is the vector of the coordinate means
(Bochner integrals). It is the true mean whenever the coordinates are integrable, which holds under the
standing assumption `ξ ∈ L²` (Chapter 3, Assumption 1.1, p.194), stated as a hypothesis wherever
`ξ̄` is used. -/
noncomputable def xiBar {r : ℕ} (μ : Measure (Fin r → ℝ)) : Fin r → ℝ :=
  fun j => ∫ ξ, ξ j ∂μ

end KallMayerSLP.ValueOfInfo


