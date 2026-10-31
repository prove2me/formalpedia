-- Prove2me | Definitions.Def_KallMayerSLP_CondExp_rhoCexp
-- name    : KallMayerSLP_CondExp_rhoCexp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:17.270373+00:00
-- url     : https://prove2.me/theorems/8bb2ab60-5ff8-4620-b471-ec0e2a208a98
-- title:
--   Conditional-loss measure $\rho_{\mathrm{cexp}}(\vartheta)=\mathbb E[-\vartheta\mid\vartheta<0]$
-- statement:
--   For a real random variable $\vartheta$ on a probability space, whose negative values are read as losses, the **conditional loss measure** is
--   $$
--   \rho_{\mathrm{cexp}}(\vartheta)=\mathbb E[-\vartheta\mid\vartheta<0]=\frac{\int_{\{\vartheta<0\}}(-\vartheta)\,d\mu}{\mathbb P(\vartheta<0)}\quad\text{if }\mathbb P(\vartheta<0)>0,
--   $$
--   and $\rho_{\mathrm{cexp}}(\vartheta)=0$ otherwise. It is the expected size of a loss given that a loss occurs, and it is the left side of the conditional-expectation constraint (4.26).
--
--   **Formalization Note** The value $0$ when $\mathbb P(\vartheta<0)=0$ is the book's own convention, written as an explicit branch.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, eq. (4.25), p.158

import Mathlib

open MeasureTheory

namespace KallMayerSLP.CondExp

/-- The conditional-loss quality measure `ρ_cexp(ϑ) := 𝔼[-ϑ | ϑ < 0]`, set to `0` when `ℙ(ϑ < 0) = 0`.
Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, eq. (4.25), p.158 (PDF 168).

**Formalization Note** The conditional expectation is the elementary one,
`(∫_{ϑ<0} (-ϑ) dμ) / ℙ(ϑ < 0)`. The `else 0` branch is the book's own convention
("and `ρ_cexp(ϑ) := 0` otherwise"), not a Lean default. -/
noncomputable def rhoCexp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ϑ : Ω → ℝ) : ℝ :=
  if 0 < μ.real {ω | ϑ ω < 0} then
    (∫ ω in {ω | ϑ ω < 0}, -ϑ ω ∂μ) / μ.real {ω | ϑ ω < 0}
  else 0

end KallMayerSLP.CondExp


