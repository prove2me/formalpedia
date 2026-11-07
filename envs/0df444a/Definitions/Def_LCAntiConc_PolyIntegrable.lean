-- Prove2me | Definitions.Def_LCAntiConc_PolyIntegrable
-- name    : LCAntiConc_PolyIntegrable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:48.445208+00:00
-- url     : https://prove2.me/theorems/dfd65e69-f0ef-4157-a003-07a4fd78c758
-- title:
--   Random polynomial with integrable coefficients
-- statement:
--   A random polynomial $F:\Omega\to\mathbb R[v]$ on a measure space $(\Omega,\nu)$ **has integrable coefficients** if for every monomial $v^\alpha$ the coefficient $\omega\mapsto[F(\omega)]_\alpha$ is $\nu$-integrable.
--
--   This is exactly the condition under which the expectation polynomial $\mathbb E_\omega F(\omega)$ exists.
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), (1.3), p.2 (PDF p.4); Definition 4.1, p.17 (PDF p.19)

import Mathlib

namespace LCAntiConc

open MeasureTheory

/-- A random polynomial `F : Ω → ℝ[v]` has integrable coefficients: for every monomial `α`, the
coefficient `ω ↦ (F ω)_α` is integrable, so the expectation polynomial `𝔼_ω F(ω)` exists.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), (1.3), p.2 (PDF p.4), and Definition 4.1,
p.17 (PDF p.19), where the expectation polynomials are written. -/
def PolyIntegrable {σ Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (F : Ω → MvPolynomial σ ℝ) : Prop :=
  ∀ α, Integrable (fun ω => (F ω).coeff α) ν

end LCAntiConc


