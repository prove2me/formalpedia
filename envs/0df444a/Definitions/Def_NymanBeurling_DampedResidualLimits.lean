-- Prove2me | Definitions.Def_NymanBeurling_DampedResidualLimits
-- name    : NymanBeurling_DampedResidualLimits
-- status  : Definition
-- author  : @pragyan
-- created : 2026-11-21T01:50:49.166726+00:00
-- url     : https://prove2.me/theorems/649c997b-6b07-465d-86c9-5d6a35e7ea26
-- title:
--   Finite damped Möbius residuals and their explicit coordinate limit
-- statement:
--   For an integer denominator cutoff $N\ge0$, damping parameter $\varepsilon>0$, and positive coordinate $m$, define
--   $$R_{N,\varepsilon}(m)=1+\sum_{d=2}^{N+1}\frac{\mu(d)}{d^\varepsilon}\frac{m\bmod d}{d}.$$
--   The corresponding explicit coordinate limit is
--   $$P_\varepsilon(m)=1+m\sum_{d\ge1}\frac{\mu(d)}{d^{1+\varepsilon}}-\sum_{1\le d\le m}\frac{\mu(d)}{d^\varepsilon}\left\lfloor\frac{m}{d}\right\rfloor.$$
--   The infinite series converges absolutely for positive damping. These definitions separate denominator truncation from the subsequent small-damping limit in the discrete Hilbert space with coordinate weights $1/[m(m+1)]$. They assert no norm convergence or cancellation bound.
--
--   **Formalization Note.** Both definitions are total on all real damping parameters and natural coordinates; the analytic obligations use $\varepsilon>0$ and $m\ge1$. The natural-index series has a zero contribution at $d=0$.
-- source:
--   B. Bagchi, On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis, https://arxiv.org/pdf/math/0607733 , Theorem 2 proof pp. 140–141 (two successive damped limits) and Theorem 1 proof p. 145 (discrete sequence identification). The displayed coordinate profile follows algebraically by m mod d = m - d floor(m/d) and the absolutely convergent Möbius Dirichlet series at 1+ε; this is a derived definition, not an unconditional norm-convergence claim.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option autoImplicit false
open scoped BigOperators

namespace NymanBeurling

noncomputable def dampedResidualFinite (N : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  1 + ∑ k : Fin N,
    ((ArithmeticFunction.moebius (k.val+2) : ℝ) / (k.val+2 : ℝ)^ε) *
      ((m % (k.val+2) : ℕ) : ℝ) / (k.val+2 : ℝ)

noncomputable def dampedResidualProfile (ε : ℝ) (m : ℕ) : ℝ :=
  1 + (m : ℝ) * (∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)^(1+ε)) -
    ∑ d ∈ Finset.Ioc 0 m,
      ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)^ε) * ((m/d : ℕ) : ℝ)

end NymanBeurling


