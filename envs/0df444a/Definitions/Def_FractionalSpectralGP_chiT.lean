-- Prove2me | Definitions.Def_FractionalSpectralGP_chiT
-- name    : FractionalSpectralGP_chiT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:55.294557+00:00
-- url     : https://prove2.me/theorems/859dee98-fd53-4283-bdf4-26db21021837
-- title:
--   $\chi_t(u)=(e^{itu}-1)/u$, with $\chi_t(0)=it$
-- statement:
--   For $t\in\mathbb R$,
--
--   $$
--   \chi_t(u)=\frac{e^{itu}-1}{u}\quad(u\ne0),\qquad \chi_t(0)=it .
--   $$
--
--   The paper shows on p.16 that $\chi_t$ is a uniform limit of Schwartz functions, which is what places $1_{[0,t]}$ in the domain of the extended $Q_\sigma$.
--
--   **Formalization Note** The value at $u=0$ is the continuous extension; Lean's division would otherwise give $0$ there.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, §5, p.16

import Mathlib

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The function `χ_t(u) = (e^{itu} − 1)/u` (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, §5, p.16), extended by its
continuous value `χ_t(0) = it` at `u = 0`.

**Formalization Note.** Lean's division would give `0` at `u = 0`, where the printed quotient is
`0/0`; the continuous extension `it` is written in. -/
noncomputable def chiT (t : ℝ) (u : ℝ) : ℂ :=
  if u = 0 then Complex.I * t else (Complex.exp (Complex.I * (t * u)) - 1) / u

end FractionalSpectralGP


