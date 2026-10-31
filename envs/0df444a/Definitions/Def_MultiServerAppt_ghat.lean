-- Prove2me | Definitions.Def_MultiServerAppt_ghat
-- name    : MultiServerAppt_ghat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:24.206754+00:00
-- url     : https://prove2.me/theorems/1098bc85-2d99-4231-a7f4-1ed4d830bf61
-- title:
--   Expectation of a function of a residual service
-- statement:
--   For a bounded function $g$ and a phase $a$, with $t=-S\mathbf 1$ and $e_a$ the unit row vector,
--
--   $$\hat g(a)=\int_0^\infty g(r)\ e_a\exp(rS)\,t\ \mathrm dr.$$
--
--   This is $\mathbb E[g(R)]$ for a residual service $R\sim\mathrm{PH}(e_a,S)$ of a service currently in phase $a$.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (6), p.10, used for the phases of Eq. (7), p.11

import Mathlib
import Definitions.Def_MatrixAnalytic_PH_Continuous

open Matrix

namespace MultiServerAppt

/-- The expectation `ĝ(a) = E_a[g(R)] = ∫₀^∞ g(r) e_a exp(rS) t dr` of `g` of the residual service
time `R`, for a service currently in phase `a`, where `t = -S𝟙` and `R ∼ PH(e_a, S)`. Kuiper–Lee,
Appointment Scheduling for Multiple Servers, SSRN 3975471, §4, Eq. (6), p.10, used to express the
meaning of the phases of Eq. (7), p.11.

**Formalization Note** The density `e_a exp(rS) t` is `MatrixAnalytic.PH.cdf_density_formula` at the
start vector `e_a`. Bounded `g` and nonsingular `S` make the integrand integrable. -/
noncomputable def ghat {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (g : ℝ → ℝ)
    (a : ι) : ℝ :=
  ∫ r in Set.Ioi (0 : ℝ),
    g r * ((Pi.single a 1 : ι → ℝ) ᵥ* NormedSpace.exp (r • S)) ⬝ᵥ MatrixAnalytic.PH.exitRates S

end MultiServerAppt


