-- Prove2me | Definitions.Def_KallMayerSLP_CondExp_cvarObjective
-- name    : KallMayerSLP_CondExp_cvarObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:23.0644+00:00
-- url     : https://prove2.me/theorems/0b25f022-f4bf-493e-962f-76a88970f240
-- title:
--   CVaR objective $u_c(z)=z+\frac{1}{1-\alpha}\mathbb E[(\vartheta-z)^+]$
-- statement:
--   For an integrable random variable $\vartheta$ and $0<\alpha<1$, the objective of the unconstrained problem (4.30) is
--   $$
--   u_c(z)=z+\frac{1}{1-\alpha}\,\mathbb E[(\vartheta-z)^+],\qquad z\in\mathbb R .
--   $$
--   Minimizing it over $z$ computes value at risk and conditional value at risk together.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, eqs. (4.30)–(4.31), pp.160–161

import Mathlib

open MeasureTheory

namespace KallMayerSLP.CondExp

/-- The objective `u_c(z) := z + (1 / (1 - α)) 𝔼[(ϑ - z)⁺]` of problem (4.30).
Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, eqs. (4.30)–(4.31), pp.160–161
(PDF 170–171).

**Formalization Note** `(ϑ - z)⁺` is `max (ϑ ω - z) 0`, a Bochner integral: statements assume `ϑ`
integrable and `0 < α < 1`, the book's standing assumptions of §4.3. -/
noncomputable def cvarObjective {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ϑ : Ω → ℝ)
    (α z : ℝ) : ℝ :=
  z + 1 / (1 - α) * ∫ ω, max (ϑ ω - z) 0 ∂μ

end KallMayerSLP.CondExp


