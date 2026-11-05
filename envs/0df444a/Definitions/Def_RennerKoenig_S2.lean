-- Prove2me | Definitions.Def_RennerKoenig_S2
-- name    : RennerKoenig_S2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:46:05.178439+00:00
-- url     : https://prove2.me/theorems/d88edbd3-fff5-45eb-a8e2-e5ae847ebd05
-- title:
--   Rényi entropy of order two $S_2$
-- statement:
--   The Rényi entropy of order $2$ of a density operator $\rho$ is
--
--   $$
--   S_2(\rho)=-\log_2\operatorname{tr}(\rho^2),
--   $$
--
--   the formula $S_\alpha(\rho)=\frac1{1-\alpha}\log_2\operatorname{tr}(\rho^\alpha)$ at $\alpha=2$. In Theorem 4.1 it is evaluated on the joint state of the string and the adversary.
--
--   **Formalization Note** The Lean value uses the real part of the trace; $\operatorname{tr}(\rho^2)$ is real and positive for a density operator.
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, §2.4, p.6

import Mathlib
import Definitions.Def_RennerKoenig_tr

namespace RennerKoenig

/-- **Rényi entropy of order 2**, `S₂(T) = −log₂ tr(T²)`: the formula
`S_α(ρ) = (1 − α)⁻¹ log₂ tr(ρ^α)` of Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, §2.4, p.6, at `α = 2`.

**Formalization Note** The real part of the trace; `tr(T²)` is real and positive on density
operators, so the logarithm is not at a junk value. -/
noncomputable def S2 {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (T : K →L[ℂ] K) : ℝ :=
  -Real.logb 2 (tr (T * T)).re

end RennerKoenig


