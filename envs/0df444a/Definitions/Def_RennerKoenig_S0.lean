-- Prove2me | Definitions.Def_RennerKoenig_S0
-- name    : RennerKoenig_S0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:48.757938+00:00
-- url     : https://prove2.me/theorems/4e4ad8c8-1346-43b6-8cd5-5f4ebac791ff
-- title:
--   Rényi entropy of order zero $S_0$
-- statement:
--   The Rényi entropy of order $0$ of a density operator $\rho$ is
--
--   $$
--   S_0(\rho)=\log_2\operatorname{rank}(\rho).
--   $$
--
--   In Theorem 4.1 it measures the size of the adversary's system.
--
--   **Formalization Note** Meaningful for finite rank; see `rankOp`.
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, §2.4, p.6

import Mathlib
import Definitions.Def_RennerKoenig_rankOp

namespace RennerKoenig

/-- **Rényi entropy of order 0**, `S₀(T) = log₂ rank(T)`. Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, §2.4, p.6.

**Formalization Note** See `rankOp`: the value is meaningful only for finite-dimensional range. -/
noncomputable def S0 {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (T : K →L[ℂ] K) : ℝ :=
  Real.logb 2 (rankOp T)

end RennerKoenig


