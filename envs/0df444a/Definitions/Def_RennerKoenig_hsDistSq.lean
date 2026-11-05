-- Prove2me | Definitions.Def_RennerKoenig_hsDistSq
-- name    : RennerKoenig_hsDistSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:45:59.738374+00:00
-- url     : https://prove2.me/theorems/740378c6-9a0e-4c72-b972-ed8e61ce9eab
-- title:
--   Squared Hilbert–Schmidt distance $\Delta(\rho,\sigma)$
-- statement:
--   For two density operators $\rho,\sigma$ on the same Hilbert space,
--
--   $$
--   \Delta(\rho,\sigma)=\operatorname{tr}\big((\rho-\sigma)^2\big).
--   $$
--
--   This is the quantity the paper's proof computes in place of the trace distance.
--
--   **Formalization Note** The Lean value is the real part of the trace; on density operators $\rho-\sigma$ is self-adjoint, so the trace is already real.
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, §4.1, p.8

import Mathlib
import Definitions.Def_RennerKoenig_tr

namespace RennerKoenig

/-- **Squared Hilbert-Schmidt distance** `Δ(a, b) = tr((a − b)²)`. Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, §4.1, p.8.

**Formalization Note** The real part of the trace. On density operators `a − b` is self-adjoint,
so the trace is already real. -/
noncomputable def hsDistSq {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (a b : K →L[ℂ] K) : ℝ :=
  (tr ((a - b) * (a - b))).re

end RennerKoenig


