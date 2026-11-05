-- Prove2me | Definitions.Def_RennerKoenig_traceDist
-- name    : RennerKoenig_traceDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:19.863129+00:00
-- url     : https://prove2.me/theorems/84ec2aeb-0b5f-4013-a681-57575990f4f5
-- title:
--   Trace distance $\delta(\rho,\sigma)$
-- statement:
--   The trace distance between two operators $\rho,\sigma$ on the same Hilbert space is
--
--   $$
--   \delta(\rho,\sigma)=\frac12\operatorname{tr}|\rho-\sigma|.
--   $$
--
--   It is the distance in which the paper measures how far a real key is from an ideal one.
--
--   **Formalization Note** $\operatorname{tr}|\cdot|$ is the published nuclear norm `traceNormValue`. The two agree on trace-class operators, and the distance is only applied to differences of density operators.
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, §2.3, p.4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

open QAlgorithms.Papers.Independent.Dependency50.P13

namespace RennerKoenig

/-- **Trace distance** `δ(a, b) = ½ tr|a − b|`. Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, §2.3, p.4.

**Formalization Note** `tr|·|` is the published nuclear norm `traceNormValue`, which equals `tr|·|`
on trace-class operators; it is applied only to differences of density operators. -/
noncomputable def traceDist {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (a b : K →L[ℂ] K) : ℝ :=
  2⁻¹ * traceNormValue (a - b)

end RennerKoenig


