-- Prove2me | Definitions.Def_HighDimStat_MetricEntropy_Diameter
-- name    : HighDimStat_MetricEntropy_Diameter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T22:58:30.09955+00:00
-- url     : https://prove2.me/theorems/e68a67c5-a9c5-4e19-823e-cf0f10dbdbdf
-- title:
--   The diameter of a finite, nonempty metric space
-- statement:
--   The **diameter** $D := \sup_{\theta,\theta'\in T} \rho_X(\theta,\theta')$ of the index set $T$
--   under the pseudometric $\rho_X$, used throughout Section 5.3 (introduced immediately before
--   Proposition 5.17, p. 135) as the natural upper endpoint for the truncation parameter $\delta$
--   in the discretization and entropy-integral bounds.
--
--   $$
--   D \;:=\; \sup_{\theta,\theta' \in T} \rho_X(\theta,\theta').
--   $$
--
--   **Formalization Note** Realized as the real supremum `⨆` over the finite, nonempty type
--   `T × T`; since `T` is a nonempty `Fintype`, this equals the true maximum, not Mathlib's junk
--   value for an empty or unbounded set.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 135 (PDF p. 155)

import Mathlib

namespace HighDimStat.MetricEntropy

/-- The diameter `D := sup_{θ,θ' ∈ T} ρX(θ,θ')` of a finite, nonempty metric space `(T, ρX)`, used
throughout Wainwright, *High-Dimensional Statistics* (2019), Section 5.3 (e.g. immediately before
Proposition 5.17, p. 135). Realized as the real supremum `⨆` over the finite, nonempty type
`T × T`; this equals the true maximum since `T` is a nonempty `Fintype`. -/
noncomputable def Diameter (T : Type*) [Fintype T] [Nonempty T] [PseudoMetricSpace T] : ℝ :=
  ⨆ p : T × T, dist p.1 p.2

end HighDimStat.MetricEntropy


