-- Prove2me | Definitions.Def_RedundancyHT_pOf
-- name    : RedundancyHT_pOf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:44.217954+00:00
-- url     : https://prove2.me/theorems/5a317719-26d1-40d3-ac3f-43c2ef619b93
-- title:
--   The arrival proportion $p_S$ of a job type
-- statement:
--   The proportion of jobs of type $S$ is
--   $$p_S=\frac{\lambda_S}{\lambda_{\mathrm{tot}}},$$
--   where $\lambda_S$ is the arrival rate of type-$S$ jobs and $\lambda_{\mathrm{tot}}=\sum_S\lambda_S$. These proportions are positive on the set of job types and sum to one.
--
--   **Formalization Note** Job types are `Fin n`, servers are `Fin m`, and the system is a published `BipartiteMatchingHT.Delay.Model`. The value $p_S$ is the nominal rate of the type divided by the total nominal rate.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, §2.1, p.4

import Definitions.Def_BipartiteMatchingHT_Delay_Primitives

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The probability `p_S`.** A job is of type `S` with probability `p_S = λ_S / λ_tot`
(arXiv:2005.14566v5, §2.1, p.4).

**Formalization Note.** Job types are `Fin n` and the data is a published
`BipartiteMatchingHT.Delay.Model`; `p_S` is the normalized nominal rate. The field `balance` of
`Model` (total nominal rate = total service rate) is a normalization, not a restriction: every
system of the paper is the model with `nominal S := µ_tot * p_S`. -/
def pOf {n m : ℕ} (D : Model n m) (i : Fin n) : ℝ :=
  D.nominal i / ∑ k, D.nominal k

end RedundancyHT


