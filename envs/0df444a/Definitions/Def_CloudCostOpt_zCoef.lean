-- Prove2me | Definitions.Def_CloudCostOpt_zCoef
-- name    : CloudCostOpt_zCoef
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:01:16.81718+00:00
-- url     : https://prove2.me/theorems/c7fe7a27-5a15-4a23-98d6-9f2f409ecb26
-- title:
--   Newsvendor factor $z_j=\Phi_N^{-1}((V_j-R_j)/V_j)$
-- statement:
--   For a real resource type $j$,
--
--   $$
--   z_j=\Phi_N^{-1}\Big(\frac{V_j-R_j}{V_j}\Big),
--   $$
--
--   where $\Phi_N$ is the standard normal distribution function. It is the newsvendor safety factor for underage cost $V_j-R_j$ and overage cost $R_j$.
--
--   **Formalization Note** $\Phi_N^{-1}$ is the platform definition `KallMayerSLP.NormalCC.normalQuantile`, $\Phi^{-1}(\alpha)=\inf\{q:\alpha\le\Phi(q)\}$ with $\Phi$ the platform's `FinancialDerivatives.FD06.standardNormalCDF`. For $\alpha\in(0,1)$ this is the unique root of $\Phi(q)=\alpha$; under $0<R_j<V_j$ the argument lies in $(0,1)$.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §4, p.16

import Mathlib
import Definitions.Def_KallMayerSLP_NormalCC_normalQuantile
import Definitions.Def_CloudCostOpt_System

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **`z_j := Φ_N⁻¹((V_j − R_j)/V_j)`**, the newsvendor safety factor of resource `j ≥ 1`, where
`Φ_N` is the standard normal CDF.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245,
§4, p.16 ("`z_j := Φ_N⁻¹((V_j − R_j)/V_j)` … where `Φ_N` denotes the standard normal CDF").

Formalization Note: `Φ_N⁻¹` is the platform definition `KallMayerSLP.NormalCC.normalQuantile`,
`Φ⁻¹(α) = inf {q | α ≤ Φ(q)}` with `Φ = FinancialDerivatives.FD06.standardNormalCDF =
cdf (gaussianReal 0 1)`.  For `α ∈ (0, 1)` this is the unique root of `Φ(q) = α`; every statement
about `z_j` assumes `0 < R_j < V_j`, which puts `(V_j − R_j)/V_j` in `(0, 1)`, so the junk value of
the infimum outside `(0, 1)` is never used. -/
noncomputable def zCoef (S : System) (j : Fin S.J) : ℝ :=
  KallMayerSLP.NormalCC.normalQuantile ((S.V j - S.R j) / S.V j)

end CloudCostOpt


