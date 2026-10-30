-- Prove2me | Definitions.Def_VehShare_MultiNet_Mc
-- name    : VehShare_MultiNet_Mc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:48:21.408379+00:00
-- url     : https://prove2.me/theorems/d45e105b-1891-4e13-b4c8-2be90c928715
-- title:
--   Workload $M_c$ of a network
-- statement:
--   For a network $c$ of $q^s$ (proof of Theorem 4, p. 18),
--
--   $$
--   M_c=\sum_{(i,j)\in\mathcal A_c}\frac{\Lambda_{ij}}{\mu_{ij}}q^s_{ij},
--   $$
--
--   summed over the pairs $(i,j)$ with $i\in\mathcal N_c$ (pairs without flow contribute $0$). $\sum_c M_c=M$.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, proof of Theorem 4, p. 18

import Mathlib
import Definitions.Def_VehShare_MultiNet_flowGraph
import Definitions.Def_VehShare_MultiNet_meanTime

namespace VehShare.MultiNet

open Classical in
/-- **Workload `M_c` of network `c`.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), proof of Theorem 4, p. 18: "`M_c = ∑_{(i,j)∈𝒜_c} (Λ_ij/μ_ij) q^s_ij`".

Summed over the pairs `(i, j)` with `i` in `c`; pairs without flow contribute 0. -/
noncomputable def Mc (P : Instance) (qs : P.L → P.L → ℝ)
    (c : (flowGraph P qs).ConnectedComponent) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => (flowGraph P qs).connectedComponentMk i = c),
    ∑ j, P.Λ i j * qs i j * meanTime P i j

end VehShare.MultiNet


