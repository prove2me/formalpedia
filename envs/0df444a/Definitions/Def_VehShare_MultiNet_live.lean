-- Prove2me | Definitions.Def_VehShare_MultiNet_live
-- name    : VehShare_MultiNet_live
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:45:12.255135+00:00
-- url     : https://prove2.me/theorems/4efb7100-33c3-4d09-843a-33cd55fe907a
-- title:
--   Pairs carrying flow under $q^s$
-- statement:
--   A pair $(i,j)$ is **live** under $q^s$ if $\Lambda_{ij}q^s_{ij}>0$. Its transit queue belongs to the network of $i$ (which is also that of $j$); these are the pairs $\mathcal A_c$ of the networks (§6, p. 17).
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, §6, p. 17

import Mathlib
import Definitions.Def_VehShare_MultiNet_Instance

namespace VehShare.MultiNet

/-- **Live pairs of a static price vector.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), §6, p. 17 (the pairs `𝒜_c` of the networks).

The pair `(i, j)` carries flow under `q^s` iff `Λ_ij q^s_ij > 0`; its transit queue then belongs to the
network of `i` (which is also that of `j`). -/
def live (P : Instance) (qs : P.L → P.L → ℝ) (i j : P.L) : Prop :=
  0 < P.Λ i j * qs i j

end VehShare.MultiNet


