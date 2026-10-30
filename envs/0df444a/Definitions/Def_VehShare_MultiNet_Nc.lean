-- Prove2me | Definitions.Def_VehShare_MultiNet_Nc
-- name    : VehShare_MultiNet_Nc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:47:35.537073+00:00
-- url     : https://prove2.me/theorems/97cf0df1-64e5-47ac-8d29-699802164dae
-- title:
--   Number of locations $N_c$ of a network
-- statement:
--   $N_c$ is the number of locations of network $c$ of $q^s$ (§6, p. 17).
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, §6, p. 17

import Mathlib
import Definitions.Def_VehShare_MultiNet_flowGraph

namespace VehShare.MultiNet

open Classical in
/-- **Number of locations `N_c` of network `c`.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), §6, p. 17: "`N_c` ... the number of locations ... associated with network `c`". -/
noncomputable def Nc (P : Instance) (qs : P.L → P.L → ℝ)
    (c : (flowGraph P qs).ConnectedComponent) : ℕ :=
  (Finset.univ.filter fun i => (flowGraph P qs).connectedComponentMk i = c).card

end VehShare.MultiNet


