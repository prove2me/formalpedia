-- Prove2me | Definitions.Def_RHX_Count1000000Data
-- name    : RHX_Count1000000Data
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:47:48.372263+00:00
-- url     : https://prove2.me/theorems/c13002fd-964a-4a91-bed9-05c22da8b41d
-- title:
--   Turing-count data for the box up to height 1000000
-- statement:
--   Turing-count data for the zeros of $\zeta$ with $121\le\operatorname{Im}\rho\le10^6$: two Gamma-factor records (`Arb4.GamD`, at heights $121$ and $10^6$) and the enclosure record `Arb4.EnclQ` of the argument changes on the boundary of the box, including the horizontal enclosure of the edge data `RHX_Edge1000000Data`. Checked by the kernel in `RHX1000000.Count.chk`.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_RHX_Edge1000000Data
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Gamma
import Definitions.Def_ArdaRH65K_Turing121_Arb4_H1000Edges_0
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Seg
import Definitions.Def_ArdaRH65K_Turing121_H11K_Turing
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q
namespace RHX1000000.Count
noncomputable def G0 : GamD := ⟨Q.ofNat 121, 12, 13, 12, 13, 1, 3, 1, 3⟩
noncomputable def G1 : GamD := ⟨Q.ofNat 1000000, 38, 10, 38, 10, 1, 1, 1, 1⟩
noncomputable def E : EnclQ := ⟨Q.frac (-249) 250, Q.frac 249 250,
  RHX1000000.Edge.E.Lo, RHX1000000.Edge.E.Hi, Arb4.H1000.E_T121.Lo, Arb4.H1000.E_T121.Hi,
  (Q.frac 5488698298208 1000000), (Q.frac 5488698302343 1000000),
  (Q.frac 5488698292010 1000000), (Q.frac 5488698296145 1000000)⟩
end RHX1000000.Count
def RHX_Count1000000Data : Nat := 0


