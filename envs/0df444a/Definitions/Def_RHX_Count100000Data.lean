-- Prove2me | Definitions.Def_RHX_Count100000Data
-- name    : RHX_Count100000Data
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:40:26.116856+00:00
-- url     : https://prove2.me/theorems/d67f41b3-47c3-4670-bc31-08e6956bdbac
-- title:
--   Turing-count data for the box up to height 100000
-- statement:
--   Turing-count data for the zeros of $\zeta$ with $121\le\operatorname{Im}\rho\le100000$: two Gamma-factor records (`Arb4.GamD`, at heights $121$ and $100000$) and the enclosure record `Arb4.EnclQ` of the five argument changes on the boundary of the Turing box, including the horizontal enclosure of the edge data `RHX_Edge100000Data`. Checked by the kernel in `RHX100000.Count.chk`, which certifies $n=138031$ zeros in the box.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000) to height 100000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_RHX_Edge100000Data
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Gamma
import Definitions.Def_ArdaRH65K_Turing121_Arb4_H1000Edges_0
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Seg
import Definitions.Def_ArdaRH65K_Turing121_H11K_Turing
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q
namespace RHX100000.Count
noncomputable def G0 : GamD := ⟨Q.ofNat 121, 12, 13, 12, 13, 1, 3, 1, 3⟩
noncomputable def G1 : GamD := ⟨Q.ofNat 100000, 32, 28, 32, 28, 1, 1, 1, 1⟩
noncomputable def E : EnclQ := ⟨Q.frac (-249) 250, Q.frac 249 250,
  RHX100000.Edge.E.Lo, RHX100000.Edge.E.Hi, Arb4.H1000.E_T121.Lo, Arb4.H1000.E_T121.Hi,
  (Q.frac 433633972347 1000000), (Q.frac 433633976486 1000000),
  (Q.frac 433633966157 1000000), (Q.frac 433633970295 1000000)⟩
end RHX100000.Count
def RHX_Count100000Data : Nat := 0


