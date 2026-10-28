-- Prove2me | Definitions.Def_ArdaRH65K_Count121Data
-- name    : ArdaRH65K_Count121Data
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:19:28.292756+00:00
-- url     : https://prove2.me/theorems/30f7dffa-6ef7-470f-b054-688fe789be90
-- title:
--   Argument and gamma data for the 121-to-65000 count
-- statement:
--   This bundle records the rational endpoint, gamma, and argument-change enclosures used in one zero-count band. The band endpoints and intended count are
--
--   $$T_0=121,\qquad T_1=65000,\qquad K=85250.$$
--
--   The arithmetic checks and their analytic interpretation are proved separately.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H11K_Turing.lean

import Definitions.Def_ArdaRH65K_Edge65000Data
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Gamma
import Definitions.Def_ArdaRH65K_Turing121_Arb4_H1000Edges_0
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Seg
import Definitions.Def_ArdaRH65K_Turing121_H11K_Turing
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q
namespace H65K.Count121
noncomputable def G0 : GamD := ⟨Q.ofNat 121, 12, 13, 12, 13, 1, 3, 1, 3⟩
noncomputable def G1 : GamD := ⟨Q.ofNat 65000, 30, 7, 30, 7, 1, 1, 1, 1⟩
noncomputable def E : EnclQ := ⟨Q.frac (-249) 250, Q.frac 249 250,
  H65K.Edge.E.Lo, H65K.Edge.E.Hi, Arb4.H1000.E_T121.Lo, Arb4.H1000.E_T121.Hi,
  Q.frac 267820180592 1000000, Q.frac 267820184735 1000000,
  Q.frac 267820174406 1000000, Q.frac 267820178548 1000000⟩
end H65K.Count121
def ArdaRH65K_Count121Data : Nat := 0


