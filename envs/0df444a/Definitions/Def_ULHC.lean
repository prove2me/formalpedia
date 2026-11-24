-- Prove2me | Definitions.Def_ULHC
-- name    : ULHC
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:46:28.991801+00:00
-- url     : https://prove2.me/theorems/6fe9c518-9c2a-4306-8281-550a39962d3e
-- title:
--   ULHC
-- statement:
--   Definitions and structural lemmas for ULHC, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC.lean

import Definitions.Def_ULHC_Grid
import Definitions.Def_ULHC_Potential
import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn
import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
import Definitions.Def_ULHC_Iso
import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
import Definitions.Def_ULHC_Phase
import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_TheoremA
import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_TwoFactor
import Definitions.Def_ULHC_Comp
import Definitions.Def_ULHC_Reroute
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Cr2
import Definitions.Def_ULHC_CrPath
import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Definitions.Def_ULHC_Stacked
import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_PathComplete
import Definitions.Def_ULHC_CostAlg
import Definitions.Def_ULHC_Main
import Definitions.Def_ULHC_Timed_Alg
set_option autoImplicit true


