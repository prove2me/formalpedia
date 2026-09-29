-- Prove2me | Definitions.Def_Freiman_trunkData
-- name    : Freiman_trunkData
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:23:33.799742+00:00
-- url     : https://prove2.me/theorems/77bc190b-494e-4040-ace9-7914167de86c
-- title:
--   trunkData
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkBoundData
import Definitions.Def_Freiman_trunkWitnessData01
import Definitions.Def_Freiman_trunkWitnessData02
import Definitions.Def_Freiman_trunkWitnessData03
import Definitions.Def_Freiman_trunkWitnessData04
import Definitions.Def_Freiman_trunkWitnessData05
import Definitions.Def_Freiman_trunkWitnessData06
import Definitions.Def_Freiman_trunkWitnessData07
import Definitions.Def_Freiman_trunkWitnessData08
import Definitions.Def_Freiman_trunkWitnessData09
import Definitions.Def_Freiman_trunkWitnessData10
import Definitions.Def_Freiman_trunkWitnessData11
import Definitions.Def_Freiman_trunkWitnessData12
import Definitions.Def_Freiman_trunkWitnessData13
import Definitions.Def_Freiman_trunkWitnessData14
import Definitions.Def_Freiman_trunkWitnessData15
import Definitions.Def_Freiman_trunkWitnessData16
import Definitions.Def_Freiman_trunkWitnessData17
import Definitions.Def_Freiman_trunkWitnessData18
import Definitions.Def_Freiman_trunkWitnessData19
import Definitions.Def_Freiman_trunkWitnessData20
import Definitions.Def_Freiman_trunkWitnessData21
import Definitions.Def_Freiman_trunkWitnessData22
import Definitions.Def_Freiman_trunkWitnessData23
import Definitions.Def_Freiman_trunkWitnessData24
import Definitions.Def_Freiman_trunkWitnessData25
import Definitions.Def_Freiman_trunkWitnessData26
import Definitions.Def_Freiman_trunkWitnessData27
import Definitions.Def_Freiman_trunkWitnessData28
import Definitions.Def_Freiman_trunkWitnessData29
import Definitions.Def_Freiman_trunkWitnessData30
import Definitions.Def_Freiman_trunkWitnessData31
import Definitions.Def_Freiman_trunkWitnessData32
import Definitions.Def_Freiman_trunkWitnessData33
import Definitions.Def_Freiman_trunkWitnessData34
import Definitions.Def_Freiman_trunkWitnessData35
import Definitions.Def_Freiman_trunkStateData00
import Definitions.Def_Freiman_trunkStateData01
import Definitions.Def_Freiman_trunkStateData02
import Definitions.Def_Freiman_trunkStateData03
import Definitions.Def_Freiman_trunkStateData04
import Definitions.Def_Freiman_trunkStateData05
import Definitions.Def_Freiman_trunkStateData06
import Definitions.Def_Freiman_trunkStateData07
import Definitions.Def_Freiman_trunkStateData08
import Definitions.Def_Freiman_trunkStateData09
import Definitions.Def_Freiman_trunkStateData10
import Definitions.Def_Freiman_trunkStateData11
import Definitions.Def_Freiman_trunkStateData12
import Definitions.Def_Freiman_trunkStateData13
import Definitions.Def_Freiman_trunkStateData14
import Definitions.Def_Freiman_trunkStateData15

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def trunkDataWitnesses : Array TrunkWitness := trunkWitnessData01 ++ trunkWitnessData02 ++ trunkWitnessData03 ++ trunkWitnessData04 ++ trunkWitnessData05 ++ trunkWitnessData06 ++ trunkWitnessData07 ++ trunkWitnessData08 ++ trunkWitnessData09 ++ trunkWitnessData10 ++ trunkWitnessData11 ++ trunkWitnessData12 ++ trunkWitnessData13 ++ trunkWitnessData14 ++ trunkWitnessData15 ++ trunkWitnessData16 ++ trunkWitnessData17 ++ trunkWitnessData18 ++ trunkWitnessData19 ++ trunkWitnessData20 ++ trunkWitnessData21 ++ trunkWitnessData22 ++ trunkWitnessData23 ++ trunkWitnessData24 ++ trunkWitnessData25 ++ trunkWitnessData26 ++ trunkWitnessData27 ++ trunkWitnessData28 ++ trunkWitnessData29 ++ trunkWitnessData30 ++ trunkWitnessData31 ++ trunkWitnessData32 ++ trunkWitnessData33 ++ trunkWitnessData34 ++ trunkWitnessData35

def trunkCatalog : TrunkCatalog :=
  ⟨trunkDataBounds,trunkDataWitnesses,![trunkStateData00,trunkStateData01,trunkStateData02,trunkStateData03,trunkStateData04,trunkStateData05,trunkStateData06,trunkStateData07,trunkStateData08,trunkStateData09,trunkStateData10,trunkStateData11,trunkStateData12,trunkStateData13,trunkStateData14,trunkStateData15]⟩
end Freiman


