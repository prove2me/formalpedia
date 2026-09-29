-- Prove2me | Definitions.Def_Freiman_lowerBridgeCatalog
-- name    : Freiman_lowerBridgeCatalog
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:27:35.760407+00:00
-- url     : https://prove2.me/theorems/149e34d6-af5d-4af3-aa30-1a43fb2c7228
-- title:
--   Freiman marked initial bridges: lowerBridgeCatalog
-- statement:
--   Exact source matrices, finite polynomial and endpoint data for the six marked initial bridge cases.
-- source:
--   Freiman report, initial_bridges.tex; certificates/target_selection/H_entry_bridges.json

import Definitions.Def_Freiman_lowerBridgeData_aZero
import Definitions.Def_Freiman_lowerBridgeData_aPos
import Definitions.Def_Freiman_lowerBridgeData_bZero
import Definitions.Def_Freiman_lowerBridgeData_bPos
import Definitions.Def_Freiman_lowerBridgeData_cZero
import Definitions.Def_Freiman_lowerBridgeData_cPos
namespace Freiman
def lowerBridgeRecords : LowerBridgeCase → List LowerBridgeRecord
  | .aZero => lowerBridgeRecords_aZero
  | .aPos => lowerBridgeRecords_aPos
  | .bZero => lowerBridgeRecords_bZero
  | .bPos => lowerBridgeRecords_bPos
  | .cZero => lowerBridgeRecords_cZero
  | .cPos => lowerBridgeRecords_cPos
def lowerBridgeEndpoints : LowerBridgeCase → List LowerBridgeEndpoint
  | .aZero => lowerBridgeEndpoints_aZero
  | .aPos => lowerBridgeEndpoints_aPos
  | .bZero => lowerBridgeEndpoints_bZero
  | .bPos => lowerBridgeEndpoints_bPos
  | .cZero => lowerBridgeEndpoints_cZero
  | .cPos => lowerBridgeEndpoints_cPos
noncomputable def lowerBridgeNumeric (c : LowerBridgeCase) (x y : ℝ) : Prop :=
  ∀ r ∈ lowerBridgeRecords c, 0 < lowerBridgeNumerator c r x y
noncomputable def lowerBridgeFacts (c : LowerBridgeCase) (n k : ℕ) : Prop :=
  ∀ r ∈ lowerBridgeRecords c, lowerBridgeRecordFact c n k r
noncomputable def lowerBridgeEndpointFacts (c : LowerBridgeCase) (n k : ℕ) : Prop :=
  ∀ e ∈ lowerBridgeEndpoints c, lowerBridgeEndpointFact c n k e
noncomputable def lowerBridgeSurvivorLarge (c : LowerBridgeCase) (n k : ℕ) : Prop :=
  let p := lowerBridgePair c n k
  let s := lowerBridgeAppend p ([1],[1])
  lowerNormalize s = s ∧ lowerThreshold s (31/100) 3 63 25 66 ≤ lowerScale s ∧ ¬ lowerA s 9
end Freiman


