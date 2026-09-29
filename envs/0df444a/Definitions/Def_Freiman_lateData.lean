-- Prove2me | Definitions.Def_Freiman_lateData
-- name    : Freiman_lateData
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:27:54.101234+00:00
-- url     : https://prove2.me/theorems/9c924a39-b61f-493f-a51a-adc908e88618
-- title:
--   Freiman late: lateData
-- statement:
--   Exact source late decision catalogue, shared-kernel finite validator or actual-cover interface; no theorem/axiom declarations.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateCoreData
import Definitions.Def_Freiman_lateWitnessData1
import Definitions.Def_Freiman_lateWitnessData2
import Definitions.Def_Freiman_lateWitnessData3
import Definitions.Def_Freiman_lateWitnessData4
import Definitions.Def_Freiman_lateWitnessData5
import Definitions.Def_Freiman_lateWitnessData6
import Definitions.Def_Freiman_lateWitnessData7
import Definitions.Def_Freiman_lateWitnessData8
import Definitions.Def_Freiman_lateProofData
import Definitions.Def_Freiman_lateEndpointData
import Definitions.Def_Freiman_latePathData1
import Definitions.Def_Freiman_latePathData2
import Definitions.Def_Freiman_latePathData3
import Definitions.Def_Freiman_latePathData4
import Definitions.Def_Freiman_lateTreeData

set_option maxRecDepth 8000
set_option maxHeartbeats 0

namespace Freiman

def lateCatalog : LateCatalog :=
  ⟨lateBoundData,lateRectangleData,
    lateWitnessData1 ++ lateWitnessData2 ++ lateWitnessData3 ++ lateWitnessData4 ++ lateWitnessData5 ++ lateWitnessData6 ++ lateWitnessData7 ++ lateWitnessData8,
    lateProofData,lateEndpointData,
    latePathData1 ++ latePathData2 ++ latePathData3 ++ latePathData4⟩
def lateRootBounds : List CertBound := lateBounds lateCatalog [17,52,258]
def lateRootRectangle (right3 : Bool) : CertRectangle :=
  ⟨13/17,4/5,1/4,if right3 then 1/3 else 4/5⟩
def lateTree (right3 : Bool) : LateDecisionTree := if right3 then lateRight3Tree else lateOtherTree
def lateWitnessBatch (lo hi : ℕ) : Prop :=
  ∀ i, lo ≤ i → i < hi → certWitnessValid (lateWitness lateCatalog (i+1))
def latePathBatch (lo hi : ℕ) : Prop :=
  ∀ i, lo ≤ i → i < hi → latePathValid lateCatalog (latePath lateCatalog (i+1))


end Freiman


