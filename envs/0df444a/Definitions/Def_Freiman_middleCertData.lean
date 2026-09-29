-- Prove2me | Definitions.Def_Freiman_middleCertData
-- name    : Freiman_middleCertData
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:18:47.058637+00:00
-- url     : https://prove2.me/theorems/47f6f55a-9860-4487-89ce-ed50e136f4b0
-- title:
--   Freiman M2B: middleCertData
-- statement:
--   Exact source model, finite certificate validator, or lossless data. Definitions only; no new axioms or theorem declarations.
-- source:
--   Freiman report (8 September 2026), M2B §§8–9 and complete middle-interval certificate appendix; m2b_readable_model.json, SHA256 a5ac6d3c8e0148e2e3137e8cfa09a2715de6a993dd6ab01eda4842a96bba4cdf.

import Definitions.Def_Freiman_middleCertTails
import Definitions.Def_Freiman_middleCertThresholds
import Definitions.Def_Freiman_middleCertEndpoints
import Definitions.Def_Freiman_middleCertParents
import Definitions.Def_Freiman_middleCertGoals
import Definitions.Def_Freiman_middleCertProofs
import Definitions.Def_Freiman_middleCertWitnesses
import Definitions.Def_Freiman_middleCertRecords

namespace Freiman

def middleCertData : MiddleCertCatalog :=
  ⟨middleCertTails,middleCertThresholds,middleCertEndpoints,middleCertParents,
    middleCertGoals,middleCertProofs,middleCertWitnesses,middleCertRecords⟩

end Freiman


