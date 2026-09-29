-- Prove2me | Definitions.Def_Freiman_middleCertRecords
-- name    : Freiman_middleCertRecords
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:09:42.649392+00:00
-- url     : https://prove2.me/theorems/2bbb3c0a-8dca-403f-b57f-3eb8bdc49696
-- title:
--   Freiman M2B: middleCertRecords
-- statement:
--   Exact source model, finite certificate validator, or lossless data. Definitions only; no new axioms or theorem declarations.
-- source:
--   Freiman report (8 September 2026), M2B §§8–9 and complete middle-interval certificate appendix; m2b_readable_model.json, SHA256 a5ac6d3c8e0148e2e3137e8cfa09a2715de6a993dd6ab01eda4842a96bba4cdf.

import Definitions.Def_Freiman_middleCertRecords0
import Definitions.Def_Freiman_middleCertRecords1
import Definitions.Def_Freiman_middleCertRecords2
import Definitions.Def_Freiman_middleCertRecords3
import Definitions.Def_Freiman_middleCertRecords4

namespace Freiman

def middleCertRecords : List MiddleCertRecord :=
  middleCertRecords0 ++ middleCertRecords1 ++ middleCertRecords2 ++ middleCertRecords3 ++ middleCertRecords4

end Freiman


