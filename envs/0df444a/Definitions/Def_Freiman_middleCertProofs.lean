-- Prove2me | Definitions.Def_Freiman_middleCertProofs
-- name    : Freiman_middleCertProofs
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:09:30.763219+00:00
-- url     : https://prove2.me/theorems/1d2d4630-d50b-4fca-a3b3-9098a8e4e794
-- title:
--   Freiman M2B: middleCertProofs
-- statement:
--   Exact source model, finite certificate validator, or lossless data. Definitions only; no new axioms or theorem declarations.
-- source:
--   Freiman report (8 September 2026), M2B §§8–9 and complete middle-interval certificate appendix; m2b_readable_model.json, SHA256 a5ac6d3c8e0148e2e3137e8cfa09a2715de6a993dd6ab01eda4842a96bba4cdf.

import Definitions.Def_Freiman_middleCertProofs0
import Definitions.Def_Freiman_middleCertProofs1
import Definitions.Def_Freiman_middleCertProofs2

namespace Freiman

def middleCertProofs : List MiddleCertProof :=
  middleCertProofs0 ++ middleCertProofs1 ++ middleCertProofs2

end Freiman


