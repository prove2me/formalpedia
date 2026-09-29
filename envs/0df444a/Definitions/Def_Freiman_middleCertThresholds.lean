-- Prove2me | Definitions.Def_Freiman_middleCertThresholds
-- name    : Freiman_middleCertThresholds
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:09:43.445317+00:00
-- url     : https://prove2.me/theorems/216b72b8-49c2-45c6-9457-a25631b2c2c1
-- title:
--   Freiman M2B: middleCertThresholds
-- statement:
--   Exact source model, finite certificate validator, or lossless data. Definitions only; no new axioms or theorem declarations.
-- source:
--   Freiman report (8 September 2026), M2B §§8–9 and complete middle-interval certificate appendix; m2b_readable_model.json, SHA256 a5ac6d3c8e0148e2e3137e8cfa09a2715de6a993dd6ab01eda4842a96bba4cdf.

import Definitions.Def_Freiman_middleCertThresholds0
import Definitions.Def_Freiman_middleCertThresholds1
import Definitions.Def_Freiman_middleCertThresholds2
import Definitions.Def_Freiman_middleCertThresholds3

namespace Freiman

def middleCertThresholds : List CertThreshold :=
  middleCertThresholds0 ++ middleCertThresholds1 ++ middleCertThresholds2 ++ middleCertThresholds3

end Freiman


