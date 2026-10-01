-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0053EndpointWitnesses_q01_q01_q00_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0053EndpointWitnesses_q01_q01_q00_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T21:25:21.86895+00:00
-- url     : https://prove2.me/theorems/d7638fdd-9426-43c5-8b2f-2c07a0a5d877
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses (piece 2 of 4) (piece 2 of 4) (piece 1 of 3) (piece 3 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses (piece 2 of 4) (piece 2 of 4) (piece 1 of 3) (piece 3 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses (piece 2 of 4) (piece 2 of 4) (piece 1 of 3) (piece 3 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses (piece 2 of 4) (piece 2 of 4) (piece 1 of 3) (piece 3 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0053EndpointWitnesses (piece 2 of 4) (piece 2 of 4) (piece 1 of 3) (piece 3 of 5).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0053EndpointWitnesses_q01_q01_q00_q01

namespace GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0053Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem centerDUpper_contains :
    centerDUpperYBox.Contains (Y (upper E8TAxisZero0053PaddedInputs.centerDInput.alpha)) := by
  have e : upper E8TAxisZero0053PaddedInputs.centerDInput.alpha = ((864539270161105163740168296694370154034046125382 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDUpperInput.alpha.Contains (upper E8TAxisZero0053PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 864539270161105163740168296694370154034046125382
  have h := checked_yBox_d0_contains (i := centerDUpperInput) (we := centerDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDUpper_primitive_checks.1 centerDUpper_primitive_checks.2 endpointLogTwo_checked
    centerDUpper_denominators ha
  rw [centerDUpper_yBox_eq] at h
  exact h

end GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses


