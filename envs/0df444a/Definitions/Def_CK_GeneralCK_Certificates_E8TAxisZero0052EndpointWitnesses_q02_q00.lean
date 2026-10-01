-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0052EndpointWitnesses_q02_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0052EndpointWitnesses_q02_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T00:26:15.012588+00:00
-- url     : https://prove2.me/theorems/4675a155-51f4-4ee9-9238-50a8145364a1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses (piece 3 of 4) (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses (piece 3 of 4) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses (piece 3 of 4) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses (piece 3 of 4) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0052EndpointWitnesses (piece 3 of 4) (piece 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0052EndpointWitnesses_q02_q00_q01

namespace GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0052Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem wholeCUpper_yBox_eq : (yBox wholeCUpperInput).d0 = wholeCUpperYBox := by decide +kernel

theorem wholeCUpper_contains :
    wholeCUpperYBox.Contains (Y (upper E8TAxisZero0052PaddedInputs.wholeCInput.alpha)) := by
  have e : upper E8TAxisZero0052PaddedInputs.wholeCInput.alpha = ((883551905517596028616811380983627993011496644083 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCUpperInput.alpha.Contains (upper E8TAxisZero0052PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 883551905517596028616811380983627993011496644083
  have h := checked_yBox_d0_contains (i := wholeCUpperInput) (we := wholeCUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCUpper_primitive_checks.1 wholeCUpper_primitive_checks.2 endpointLogTwo_checked
    wholeCUpper_denominators ha
  rw [wholeCUpper_yBox_eq] at h
  exact h

def wholeDLowerAlpha : DyadicInterval precision := ⟨870712988176454679833831807012927217752906166802, 870712988176454679833831807012927217752906166802⟩
def wholeDLowerExp : DyadicInterval precision := ⟨443939237141351316813290285207320725578082410616, 443939237141351316813290285207320725578082541689⟩
def wholeDLowerLog : DyadicInterval precision := ⟨387661827478115861734404726101104696717286354130, 387661827478115861734404726101104696717286456721⟩
end GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses


