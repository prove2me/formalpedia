-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0055EndpointWitnesses_q02_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0055EndpointWitnesses_q02_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T23:50:48.444033+00:00
-- url     : https://prove2.me/theorems/a5f6b1ac-0171-46a5-a9cc-197deb86f32d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses (piece 3 of 4) (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses (piece 3 of 4) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses (piece 3 of 4) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses (piece 3 of 4) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0055EndpointWitnesses (piece 3 of 4) (piece 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0055EndpointWitnesses_q02_q00_q01

namespace GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0055Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem wholeCUpper_yBox_eq : (yBox wholeCUpperInput).d0 = wholeCUpperYBox := by decide +kernel

theorem wholeCUpper_contains :
    wholeCUpperYBox.Contains (Y (upper E8TAxisZero0055PaddedInputs.wholeCInput.alpha)) := by
  have e : upper E8TAxisZero0055PaddedInputs.wholeCInput.alpha = ((846558906105246096241254902365722108228395747060 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCUpperInput.alpha.Contains (upper E8TAxisZero0055PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 846558906105246096241254902365722108228395747060
  have h := checked_yBox_d0_contains (i := wholeCUpperInput) (we := wholeCUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCUpper_primitive_checks.1 wholeCUpper_primitive_checks.2 endpointLogTwo_checked
    wholeCUpper_denominators ha
  rw [wholeCUpper_yBox_eq] at h
  exact h

def wholeDLowerAlpha : DyadicInterval precision := ⟨833959591445470778384083818034390997094854557682, 833959591445470778384083818034390997094854557682⟩
def wholeDLowerExp : DyadicInterval precision := ⟨466838367135635595432846250236128803063002005916, 466838367135635595432846250236128803063002136989⟩
def wholeDLowerLog : DyadicInterval precision := ⟨405121100734994108525530084726425876454688285922, 405121100734994108525530084726425876454688387321⟩
end GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses


