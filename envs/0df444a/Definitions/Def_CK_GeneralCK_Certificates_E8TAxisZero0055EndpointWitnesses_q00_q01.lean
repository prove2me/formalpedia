-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0055EndpointWitnesses_q00_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0055EndpointWitnesses_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T18:56:04.259706+00:00
-- url     : https://prove2.me/theorems/386df5fe-4bac-4dec-b23a-f6a876ecd287
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses (piece 1 of 4) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0055EndpointWitnesses (piece 1 of 4) (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0055EndpointWitnesses_q00_q00

namespace GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0055Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerBUpperExp : DyadicInterval precision := ⟨79701391611912706154252071087807998282733595642, 79701391611912706154252071087807998282733726715⟩
def centerBUpperLog : DyadicInterval precision := ⟨77604090130187952127185934389566887833986037894, 77604090130187952127185934389566887833986164241⟩
def centerBUpperYBox : DyadicInterval precision := ⟨8735669317883806286400587436051357911549738271323, 8735669317883806286400587436051357911549748060407⟩
def centerBUpperInput : Inputs precision :=
  ⟨centerBUpperAlpha, centerBUpperExp, centerBUpperLog, endpointLogTwo⟩
def centerBUpperExpWitness : ExpWitness precision :=
  ⟨79701391611912706154252071087807998282733595642, scale precision, 79701391611912706154252071087807998282733726715, scale precision,
    0, 1024, 0, 1024, ⟨-4251409843413455196286500889210667611569445706777, -4251409843413455196286500889210667611569445704624⟩, ⟨-4251409843413455196286500889210667611569443303263, -4251409843413455196286500889210667611569443301118⟩⟩

theorem centerBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBUpperAlpha) centerBUpperExp centerBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBUpperExp) centerBUpperLog fastLogWitness = true := by decide +kernel

theorem centerBUpper_denominators : DenominatorsPositive centerBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerBUpper_yBox_eq : (yBox centerBUpperInput).d0 = centerBUpperYBox := by decide +kernel

theorem centerBUpper_contains :
    centerBUpperYBox.Contains (Y (upper E8TAxisZero0055PaddedInputs.centerBInput.alpha)) := by
  have e : upper E8TAxisZero0055PaddedInputs.centerBInput.alpha = ((2125704921706727598143250444605333805784722251697 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerBUpperInput.alpha.Contains (upper E8TAxisZero0055PaddedInputs.centerBInput.alpha) := by
    rw [e]; exact point_contains precision 2125704921706727598143250444605333805784722251697
  have h := checked_yBox_d0_contains (i := centerBUpperInput) (we := centerBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerBUpper_primitive_checks.1 centerBUpper_primitive_checks.2 endpointLogTwo_checked
    centerBUpper_denominators ha
  rw [centerBUpper_yBox_eq] at h
  exact h

def centerCLowerAlpha : DyadicInterval precision := ⟨840249077102780541471889978262527100080569423870, 840249077102780541471889978262527100080569423870⟩
def centerCLowerExp : DyadicInterval precision := ⟨462837586478754670543573783851119662872167849639, 462837586478754670543573783851119662872167980712⟩
def centerCLowerLog : DyadicInterval precision := ⟨402085732755486751135426535363361061218229695426, 402085732755486751135426535363361061218229797035⟩
def centerCLowerYBox : DyadicInterval precision := ⟨4368291378203569050362232369535902794218416272875, 4368291378203569050362232369535902794218418230921⟩
def centerCLowerInput : Inputs precision :=
  ⟨centerCLowerAlpha, centerCLowerExp, centerCLowerLog, endpointLogTwo⟩
def centerCLowerExpWitness : ExpWitness precision :=
  ⟨462837586478754670543573783851119662872167849639, scale precision, 462837586478754670543573783851119662872167980712, scale precision,
    0, 1024, 0, 1024, ⟨-1680498154205561082943779956525054200161139056657, -1680498154205561082943779956525054200161139054596⟩, ⟨-1680498154205561082943779956525054200161138642763, -1680498154205561082943779956525054200161138640706⟩⟩

end GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses


