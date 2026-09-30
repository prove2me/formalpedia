-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0069PaddedInputs_part00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0069PaddedInputs_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:22:49.915984+00:00
-- url     : https://prove2.me/theorems/5d8ad182-761e-4535-8cf1-bf021f9acac7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0069PaddedInputs (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0069PaddedInputs (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0069PaddedInputs (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0069PaddedInputs (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0069PaddedInputs (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0069StableWitnesses

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0069PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0069StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨1637817266757676828673598708592026054607660640094, 1637817266757676828673598708592026054607694194527⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0069StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0069StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0069StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨676838088292568422841948504387387915570633782618, 676838088292568422841948504387387915570667337051⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0069StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0069StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0069StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨676643340013426075185609328596269506214095417902, 676643340013426075185609328596269506214128972335⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0069StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0069StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0069StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1620903550425908375993486831338272100554110669578, 1654799518693000536357843956327185517074366915700⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0069StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0069StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0069StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨671052481512572809340093335645151882932857337321, 682640618143014187111337022065288110830293046004⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0069StableWitnesses.wholeCInput with alpha := wholeCAlpha }

end GeneralCK.Certificates.E8TAxisZero0069PaddedInputs


