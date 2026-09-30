-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0022PaddedInputs__4_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0022PaddedInputs__4_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T22:51:36.264653+00:00
-- url     : https://prove2.me/theorems/dd3b42ad-9189-44e5-95b0-9e8fb6cbc3a7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0022PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0025PaddedInputs, GeneralCK.Certificates.E8TAxisProd0026Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0022PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0025PaddedInputs, GeneralCK.Certificates.E8TAxisProd0026PaddedInputs, GeneralCK.Certificates.E8TAxisProd0027PaddedInputs) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0022PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0025PaddedInputs, GeneralCK.Certificates.E8TAxisProd0026PaddedInputs, GeneralCK.Certificates.E8TAxisProd0027PaddedInputs) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0022PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0025PaddedInputs, GeneralCK.Certificates.E8TAxisProd0026PaddedInputs, GeneralCK.Certificates.E8TAxisProd0027PaddedInputs) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0022PaddedInputs (+3 modules: GeneralCK/Certificates/E8TAxisProd0025PaddedInputs, GeneralCK/Certificates/E8TAxisProd0026PaddedInputs, GeneralCK/Certificates/E8TAxisProd0027PaddedInputs) (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0022PaddedInputs__4_q00

-- ===== source module GeneralCK.Certificates.E8TAxisProd0025PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0025PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0025StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230211955, 1899443256066344012630337314537754309230343028⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0025StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0025StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0025StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨85906275728821593024606426695861450515629701701, 85906275728821593024606426695861450515629832774⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0025StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0025StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0025StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨43860768496766159427869749838833067361716021889, 43860768496766159427869749838833067361716152962⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0025StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0025StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0025StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨41959420742712281670701379146144140997527230907, 41959420742712281670701379146144140997527361980⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0025StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0025StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0025StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011124059, 2532592299075639559542598685704412299858937318⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0025StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0025StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0025StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨80504233142141611642933172006386671113699753312, 91311034991450526690257298210518105305139577815⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0025StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0025StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0025StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨40850377929490787525132265847486563880844396744, 46871591652396955948239255283142047275791461482⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0025StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0025StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0025StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨39582967301423713423413965103485819080159404912, 44336132104644388932745897738796280177181915501⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0025StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0025StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0025StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0025PaddedInputs

end


