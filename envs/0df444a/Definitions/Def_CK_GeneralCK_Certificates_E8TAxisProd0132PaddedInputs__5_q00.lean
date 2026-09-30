-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0132PaddedInputs__5_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0132PaddedInputs__5_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T00:06:20.2373+00:00
-- url     : https://prove2.me/theorems/24aa6a7f-e6d6-49aa-8dd9-27501ee07e92
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0133PaddedInputs, GeneralCK.Certificates.E8TAxisProd0134Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0133PaddedInputs, GeneralCK.Certificates.E8TAxisProd0134PaddedInputs, GeneralCK.Certificates.E8TAxisProd0135PaddedInputs, GeneralCK.Certificates.E8TAxisProd0136PaddedInputs) (piece 1 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0133PaddedInputs, GeneralCK.Certificates.E8TAxisProd0134PaddedInputs, GeneralCK.Certificates.E8TAxisProd0135PaddedInputs, GeneralCK.Certificates.E8TAxisProd0136PaddedInputs) (piece 1 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0133PaddedInputs, GeneralCK.Certificates.E8TAxisProd0134PaddedInputs, GeneralCK.Certificates.E8TAxisProd0135PaddedInputs, GeneralCK.Certificates.E8TAxisProd0136PaddedInputs) (piece 1 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK/Certificates/E8TAxisProd0133PaddedInputs, GeneralCK/Certificates/E8TAxisProd0134PaddedInputs, GeneralCK/Certificates/E8TAxisProd0135PaddedInputs, GeneralCK/Certificates/E8TAxisProd0136PaddedInputs) (piece 1 of 5).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0129StableWitnesses__4
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0133StableWitnesses__4

-- ===== source module GeneralCK.Certificates.E8TAxisProd0132PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0132PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0132StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨2216017656540843594568486214625237657012888708, 2216017656540843594568486214625237657013019781⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0132StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0132StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0132StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1095501174999892078111499867170921169955493624056, 1095501174999892078111499867170921169955493755129⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0132StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0132StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0132StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨488409377652419635529576040197023321630283581347, 488409377652419635529576040197023321630283712420⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0132StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0132StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0132StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨485917755434160891773462032334740628415117510306, 485917755434160891773462032334740628415117641379⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0132StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0132StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0132StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230211955, 2532592299075639559542598685704412299858937318⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0132StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0132StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0132StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1071163533946626840883335333769298938372431629277, 1120111434970572534491071289146400107461811361288⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0132StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0132StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0132StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨479168318693266819909468923991435055930292405163, 497687795998397117649244397984432485175960516660⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0132StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0132StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0132StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨477040995173626483635311023942643508471660604503, 494828875109284674194281948410566590218630954146⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0132StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0132StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0132StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0132PaddedInputs

end


