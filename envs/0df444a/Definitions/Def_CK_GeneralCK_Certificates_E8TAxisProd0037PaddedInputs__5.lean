-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0037PaddedInputs__5
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0037PaddedInputs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T01:23:18.052982+00:00
-- url     : https://prove2.me/theorems/a387af86-eb52-47ef-a778-c221dc0c8ec6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0037PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0038PaddedInputs, GeneralCK.Certificates.E8TAxisProd0039Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0037PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0038PaddedInputs, GeneralCK.Certificates.E8TAxisProd0039PaddedInputs, GeneralCK.Certificates.E8TAxisProd0040PaddedInputs, GeneralCK.Certificates.E8TAxisProd0041PaddedInputs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0037PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0038PaddedInputs, GeneralCK.Certificates.E8TAxisProd0039PaddedInputs, GeneralCK.Certificates.E8TAxisProd0040PaddedInputs, GeneralCK.Certificates.E8TAxisProd0041PaddedInputs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0037PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0038PaddedInputs, GeneralCK.Certificates.E8TAxisProd0039PaddedInputs, GeneralCK.Certificates.E8TAxisProd0040PaddedInputs, GeneralCK.Certificates.E8TAxisProd0041PaddedInputs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0037PaddedInputs (+4 modules: GeneralCK/Certificates/E8TAxisProd0038PaddedInputs, GeneralCK/Certificates/E8TAxisProd0039PaddedInputs, GeneralCK/Certificates/E8TAxisProd0040PaddedInputs, GeneralCK/Certificates/E8TAxisProd0041PaddedInputs).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0037PaddedInputs__5_q03

-- ===== source module GeneralCK.Certificates.E8TAxisProd0041PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0041PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0041StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230211955, 1899443256066344012630337314537754309230343028⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0041StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0041StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0041StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨250010485980183976055392476858641416483499889473, 250010485980183976055392476858641416483500020546⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0041StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0041StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0041StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨124923588769881387089525846289839825785387635377, 124923588769881387089525846289839825785387766450⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0041StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0041StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0041StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨123008276316677968590567857617524352972070117721, 123008276316677968590567857617524352972070248794⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0041StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0041StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0041StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011124059, 2532592299075639559542598685704412299858937318⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0041StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0041StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0041StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨241184626806749055639611155786176124284241469044, 258856523389556057576596003104549794743303221408⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0041StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0041StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0041StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨120295746166073688299697151201661012754942091761, 129554310903328861618553401759095070205044194088⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0041StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0041StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0041StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨119019592332330079773337734920394720791278175481, 126999067220414009923202423697912773180597464283⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0041StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0041StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0041StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0041PaddedInputs

end


