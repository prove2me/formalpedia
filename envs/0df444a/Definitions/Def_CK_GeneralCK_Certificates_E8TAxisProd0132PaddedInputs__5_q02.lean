-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0132PaddedInputs__5_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0132PaddedInputs__5_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T00:25:49.240392+00:00
-- url     : https://prove2.me/theorems/4830e098-ca1c-448c-a13f-86e1b1801747
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0133PaddedInputs, GeneralCK.Certificates.E8TAxisProd0134Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0133PaddedInputs, GeneralCK.Certificates.E8TAxisProd0134PaddedInputs, GeneralCK.Certificates.E8TAxisProd0135PaddedInputs, GeneralCK.Certificates.E8TAxisProd0136PaddedInputs) (piece 3 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0133PaddedInputs, GeneralCK.Certificates.E8TAxisProd0134PaddedInputs, GeneralCK.Certificates.E8TAxisProd0135PaddedInputs, GeneralCK.Certificates.E8TAxisProd0136PaddedInputs) (piece 3 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0133PaddedInputs, GeneralCK.Certificates.E8TAxisProd0134PaddedInputs, GeneralCK.Certificates.E8TAxisProd0135PaddedInputs, GeneralCK.Certificates.E8TAxisProd0136PaddedInputs) (piece 3 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK/Certificates/E8TAxisProd0133PaddedInputs, GeneralCK/Certificates/E8TAxisProd0134PaddedInputs, GeneralCK/Certificates/E8TAxisProd0135PaddedInputs, GeneralCK/Certificates/E8TAxisProd0136PaddedInputs) (piece 3 of 5).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0132PaddedInputs__5_q01

-- ===== source module GeneralCK.Certificates.E8TAxisProd0134PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0134PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0134StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨1582869063071984205522252427078437298396856442, 1582869063071984205522252427078437298396987515⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0134StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0134StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0134StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1094541628866367962985536806328740593267704903503, 1094541628866367962985536806328740593267705034576⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0134StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0134StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0134StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨487697209886689993354265177427928986880810292280, 487697209886689993354265177427928986880810423353⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0134StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0134StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0134StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨485917755434160891773462032334740628415117510306, 485917755434160891773462032334740628415117641379⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0134StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0134StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0134StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011124059, 1899443256066344012630337314537754309230343028⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0134StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0134StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0134StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1070214655428945250809954185107274242530860661103, 1119141178981667648123611132975238308851399615129⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0134StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0134StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0134StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨478458994542216572420101618630227318965760365739, 496972728536424257573486884023855659610055976894⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0134StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0134StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0134StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨477040995173626483635311023942643508471660604503, 494828875109284674194281948410566590218630954146⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0134StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0134StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0134StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0134PaddedInputs

end


