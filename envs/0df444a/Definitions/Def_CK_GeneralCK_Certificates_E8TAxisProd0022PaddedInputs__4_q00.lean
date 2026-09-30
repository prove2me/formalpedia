-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0022PaddedInputs__4_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0022PaddedInputs__4_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T22:41:18.161125+00:00
-- url     : https://prove2.me/theorems/43a9c7ea-4df5-4854-971e-522b15190a77
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0022PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0025PaddedInputs, GeneralCK.Certificates.E8TAxisProd0026Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0022PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0025PaddedInputs, GeneralCK.Certificates.E8TAxisProd0026PaddedInputs, GeneralCK.Certificates.E8TAxisProd0027PaddedInputs) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0022PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0025PaddedInputs, GeneralCK.Certificates.E8TAxisProd0026PaddedInputs, GeneralCK.Certificates.E8TAxisProd0027PaddedInputs) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0022PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0025PaddedInputs, GeneralCK.Certificates.E8TAxisProd0026PaddedInputs, GeneralCK.Certificates.E8TAxisProd0027PaddedInputs) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0022PaddedInputs (+3 modules: GeneralCK/Certificates/E8TAxisProd0025PaddedInputs, GeneralCK/Certificates/E8TAxisProd0026PaddedInputs, GeneralCK/Certificates/E8TAxisProd0027PaddedInputs) (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0019StableWitnesses__4
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0025StableWitnesses__4

-- ===== source module GeneralCK.Certificates.E8TAxisProd0022PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0022PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0022StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978008272, 3165742448647063503620071141085134670978139345⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0022StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0022StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0022StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨68120650460703907603631028339867798629407608077, 68120650460703907603631028339867798629407739150⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0022StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0022StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0022StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨35622745018205107326113070868805683251490191144, 35622745018205107326113070868805683251490322217⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0022StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0022StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0022StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨32455008327171042732967145611016798201694217846, 32455008327171042732967145611016798201694348919⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0022StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0022StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0022StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858806245, 3798893981423257492988718450954299577395530717⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0022StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0022StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0022StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨62726345849935814033225453180246540326085305863, 73517107907555267916357274697553514970858759600⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0022StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0022StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0022StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨32613386452068186512645484902019899271106635001, 38632454867883059004928015843439109440062556883⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0022StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0022StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0022StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨30079440410711523067074041860544926828153403852, 34830775707694518323356855819802492385993908646⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0022StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0022StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0022StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0022PaddedInputs

end


