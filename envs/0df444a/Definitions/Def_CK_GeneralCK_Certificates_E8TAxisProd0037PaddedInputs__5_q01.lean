-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0037PaddedInputs__5_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0037PaddedInputs__5_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T00:40:56.015299+00:00
-- url     : https://prove2.me/theorems/a6761b00-6177-4e1c-a19c-cd41670ca2ac
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0037PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0038PaddedInputs, GeneralCK.Certificates.E8TAxisProd0039Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0037PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0038PaddedInputs, GeneralCK.Certificates.E8TAxisProd0039PaddedInputs, GeneralCK.Certificates.E8TAxisProd0040PaddedInputs, GeneralCK.Certificates.E8TAxisProd0041PaddedInputs) (piece 2 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0037PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0038PaddedInputs, GeneralCK.Certificates.E8TAxisProd0039PaddedInputs, GeneralCK.Certificates.E8TAxisProd0040PaddedInputs, GeneralCK.Certificates.E8TAxisProd0041PaddedInputs) (piece 2 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0037PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0038PaddedInputs, GeneralCK.Certificates.E8TAxisProd0039PaddedInputs, GeneralCK.Certificates.E8TAxisProd0040PaddedInputs, GeneralCK.Certificates.E8TAxisProd0041PaddedInputs) (piece 2 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0037PaddedInputs (+4 modules: GeneralCK/Certificates/E8TAxisProd0038PaddedInputs, GeneralCK/Certificates/E8TAxisProd0039PaddedInputs, GeneralCK/Certificates/E8TAxisProd0040PaddedInputs, GeneralCK/Certificates/E8TAxisProd0041PaddedInputs) (piece 2 of 5).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0037PaddedInputs__5_q00

-- ===== source module GeneralCK.Certificates.E8TAxisProd0038PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0038PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0038StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864610368, 4432047174048269527644776165804031130864741441⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0038StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0038StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0038StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨203802040624012852586366857882370360086913538932, 203802040624012852586366857882370360086913670005⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0038StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0038StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0038StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨103562170067272545061760203282565258788806074927, 103562170067272545061760203282565258788806206000⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0038StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0038StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0038StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨99105371957748756558358702025034649328540403453, 99105371957748756558358702025034649328540534526⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0038StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0038StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0038StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395399644, 5065202303167835215808940955361609459283176271⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0038StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0038StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0038StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨195070384091725537299207625964822441604096809461, 212550077699428455989854073007082018901742888303⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0038StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0038StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0038StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨98946240501651460655236999370633104625806373395, 108180484096466973298783154526216413755061565472⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0038StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0038StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0038StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨95127887983717436574352739463518235552733741458, 103084551358829778834915002511195342403115297212⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0038StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0038StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0038StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0038PaddedInputs

end


