-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0132PaddedInputs__5
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0132PaddedInputs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T00:57:02.888927+00:00
-- url     : https://prove2.me/theorems/95354a22-712e-45e6-b601-9ce237238749
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0133PaddedInputs, GeneralCK.Certificates.E8TAxisProd0134Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0133PaddedInputs, GeneralCK.Certificates.E8TAxisProd0134PaddedInputs, GeneralCK.Certificates.E8TAxisProd0135PaddedInputs, GeneralCK.Certificates.E8TAxisProd0136PaddedInputs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0133PaddedInputs, GeneralCK.Certificates.E8TAxisProd0134PaddedInputs, GeneralCK.Certificates.E8TAxisProd0135PaddedInputs, GeneralCK.Certificates.E8TAxisProd0136PaddedInputs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0133PaddedInputs, GeneralCK.Certificates.E8TAxisProd0134PaddedInputs, GeneralCK.Certificates.E8TAxisProd0135PaddedInputs, GeneralCK.Certificates.E8TAxisProd0136PaddedInputs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK/Certificates/E8TAxisProd0133PaddedInputs, GeneralCK/Certificates/E8TAxisProd0134PaddedInputs, GeneralCK/Certificates/E8TAxisProd0135PaddedInputs, GeneralCK/Certificates/E8TAxisProd0136PaddedInputs).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0132PaddedInputs__5_q03

-- ===== source module GeneralCK.Certificates.E8TAxisProd0136PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0136PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0136StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨949721161203312387564849132921065893757532294, 949721161203312387564849132921065893757663367⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0136StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0136StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0136StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1191576947845851287139810413168730921751281509224, 1191576947845851287139810413168730921751281640297⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0136StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0136StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0136StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨522859527575814142947524500459698736552373833253, 522859527575814142947524500459698736552373964326⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0136StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0136StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0136StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨521774884976969249658675544420781985592392290640, 521774884976969249658675544420781985592392421713⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0136StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0136StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0136StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669058530, 1266295042977660303900587558721132456011255132⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0136StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0136StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0136StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1166188388182342115326847483651789008827456481217, 1217239001437486599715214062593104088327201670724⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0136StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0136StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0136StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨513476891620287433729744816122965384439477570038, 532282228172866116854382691727110279060616827677⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0136StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0136StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0136StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨512756788786713314020267203907621024217207591083, 530829944683894805437507571749273968698214498764⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0136StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0136StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0136StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0136PaddedInputs

end


