-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0441PaddedInputs__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0441PaddedInputs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:49:40.792731+00:00
-- url     : https://prove2.me/theorems/7b7c2db0-f6b6-41bb-aa7e-f68b2241a19f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0441PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0442PaddedInputs, GeneralCK.Certificates.E8TAxisProd0443Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0441PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0442PaddedInputs, GeneralCK.Certificates.E8TAxisProd0443PaddedInputs, GeneralCK.Certificates.E8TAxisProd0444PaddedInputs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0441PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0442PaddedInputs, GeneralCK.Certificates.E8TAxisProd0443PaddedInputs, GeneralCK.Certificates.E8TAxisProd0444PaddedInputs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0441PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0442PaddedInputs, GeneralCK.Certificates.E8TAxisProd0443PaddedInputs, GeneralCK.Certificates.E8TAxisProd0444PaddedInputs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0441PaddedInputs (+3 modules: GeneralCK/Certificates/E8TAxisProd0442PaddedInputs, GeneralCK/Certificates/E8TAxisProd0443PaddedInputs, GeneralCK/Certificates/E8TAxisProd0444PaddedInputs).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0441PaddedInputs__4_q02

-- ===== source module GeneralCK.Certificates.E8TAxisProd0444PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0444PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0444StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨474860522247948771940036538063380708083726959, 474860522247948771940036538063380708083858032⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0444StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0444StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0444StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1842739263080707481383814258374794682881764212876, 1842739263080707481383814258374794682881764343949⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0444StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0444StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0444StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨745605748652116474316382937620362335642460134859, 745605748652116474316382937620362335642460265932⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0444StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0444StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0444StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨745000746231477256788872225997272556554271654647, 745000746231477256788872225997272556554271785720⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0444StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0444StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0444StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨316573674294471837011765157253655004433713100, 633147383168915695688804483341311756669189603⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0444StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0444StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0444StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1825097555394958903314865090464227326945826512711, 1860434064699739997035476645245395239720023361965⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0444StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0444StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0444StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨739614424302254009127841865748253801302561830759, 751615544201671264255581054823251973363364379992⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0444StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0444StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0444StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨739212305620516788391447838602016614455786913409, 750806424999049798752938234956163650116084066834⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0444StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0444StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0444StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0444PaddedInputs

end


