-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0163PaddedInputs__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0163PaddedInputs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T23:01:25.205231+00:00
-- url     : https://prove2.me/theorems/a4ec215b-4528-4319-9bd7-6a81089b7e58
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0163PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0164PaddedInputs, GeneralCK.Certificates.E8TAxisProd0165Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0163PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0164PaddedInputs, GeneralCK.Certificates.E8TAxisProd0165PaddedInputs, GeneralCK.Certificates.E8TAxisProd0166PaddedInputs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0163PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0164PaddedInputs, GeneralCK.Certificates.E8TAxisProd0165PaddedInputs, GeneralCK.Certificates.E8TAxisProd0166PaddedInputs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0163PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0164PaddedInputs, GeneralCK.Certificates.E8TAxisProd0165PaddedInputs, GeneralCK.Certificates.E8TAxisProd0166PaddedInputs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0163PaddedInputs (+3 modules: GeneralCK/Certificates/E8TAxisProd0164PaddedInputs, GeneralCK/Certificates/E8TAxisProd0165PaddedInputs, GeneralCK/Certificates/E8TAxisProd0166PaddedInputs).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0160StableWitnesses__4
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0164StableWitnesses__4

-- ===== source module GeneralCK.Certificates.E8TAxisProd0163PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0163PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0163StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312195361, 2849167218250950044280193223065006085312326434⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0163StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0163StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0163StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨785082485456542858078616503041718193298230940049, 785082485456542858078616503041718193298231071122⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0163StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0163StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0163StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨367531222026435598338296243856880595918896465916, 367531222026435598338296243856880595918896596989⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0163StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0163StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0163StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨364478458648618710654128585069611790600183034707, 364478458648618710654128585069611790600183165780⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0163StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0163StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0163StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858806245, 3165742448647063503620071141085134670978139345⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0163StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0163StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0163StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨764200081313133845645516728213200410612534926120, 806191676902218350774848309971121500205719119555⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0163StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0163StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0163StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨358721125013013616465942719726870605036528264125, 376369150439637581292147110637812924897628776162⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0163StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0163StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0163StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨356015818146773315735630103594046256346147427244, 372966609392870424646531471060848444542040916117⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0163StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0163StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0163StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0163PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0164PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0164PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0164StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨3482318024844347500022322904444928295572329716, 3482318024844347500022322904444928295572460789⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0164StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0164StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0164StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨745151979234803432679121772194049066083718940144, 745151979234803432679121772194049066083719071217⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0164StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0164StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0164StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨351287653634052115918640421955932629673342345080, 351287653634052115918640421955932629673342476153⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0164StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0164StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0164StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨347578074592523924908318039364714024927705806461, 347578074592523924908318039364714024927705937534⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0164StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0164StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0164StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978008272, 3798893981423257492988718450954299577395530717⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0164StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0164StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0164StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨724691129966073447455472889180408340633634879221, 765829836543995576408455012925101753097866885294⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0164StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0164StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0164StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨342527124855344147975691026216652607152220169794, 360074740751160892894090487962528567327495250140⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0164StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0164StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0164StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨339164617338553850423871699333891257707773844052, 356015818146773315735630103594046256346147558317⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0164StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0164StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0164StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0164PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0165PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0165PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0165StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨3482318024844347500022322904444928295572329716, 3482318024844347500022322904444928295572460789⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0165StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0165StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0165StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨705232195447749529846185115854158530882609448366, 705232195447749529846185115854158530882609579439⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0165StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0165StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0165StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨334463462800637956082555704524588433407429874075, 334463462800637956082555704524588433407430005148⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0165StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0165StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0165StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨330774838385704024446645164332729497941801280695, 330774838385704024446645164332729497941801411768⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0165StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0165StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0165StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978008272, 3798893981423257492988718450954299577395530717⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0165StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0165StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0165StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨685181525156330141608904861608166484527614935606, 725489492374379835709792374714335031090376372255⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0165StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0165StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0165StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨325752084660906962361547582823826438291185288987, 343200084397114651700616511900199179081958805127⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0165StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0165StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0165StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨322408132378444526209018649139695484921606285046, 339164617338553850423871699333891257707773975125⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0165StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0165StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0165StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0165PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0166PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0166PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0166StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312195361, 2849167218250950044280193223065006085312326434⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0166StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0166StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0166StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨744345538749972729491016259880384513359700248924, 744345538749972729491016259880384513359700379997⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0166StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0166StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0166StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨350612832656534878273289350463466381304707987776, 350612832656534878273289350463466381304708118849⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0166StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0166StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0166StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨347578074592523924908318039364714024927705806461, 347578074592523924908318039364714024927705937534⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0166StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0166StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0166StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858806245, 3165742448647063503620071141085134670978139345⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0166StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0166StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0166StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨723893093223027775688689165539107035389142775996, 765014788252282813250131160493631294323377206531⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0166StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0166StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0166StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨341854318407743454016368281757269571767095183763, 359397852428554738106003131332373091015701646594⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0166StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0166StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0166StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨339164617338553850423871699333891257707773844052, 356015818146773315735630103594046256346147558317⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0166StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0166StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0166StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0166PaddedInputs

end


