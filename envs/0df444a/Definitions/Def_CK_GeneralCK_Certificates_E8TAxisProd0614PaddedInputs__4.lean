-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0614PaddedInputs__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0614PaddedInputs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T22:11:42.850454+00:00
-- url     : https://prove2.me/theorems/115e3eec-084e-4149-a327-05abb9751642
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0614PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0615PaddedInputs, GeneralCK.Certificates.E8TAxisProd0616Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0614PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0615PaddedInputs, GeneralCK.Certificates.E8TAxisProd0616PaddedInputs, GeneralCK.Certificates.E8TAxisProd0617PaddedInputs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0614PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0615PaddedInputs, GeneralCK.Certificates.E8TAxisProd0616PaddedInputs, GeneralCK.Certificates.E8TAxisProd0617PaddedInputs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0614PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0615PaddedInputs, GeneralCK.Certificates.E8TAxisProd0616PaddedInputs, GeneralCK.Certificates.E8TAxisProd0617PaddedInputs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0614PaddedInputs (+3 modules: GeneralCK/Certificates/E8TAxisProd0615PaddedInputs, GeneralCK/Certificates/E8TAxisProd0616PaddedInputs, GeneralCK/Certificates/E8TAxisProd0617PaddedInputs).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0612StableWitnesses__3
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0615StableWitnesses__4

-- ===== source module GeneralCK.Certificates.E8TAxisProd0614PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0614PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0614StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨791434261379870553054051158387221052156972690, 791434261379870553054051158387221052157103763⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0614StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0614StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0614StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1638976277612459545604728472016709855628306660503, 1638976277612459545604728472016709855628306791576⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0614StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0614StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0614StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨677617272668662098003396523753343280296455963024, 677617272668662098003396523753343280296456094097⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0614StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0614StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0614StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨676643340013426075185609328596269506214112129582, 676643340013426075185609328596269506214112260655⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0614StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0614StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0614StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669058530, 949721161203312387564849132921065893757663367⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0614StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0614StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0614StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1622057835528132829319400860237386272743903836644, 1655963170159742824113806158995371364429461370879⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0614StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0614StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0614StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨671829398415878916709668185736397735140620168833, 683422088231788273366170897964092704923568965941⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0614StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0614StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0614StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨671052481512572809340093335645151882932874049001, 682249998762477519670394645145297230397519482050⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0614StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0614StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0614StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0614PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0615PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0615PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0615StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨791434261379870553054051158387221052156972690, 791434261379870553054051158387221052157103763⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0615StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0615StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0615StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1605783942493403854348775546974689081446001050286, 1605783942493403854348775546974689081446001181359⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0615StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0615StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0615StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨666445776493314386337445349861623137231736316592, 666445776493314386337445349861623137231736447665⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0615StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0615StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0615StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨665477300625433477361232002502002625345921401583, 665477300625433477361232002502002625345921532656⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0615StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0615StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0615StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669058530, 949721161203312387564849132921065893757663367⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0615StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0615StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0615StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1589003646964395474952013628326868085637101261209, 1622635100284105953974446604147280203381626996765⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0615StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0615StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0615StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨660690260676224183795332600748161552670416480605, 672217970774525288215831189543872211298063833582⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0615StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0615StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0615StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨659917674403335303398947154306570012946021962031, 671052481512572809340093335645151882932874180074⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0615StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0615StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0615StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0615PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0616PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0616PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0616StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨474860522247948771940036538063380708083726959, 474860522247948771940036538063380708083858032⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0616StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0616StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0616StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1705556462727371314097646533383415684499544846102, 1705556462727371314097646533383415684499544977175⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0616StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0616StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0616StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨699756999215241399956480375366813049264509671004, 699756999215241399956480375366813049264509802077⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0616StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0616StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0616StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨699165997627898866254694872768746753397359862099, 699165997627898866254694872768746753397359993172⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0616StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0616StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0616StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨316573674294471837011765157253655004433713100, 633147383168915695688804483341311756669189603⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0616StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0616StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0616StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1688378377367966863591789527183587307558995628580, 1722798026884796605435096683569979212267277896147⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0616StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0616StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0616StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨693904058069515033255127039781986599918628811210, 705627393751618059150757717755430214801700153348⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0616StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0616StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0616StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨693511205829020257423882496604739492695821348878, 704837076587479092158941059188951191105662088375⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0616StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0616StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0616StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0616PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0617PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0617PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0617StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨474860522247948771940036538063380708083726959, 474860522247948771940036538063380708083858032⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0617StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0617StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0617StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1671849052970953610058849103865138337028696223512, 1671849052970953610058849103865138337028696354585⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0617StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0617StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0617StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨688460206550326127935087978212372974843458583150, 688460206550326127935087978212372974843458714223⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0617StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0617StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0617StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨687872580056255843160164202748380391008755393117, 687872580056255843160164202748380391008755524190⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0617StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0617StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0617StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨316573674294471837011765157253655004433713100, 633147383168915695688804483341311756669189603⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0617StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0617StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0617StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1654799518693000536357843956327185517074350072947, 1688964600286453078456680412066824107088343785434⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0617StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0617StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0617StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨682640618143014187111337022065288110830276203251, 694296988583586797328139099438936365019573828732⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0617StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0617StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0617StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨682249998762477519670394645145297230397519350977, 693511205829020257423882496604739492695821479951⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0617StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0617StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0617StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0617PaddedInputs

end


