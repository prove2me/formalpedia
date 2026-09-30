-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051PaddedInputs__4
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0051PaddedInputs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T23:01:31.564377+00:00
-- url     : https://prove2.me/theorems/f721ef09-84cc-448c-b728-392c580dd2dd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0051PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisZero0052PaddedInputs, GeneralCK.Certificates.E8TAxisZero0053Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0051PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisZero0052PaddedInputs, GeneralCK.Certificates.E8TAxisZero0053PaddedInputs, GeneralCK.Certificates.E8TAxisZero0054PaddedInputs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0051PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisZero0052PaddedInputs, GeneralCK.Certificates.E8TAxisZero0053PaddedInputs, GeneralCK.Certificates.E8TAxisZero0054PaddedInputs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0051PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisZero0052PaddedInputs, GeneralCK.Certificates.E8TAxisZero0053PaddedInputs, GeneralCK.Certificates.E8TAxisZero0054PaddedInputs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0051PaddedInputs (+3 modules: GeneralCK/Certificates/E8TAxisZero0052PaddedInputs, GeneralCK/Certificates/E8TAxisZero0053PaddedInputs, GeneralCK/Certificates/E8TAxisZero0054PaddedInputs).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0049StableWitnesses__5
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0054StableWitnesses__4

-- ===== source module GeneralCK.Certificates.E8TAxisZero0051PaddedInputs =====
section

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0051PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0051StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨2270908830027593634566325072869940492360113982922, 2270908830027593634566325072869940492360147537355⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0051StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0051StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0051StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨889568579085315104981341544877329197109774493106, 889568579085315104981341544877329197109808047539⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0051StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0051StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0051StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨889351442612263296687940979624415955523286579636, 889351442612263296687940979624415955523320134069⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0051StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0051StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0051StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2252344891692604840925366006970977595417093300754, 2289498348206320816860169387570737970765270107519⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0051StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0051StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0051StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨883118980747789020882084464779538700246857628050, 896039345883247891012692341783045457574250700463⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0051StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisZero0051StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisZero0051StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨883118980747789020882084464779538700246857628050, 895603670620266646532188138393358736598424840854⟩
def wholeDInput : Inputs precision :=
  { E8TAxisZero0051StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisZero0051StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisZero0051StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisZero0051PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0052PaddedInputs =====
section

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0052PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0052StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨2234440797417960962512456499575835485272377238850, 2234440797417960962512456499575835485272410793283⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0052StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0052StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0052StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨877121961275332815348515408942289040848478547603, 877121961275332815348515408942289040848512102036⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0052StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0052StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0052StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨876906193579724784222253173988686333103939287496, 876906193579724784222253173988686333103972841929⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0052StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0052StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0052StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2215929949949202375694063104874887815254848160424, 2252979123662759141363780668401055367421000105189⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0052StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0052StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0052StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨870712988176454679833831807012927217752906166802, 883551905517596028616811380983627993011496644083⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0052StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisZero0052StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisZero0052StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨870712988176454679833831807012927217752906166802, 883118980747789020882084464779538700246891182483⟩
def wholeDInput : Inputs precision :=
  { E8TAxisZero0052StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisZero0052StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisZero0052StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisZero0052PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0053PaddedInputs =====
section

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0053PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0053StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨2198078974265077670796151698551412219080296043584, 2198078974265077670796151698551412219080329598017⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0053StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0053StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0053StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨864753682105473134926531948268092697857242845477, 864753682105473134926531948268092697857276399910⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0053StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0053StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0053StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨864539270161105163740168296694370154034012570949, 864539270161105163740168296694370154034046125382⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0053StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0053StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0053StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2179625075014223488918515620806299281281264036138, 2216562335033091387254814734775112079611626366410⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0053StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0053StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0053StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨858384943750592238779991986336301839154799216100, 871143188090492117311131821217990885949995114836⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0053StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisZero0053StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisZero0053StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨858384943750592238779991986336301839154799216100, 870712988176454679833831807012927217752939721235⟩
def wholeDInput : Inputs precision :=
  { E8TAxisZero0053StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisZero0053StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisZero0053StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisZero0053PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0054PaddedInputs =====
section

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0054PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0054StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨2161831022368146643392260577941081767660351386648, 2161831022368146643392260577941081767660384941081⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0054StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0054StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0054StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨852462981405285549387058583896780795777561794292, 852462981405285549387058583896780795777595348725⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0054StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0054StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0054StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨852249911794452062012049136358764955095117012268, 852249911794452062012049136358764955095150566701⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0054StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0054StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0054StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2143438091420645379159908740123291916485695580991, 2180255479959191032916878577759762122612930269664⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0054StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0054StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0054StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨846134075813431409586727826645377644661755192554, 858812445251375397578851393656460285506904066872⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0054StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisZero0054StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisZero0054StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨846134075813431409586727826645377644661755192554, 858384943750592238779991986336301839154832770533⟩
def wholeDInput : Inputs precision :=
  { E8TAxisZero0054StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisZero0054StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisZero0054StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisZero0054PaddedInputs

end


