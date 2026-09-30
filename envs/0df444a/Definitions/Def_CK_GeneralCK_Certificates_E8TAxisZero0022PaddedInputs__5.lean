-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0022PaddedInputs__5
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0022PaddedInputs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T22:08:32.123212+00:00
-- url     : https://prove2.me/theorems/4cd63dbb-f2ea-483c-b63a-a71e6a6027ad
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0022PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisZero0023PaddedInputs, GeneralCK.Certificates.E8TAxisZero0024Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0022PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisZero0023PaddedInputs, GeneralCK.Certificates.E8TAxisZero0024PaddedInputs, GeneralCK.Certificates.E8TAxisZero0025PaddedInputs, GeneralCK.Certificates.E8TAxisZero0026PaddedInputs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0022PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisZero0023PaddedInputs, GeneralCK.Certificates.E8TAxisZero0024PaddedInputs, GeneralCK.Certificates.E8TAxisZero0025PaddedInputs, GeneralCK.Certificates.E8TAxisZero0026PaddedInputs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0022PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisZero0023PaddedInputs, GeneralCK.Certificates.E8TAxisZero0024PaddedInputs, GeneralCK.Certificates.E8TAxisZero0025PaddedInputs, GeneralCK.Certificates.E8TAxisZero0026PaddedInputs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0022PaddedInputs (+4 modules: GeneralCK/Certificates/E8TAxisZero0023PaddedInputs, GeneralCK/Certificates/E8TAxisZero0024PaddedInputs, GeneralCK/Certificates/E8TAxisZero0025PaddedInputs, GeneralCK/Certificates/E8TAxisZero0026PaddedInputs).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0021StableWitnesses__5
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0026StableWitnesses__5

-- ===== source module GeneralCK.Certificates.E8TAxisZero0022PaddedInputs =====
section

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0022PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0022StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨167680817176903094497100275096363859604670211159, 167680817176903094497100275096363859604703765592⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0022StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0022StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0022StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨83840477401825880878169979660152749767455268663, 83840477401825880878169979660152749767488823096⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0022StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0022StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0022StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨83204925566128923103386656610767262849225684246, 83204925566128923103386656610767262849259238679⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0022StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0022StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0022StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨159009523631476834293416684122073812609703309768, 176365549723902348143424292968104815592837804368⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0022StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0022StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0022StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨79233540548598202161862116954926444096855092059, 88449342971355302470485152083509965479366969075⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0022StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisZero0022StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisZero0022StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨79233540548598202161862116954926444096855092059, 87177733031446937316788780256552774640385126639⟩
def wholeDInput : Inputs precision :=
  { E8TAxisZero0022StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisZero0022StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisZero0022StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisZero0022PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0023PaddedInputs =====
section

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0023PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0023StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨151632939129008056697517373665649318183466256282, 151632939129008056697517373665649318183499810715⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0023StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0023StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0023StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨75898626579489180817964566504327908828178423967, 75898626579489180817964566504327908828211978400⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0023StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0023StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0023StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨75263509879409481448600087548378166009112450911, 75263509879409481448600087548378166009146005344⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0023StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0023StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0023StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨142984678294030808430193174439689638732857022308, 160293339111948018245674211080042528839701788999⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0023StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0023StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0023StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨71294765512122033387053971255115540159891437298, 80504233142141611642933172006386671113716596065⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0023StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisZero0023StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisZero0023StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨71294765512122033387053971255115540159891437298, 79233540548598202161862116954926444096888646492⟩
def wholeDInput : Inputs precision :=
  { E8TAxisZero0023StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisZero0023StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisZero0023StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisZero0023PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0024PaddedInputs =====
section

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0024PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0024StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨135626692008785377142630029624202994261538126883, 135626692008785377142630029624202994261571681316⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0024StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0024StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0024StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨67961964551488262188828254855795778735997840476, 67961964551488262188828254855795778736031394909⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0024StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0024StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0024StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨67327239450709848584332901078869677125797090391, 67327239450709848584332901078869677125830644824⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0024StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0024StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0024StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨126999067220414009923202423697912773180580621530, 144265163383122164482546534975845208150916073503⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0024StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0024StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0024StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨63360863746962342702697993485127651995668175417, 72564627903854707163651962613527732691573486132⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0024StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisZero0024StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisZero0024StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨63360863746962342702697993485127651995668175417, 71294765512122033387053971255115540159924991731⟩
def wholeDInput : Inputs precision :=
  { E8TAxisZero0024StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisZero0024StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisZero0024StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisZero0024PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0025PaddedInputs =====
section

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0025PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0025StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨513476891620287433729744816122965384439460858358, 513476891620287433729744816122965384439494412791⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0025StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0025StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0025StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨248701695666007263736444087294378506122778388971, 248701695666007263736444087294378506122811943404⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0025StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0025StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0025StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨248047465841179905852080519169529384371613978394, 248047465841179905852080519169529384371647532827⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0025StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0025StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0025StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨494828875109284674194281948410566590218614111393, 532282228172866116854382691727110279060633539357⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0025StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0025StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0025StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨239878763828786629732963390089367294542231973874, 257544697616875877678682630457661034482258682997⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0025StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisZero0025StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisZero0025StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨239878763828786629732963390089367294542231973874, 256233328382592948799518632260864583083652152500⟩
def wholeDInput : Inputs precision :=
  { E8TAxisZero0025StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisZero0025StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisZero0025StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisZero0025PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0026PaddedInputs =====
section

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0026PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0026StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨477749886812595267904089875359623307557255768053, 477749886812595267904089875359623307557289322486⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0026StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0026StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0026StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨232378217379230243663107254932754002013491934309, 232378217379230243663107254932754002013525488742⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0026StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0026StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0026StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨231726644506236789334274380203310872944632344499, 231726644506236789334274380203310872944665898932⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0026StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0026StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0026StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨459387967798615484561738103898747303530768402213, 496257886122708299080717656232804391559819583790⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0026StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0026StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0026StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨223590532296792858273138350117122513977201034060, 241184626806749055639611155786176124284258311797⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0026StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisZero0026StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisZero0026StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨223590532296792858273138350117122513977201034060, 239878763828786629732963390089367294542265528307⟩
def wholeDInput : Inputs precision :=
  { E8TAxisZero0026StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisZero0026StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisZero0026StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisZero0026PaddedInputs

end


