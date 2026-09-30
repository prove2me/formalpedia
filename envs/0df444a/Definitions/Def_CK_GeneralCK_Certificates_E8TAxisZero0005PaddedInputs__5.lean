-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0005PaddedInputs__5
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0005PaddedInputs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T22:17:35.409702+00:00
-- url     : https://prove2.me/theorems/c87a5ad9-a945-44c0-a2f8-d9776653560f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0005PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisZero0006PaddedInputs, GeneralCK.Certificates.E8TAxisZero0007Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0005PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisZero0006PaddedInputs, GeneralCK.Certificates.E8TAxisZero0007PaddedInputs, GeneralCK.Certificates.E8TAxisZero0008PaddedInputs, GeneralCK.Certificates.E8TAxisZero0009PaddedInputs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0005PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisZero0006PaddedInputs, GeneralCK.Certificates.E8TAxisZero0007PaddedInputs, GeneralCK.Certificates.E8TAxisZero0008PaddedInputs, GeneralCK.Certificates.E8TAxisZero0009PaddedInputs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0005PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisZero0006PaddedInputs, GeneralCK.Certificates.E8TAxisZero0007PaddedInputs, GeneralCK.Certificates.E8TAxisZero0008PaddedInputs, GeneralCK.Certificates.E8TAxisZero0009PaddedInputs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0005PaddedInputs (+4 modules: GeneralCK/Certificates/E8TAxisZero0006PaddedInputs, GeneralCK/Certificates/E8TAxisZero0007PaddedInputs, GeneralCK/Certificates/E8TAxisZero0008PaddedInputs, GeneralCK/Certificates/E8TAxisZero0009PaddedInputs).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0005StableWitnesses__5

-- ===== source module GeneralCK.Certificates.E8TAxisZero0005PaddedInputs =====
section

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0005PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0005StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨47188546783399559438734684046034277281537275736, 47188546783399559438734684046034277281570830169⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0005StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0005StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0005StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨24220466060029118896113524058399908749091715764, 24220466060029118896113524058399908749125270197⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0005StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0005StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0005StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨22953787393551632719727143497985289631540024200, 22953787393551632719727143497985289631573578633⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0005StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0005StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0005StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨44336132104644388932745897738796280177165072748, 50041379200560764912647798132580101207521423754⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0005StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0005StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0005StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨22162133741881529770516429908069211989416209757, 26278910172762769820712328120209532577651066928⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0005StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisZero0005StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisZero0005StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨22162133741881529770516429908069211989416209757, 23745456717760790936231587082098894243355536452⟩
def wholeDInput : Inputs precision :=
  { E8TAxisZero0005StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisZero0005StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisZero0005StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisZero0005PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0006PaddedInputs =====
section

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0006PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0006StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨44019221828644720306073496201742716112975451061, 44019221828644720306073496201742716113009005494⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0006StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0006StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0006StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨22637124082456445254227729657395697674858897453, 22637124082456445254227729657395697674892451886⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0006StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0006StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0006StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨21370495222089901813019887143702178164813015270, 21370495222089901813019887143702178164846569703⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0006StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0006StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0006StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨41167241659773099362357909881550147015232376828, 46871591652396955948239255283142047275808173162⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0006StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0006StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0006StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨20578871293540181087774692060534010761915678562, 24695481355850246866248295865805301976361392228⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0006StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisZero0006StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisZero0006StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨20578871293540181087774692060534010761915678562, 22162133741881529770516429908069211989449764190⟩
def wholeDInput : Inputs precision :=
  { E8TAxisZero0006StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisZero0006StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisZero0006StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisZero0006PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0007PaddedInputs =====
section

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0007PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0007StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨40850377929490787525132265847486563880827685064, 40850377929490787525132265847486563880861239497⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0007StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0007StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0007StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨21053843929995845187789694472046872430415469725, 21053843929995845187789694472046872430449024158⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0007StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0007StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0007StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨19787261415618956269193137821462137643282882928, 19787261415618956269193137821462137643316437361⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0007StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0007StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0007StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨37998801077005824018584868335497446470077431658, 43702316363191017940573234188486312291640414803⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0007StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0007StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0007StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨18995665047735116218618892934888584156016955441, 23112119987288769110966614346048366509754229276⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0007StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisZero0007StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisZero0007StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨18995665047735116218618892934888584156016955441, 20578871293540181087774692060534010761949232995⟩
def wholeDInput : Inputs precision :=
  { E8TAxisZero0007StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisZero0007StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisZero0007StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisZero0007PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0008PaddedInputs =====
section

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0008PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0008StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨122848688962441263613203278400959891368573028905, 122848688962441263613203278400959891368606583338⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0008StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0008StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0008StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨61616005372896281097397239346326085284439605754, 61616005372896281097397239346326085284473160187⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0008StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0008StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0008StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨60981562246941182391851692343549914653698857045, 60981562246941182391851692343549914653732411478⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0008StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0008StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0008StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨117424693269005932071068146852707840826712022796, 128276576533857721025787388172632631798962516663⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0008StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0008StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0008StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨58602635770181898821662589353151101542119785776, 64629982951322598580719314150188454126498620355⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0008StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisZero0008StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisZero0008StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨58602635770181898821662589353151101542119785776, 63360863746962342702697993485127651995701729850⟩
def wholeDInput : Inputs precision :=
  { E8TAxisZero0008StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisZero0008StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisZero0008StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisZero0008PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0009PaddedInputs =====
section

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0009PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0009StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨113279450314663153109211311785784474832407254710, 113279450314663153109211311785784474832440809143⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0009StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0009StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0009StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨56858319549409132114990700219771222531243129127, 56858319549409132114990700219771222531276683560⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0009StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0009StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0009StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨56224069662401947129176131245290424868334543482, 56224069662401947129176131245290424868368097915⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0009StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0009StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0009StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨107861900919962465695529931627750650712772291625, 118700586572171500710721487428242681162042080960⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0009StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0009StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0009StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨53845849274430363340356920789158241656361784168, 59871350779906312655059654590921689440172470844⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0009StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisZero0009StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisZero0009StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨53845849274430363340356920789158241656361784168, 58602635770181898821662589353151101542153340209⟩
def wholeDInput : Inputs precision :=
  { E8TAxisZero0009StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisZero0009StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisZero0009StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisZero0009PaddedInputs

end


