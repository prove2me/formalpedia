-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0019StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0019StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:09:05.153216+00:00
-- url     : https://prove2.me/theorems/ca9bbd14-1465-411c-957b-1c19269e17b9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0019StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0020StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0019StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0020StableWitnesses, GeneralCK.Certificates.E8TAxisProd0021StableWitnesses, GeneralCK.Certificates.E8TAxisProd0022StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0019StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0020StableWitnesses, GeneralCK.Certificates.E8TAxisProd0021StableWitnesses, GeneralCK.Certificates.E8TAxisProd0022StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0019StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0020StableWitnesses, GeneralCK.Certificates.E8TAxisProd0021StableWitnesses, GeneralCK.Certificates.E8TAxisProd0022StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0019StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0020StableWitnesses, GeneralCK/Certificates/E8TAxisProd0021StableWitnesses, GeneralCK/Certificates/E8TAxisProd0022StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0019StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0019StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 4432047174048269527644776165804031130864675905⟩
def centerAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1452664369350591901250217311774540050861815457867⟩
def centerALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1008610412272733567070593870872814922068705325217⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨32455008327171042732967145611016798201694283382, 32455008327171042732967145611016798201694283383⟩
def centerDExp : DyadicInterval precision := ⟨1398011947908555347946217879565997676739193473356, 1398011947908555347946217879565997678938216728909⟩
def centerDLog : DyadicInterval precision := ⟨980941059342323278062008541570423721439995577604, 980941059342323278062008541570423723639018833157⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1398011947908555347946217879565997677288949287244, scale precision, 1398011947908555347946217879565997678388460915021, scale precision,
    0, 128, 0, 128, ⟨-64910016654342085465934291222033596978112187156, -64910016654342085465934291222033596978110090003⟩, ⟨-64910016654342085465934291222033595828667043526, -64910016654342085465934291222033595828664946373⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨36889946740468939943174776978895416046777163432, 36889946740468939943174776978895416046777163433⟩
def centerCExp : DyadicInterval precision := ⟨1389553085472617291809897398712689663207251706083, 1389553085472617291809897398712689665406274961636⟩
def centerCLog : DyadicInterval precision := ⟨976611315024410773222649471764038185354918146684, 976611315024410773222649471764038187553941402237⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1389553085472617291809897398712689663757007519971, scale precision, 1389553085472617291809897398712689664856519147748, scale precision,
    0, 128, 0, 128, ⟨-73779893480937879886349553957790832671776553552, -73779893480937879886349553957790832671774456399⟩, ⟨-73779893480937879886349553957790831515334197329, -73779893480937879886349553957790831515332100176⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨69390205142594838798200291691857354333789679219, 69390205142594838798200291691857354333789679220⟩
def centerBExp : DyadicInterval precision := ⟨1329106638031005012173728960669151071506348135501, 1329106638031005012173728960669151073705371391054⟩
def centerBLog : DyadicInterval precision := ⟨945292194179799511554524359338407840009524314682, 945292194179799511554524359338407842208547570235⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1329106638031005012173728960669151072056103949389, scale precision, 1329106638031005012173728960669151073155615577166, scale precision,
    0, 128, 0, 128, ⟨-138780410285189677596400583383714709272098508979, -138780410285189677596400583383714709272096411826⟩, ⟨-138780410285189677596400583383714708063062305051, -138780410285189677596400583383714708063060207898⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨30079440410711523067074041860544926828153469388, 34830775707694518323356855819802492385993843110⟩
def wholeDExp : DyadicInterval precision := ⟨1393474206903787201785230037422771619329955308483, 1402564082875305177309105820725636622954765925773⟩
def wholeDLog : DyadicInterval precision := ⟨978619971033722696354607064598753113312271289775, 983265812352629886822137551849227704024579594240⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1393474206903787201785230037422771619879711122371, scale precision, 1402564082875305177309105820725636622405010111885, scale precision,
    0, 128, 0, 128, ⟨-69661551415389036646713711639604985348582846224, -69661551415389036646713711639604985348580749071⟩, ⟨-60158880821423046134148083721089853083450724046, -60158880821423046134148083721089853083448626893⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨33880443884864586154657489466470909049962329721, 39899813383783773507048465821561279311279824194⟩
def wholeCExp : DyadicInterval precision := ⟨1383841469593821749822064582626245044018339086770, 1395287580650204456423074730230928992028527983824⟩
def wholeCLog : DyadicInterval precision := ⟨973680501901597785353360659766093915976436771482, 979547967462026938251631715868490062496721981465⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1383841469593821749822064582626245044568094900658, scale precision, 1395287580650204456423074730230928991478772169936, scale precision,
    0, 128, 0, 128, ⟨-79799626767567547014096931643122559203168403688, -79799626767567547014096931643122559203166306535⟩, ⟨-67760887769729172309314978932941817524080962267, -67760887769729172309314978932941817524078865114⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨63995409354739664946199090038659955629555415883, 74787193979389146189860982936510283073087858570⟩
def wholeBExp : DyadicInterval precision := ⟨1319326628595087259836155149828061374875966268508, 1338955127168439721994813637441323871166584921605⟩
def wholeBLog : DyadicInterval precision := ⟨940161196319909489509607646905781357862636709800, 950440979888312503733346527924088746223078293996⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1319326628595087259836155149828061375425722082396, scale precision, 1338955127168439721994813637441323870616829107717, scale precision,
    0, 128, 0, 128, ⟨-149574387958778292379721965873020566755176087578, -149574387958778292379721965873020566755173990425⟩, ⟨-127990818709479329892398180077319910659040223103, -127990818709479329892398180077319910659038125950⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0019StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0020StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0020StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4748624479255801076876082777124010865681651338, 4748624479255801076876082777124010865681651339⟩
def centerAExp : DyadicInterval precision := ⟨1452035179538035812075122148102075716455422985340, 1452035179538035812075122148102075718654446240893⟩
def centerALog : DyadicInterval precision := ⟨1008294829281404787796718047455216463185937117999, 1008294829281404787796718047455216465384960373552⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452035179538035812075122148102075717005178799228, scale precision, 1452035179538035812075122148102075718104690427005, scale precision,
    0, 128, 0, 128, ⟨-9497248958511602153752165554248022284704265776, -9497248958511602153752165554248022284702168623⟩, ⟨-9497248958511602153752165554248021178024436730, -9497248958511602153752165554248021178022339577⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨27704057351801426546684601097727000326331977355, 27704057351801426546684601097727000326331977356⟩
def centerDExp : DyadicInterval precision := ⟨1407130684310035281592181556628555966755160121473, 1407130684310035281592181556628555968954183377026⟩
def centerDLog : DyadicInterval precision := ⟨985594243690497964310298929048384649891451124795, 985594243690497964310298929048384652090474380348⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1407130684310035281592181556628555967304915935361, scale precision, 1407130684310035281592181556628555968404427563138, scale precision,
    0, 128, 0, 128, ⟨-55408114703602853093369202195454001223663156543, -55408114703602853093369202195454001223661059390⟩, ⟨-55408114703602853093369202195454000081666850032, -55408114703602853093369202195454000081664752879⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨32455008327171042732967145611016798201694283382, 32455008327171042732967145611016798201694283383⟩
def centerCExp : DyadicInterval precision := ⟨1398011947908555347946217879565997676739193473356, 1398011947908555347946217879565997678938216728909⟩
def centerCLog : DyadicInterval precision := ⟨980941059342323278062008541570423721439995577604, 980941059342323278062008541570423723639018833157⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1398011947908555347946217879565997677288949287244, scale precision, 1398011947908555347946217879565997678388460915021, scale precision,
    0, 128, 0, 128, ⟨-64910016654342085465934291222033596978112187156, -64910016654342085465934291222033596978110090003⟩, ⟨-64910016654342085465934291222033595828667043526, -64910016654342085465934291222033595828664946373⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨60188545809212462208685209789842065762909125936, 60188545809212462208685209789842065762909125937⟩
def centerBExp : DyadicInterval precision := ⟨1345948645971501065352234789101807192187909364573, 1345948645971501065352234789101807194386932620126⟩
def centerBLog : DyadicInterval precision := ⟨954086205956751408227534441305632529992691498484, 954086205956751408227534441305632532191714754037⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1345948645971501065352234789101807192737665178461, scale precision, 1345948645971501065352234789101807193837176806238, scale precision,
    0, 128, 0, 128, ⟨-120377091618424924417370419579684132122772998895, -120377091618424924417370419579684132122770901742⟩, ⟨-120377091618424924417370419579684130928865602004, -120377091618424924417370419579684130928863504851⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1452664369350591901250217311774540050861815457867⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1008610412272733567070593870872814922068705325217⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨25328844546563792145364175869944518712165973939, 30079440410711523067074041860544926828153469389⟩
def wholeDExp : DyadicInterval precision := ⟨1402564082875305177309105820725636620755742670220, 1411711825212582109366700862001636148587605359971⟩
def wholeDLog : DyadicInterval precision := ⟨983265812352629886822137551849227701825556338687, 987926367053698422343402489929183443761757914490⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1402564082875305177309105820725636621305498484108, scale precision, 1411711825212582109366700862001636148037849546083, scale precision,
    0, 128, 0, 128, ⟨-60158880821423046134148083721089854229165250662, -60158880821423046134148083721089854229163153509⟩, ⟨-50657689093127584290728351739889036855187787228, -50657689093127584290728351739889036855185690075⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨29762712307652229783591561590651970335942429619, 35147560547285289813533577747055089042057399322⟩
def wholeCExp : DyadicInterval precision := ⟨1392870258438640800857414402689503949944641751754, 1403172125637897065631203629503689032395757411241⟩
def wholeCLog : DyadicInterval precision := ⟨978310768752074097249526093622470834630947155556, 983576057040503101902968810124604911702402717192⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1392870258438640800857414402689503950494397565642, scale precision, 1403172125637897065631203629503689031846001597353, scale precision,
    0, 128, 0, 128, ⟨-70295121094570579627067155494110178660959969823, -70295121094570579627067155494110178660957872670⟩, ⟨-59525424615304459567183123181303940099276883271, -59525424615304459567183123181303940099274786118⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨55114191349500929383767732776807590001211495094, 65264584814794149197254506924916978438718970035⟩
def wholeBExp : DyadicInterval precision := ⟨1336631634591411248247437940661146183712302894351, 1355327477382912160807407512816259140896722585358⟩
def wholeBLog : DyadicInterval precision := ⟨949227892886577568082084934984416535907032134269, 958960498003603095356594726853619711080259091341⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1336631634591411248247437940661146184262058708239, scale precision, 1355327477382912160807407512816259140346966771470, scale precision,
    0, 128, 0, 128, ⟨-130529169629588298394509013849833957478553762034, -130529169629588298394509013849833957478551664881⟩, ⟨-110228382699001858767535465553615179409601244616, -110228382699001858767535465553615179409599147463⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0020StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0021StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0021StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4115470352964345628383522602588716836376905846, 4115470352964345628383522602588716836376905847⟩
def centerAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453293830838237185210198542808669484539789010133⟩
def centerALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1008926063354791867585944205900164502304869828050⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453293830838237185210198542808669483990033196245, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-8230940705928691256767045205177433119894175747, -8230940705928691256767045205177433119892078594⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨27704057351801426546684601097727000326331977355, 27704057351801426546684601097727000326331977356⟩
def centerDExp : DyadicInterval precision := ⟨1407130684310035281592181556628555966755160121473, 1407130684310035281592181556628555968954183377026⟩
def centerDLog : DyadicInterval precision := ⟨985594243690497964310298929048384649891451124795, 985594243690497964310298929048384652090474380348⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1407130684310035281592181556628555967304915935361, scale precision, 1407130684310035281592181556628555968404427563138, scale precision,
    0, 128, 0, 128, ⟨-55408114703602853093369202195454001223663156543, -55408114703602853093369202195454001223661059390⟩, ⟨-55408114703602853093369202195454000081666850032, -55408114703602853093369202195454000081664752879⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨31821504649359423322722618983161547322615965175, 31821504649359423322722618983161547322615965176⟩
def centerCExp : DyadicInterval precision := ⟨1399224440172204708204023888033290903110946053094, 1399224440172204708204023888033290905309969308647⟩
def centerCLog : DyadicInterval precision := ⟨981560634590771557702031602585231323486566765283, 981560634590771557702031602585231325685590020836⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1399224440172204708204023888033290903660701866982, scale precision, 1399224440172204708204023888033290904760213494759, scale precision,
    0, 128, 0, 128, ⟨-63643009298718846645445237966323095219457527228, -63643009298718846645445237966323095219455430075⟩, ⟨-63643009298718846645445237966323094071008430625, -63643009298718846645445237966323094071006333472⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨59554162296084967707870317227341833954390546995, 59554162296084967707870317227341833954390546996⟩
def centerBExp : DyadicInterval precision := ⟨1347117605813185889804861433291879176112552447434, 1347117605813185889804861433291879178311575702987⟩
def centerBLog : DyadicInterval precision := ⟨954694616069633278708870925214764823030153905670, 954694616069633278708870925214764825229177161223⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1347117605813185889804861433291879176662308261322, scale precision, 1347117605813185889804861433291879177761819889099, scale precision,
    0, 128, 0, 128, ⟨-119108324592169935415740634454683668505217835089, -119108324592169935415740634454683668505215737936⟩, ⟨-119108324592169935415740634454683667312346450047, -119108324592169935415740634454683667312344352894⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4432047174048269527644776165804031130864675905⟩
def wholeAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨25328844546563792145364175869944518712165973939, 30079440410711523067074041860544926828153469389⟩
def wholeDExp : DyadicInterval precision := ⟨1402564082875305177309105820725636620755742670220, 1411711825212582109366700862001636148587605359971⟩
def wholeDLog : DyadicInterval precision := ⟨983265812352629886822137551849227701825556338687, 987926367053698422343402489929183443761757914490⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1402564082875305177309105820725636621305498484108, scale precision, 1411711825212582109366700862001636148037849546083, scale precision,
    0, 128, 0, 128, ⟨-60158880821423046134148083721089854229165250662, -60158880821423046134148083721089854229163153509⟩, ⟨-50657689093127584290728351739889036855187787228, -50657689093127584290728351739889036855185690075⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨29129265822115513773443708134946641963131034570, 34513994673849056249355123398713418481189360347⟩
def wholeCExp : DyadicInterval precision := ⟨1394078409980602946896329831479021586411470776403, 1404388983396149432262332364367156295124654897612⟩
def wholeCLog : DyadicInterval precision := ⟨978929238224557456986699259969584039246976828266, 984196742723007517240480957521358429927539696233⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1394078409980602946896329831479021586961226590291, scale precision, 1404388983396149432262332364367156294574899083724, scale precision,
    0, 128, 0, 128, ⟨-69027989347698112498710246797426837538723980884, -69027989347698112498710246797426837538721883731⟩, ⟨-58258531644231027546887416269893283354150240423, -58258531644231027546887416269893283354148143270⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨54480008401571157749295831407036360590188306111, 64629982951322598580719314150188454126481843139⟩
def wholeBExp : DyadicInterval precision := ⟨1337792902321001359725941128831362487348157711088, 1356504210451292337311685930877116539078304955640⟩
def wholeBLog : DyadicInterval precision := ⟨949834312395558470178147735810135993135986371821, 959570914224339324745622575400247899776644419711⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1337792902321001359725941128831362487897913524976, scale precision, 1356504210451292337311685930877116538528549141752, scale precision,
    0, 128, 0, 128, ⟨-129259965902645197161438628300376908853557712090, -129259965902645197161438628300376908853555614937⟩, ⟨-108960016803142315498591662814072720588069125419, -108960016803142315498591662814072720588067028266⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0021StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0022StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0022StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3165742448647063503620071141085134670978073809⟩
def centerAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1455183847209450510423929547351191477780877052172⟩
def centerALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1009873425488092576137085252579843092274389747387⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨32455008327171042732967145611016798201694283382, 32455008327171042732967145611016798201694283383⟩
def centerDExp : DyadicInterval precision := ⟨1398011947908555347946217879565997676739193473356, 1398011947908555347946217879565997678938216728909⟩
def centerDLog : DyadicInterval precision := ⟨980941059342323278062008541570423721439995577604, 980941059342323278062008541570423723639018833157⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1398011947908555347946217879565997677288949287244, scale precision, 1398011947908555347946217879565997678388460915021, scale precision,
    0, 128, 0, 128, ⟨-64910016654342085465934291222033596978112187156, -64910016654342085465934291222033596978110090003⟩, ⟨-64910016654342085465934291222033595828667043526, -64910016654342085465934291222033595828664946373⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨35622745018205107326113070868805683251490256680, 35622745018205107326113070868805683251490256681⟩
def centerCExp : DyadicInterval precision := ⟨1391964812765862841814176265736250958939657713415, 1391964812765862841814176265736250961138680968968⟩
def centerCLog : DyadicInterval precision := ⟨977847086964261203225477968971348083507633191635, 977847086964261203225477968971348085706656447188⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1391964812765862841814176265736250959489413527303, scale precision, 1391964812765862841814176265736250960588925155080, scale precision,
    0, 128, 0, 128, ⟨-71245490036410214652226141737611367080200910272, -71245490036410214652226141737611367080198813119⟩, ⟨-71245490036410214652226141737611365925762213602, -71245490036410214652226141737611365925760116449⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨68120650460703907603631028339867798629407673613, 68120650460703907603631028339867798629407673614⟩
def centerBExp : DyadicInterval precision := ⟨1331417740697912930412936030295769273953895410666, 1331417740697912930412936030295769276152918666219⟩
def centerBLog : DyadicInterval precision := ⟨946502067483666272179620873663336685652218146239, 946502067483666272179620873663336687851241401792⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1331417740697912930412936030295769274503651224554, scale precision, 1331417740697912930412936030295769275603162852331, scale precision,
    0, 128, 0, 128, ⟨-136241300921407815207262056679735597862285162646, -136241300921407815207262056679735597862283065493⟩, ⟨-136241300921407815207262056679735596655347628962, -136241300921407815207262056679735596655345531809⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨30079440410711523067074041860544926828153469388, 34830775707694518323356855819802492385993843110⟩
def wholeDExp : DyadicInterval precision := ⟨1393474206903787201785230037422771619329955308483, 1402564082875305177309105820725636622954765925773⟩
def wholeDLog : DyadicInterval precision := ⟨978619971033722696354607064598753113312271289775, 983265812352629886822137551849227704024579594240⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1393474206903787201785230037422771619879711122371, scale precision, 1402564082875305177309105820725636622405010111885, scale precision,
    0, 128, 0, 128, ⟨-69661551415389036646713711639604985348582846224, -69661551415389036646713711639604985348580749071⟩, ⟨-60158880821423046134148083721089853083450724046, -60158880821423046134148083721089853083448626893⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨32613386452068186512645484902019899271106700537, 38632454867883059004928015843439109440062491347⟩
def wholeCExp : DyadicInterval precision := ⟨1386243581168110757962356618682828762093889765683, 1397708984828652127800670294526114221743167334430⟩
def wholeCLog : DyadicInterval precision := ⟨974913818515194634191299090803398235106428622793, 980786206259123103316407863840628219988342665728⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1386243581168110757962356618682828762643645579571, scale precision, 1397708984828652127800670294526114221193411520542, scale precision,
    0, 128, 0, 128, ⟨-77264909735766118009856031686878219459727648940, -77264909735766118009856031686878219459725551787⟩, ⟨-65226772904136373025290969804039797967367302749, -65226772904136373025290969804039797967365205596⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨62726345849935814033225453180246540326085371399, 73517107907555267916357274697553514970858694064⟩
def wholeBExp : DyadicInterval precision := ⟨1321621686459769014250747742880888139459938724571, 1341282453225232093451256320206580483955177826172⟩
def wholeBLog : DyadicInterval precision := ⟨941366897326883274359109794961412012905660287160, 951655059784641468691969283733877778235336922766⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1321621686459769014250747742880888140009694538459, scale precision, 1341282453225232093451256320206580483405422012284, scale precision,
    0, 128, 0, 128, ⟨-147034215815110535832714549395107030549660202765, -147034215815110535832714549395107030549658105612⟩, ⟨-125452691699871628066450906360493080053141348386, -125452691699871628066450906360493080053139251233⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0022StableWitnesses

end


