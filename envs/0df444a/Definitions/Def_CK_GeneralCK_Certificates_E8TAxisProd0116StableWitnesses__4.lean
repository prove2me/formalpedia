-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0116StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0116StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:36:02.15476+00:00
-- url     : https://prove2.me/theorems/fa2bddb9-a3be-4046-a310-6f2a1bbe507d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0116StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0117StableWitnesses, GeneralCK.Certificates.E8TAxisProd01…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0116StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0117StableWitnesses, GeneralCK.Certificates.E8TAxisProd0118StableWitnesses, GeneralCK.Certificates.E8TAxisProd0119StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0116StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0117StableWitnesses, GeneralCK.Certificates.E8TAxisProd0118StableWitnesses, GeneralCK.Certificates.E8TAxisProd0119StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0116StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0117StableWitnesses, GeneralCK.Certificates.E8TAxisProd0118StableWitnesses, GeneralCK.Certificates.E8TAxisProd0119StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0116StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0117StableWitnesses, GeneralCK/Certificates/E8TAxisProd0118StableWitnesses, GeneralCK/Certificates/E8TAxisProd0119StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0116StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0116StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨415811666137855580659299169097621045230774887708, 415811666137855580659299169097621045230774887709⟩
def centerDExp : DyadicInterval precision := ⟨827326924127804017482711149170086570224978765524, 827326924127804017482711149170086572424002021077⟩
def centerDLog : DyadicInterval precision := ⟨655594142802634878792195049006890681368280371847, 655594142802634878792195049006890683567303627400⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨827326924127804017482711149170086570774734579412, scale precision, 827326924127804017482711149170086571874246207189, scale precision,
    0, 128, 0, 128, ⟨-831623332275711161318598338195242091432713491011, -831623332275711161318598338195242091432711393858⟩, ⟨-831623332275711161318598338195242089490388156978, -831623332275711161318598338195242089490386059825⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨421000659291404872566926752102477979269996773205, 421000659291404872566926752102477979269996773206⟩
def centerCExp : DyadicInterval precision := ⟨821472961907043477749209633385636929878984537154, 821472961907043477749209633385636932078007792707⟩
def centerCLog : DyadicInterval precision := ⟨651851383219354185660766460097885566299192619585, 651851383219354185660766460097885568498215875138⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨821472961907043477749209633385636930428740351042, scale precision, 821472961907043477749209633385636931528251978819, scale precision,
    0, 128, 0, 128, ⟨-842001318582809745133853504204955959518077939648, -842001318582809745133853504204955959518075842495⟩, ⟨-842001318582809745133853504204955957561911250327, -842001318582809745133853504204955957561909153174⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨915304636267657328577495315982964216661901117878, 915304636267657328577495315982964216661901117879⟩
def centerBExp : DyadicInterval precision := ⟨417659293270168103863888038246511166508082174531, 417659293270168103863888038246511168707105430084⟩
def centerBLog : DyadicInterval precision := ⟨367364422195503697898543122035584129641242515335, 367364422195503697898543122035584131840265770888⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨417659293270168103863888038246511167057837988419, scale precision, 417659293270168103863888038246511168157349616196, scale precision,
    1, 128, 1, 128, ⟨-1830609272535314657154990631965928435247545997775, -1830609272535314657154990631965928435247543900622⟩, ⟨-1830609272535314657154990631965928431400060570889, -1830609272535314657154990631965928431400058473736⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨407186672849656374487538180028229486749868035095, 424465904280623337412236094991656409259795096050⟩
def wholeDExp : DyadicInterval precision := ⟨817586731060820878424464751762154416938532124195, 837149651842014699656242248506338776332018800396⟩
def wholeDLog : DyadicInterval precision := ⟨649361398245907818978439547465799272052779798379, 661852897083560210399534374966476335226142823792⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨817586731060820878424464751762154417488287938083, scale precision, 837149651842014699656242248506338775782262986508, scale precision,
    0, 128, 0, 128, ⟨-848931808561246674824472189983312819502323703918, -848931808561246674824472189983312819502321606765⟩, ⟨-814373345699312748975076360056458972539969626347, -814373345699312748975076360056458972539967529194⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨412013103369899024069530913214965111556865971996, 430020255848871057996723868378530389896812048619⟩
def wholeCExp : DyadicInterval precision := ⟨811395907539575989205372525227068894781030924708, 831638702309372174108721356206934857236170106854⟩
def wholeCLog : DyadicInterval precision := ⟨645386032564338615019803630851229122526109369488, 658344782481043794267062701001445090928012080338⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨811395907539575989205372525227068895330786738596, scale precision, 831638702309372174108721356206934856686414292966, scale precision,
    0, 128, 0, 128, ⟨-860040511697742115993447736757060780783855703627, -860040511697742115993447736757060780783853606474⟩, ⟨-824026206739798048139061826429930222147605490447, -824026206739798048139061826429930222147603393294⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨892991635890052814963211571405608588618006768387, 937870959556804946741015883093282995250107729342⟩
def wholeBExp : DyadicInterval precision := ⟨404958665886029675189044684123358304031737180909, 430608946303960619457672773392940429561577101744⟩
def wholeBLog : DyadicInterval precision := ⟨357453084290518970416155644033119007745757788890, 377401362481759478917040195805505400787550514175⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨404958665886029675189044684123358304581492994797, scale precision, 430608946303960619457672773392940429011821287856, scale precision,
    1, 128, 1, 128, ⟨-1875741919113609893482031766186565992484293129924, -1875741919113609893482031766186565992484291032771⟩, ⟨-1785983271780105629926423142811217175370124364011, -1785983271780105629926423142811217175370122266858⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0116StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0117StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0117StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨398590295572446657843406049747194007801292752073, 398590295572446657843406049747194007801292752074⟩
def centerDExp : DyadicInterval precision := ⟨847055832185589353041431034353733246155211165949, 847055832185589353041431034353733248354234421502⟩
def centerDLog : DyadicInterval precision := ⟨668137796188982437048462187236859676234037540057, 668137796188982437048462187236859678433060795610⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨847055832185589353041431034353733246704966979837, scale precision, 847055832185589353041431034353733247804478607614, scale precision,
    0, 128, 0, 128, ⟨-797180591144893315686812099494388016551129720247, -797180591144893315686812099494388016551127623094⟩, ⟨-797180591144893315686812099494388014654043385201, -797180591144893315686812099494388014654041288048⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨403744723148441277135090050074019244134916194169, 403744723148441277135090050074019244134916194170⟩
def centerCExp : DyadicInterval precision := ⟨841102057465377917574533816984952581352090136065, 841102057465377917574533816984952583551113391618⟩
def centerCLog : DyadicInterval precision := ⟨664363711516053897070920327650780484668424573478, 664363711516053897070920327650780486867447829031⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨841102057465377917574533816984952581901845949953, scale precision, 841102057465377917574533816984952583001357577730, scale precision,
    0, 128, 0, 128, ⟨-807489446296882554270180100148038489225090905374, -807489446296882554270180100148038489225088808221⟩, ⟨-807489446296882554270180100148038487314575968456, -807489446296882554270180100148038487314573871303⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨871788664855766744352473894216394539310604500141, 871788664855766744352473894216394539310604500142⟩
def centerBExp : DyadicInterval precision := ⟨443286232348120235716611835629455768091049277370, 443286232348120235716611835629455770290072532923⟩
def centerBLog : DyadicInterval precision := ⟨387160877195117264669233447532794904528933965795, 387160877195117264669233447532794906727957221348⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨443286232348120235716611835629455768640805091258, scale precision, 443286232348120235716611835629455769740316719035, scale precision,
    1, 128, 1, 128, ⟨-1743577329711533488704947788432789080433738757171, -1743577329711533488704947788432789080433736660018⟩, ⟨-1743577329711533488704947788432789076808681340548, -1743577329711533488704947788432789076808679243395⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨390021907983024779256146395473341757167804190697, 407186672849656374487538180028229486749868035096⟩
def wholeDExp : DyadicInterval precision := ⟨837149651842014699656242248506338774132995544843, 857046406820575460675375243512252172179026178685⟩
def wholeDLog : DyadicInterval precision := ⟨661852897083560210399534374966476333027119568239, 674448983099953378325059509857368476506693482805⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨837149651842014699656242248506338774682751358731, scale precision, 857046406820575460675375243512252171629270364797, scale precision,
    0, 128, 0, 128, ⟨-814373345699312748975076360056458974459504611190, -814373345699312748975076360056458974459502514037⟩, ⟨-780043815966049558512292790946683513398123413187, -780043815966049558512292790946683513398121316034⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨394816793649930260865803568113874655646762532967, 412703332441082733977165783905492054480561084554⟩
def wholeCExp : DyadicInterval precision := ⟨830853550675597928063445688942458938882655080729, 851441231098437619362828790676466226291122331332⟩
def wholeCLog : DyadicInterval precision := ⟨657844291137148787942630712202797077208820436299, 670911471033301839823247132083422620220362045275⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨830853550675597928063445688942458939432410894617, scale precision, 851441231098437619362828790676466225741366517444, scale precision,
    0, 128, 0, 128, ⟨-825406664882165467954331567810984109928163704513, -825406664882165467954331567810984109928161607360⟩, ⟨-789633587299860521731607136227749310349868475225, -789633587299860521731607136227749310349866378072⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨849960879361055916238778446333942431649780212695, 893861930172627991491266767372472783908120487083⟩
def wholeBExp : DyadicInterval precision := ⟨430096413956172398876677779788961208137853457986, 456727091192909713204266828372060282065009330876⟩
def wholeBLog : DyadicInterval precision := ⟨377005419272419588634950912314011089713515237465, 397437535766550800592075976754544798673564485356⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨430096413956172398876677779788961208687609271874, scale precision, 456727091192909713204266828372060281515253516988, scale precision,
    1, 128, 1, 128, ⟨-1787723860345255982982533534744945569684355766678, -1787723860345255982982533534744945569684353669525⟩, ⟨-1699921758722111832477556892667884861540373027250, -1699921758722111832477556892667884861540370930097⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0117StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0118StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0118StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨415811666137855580659299169097621045230774887708, 415811666137855580659299169097621045230774887709⟩
def centerDExp : DyadicInterval precision := ⟨827326924127804017482711149170086570224978765524, 827326924127804017482711149170086572424002021077⟩
def centerDLog : DyadicInterval precision := ⟨655594142802634878792195049006890681368280371847, 655594142802634878792195049006890683567303627400⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨827326924127804017482711149170086570774734579412, scale precision, 827326924127804017482711149170086571874246207189, scale precision,
    0, 128, 0, 128, ⟨-831623332275711161318598338195242091432713491011, -831623332275711161318598338195242091432711393858⟩, ⟨-831623332275711161318598338195242089490388156978, -831623332275711161318598338195242089490386059825⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨420308180351995148110226404636455053696032799423, 420308180351995148110226404636455053696032799424⟩
def centerCExp : DyadicInterval precision := ⟨822251780522135375352692343768924922948926311145, 822251780522135375352692343768924925147949566698⟩
def centerCLog : DyadicInterval precision := ⟨652349877847418666104474447268036467312632705168, 652349877847418666104474447268036469511655960721⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨822251780522135375352692343768924923498682125033, scale precision, 822251780522135375352692343768924924598193752810, scale precision,
    0, 128, 0, 128, ⟨-840616360703990296220452809272910108369223573274, -840616360703990296220452809272910108369221476121⟩, ⟨-840616360703990296220452809272910106414909721573, -840616360703990296220452809272910106414907624420⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨914424868825717545599751895144306726905349812851, 914424868825717545599751895144306726905349812852⟩
def centerBExp : DyadicInterval precision := ⟨418162425547191965894876268896111020922579449065, 418162425547191965894876268896111023121602704618⟩
def centerBLog : DyadicInterval precision := ⟨367755676724422510828708029442898684025310537450, 367755676724422510828708029442898686224333793003⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨418162425547191965894876268896111021472335262953, scale precision, 418162425547191965894876268896111022571846890730, scale precision,
    1, 128, 1, 128, ⟨-1828849737651435091199503790288613455732128743956, -1828849737651435091199503790288613455732126646803⟩, ⟨-1828849737651435091199503790288613451889272604603, -1828849737651435091199503790288613451889270507450⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨407186672849656374487538180028229486749868035095, 424465904280623337412236094991656409259795096050⟩
def wholeDExp : DyadicInterval precision := ⟨817586731060820878424464751762154416938532124195, 837149651842014699656242248506338776332018800396⟩
def wholeDLog : DyadicInterval precision := ⟨649361398245907818978439547465799272052779798379, 661852897083560210399534374966476335226142823792⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨817586731060820878424464751762154417488287938083, scale precision, 837149651842014699656242248506338775782262986508, scale precision,
    0, 128, 0, 128, ⟨-848931808561246674824472189983312819502323703918, -848931808561246674824472189983312819502321606765⟩, ⟨-814373345699312748975076360056458972539969626347, -814373345699312748975076360056458972539967529194⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨411323059691667375415976645368632603658563266151, 429325287008572579663595987881538496397581761006⟩
def wholeCExp : DyadicInterval precision := ⟨812167939653786128410994438555440938787116588967, 832424384718975191417208266172211458454767397020⟩
def wholeCLog : DyadicInterval precision := ⟨645882374608608025561610737769015378213690196868, 658845440657204564610422431630405642518644215608⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨812167939653786128410994438555440939336872402855, scale precision, 832424384718975191417208266172211457905011583132, scale precision,
    0, 128, 0, 128, ⟨-858650574017145159327191975763076993784453833191, -858650574017145159327191975763076993784451736038⟩, ⟨-822646119383334750831953290737265206351911956639, -822646119383334750831953290737265206351909859486⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨892121725246422063302923523336912933495849445053, 936981187970073304092208690985708409250606247126⟩
def wholeBExp : DyadicInterval precision := ⟨405452049075106252260352819774481035087627552162, 431121863084453300383171023428657878261952163669⟩
def wholeBLog : DyadicInterval precision := ⟨357839368985904470535700043977567938870229166798, 377797495315637019273665804781509368958513761119⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨405452049075106252260352819774481035637383366050, scale precision, 431121863084453300383171023428657877712196349781, scale precision,
    1, 128, 1, 128, ⟨-1873962375940146608184417381971416820482875798484, -1873962375940146608184417381971416820482873701331⟩, ⟨-1784243450492844126605847046673825865128029614981, -1784243450492844126605847046673825865128027517828⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0118StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0119StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0119StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨398590295572446657843406049747194007801292752073, 398590295572446657843406049747194007801292752074⟩
def centerDExp : DyadicInterval precision := ⟨847055832185589353041431034353733246155211165949, 847055832185589353041431034353733248354234421502⟩
def centerDLog : DyadicInterval precision := ⟨668137796188982437048462187236859676234037540057, 668137796188982437048462187236859678433060795610⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨847055832185589353041431034353733246704966979837, scale precision, 847055832185589353041431034353733247804478607614, scale precision,
    0, 128, 0, 128, ⟨-797180591144893315686812099494388016551129720247, -797180591144893315686812099494388016551127623094⟩, ⟨-797180591144893315686812099494388014654043385201, -797180591144893315686812099494388014654041288048⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨403056879099322374103321827626544743921834584085, 403056879099322374103321827626544743921834584086⟩
def centerCExp : DyadicInterval precision := ⟨841894146100976814863975803622318764551610677754, 841894146100976814863975803622318766750633933307⟩
def centerCLog : DyadicInterval precision := ⟨664866377161033971902392717081897086544238368973, 664866377161033971902392717081897088743261624526⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨841894146100976814863975803622318765101366491642, scale precision, 841894146100976814863975803622318766200878119419, scale precision,
    0, 128, 0, 128, ⟨-806113758198644748206643655253089488798028939696, -806113758198644748206643655253089488798026842543⟩, ⟨-806113758198644748206643655253089486889311493800, -806113758198644748206643655253089486889309396647⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨870928076343190402468776520141590039614336434809, 870928076343190402468776520141590039614336434810⟩
def centerBExp : DyadicInterval precision := ⟨443808587920057073844108424110651188252827634124, 443808587920057073844108424110651190451850889677⟩
def centerBLog : DyadicInterval precision := ⟨387561614136485533041224203637973520666233841784, 387561614136485533041224203637973522865257097337⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨443808587920057073844108424110651188802583448012, scale precision, 443808587920057073844108424110651189902095075789, scale precision,
    1, 128, 1, 128, ⟨-1741856152686380804937553040283180081039069309359, -1741856152686380804937553040283180081039067212206⟩, ⟨-1741856152686380804937553040283180077418278527028, -1741856152686380804937553040283180077418276429875⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨390021907983024779256146395473341757167804190697, 407186672849656374487538180028229486749868035096⟩
def wholeDExp : DyadicInterval precision := ⟨837149651842014699656242248506338774132995544843, 857046406820575460675375243512252172179026178685⟩
def wholeDLog : DyadicInterval precision := ⟨661852897083560210399534374966476333027119568239, 674448983099953378325059509857368476506693482805⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨837149651842014699656242248506338774682751358731, scale precision, 857046406820575460675375243512252171629270364797, scale precision,
    0, 128, 0, 128, ⟨-814373345699312748975076360056458974459504611190, -814373345699312748975076360056458974459502514037⟩, ⟨-780043815966049558512292790946683513398123413187, -780043815966049558512292790946683513398121316034⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨394131280415088114324880764542299808171984852989, 412013103369899024069530913214965111556865971997⟩
def wholeCExp : DyadicInterval precision := ⟨831638702309372174108721356206934855037146851301, 852240338090969698012242422231538058144447605840⟩
def wholeCLog : DyadicInterval precision := ⟨658344782481043794267062701001445088728988824785, 671416323310479763794961458183140405442526050520⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨831638702309372174108721356206934855586902665189, scale precision, 852240338090969698012242422231538057594691791952, scale precision,
    0, 128, 0, 128, ⟨-824026206739798048139061826429930224079860494691, -824026206739798048139061826429930224079858397538⟩, ⟨-788262560830176228649761529084599615401197940106, -788262560830176228649761529084599615401195842953⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨849109830422090606343973935201037773517472456718, 892991635890052814963211571405608588618006768388⟩
def wholeBExp : DyadicInterval precision := ⟨430608946303960619457672773392940427362553846191, 457259315758436770561310900026107779872270937124⟩
def wholeBLog : DyadicInterval precision := ⟨377401362481759478917040195805505398588527258622, 397842982298065647982124035381778511934169714187⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨430608946303960619457672773392940427912309660079, scale precision, 457259315758436770561310900026107779322515123236, scale precision,
    1, 128, 1, 128, ⟨-1785983271780105629926423142811217179101904806692, -1785983271780105629926423142811217179101902709539⟩, ⟨-1698219660844181212687947870402075545277805113396, -1698219660844181212687947870402075545277803016243⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0119StableWitnesses

end


