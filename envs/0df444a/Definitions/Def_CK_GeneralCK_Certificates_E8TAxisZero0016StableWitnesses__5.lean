-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0016StableWitnesses__5
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0016StableWitnesses__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:27:01.395033+00:00
-- url     : https://prove2.me/theorems/e15a9be9-4c2e-47ff-a97d-c8b3fd656104
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0016StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0017StableWitnesses, GeneralCK.Certificates.E8TAxisZero00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0016StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0017StableWitnesses, GeneralCK.Certificates.E8TAxisZero0018StableWitnesses, GeneralCK.Certificates.E8TAxisZero0019StableWitnesses, GeneralCK.Certificates.E8TAxisZero0020StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0016StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0017StableWitnesses, GeneralCK.Certificates.E8TAxisZero0018StableWitnesses, GeneralCK.Certificates.E8TAxisZero0019StableWitnesses, GeneralCK.Certificates.E8TAxisZero0020StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0016StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0017StableWitnesses, GeneralCK.Certificates.E8TAxisZero0018StableWitnesses, GeneralCK.Certificates.E8TAxisZero0019StableWitnesses, GeneralCK.Certificates.E8TAxisZero0020StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0016StableWitnesses (+4 modules: GeneralCK/Certificates/E8TAxisZero0017StableWitnesses, GeneralCK/Certificates/E8TAxisZero0018StableWitnesses, GeneralCK/Certificates/E8TAxisZero0019StableWitnesses, GeneralCK/Certificates/E8TAxisZero0020StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0016StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0016StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨26516430580118506903128854198095173449986498411, 26516430580118506903128854198095173449986498412⟩
def centerDExp : DyadicInterval precision := ⟨1409419432745952657043289959536708377428786541143, 1409419432745952657043289959536708379627809796696⟩
def centerDLog : DyadicInterval precision := ⟨986759843010006569375564672930469553051891220885, 986759843010006569375564672930469555250914476438⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1409419432745952657043289959536708377978542355031, scale precision, 1409419432745952657043289959536708379078053982808, scale precision,
    0, 128, 0, 128, ⟨-53032861160237013806257708396190347470044957907, -53032861160237013806257708396190347470042860754⟩, ⟨-53032861160237013806257708396190346329903132893, -53032861160237013806257708396190346329901035740⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨26833126993932681256674390662338809660933212144, 26833126993932681256674390662338809660933212145⟩
def centerCExp : DyadicInterval precision := ⟨1408808743903677167729515991161945661329334941086, 1408808743903677167729515991161945663528358196639⟩
def centerCLog : DyadicInterval precision := ⟨986448926178375413202383945804188571453345590715, 986448926178375413202383945804188573652368846268⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1408808743903677167729515991161945661879090754974, scale precision, 1408808743903677167729515991161945662978602382751, scale precision,
    0, 128, 0, 128, ⟨-53666253987865362513348781324677619892185499077, -53666253987865362513348781324677619892183401924⟩, ⟨-53666253987865362513348781324677618751549446657, -53666253987865362513348781324677618751547349504⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨53370245394433761539404939910283149997486243189, 53370245394433761539404939910283149997486243190⟩
def centerBExp : DyadicInterval precision := ⟨1358565846000905640574303170236611544459701108189, 1358565846000905640574303170236611546658724363742⟩
def centerBLog : DyadicInterval precision := ⟨960639748802635514472889052596215460521550014530, 960639748802635514472889052596215462720573270083⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1358565846000905640574303170236611545009456922077, scale precision, 1358565846000905640574303170236611546108968549854, scale precision,
    0, 128, 0, 128, ⟨-106740490788867523078809879820566300586383236954, -106740490788867523078809879820566300586381139801⟩, ⟨-106740490788867523078809879820566299403563832955, -106740490788867523078809879820566299403561735802⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨25328844546563792145364175869944518712165973939, 27704057351801426546684601097727000326331977356⟩
def wholeDExp : DyadicInterval precision := ⟨1407130684310035281592181556628555966755160121473, 1411711825212582109366700862001636148587605359971⟩
def wholeDLog : DyadicInterval precision := ⟨985594243690497964310298929048384649891451124795, 987926367053698422343402489929183443761757914490⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1407130684310035281592181556628555967304915935361, scale precision, 1411711825212582109366700862001636148037849546083, scale precision,
    0, 128, 0, 128, ⟨-55408114703602853093369202195454001223663156543, -55408114703602853093369202195454001223661059390⟩, ⟨-50657689093127584290728351739889036855187787228, -50657689093127584290728351739889036855185690075⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨25328844546563792145364175869944518712165973939, 28337475584291120905871946103453046799811665548⟩
def wholeCExp : DyadicInterval precision := ⟨1405911505313178891752593673021890838587723197732, 1411711825212582109366700862001636148587605359971⟩
def wholeCLog : DyadicInterval precision := ⟨984972968235820479042473659614684324240962526938, 987926367053698422343402489929183443761757914490⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1405911505313178891752593673021890839137479011620, scale precision, 1411711825212582109366700862001636148037849546083, scale precision,
    0, 128, 0, 128, ⟨-56674951168582241811743892206906094171117691373, -56674951168582241811743892206906094171115594220⟩, ⟨-50657689093127584290728351739889036855187787228, -50657689093127584290728351739889036855185690075⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨50675401233111028984527014235762266433255952022, 56065511042826457004347540631643291441374840830⟩
def wholeBExp : DyadicInterval precision := ⟨1353564207621696507596780595264882461943024675134, 1363585179744312424863179245872609410219592422490⟩
def wholeBLog : DyadicInterval precision := ⟨958045345378871634782107617527196204029239532650, 963238709265741788282291969515179158716334189642⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1353564207621696507596780595264882462492780489022, scale precision, 1363585179744312424863179245872609409669836608602, scale precision,
    0, 128, 0, 128, ⟨-112131022085652914008695081263286583476345786611, -112131022085652914008695081263286583476343689458⟩, ⟨-101350802466222057969054028471524532277280219628, -101350802466222057969054028471524532277278122475⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0016StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0017StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0017StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨123008276316677968590567857617524352972070183257, 123008276316677968590567857617524352972070183258⟩
def centerDExp : DyadicInterval precision := ⟨1235076695440473766556638255203847372603080990588, 1235076695440473766556638255203847374802104246141⟩
def centerDLog : DyadicInterval precision := ⟨895197900350273137203831070133649824645107273249, 895197900350273137203831070133649826844130528802⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1235076695440473766556638255203847373152836804476, scale precision, 1235076695440473766556638255203847374252348432253, scale precision,
    0, 128, 0, 128, ⟨-246016552633355937181135715235048706594683219577, -246016552633355937181135715235048706594681122424⟩, ⟨-246016552633355937181135715235048705293599610606, -246016552633355937181135715235048705293597513453⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨123646659488267513041843642921972473191175747215, 123646659488267513041843642921972473191175747216⟩
def centerCExp : DyadicInterval precision := ⟨1233998204848856383662776745541963461702913829304, 1233998204848856383662776745541963463901937084857⟩
def centerCLog : DyadicInterval precision := ⟨894613259054144972092534922547005590101150607665, 894613259054144972092534922547005592300173863218⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1233998204848856383662776745541963462252669643192, scale precision, 1233998204848856383662776745541963463352181270969, scale precision,
    0, 128, 0, 128, ⟨-247293318976535026083687285843944947033462908463, -247293318976535026083687285843944947033460811310⟩, ⟨-247293318976535026083687285843944945731242177552, -247293318976535026083687285843944945731240080399⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨248701695666007263736444087294378506122795166187, 248701695666007263736444087294378506122795166188⟩
def centerBExp : DyadicInterval precision := ⟨1039902766188338484594708114472613156400684641510, 1039902766188338484594708114472613158599707897063⟩
def centerBLog : DyadicInterval precision := ⟨785393309873193213427749859756639256284439874973, 785393309873193213427749859756639258483463130526⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1039902766188338484594708114472613156950440455398, scale precision, 1039902766188338484594708114472613158049952083175, scale precision,
    0, 128, 0, 128, ⟨-497403391332014527472888174588757013018229985497, -497403391332014527472888174588757013018227888344⟩, ⟨-497403391332014527472888174588757011472952776407, -497403391332014527472888174588757011472950679254⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨119019592332330079773337734920394720791278241017, 126999067220414009923202423697912773180597398747⟩
def wholeDExp : DyadicInterval precision := ⟨1228350054579566692017908102915209765594934478659, 1241836591959774864289057338296444370704392702246⟩
def wholeDLog : DyadicInterval precision := ⟨891547615580027951955449639520829062035069301574, 898857069849833759981739512399832702035676431148⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1228350054579566692017908102915209766144690292547, scale precision, 1241836591959774864289057338296444370154636888358, scale precision,
    0, 128, 0, 128, ⟨-253998134440828019846404847395825547015300121259, -253998134440828019846404847395825547015298024106⟩, ⟨-238039184664660159546675469840789440935556928976, -238039184664660159546675469840789440935554831823⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨119019592332330079773337734920394720791278241017, 128276576533857721025787388172632631798945739447⟩
def wholeCExp : DyadicInterval precision := ⟨1226204510955732588180712779922086012362307247027, 1241836591959774864289057338296444370704392702246⟩
def wholeCLog : DyadicInterval precision := ⟨890381392629473614381711917360076507391241130920, 898857069849833759981739512399832702035676431148⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1226204510955732588180712779922086012912063060915, scale precision, 1241836591959774864289057338296444370154636888358, scale precision,
    0, 128, 0, 128, ⟨-256553153067715442051574776345265264253141317498, -256553153067715442051574776345265264253139220345⟩, ⟨-238039184664660159546675469840789440935556928976, -238039184664660159546675469840789440935554831823⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨239878763828786629732963390089367294542248751090, 257544697616875877678682630457661034482241905781⟩
def wholeBExp : DyadicInterval precision := ⟨1027394473369725711169456262584538343569053044456, 1052534436295863801714746685306812133363569214732⟩
def wholeBLog : DyadicInterval precision := ⟨778066725565575372226855198307689506486498465002, 792755074273575496363197836249071888393767558659⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1027394473369725711169456262584538344118808858344, scale precision, 1052534436295863801714746685306812132813813400844, scale precision,
    0, 128, 0, 128, ⟨-515089395233751755357365260915322069746530163043, -515089395233751755357365260915322069746528065890⟩, ⟨-479757527657573259465926780178734588321132532104, -479757527657573259465926780178734588321130434951⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0017StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0018StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0018StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨115032946497916170088737142525822549131339623218, 115032946497916170088737142525822549131339623219⟩
def centerDExp : DyadicInterval precision := ⟨1248630004573113102149096526493550178299957551294, 1248630004573113102149096526493550180498980806847⟩
def centerDLog : DyadicInterval precision := ⟨902525175189120016129211831586767280434114094617, 902525175189120016129211831586767282633137350170⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1248630004573113102149096526493550178849713365182, scale precision, 1248630004573113102149096526493550179949224992959, scale precision,
    0, 128, 0, 128, ⟨-230065892995832340177474285051645098906160764959, -230065892995832340177474285051645098906158667806⟩, ⟨-230065892995832340177474285051645097619199825069, -230065892995832340177474285051645097619197727916⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨115670675699841828755977682908711048052233863086, 115670675699841828755977682908711048052233863087⟩
def centerCExp : DyadicInterval precision := ⟨1247540795453891350849345083970934405537194909617, 1247540795453891350849345083970934407736218165170⟩
def centerCLog : DyadicInterval precision := ⟨901937675724945358974818754539300288840331406155, 901937675724945358974818754539300291039354661708⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1247540795453891350849345083970934406086950723505, scale precision, 1247540795453891350849345083970934407186462351282, scale precision,
    0, 128, 0, 128, ⟨-231341351399683657511955365817422096748511057822, -231341351399683657511955365817422096748508960669⟩, ⟨-231341351399683657511955365817422095460426491676, -231341351399683657511955365817422095460424394523⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨232378217379230243663107254932754002013508711525, 232378217379230243663107254932754002013508711526⟩
def centerBExp : DyadicInterval precision := ⟨1063393456707912304681398863877223320762677058436, 1063393456707912304681398863877223322961700313989⟩
def centerBLog : DyadicInterval precision := ⟨799054227864764035979759280699562560575947932882, 799054227864764035979759280699562562774971188435⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1063393456707912304681398863877223321312432872324, scale precision, 1063393456707912304681398863877223322411944500101, scale precision,
    0, 128, 0, 128, ⟨-464756434758460487326214509865508004782589250309, -464756434758460487326214509865508004782587153156⟩, ⟨-464756434758460487326214509865508003271447692945, -464756434758460487326214509865508003271445595792⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨111048270122241576078328386047482676587330985904, 119019592332330079773337734920394720791278241018⟩
def wholeDExp : DyadicInterval precision := ⟨1241836591959774864289057338296444368505369446693, 1255457196643991312782767932801799989113568160976⟩
def wholeDLog : DyadicInterval precision := ⟨898857069849833759981739512399832699836653175595, 906202267987834631995011695345793201716926871713⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1241836591959774864289057338296444369055125260581, scale precision, 1255457196643991312782767932801799988563812347088, scale precision,
    0, 128, 0, 128, ⟨-238039184664660159546675469840789442229558132246, -238039184664660159546675469840789442229556035093⟩, ⟨-222096540244483152156656772094965352534681805353, -222096540244483152156656772094965352534679708200⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨111048270122241576078328386047482676587330985904, 120295746166073688299697151201661012754942157298⟩
def wholeCExp : DyadicInterval precision := ⟨1239669791048700762763922815625918519018189802449, 1255457196643991312782767932801799989113568160976⟩
def wholeCLog : DyadicInterval precision := ⟨897685165847594704246171044993454081574913471733, 906202267987834631995011695345793201716926871713⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1239669791048700762763922815625918519567945616337, scale precision, 1255457196643991312782767932801799988563812347088, scale precision,
    0, 128, 0, 128, ⟨-240591492332147376599394302403322026158016847807, -240591492332147376599394302403322026158014750654⟩, ⟨-222096540244483152156656772094965352534681805353, -222096540244483152156656772094965352534679708200⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨223590532296792858273138350117122513977217811276, 241184626806749055639611155786176124284241534581⟩
def wholeBExp : DyadicInterval precision := ⟨1050655220626468140158581794906027347133078478426, 1076258554488359441934578352032876250046492487573⟩
def wholeBLog : DyadicInterval precision := ⟨791662208582552229743762264383106989815954966690, 806482109433465224369192354012429701629745321451⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1050655220626468140158581794906027347682834292314, scale precision, 1076258554488359441934578352032876249496736673685, scale precision,
    0, 128, 0, 128, ⟨-482369253613498111279222311572352249333215502836, -482369253613498111279222311572352249333213405683⟩, ⟨-447181064593585716546276700234245027207897636639, -447181064593585716546276700234245027207895539486⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0018StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0019StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0019StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨107065494589907116025240672481192988302250052280, 107065494589907116025240672481192988302250052281⟩
def centerDExp : DyadicInterval precision := ⟨1262318434497260164208401614240797141306259170539, 1262318434497260164208401614240797143505282426092⟩
def centerDLog : DyadicInterval precision := ⟨909888400376604858648946115122446892680058539307, 909888400376604858648946115122446894879081794860⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1262318434497260164208401614240797141856014984427, scale precision, 1262318434497260164208401614240797142955526612204, scale precision,
    0, 128, 0, 128, ⟨-214130989179814232050481344962385977241003797932, -214130989179814232050481344962385977241001700779⟩, ⟨-214130989179814232050481344962385975967998508344, -214130989179814232050481344962385975967996411191⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨107702613764298091007146266492718353521765803971, 107702613764298091007146266492718353521765803972⟩
def centerCExp : DyadicInterval precision := ⟨1261218337499894815409095275349286210490027378432, 1261218337499894815409095275349286212689050633985⟩
def centerCLog : DyadicInterval precision := ⟨909298009570345194547544221060999601672904459841, 909298009570345194547544221060999603871927715394⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1261218337499894815409095275349286211039783192320, scale precision, 1261218337499894815409095275349286212139294820097, scale precision,
    0, 128, 0, 128, ⟨-215405227528596182014292532985436707680590490393, -215405227528596182014292532985436707680588393240⟩, ⟨-215405227528596182014292532985436706406474822644, -215405227528596182014292532985436706406472725491⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨216118953614859556917907414642547971679695779635, 216118953614859556917907414642547971679695779636⟩
def centerBExp : DyadicInterval precision := ⟨1087319233751136707494100311630733283140787244042, 1087319233751136707494100311630733285339810499595⟩
def centerBLog : DyadicInterval precision := ⟨812838137630430626470014391721701505254155460434, 812838137630430626470014391721701507453178715987⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1087319233751136707494100311630733283690543057930, scale precision, 1087319233751136707494100311630733284790054685707, scale precision,
    0, 128, 0, 128, ⟨-432237907229719113835814829285095944098337525944, -432237907229719113835814829285095944098335428791⟩, ⟨-432237907229719113835814829285095942620447689749, -432237907229719113835814829285095942620445592596⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨103084551358829778834915002511195342403115231675, 111048270122241576078328386047482676587330985905⟩
def wholeDExp : DyadicInterval precision := ⟨1255457196643991312782767932801799986914544905423, 1269213987453105464161597200857722394416664115457⟩
def wholeDLog : DyadicInterval precision := ⟨906202267987834631995011695345793199517903616160, 913583624998653703523149262826058897164757379534⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1255457196643991312782767932801799987464300719311, scale precision, 1269213987453105464161597200857722393866908301569, scale precision,
    0, 128, 0, 128, ⟨-222096540244483152156656772094965353814644235419, -222096540244483152156656772094965353814642138266⟩, ⟨-206169102717659557669830005022390684173186942555, -206169102717659557669830005022390684173184845402⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨103084551358829778834915002511195342403115231675, 112323156467442955010968215135395036933059521669⟩
def wholeCExp : DyadicInterval precision := ⟨1253268803809595188304966484721289874070871008479, 1269213987453105464161597200857722394416664115457⟩
def wholeCLog : DyadicInterval precision := ⟨905024617290735910973596382386661960243964330913, 913583624998653703523149262826058897164757379534⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1253268803809595188304966484721289874620626822367, scale precision, 1269213987453105464161597200857722393866908301569, scale precision,
    0, 128, 0, 128, ⟨-224646312934885910021936430270790074507218808875, -224646312934885910021936430270790074507216711722⟩, ⟨-206169102717659557669830005022390684173186942555, -206169102717659557669830005022390684173184845402⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨207364037900146833805279022757379167895402526013, 224891258230253913064710509213309086355856044063⟩
def wholeBExp : DyadicInterval precision := ⟨1074344533730943943617918492684994410200193259747, 1100424441361699833197968540687666015087121635409⟩
def wholeBLog : DyadicInterval precision := ⟨805379404807415472260164889560497952148103862327, 820333450761233184846212780159319759056095221943⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1074344533730943943617918492684994410749949073635, scale precision, 1100424441361699833197968540687666014537365821521, scale precision,
    0, 128, 0, 128, ⟨-449782516460507826129421018426618173459582183273, -449782516460507826129421018426618173459580086120⟩, ⟨-414728075800293667610558045514758335060661447385, -414728075800293667610558045514758335060659350232⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0019StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0020StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0020StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨99105371957748756558358702025034649328540468989, 99105371957748756558358702025034649328540468990⟩
def centerDExp : DyadicInterval precision := ⟨1276144127861541994145963581661485621034162019732, 1276144127861541994145963581661485623233185275285⟩
def centerDLog : DyadicInterval precision := ⟨917287995011510229356867982908921321385400443938, 917287995011510229356867982908921323584423699491⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1276144127861541994145963581661485621583917833620, scale precision, 1276144127861541994145963581661485622683429461397, scale precision,
    0, 128, 0, 128, ⟨-198210743915497513116717404050069299286688787692, -198210743915497513116717404050069299286686690539⟩, ⟨-198210743915497513116717404050069298027475185421, -198210743915497513116717404050069298027473088268⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨99741924952641264037723029627018281213874527817, 99741924952641264037723029627018281213874527818⟩
def centerCExp : DyadicInterval precision := ⟨1275032969804752314514723632597307583183888748856, 1275032969804752314514723632597307585382912004409⟩
def centerCLog : DyadicInterval precision := ⟨916694679033160724683830653449404491777179954842, 916694679033160724683830653449404493976203210395⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1275032969804752314514723632597307583733644562744, scale precision, 1275032969804752314514723632597307584833156190521, scale precision,
    0, 128, 0, 128, ⟨-199483849905282528075446059254036563057905591291, -199483849905282528075446059254036563057903494138⟩, ⟨-199483849905282528075446059254036561797594617131, -199483849905282528075446059254036561797592519978⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨199919324552184362978580257775708484377034756313, 199919324552184362978580257775708484377034756314⟩
def centerBExp : DyadicInterval precision := ⟨1111692601737834304960484805256848518456948593643, 1111692601737834304960484805256848520655971849196⟩
def centerBLog : DyadicInterval precision := ⟨826747501553732937550752135409491201983324755094, 826747501553732937550752135409491204182348010647⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1111692601737834304960484805256848519006704407531, scale precision, 1111692601737834304960484805256848520106216035308, scale precision,
    0, 128, 0, 128, ⟨-399838649104368725957160515551416969476814439210, -399838649104368725957160515551416969476812342057⟩, ⟨-399838649104368725957160515551416968031326683198, -399838649104368725957160515551416968031324586045⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨95127887983717436574352739463518235552733806994, 103084551358829778834915002511195342403115231676⟩
def wholeDExp : DyadicInterval precision := ⟨1269213987453105464161597200857722392217640859904, 1283109131137421329953040259475754031879254989498⟩
def wholeDLog : DyadicInterval precision := ⟨913583624998653703523149262826058894965734123981, 921001564088758741914731412563984562181431746082⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1269213987453105464161597200857722392767396673792, scale precision, 1283109131137421329953040259475754031329499175610, scale precision,
    0, 128, 0, 128, ⟨-206169102717659557669830005022390685439276081302, -206169102717659557669830005022390685439273984149⟩, ⟨-190255775967434873148705478927036470479279507931, -190255775967434873148705478927036470479277410778⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨95127887983717436574352739463518235552733806994, 104358258011611726998445045028828451687585466342⟩
def wholeCExp : DyadicInterval precision := ⟨1267003660491626537512866653176074203657491292939, 1283109131137421329953040259475754031879254989498⟩
def wholeCLog : DyadicInterval precision := ⟨912400160656194878996222611181732224632599479572, 921001564088758741914731412563984562181431746082⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1267003660491626537512866653176074204207247106827, scale precision, 1283109131137421329953040259475754031329499175610, scale precision,
    0, 128, 0, 128, ⟨-208716516023223453996890090057656904009320916408, -208716516023223453996890090057656904009318819255⟩, ⟨-190255775967434873148705478927036470479279507931, -190255775967434873148705478927036470479277410778⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨191194719185872429583518944051791718612165764688, 208659993168738163327113473155546913729082918463⟩
def wholeBExp : DyadicInterval precision := ⟨1098474615239151709131967435382893979535030622907, 1125044909933745912773463128462173915391977363052⟩
def wholeBLog : DyadicInterval precision := ⟨819220710211348203542880090538222363061315522711, 834311627217828832252519695712052890740898632922⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1098474615239151709131967435382893980084786436795, scale precision, 1125044909933745912773463128462173914842221549164, scale precision,
    0, 128, 0, 128, ⟨-417319986337476326654226946311093828189607567866, -417319986337476326654226946311093828189605470713⟩, ⟨-382389438371744859167037888103583436510166401088, -382389438371744859167037888103583436510164303935⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0020StableWitnesses

end


