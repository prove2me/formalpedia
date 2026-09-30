-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0126StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0126StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:53:56.237293+00:00
-- url     : https://prove2.me/theorems/5fb1e101-5ebe-4ef3-90b6-06d19b4d5fac
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0126StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0127StableWitnesses, GeneralCK.Certificates.E8TAxisProd01…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0126StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0127StableWitnesses, GeneralCK.Certificates.E8TAxisProd0128StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0126StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0127StableWitnesses, GeneralCK.Certificates.E8TAxisProd0128StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0126StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0127StableWitnesses, GeneralCK.Certificates.E8TAxisProd0128StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0126StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0127StableWitnesses, GeneralCK/Certificates/E8TAxisProd0128StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0126StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0126StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312260897, 2849167218250950044280193223065006085312260898⟩
def centerAExp : DyadicInterval precision := ⟨1455814397256041217437249255499380272227928609805, 1455814397256041217437249255499380274426951865358⟩
def centerALog : DyadicInterval precision := ⟨1010189349275934740575240882696318021950304507166, 1010189349275934740575240882696318024149327762719⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455814397256041217437249255499380272777684423693, scale precision, 1455814397256041217437249255499380273877196051470, scale precision,
    0, 128, 0, 128, ⟨-5698334436501900088560386446130012722529043537, -5698334436501900088560386446130012722526946384⟩, ⟨-5698334436501900088560386446130011618722097206, -5698334436501900088560386446130011618720000053⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨418923789944494851264925608228606449078018430165, 418923789944494851264925608228606449078018430166⟩
def centerCExp : DyadicInterval precision := ⟨823810993851236134690751161462437833401478586257, 823810993851236134690751161462437835600501841810⟩
def centerCLog : DyadicInterval precision := ⟨653347365254005261162896939902595036987123796673, 653347365254005261162896939902595039186147052226⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨823810993851236134690751161462437833951234400145, scale precision, 823810993851236134690751161462437835050746027922, scale precision,
    0, 128, 0, 128, ⟨-837847579888989702529851216457212899131345386141, -837847579888989702529851216457212899131343288988⟩, ⟨-837847579888989702529851216457212897180730431674, -837847579888989702529851216457212897180728334521⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨912666501870168905412732512241707366121460928767, 912666501870168905412732512241707366121460928768⟩
def centerBExp : DyadicInterval precision := ⟨419169839180607774768237048957383005505036501303, 419169839180607774768237048957383007704059756856⟩
def centerBLog : DyadicInterval precision := ⟨368538764666713139136468456069703461440831259860, 368538764666713139136468456069703463639854515413⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨419169839180607774768237048957383006054792315191, scale precision, 419169839180607774768237048957383007154303942968, scale precision,
    1, 128, 1, 128, ⟨-1825333003740337810825465024483414734159733103383, -1825333003740337810825465024483414734159731006230⟩, ⟨-1825333003740337810825465024483414730326112708839, -1825333003740337810825465024483414730326110611686⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 3165742448647063503620071141085134670978073809⟩
def wholeAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨409943527226177432185621695170239210992121518613, 427935929430565485324672558056114698713985782681⟩
def wholeCExp : DyadicInterval precision := ⟨813713562352784051832885625982383215281828896729, 833997343745599858584413854167126995079724474694⟩
def wholeCLog : DyadicInterval precision := ⟨646875554389199225702248453391544194683358203349, 659847257783016669418359171739257334878103795445⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨813713562352784051832885625982383215831584710617, scale precision, 833997343745599858584413854167126994529968660806, scale precision,
    0, 128, 0, 128, ⟨-855871858861130970649345116112229398415382753455, -855871858861130970649345116112229398415380656302⟩, ⟨-819887054452354864371243390340478421020848904565, -819887054452354864371243390340478421020846807412⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨890383053906861011304981145854085152341339310930, 935202829477217853128384102912426720386644354671⟩
def wholeBExp : DyadicInterval precision := ⟨406439960618450687008431800255530588799480678828, 432148850192125891665144792388294672219735559020⟩
def wholeBLog : DyadicInterval precision := ⟨358612528210933558039494961077288687822256115433, 378590329316013759971508990892664987972856114237⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨406439960618450687008431800255530589349236492716, scale precision, 432148850192125891665144792388294671669979745132, scale precision,
    1, 128, 1, 128, ⟨-1870405658954435706256768205824853442750135294728, -1870405658954435706256768205824853442750133197575⟩, ⟨-1780766107813722022609962291708170302823438296146, -1780766107813722022609962291708170302823436198993⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0126StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0127StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0127StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312260897, 2849167218250950044280193223065006085312260898⟩
def centerAExp : DyadicInterval precision := ⟨1455814397256041217437249255499380272227928609805, 1455814397256041217437249255499380274426951865358⟩
def centerALog : DyadicInterval precision := ⟨1010189349275934740575240882696318021950304507166, 1010189349275934740575240882696318024149327762719⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455814397256041217437249255499380272777684423693, scale precision, 1455814397256041217437249255499380273877196051470, scale precision,
    0, 128, 0, 128, ⟨-5698334436501900088560386446130012722529043537, -5698334436501900088560386446130012722526946384⟩, ⟨-5698334436501900088560386446130011618722097206, -5698334436501900088560386446130011618720000053⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨401681734325522873829587829920180725980264923071, 401681734325522873829587829920180725980264923072⟩
def centerCExp : DyadicInterval precision := ⟨843479934728238608185249041985872693486794573869, 843479934728238608185249041985872695685817829422⟩
def centerCLog : DyadicInterval precision := ⟨665872211791273428978520633123812675326769374827, 665872211791273428978520633123812677525792630380⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨843479934728238608185249041985872694036550387757, scale precision, 843479934728238608185249041985872695136062015534, scale precision,
    0, 128, 0, 128, ⟨-803363468651045747659175659840361452913095370824, -803363468651045747659175659840361452913093273671⟩, ⟨-803363468651045747659175659840361451007966418612, -803363468651045747659175659840361451007964321459⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨869208030928855990633759988506863837488527221985, 869208030928855990633759988506863837488527221986⟩
def centerBExp : DyadicInterval precision := ⟨444854457491036342788700663599825430989779004398, 444854457491036342788700663599825433188802259951⟩
def centerBLog : DyadicInterval precision := ⟨388363646633785422842569260329082876224023198360, 388363646633785422842569260329082878423046453913⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨444854457491036342788700663599825431539534818286, scale precision, 444854457491036342788700663599825432639046446063, scale precision,
    1, 128, 1, 128, ⟨-1738416061857711981267519977013727676783194576016, -1738416061857711981267519977013727676783192478863⟩, ⟨-1738416061857711981267519977013727673170916409077, -1738416061857711981267519977013727673170914311924⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 3165742448647063503620071141085134670978073809⟩
def wholeAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨392760784790180292139123525495050640775660750371, 410633201084391467870583087491309252328333438808⟩
def wholeCExp : DyadicInterval precision := ⟨833210598374149454201945420759125265341111609227, 853840182486705188164996754687631267887724548140⟩
def wholeCLog : DyadicInterval precision := ⟨659346265734723569464142280950708826813191231787, 672426534142843849849723373732993902346578958728⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨833210598374149454201945420759125265890867423115, scale precision, 853840182486705188164996754687631267337968734252, scale precision,
    0, 128, 0, 128, ⟨-821266402168782935741166174982618505620972777447, -821266402168782935741166174982618505620970680294⟩, ⟨-785521569580360584278247050990101280610316212757, -785521569580360584278247050990101280610314115604⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨847408844063416313893716486071623707147098706301, 891252197999596923310947393377686358564274924210⟩
def wholeBExp : DyadicInterval precision := ⟨431635164359713830805111755543787345181015301502, 458324929075381578872203088156420459760650584733⟩
def wholeBLog : DyadicInterval precision := ⟨378193817638747193797885219962986194325519696675, 398654424340000861397377527043933164031801360955⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨431635164359713830805111755543787345730771115390, scale precision, 458324929075381578872203088156420459210894770845, scale precision,
    1, 128, 1, 128, ⟨-1782504395999193846621894786755372718990004940764, -1782504395999193846621894786755372718990002843611⟩, ⟨-1694817688126832627787432972143247412541142995157, -1694817688126832627787432972143247412541140898004⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0127StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0128StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0128StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2216017656540843594568486214625237657012954244, 2216017656540843594568486214625237657012954245⟩
def centerAExp : DyadicInterval precision := ⟨1457076315351450948047082186788007224970773813488, 1457076315351450948047082186788007227169797069041⟩
def centerALog : DyadicInterval precision := ⟨1010821401672838003372446069258059721789517968263, 1010821401672838003372446069258059723988541223816⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457076315351450948047082186788007225520529627376, scale precision, 1457076315351450948047082186788007226620041255153, scale precision,
    0, 128, 0, 128, ⟨-4432035313081687189136972429250475865452447731, -4432035313081687189136972429250475865450350578⟩, ⟨-4432035313081687189136972429250474762601466399, -4432035313081687189136972429250474762599369246⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨521774884976969249658675544420781985592392356176, 521774884976969249658675544420781985592392356177⟩
def centerDExp : DyadicInterval precision := ⟨715651972798857079113875938009045310901254744990, 715651972798857079113875938009045313100278000543⟩
def centerDLog : DyadicInterval precision := ⟨582487198387037182294075308140412786716139382242, 582487198387037182294075308140412788915162637795⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨715651972798857079113875938009045311451010558878, scale precision, 715651972798857079113875938009045312550522186655, scale precision,
    1, 128, 1, 128, ⟨-1043549769953938499317351088841563972307494916592, -1043549769953938499317351088841563972307492819439⟩, ⟨-1043549769953938499317351088841563970062076605264, -1043549769953938499317351088841563970062074508111⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨524306547641570385389161185830171207362782950007, 524306547641570385389161185830171207362782950008⟩
def centerCExp : DyadicInterval precision := ⟨713176909463409716932521316444454301241365523238, 713176909463409716932521316444454303440388778791⟩
def centerCLog : DyadicInterval precision := ⟨580824767770762637012989164909865403011995786326, 580824767770762637012989164909865405211019041879⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨713176909463409716932521316444454301791121337126, scale precision, 713176909463409716932521316444454302890632964903, scale precision,
    1, 128, 1, 128, ⟨-1048613095283140770778322371660342415852172439415, -1048613095283140770778322371660342415852170342262⟩, ⟨-1048613095283140770778322371660342413598961457767, -1048613095283140770778322371660342413598959360614⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1193579782293784189863164453931573962103148646081, 1193579782293784189863164453931573962103148646082⟩
def centerBExp : DyadicInterval precision := ⟨285390623157168366023862002535629031860786686218, 285390623157168366023862002535629034059809941771⟩
def centerBLog : DyadicInterval precision := ⟨260693793990465616099203521526045923044103347479, 260693793990465616099203521526045925243126603032⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨285390623157168366023862002535629032410542500106, scale precision, 285390623157168366023862002535629033510054127883, scale precision,
    2, 128, 2, 128, ⟨-2387159564587568379726328907863147927021629178320, -2387159564587568379726328907863147927021627081167⟩, ⟨-2387159564587568379726328907863147921390967503162, -2387159564587568379726328907863147921390965406009⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1457707683773513925477741956702213446679176875042⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1011137530350683182654731711817158199758569694808⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨512756788786713314020267203907621024217207656619, 530829944683894805437507571749273968698214433228⟩
def wholeDExp : DyadicInterval precision := ⟨706838726837510462039096914346652691200364343781, 724538456853667540563062557829026726602043072281⟩
def wholeDLog : DyadicInterval precision := ⟨576558946667156773600005109862481905428300877399, 588440465573623044036052405976243775513762722746⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨706838726837510462039096914346652691750120157669, scale precision, 724538456853667540563062557829026726052287258393, scale precision,
    1, 128, 1, 128, ⟨-1061659889367789610875015143498547938533137613158, -1061659889367789610875015143498547938533135516005⟩, ⟨-1025513577573426628040534407815242047325477264753, -1025513577573426628040534407815242047325475167600⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨514917795777685095537795947665298298661090422770, 533735477367524214415483762183972136785277995954⟩
def wholeCExp : DyadicInterval precision := ⟨704033850755750596856942594226690043290622365314, 722398986344962202368518281249828937644436421683⟩
def wholeCLog : DyadicInterval precision := ⟨574667184328729225728115524796933597341884829664, 587009398150422054872458466897927028918748478648⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨704033850755750596856942594226690043840378179202, scale precision, 722398986344962202368518281249828937094680607795, scale precision,
    1, 128, 1, 128, ⟨-1067470954735048428830967524367944274711793390507, -1067470954735048428830967524367944274711791293354⟩, ⟨-1029835591555370191075591895330596596209958542039, -1029835591555370191075591895330596596209956444886⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1168169751372388358053427979631983457349379525151, 1219263255599082686606101690011205825375393412748⟩
def wholeBExp : DyadicInterval precision := ⟨275534310070000649047984946289026717846731332021, 295488921894342802484940373930546680259344771354⟩
def wholeBLog : DyadicInterval precision := ⟨252424360588459660022131642981383376019390362986, 269118003223819914409534406585803705747336706921⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨275534310070000649047984946289026718396487145909, scale precision, 295488921894342802484940373930546679709588957466, scale precision,
    2, 128, 2, 128, ⟨-2438526511198165373212203380022411653666827702019, -2438526511198165373212203380022411653666825604866⟩, ⟨-2336339502744776716106855959263966911979642857600, -2336339502744776716106855959263966911979640760447⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0128StableWitnesses

end


