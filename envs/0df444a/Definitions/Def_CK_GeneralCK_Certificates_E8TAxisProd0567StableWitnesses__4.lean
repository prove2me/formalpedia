-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0567StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0567StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:49:47.515369+00:00
-- url     : https://prove2.me/theorems/56ddd5b7-a309-4de3-9923-0e59193ca76f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0567StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0568StableWitnesses, GeneralCK.Certificates.E8TAxisProd05…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0567StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0568StableWitnesses, GeneralCK.Certificates.E8TAxisProd0569StableWitnesses, GeneralCK.Certificates.E8TAxisProd0570StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0567StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0568StableWitnesses, GeneralCK.Certificates.E8TAxisProd0569StableWitnesses, GeneralCK.Certificates.E8TAxisProd0570StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0567StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0568StableWitnesses, GeneralCK.Certificates.E8TAxisProd0569StableWitnesses, GeneralCK.Certificates.E8TAxisProd0570StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0567StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0568StableWitnesses, GeneralCK/Certificates/E8TAxisProd0569StableWitnesses, GeneralCK/Certificates/E8TAxisProd0570StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0567StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0567StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3324030191359282881556817859241043973740987770, 3324030191359282881556817859241043973740987771⟩
def centerAExp : DyadicInterval precision := ⟨1454868674354870198336951421367206718659928330939, 1454868674354870198336951421367206720858951586492⟩
def centerALog : DyadicInterval precision := ⟨1009715489181788885783740077569471416073335956070, 1009715489181788885783740077569471418272359211623⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454868674354870198336951421367206719209684144827, scale precision, 1454868674354870198336951421367206720309195772604, scale precision,
    0, 128, 0, 128, ⟨-6648060382718565763113635718482088499745256643, -6648060382718565763113635718482088499743159490⟩, ⟨-6648060382718565763113635718482087395220791593, -6648060382718565763113635718482087395218694440⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨536053595931077576481867337467978800983992300722, 536053595931077576481867337467978800983992300723⟩
def centerDExp : DyadicInterval precision := ⟨701804023530382254660990345893463172517499932104, 701804023530382254660990345893463174716523187657⟩
def centerDLog : DyadicInterval precision := ⟨573161517422994399504898462730524988803441785707, 573161517422994399504898462730524991002465041260⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨701804023530382254660990345893463173067255745992, scale precision, 701804023530382254660990345893463174166767373769, scale precision,
    1, 128, 1, 128, ⟨-1072107191862155152963734674935957603112848026398, -1072107191862155152963734674935957603112845929245⟩, ⟨-1072107191862155152963734674935957600823123273644, -1072107191862155152963734674935957600823121176491⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨539877064464345443400281375495563480749450390449, 539877064464345443400281375495563480749450390450⟩
def centerCExp : DyadicInterval precision := ⟨698141601472519716345748237137593415049903477680, 698141601472519716345748237137593417248926733233⟩
def centerCLog : DyadicInterval precision := ⟨570685135102025163328000866797194137885218348590, 570685135102025163328000866797194140084241604143⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨698141601472519716345748237137593415599659291568, scale precision, 698141601472519716345748237137593416699170919345, scale precision,
    1, 128, 1, 128, ⟨-1079754128928690886800562750991126962649770106679, -1079754128928690886800562750991126962649768009526⟩, ⟨-1079754128928690886800562750991126960348033552274, -1079754128928690886800562750991126960348031455121⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1235135415227862660109772476552532853709419016618, 1235135415227862660109772476552532853709419016619⟩
def centerBExp : DyadicInterval precision := ⟨269614136743614698278652260020450628288157696050, 269614136743614698278652260020450630487180951603⟩
def centerBLog : DyadicInterval precision := ⟨247434756840609704608606903796731482730527096469, 247434756840609704608606903796731484929550352022⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨269614136743614698278652260020450628837913509938, scale precision, 269614136743614698278652260020450629937425137715, scale precision,
    2, 128, 2, 128, ⟨-2470270830455725320219544953105065710398909162095, -2470270830455725320219544953105065710398907064942⟩, ⟨-2470270830455725320219544953105065704438769001535, -2470270830455725320219544953105065704438766904382⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3482318024844347500022322904444928295572395253⟩
def wholeAExp : DyadicInterval precision := ⟨1454553569581723058392238696431353224119669669100, 1455183847209450510423929547351191477780877052172⟩
def wholeALog : DyadicInterval precision := ⟨1009557569928173087760872372803888449827653659813, 1009873425488092576137085252579843092274389747387⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1454553569581723058392238696431353224669425482988, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-6964636049688695000044645808889857143527710010, -6964636049688695000044645808889857143525612857⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨530829944683894805437507571749273968698214433227, 541289809268942399956535792498120861936820641713⟩
def wholeDExp : DyadicInterval precision := ⟨696793203199184192771083052087923259249531509367, 706838726837510462039096914346652693399387599334⟩
def wholeDLog : DyadicInterval precision := ⟨569772344639491636839148332004312889556812159164, 576558946667156773600005109862481907627324132952⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨696793203199184192771083052087923259799287323255, scale precision, 706838726837510462039096914346652692849631785446, scale precision,
    1, 128, 1, 128, ⟨-1082579618537884799913071584996241725026737710144, -1082579618537884799913071584996241725026735612991⟩, ⟨-1061659889367789610875015143498547936259722216904, -1061659889367789610875015143498547936259720119751⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨534462464943461988627643447017480232956872335843, 545305212704413565956089427135971588116999383861⟩
def wholeCExp : DyadicInterval precision := ⟨692974893724183877263531990283358040763437966545, 703333790844970445594430493989792989387989694238⟩
def wholeCLog : DyadicInterval precision := ⟨567184464816143044109543686774235121234143594613, 574194643415014070803989257396184405588225222324⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨692974893724183877263531990283358041313193780433, scale precision, 703333790844970445594430493989792988838233880350, scale precision,
    1, 128, 1, 128, ⟨-1090610425408827131912178854271943177393448779611, -1090610425408827131912178854271943177393446682458⟩, ⟨-1068924929886923977255286894034960464771373446120, -1068924929886923977255286894034960464771371348967⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1220276011489811637820224973169820958582993525707, 1250084216065429134407531341899247018872414016115⟩
def wholeBExp : DyadicInterval precision := ⟨264154733834754447386985209613945516980968381076, 275152708422481421135963576643696941937889846145⟩
def wholeBLog : DyadicInterval precision := ⟨242818350211036666079485436457325349020968848905, 252103254567004538347859354165711366940822777780⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨264154733834754447386985209613945517530724194964, scale precision, 275152708422481421135963576643696941388134032257, scale precision,
    2, 128, 2, 128, ⟨-2500168432130858268815062683798494040786489589653, -2500168432130858268815062683798494040786487492500⟩, ⟨-2440552022979623275640449946339641914245904097415, -2440552022979623275640449946339641914245902000262⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0567StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0568StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0568StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3007454792385135386557447160398116569795982507, 3007454792385135386557447160398116569795982508⟩
def centerAExp : DyadicInterval precision := ⟨1455499088168743985690617101081856958065120579782, 1455499088168743985690617101081856960264143835335⟩
def centerALog : DyadicInterval precision := ⟨1010031378851376569271247815372298287995916580825, 1010031378851376569271247815372298290194939836378⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455499088168743985690617101081856958614876393670, scale precision, 1455499088168743985690617101081856959714388021447, scale precision,
    0, 128, 0, 128, ⟨-6014909584770270773114894320796233691616047245, -6014909584770270773114894320796233691613950092⟩, ⟨-6014909584770270773114894320796232587569979939, -6014909584770270773114894320796232587567882786⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨567663676182737085008043281595790637958622415352, 567663676182737085008043281595790637958622415353⟩
def centerDExp : DyadicInterval precision := ⟨672093324830871043359987491990956794091407910102, 672093324830871043359987491990956796290431165655⟩
def centerDLog : DyadicInterval precision := ⟨552950239283275349899356499051421616923499990001, 552950239283275349899356499051421619122523245554⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨672093324830871043359987491990956794641163723990, scale precision, 672093324830871043359987491990956795740675351767, scale precision,
    1, 128, 1, 128, ⟨-1135327352365474170016086563191581277112718282361, -1135327352365474170016086563191581277112716185208⟩, ⟨-1135327352365474170016086563191581274721773476199, -1135327352365474170016086563191581274721771379046⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨571174175250679415686741669271135781813821462776, 571174175250679415686741669271135781813821462777⟩
def centerCExp : DyadicInterval precision := ⟨668872357024316966735525357709451732907918715648, 668872357024316966735525357709451735106941971201⟩
def centerCLog : DyadicInterval precision := ⟨550742225732305185850376704270956341870493571966, 550742225732305185850376704270956344069516827519⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨668872357024316966735525357709451733457674529536, scale precision, 668872357024316966735525357709451734557186157313, scale precision,
    1, 128, 1, 128, ⟨-1142348350501358831373483338542271564828873197750, -1142348350501358831373483338542271564828871100597⟩, ⟨-1142348350501358831373483338542271562426414750507, -1142348350501358831373483338542271562426412653354⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1324047330030922484301041242826867384555324140075, 1324047330030922484301041242826867384555324140076⟩
def centerBExp : DyadicInterval precision := ⟨238726802424795800265899837127474598879415136954, 238726802424795800265899837127474601078438392507⟩
def centerBLog : DyadicInterval precision := ⟨221122556041018507600936199070847492727228806041, 221122556041018507600936199070847494926252061594⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨238726802424795800265899837127474599429170950842, scale precision, 238726802424795800265899837127474600528682578619, scale precision,
    2, 128, 2, 128, ⟨-2648094660061844968602082485653734772476291619282, -2648094660061844968602082485653734772476289522129⟩, ⟨-2648094660061844968602082485653734765745007038169, -2648094660061844968602082485653734765745004941016⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312260897, 3165742448647063503620071141085134670978073809⟩
def wholeAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1455814397256041217437249255499380274426951865358⟩
def wholeALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1010189349275934740575240882696318024149327762719⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1455814397256041217437249255499380273877196051470, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-5698334436501900088560386446130011618722097206, -5698334436501900088560386446130011618720000053⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨562362779591003425345044647758252905789383238157, 572977884517961874928161575521614457065497220142⟩
def wholeDExp : DyadicInterval precision := ⟨667223417983630662234844101180676642856752596602, 676986443527636285719880989929562988819692333983⟩
def wholeDLog : DyadicInterval precision := ⟨549610565162722028431892812520915518488782484595, 556298163020790248856133545839930270877081982575⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨667223417983630662234844101180676643406508410490, scale precision, 676986443527636285719880989929562988269936520095, scale precision,
    1, 128, 1, 128, ⟨-1145955769035923749856323151043228915335193363926, -1145955769035923749856323151043228915335191266773⟩, ⟨-1124725559182006850690089295516505810391935750325, -1124725559182006850690089295516505810391933653172⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨565680050359218411737838960567931613525330346486, 576682642582073383101979471545765472470281892211⟩
def wholeCExp : DyadicInterval precision := ⟨663849291219052969251312523726729916747569882810, 673920203080667568363880347398922536968668285327⟩
def wholeCLog : DyadicInterval precision := ⟨547292180233176253188341073480463118315923060244, 554201106093946468457818328853517461328754501034⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨663849291219052969251312523726729917297325696698, scale precision, 673920203080667568363880347398922536418912471439, scale precision,
    1, 128, 1, 128, ⟨-1153365285164146766203958943091530946150883248272, -1153365285164146766203958943091530946150881151119⟩, ⟨-1131360100718436823475677921135863225858430052312, -1131360100718436823475677921135863225858427955159⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1308668878170221225058508475134335127479664367200, 1339512744176854336106566931956356444433446459115⟩
def wholeBExp : DyadicInterval precision := ⟨233727540583109634409941781584328052900197320173, 243803979455572315941788232053864266793534766949⟩
def wholeBLog : DyadicInterval precision := ⟨216818903650465130617555419393104023261679785333, 225480350100877508624293294418356752353420843239⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨233727540583109634409941781584328053449953134061, scale precision, 243803979455572315941788232053864266243778953061, scale precision,
    2, 128, 2, 128, ⟨-2679025488353708672213133863912712892304524894360, -2679025488353708672213133863912712892304522797207⟩, ⟨-2617337756340442450117016950268670251663776429317, -2617337756340442450117016950268670251663774332164⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0568StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0569StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0569StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3007454792385135386557447160398116569795982507, 3007454792385135386557447160398116569795982508⟩
def centerAExp : DyadicInterval precision := ⟨1455499088168743985690617101081856958065120579782, 1455499088168743985690617101081856960264143835335⟩
def centerALog : DyadicInterval precision := ⟨1010031378851376569271247815372298287995916580825, 1010031378851376569271247815372298290194939836378⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455499088168743985690617101081856958614876393670, scale precision, 1455499088168743985690617101081856959714388021447, scale precision,
    0, 128, 0, 128, ⟨-6014909584770270773114894320796233691616047245, -6014909584770270773114894320796233691613950092⟩, ⟨-6014909584770270773114894320796232587569979939, -6014909584770270773114894320796232587567882786⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨557075069631301290362165038182134082283955558325, 557075069631301290362165038182134082283955558326⟩
def centerDExp : DyadicInterval precision := ⟨681902880895464588128477464036409276306339175751, 681902880895464588128477464036409278505362431304⟩
def centerDLog : DyadicInterval precision := ⟨559654335205987407427227649575573486508888333329, 559654335205987407427227649575573488707911588882⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨681902880895464588128477464036409276856094989639, scale precision, 681902880895464588128477464036409277955606617416, scale precision,
    1, 128, 1, 128, ⟨-1114150139262602580724330076364268165746187026121, -1114150139262602580724330076364268165746184928968⟩, ⟨-1114150139262602580724330076364268163389637304333, -1114150139262602580724330076364268163389635207180⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨560568084769769355751473604285230595242129881275, 560568084769769355751473604285230595242129881276⟩
def centerCExp : DyadicInterval precision := ⟨678651138566627703753808592917503514214642748637, 678651138566627703753808592917503516413666004190⟩
def centerCLog : DyadicInterval precision := ⟨557435418859435711647271095498896370788634360145, 557435418859435711647271095498896372987657615698⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨678651138566627703753808592917503514764398562525, scale precision, 678651138566627703753808592917503515863910190302, scale precision,
    1, 128, 1, 128, ⟨-1121136169539538711502947208570461191668181350667, -1121136169539538711502947208570461191668179253514⟩, ⟨-1121136169539538711502947208570461189300340271590, -1121136169539538711502947208570461189300338174437⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1293899241922139550933164131292639996708073682735, 1293899241922139550933164131292639996708073682736⟩
def centerBExp : DyadicInterval precision := ⟨248781780817998827210039288786812270173881265440, 248781780817998827210039288786812272372904520993⟩
def centerBLog : DyadicInterval precision := ⟨229740271255155740879577785641217763401505793588, 229740271255155740879577785641217765600529049141⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨248781780817998827210039288786812270723637079328, scale precision, 248781780817998827210039288786812271823148707105, scale precision,
    2, 128, 2, 128, ⟨-2587798483844279101866328262585279996645762011507, -2587798483844279101866328262585279996645759914354⟩, ⟨-2587798483844279101866328262585279990186534816586, -2587798483844279101866328262585279990186532719433⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312260897, 3165742448647063503620071141085134670978073809⟩
def wholeAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1455814397256041217437249255499380274426951865358⟩
def wholeALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1010189349275934740575240882696318024149327762719⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1455814397256041217437249255499380273877196051470, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-5698334436501900088560386446130011618722097206, -5698334436501900088560386446130011618720000053⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨551800421242914454820810459967297938576086292890, 562362779591003425345044647758252905789383238158⟩
def wholeDExp : DyadicInterval precision := ⟨676986443527636285719880989929562986620669078430, 686842745746340006938348233447115253267032256778⟩
def wholeDLog : DyadicInterval precision := ⟨556298163020790248856133545839930268678058727022, 563018755595924057929845042473976397959717252098⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨676986443527636285719880989929562987170424892318, scale precision, 686842745746340006938348233447115252717276442890, scale precision,
    1, 128, 1, 128, ⟨-1124725559182006850690089295516505812765599299460, -1124725559182006850690089295516505812765597202307⟩, ⟨-1103600842485828909641620919934595875982373083786, -1103600842485828909641620919934595875982370986633⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨555101287630724317301305570148481015109508228224, 566048956405302036594749330346065341400904597814⟩
def wholeCExp : DyadicInterval precision := ⟨673580072782068948228961538371724721689604321831, 683747212688317826425246444576045950368056512039⟩
def wholeCLog : DyadicInterval precision := ⟨553968299361214539309221410219483166059529645773, 560911370396177847938484401033216357759335176851⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨673580072782068948228961538371724722239360135719, scale precision, 683747212688317826425246444576045949818300698151, scale precision,
    1, 128, 1, 128, ⟨-1132097912810604073189498660692130683994643961526, -1132097912810604073189498660692130683994641864373⟩, ⟨-1110202575261448634602611140296962029043920909061, -1110202575261448634602611140296962029043918811908⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1278693257066070490810570535403585515964076493846, 1309193195564311044107608210913737679219583067387⟩
def wholeBExp : DyadicInterval precision := ⟨243629111613750990400561021052593784166136713888, 254012846890726687928583468497089310999010833171⟩
def wholeBLog : DyadicInterval precision := ⟨225330475064398082237253558545406153902794744445, 234203592087300546636086378686296301117048171069⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨243629111613750990400561021052593784715892527776, scale precision, 254012846890726687928583468497089310449255019283, scale precision,
    2, 128, 2, 128, ⟨-2618386391128622088215216421827475361737085961641, -2618386391128622088215216421827475361737083864488⟩, ⟨-2557386514132140981621141070807171028765050154067, -2557386514132140981621141070807171028765048056914⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0569StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0570StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0570StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2690879721921964209596752456793030551114759613, 2690879721921964209596752456793030551114759614⟩
def centerAExp : DyadicInterval precision := ⟨1456129774494643406468543322663438605390699476049, 1456129774494643406468543322663438607589722731602⟩
def centerALog : DyadicInterval precision := ⟨1010347336766062430648993258467353377680688109432, 1010347336766062430648993258467353379879711364985⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1456129774494643406468543322663438605940455289937, scale precision, 1456129774494643406468543322663438607039966917714, scale precision,
    0, 128, 0, 128, ⟨-5381759443843928419193504913586061654014506435, -5381759443843928419193504913586061654012409282⟩, ⟨-5381759443843928419193504913586060550446629170, -5381759443843928419193504913586060550444532017⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨567663676182737085008043281595790637958622415352, 567663676182737085008043281595790637958622415353⟩
def centerDExp : DyadicInterval precision := ⟨672093324830871043359987491990956794091407910102, 672093324830871043359987491990956796290431165655⟩
def centerDLog : DyadicInterval precision := ⟨552950239283275349899356499051421616923499990001, 552950239283275349899356499051421619122523245554⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨672093324830871043359987491990956794641163723990, scale precision, 672093324830871043359987491990956795740675351767, scale precision,
    1, 128, 1, 128, ⟨-1135327352365474170016086563191581277112718282361, -1135327352365474170016086563191581277112716185208⟩, ⟨-1135327352365474170016086563191581274721773476199, -1135327352365474170016086563191581274721771379046⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨570804374174719288398429986981096011899891378791, 570804374174719288398429986981096011899891378792⟩
def centerCExp : DyadicInterval precision := ⟨669210929774413931340894545366034377446453989364, 669210929774413931340894545366034379645477244917⟩
def centerCLog : DyadicInterval precision := ⟨550974478526293992039576111935337037981147428197, 550974478526293992039576111935337040180170683750⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨669210929774413931340894545366034377996209803252, scale precision, 669210929774413931340894545366034379095721431029, scale precision,
    1, 128, 1, 128, ⟨-1141608748349438576796859973962192025000405293919, -1141608748349438576796859973962192025000403196766⟩, ⟨-1141608748349438576796859973962192022599162318401, -1141608748349438576796859973962192022599160221248⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1323520132095532348242637420443758351651753456602, 1323520132095532348242637420443758351651753456603⟩
def centerBExp : DyadicInterval precision := ⟨238899093285615897483091981254161400805353570970, 238899093285615897483091981254161403004376826523⟩
def centerBLog : DyadicInterval precision := ⟨221270648269124409189430858349674745688729209921, 221270648269124409189430858349674747887752465474⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨238899093285615897483091981254161401355109384858, scale precision, 238899093285615897483091981254161402454621012635, scale precision,
    2, 128, 2, 128, ⟨-2647040264191064696485274840887516706666722995713, -2647040264191064696485274840887516706666720898560⟩, ⟨-2647040264191064696485274840887516699940292927854, -2647040264191064696485274840887516699940290830701⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 2849167218250950044280193223065006085312260898⟩
def wholeAExp : DyadicInterval precision := ⟨1455814397256041217437249255499380272227928609805, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1010189349275934740575240882696318021950304507166, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455814397256041217437249255499380272777684423693, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-5698334436501900088560386446130012722529043537, -5698334436501900088560386446130012722526946384⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨562362779591003425345044647758252905789383238157, 572977884517961874928161575521614457065497220142⟩
def wholeDExp : DyadicInterval precision := ⟨667223417983630662234844101180676642856752596602, 676986443527636285719880989929562988819692333983⟩
def wholeDLog : DyadicInterval precision := ⟨549610565162722028431892812520915518488782484595, 556298163020790248856133545839930270877081982575⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨667223417983630662234844101180676643406508410490, scale precision, 676986443527636285719880989929562988269936520095, scale precision,
    1, 128, 1, 128, ⟨-1145955769035923749856323151043228915335193363926, -1145955769035923749856323151043228915335191266773⟩, ⟨-1124725559182006850690089295516505810391935750325, -1124725559182006850690089295516505810391933653172⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨565311208506485336356617145709055187973115398754, 576311872960411135781275250290339654214148110810⟩
def wholeCExp : DyadicInterval precision := ⟨664186201691213820714473875448160096848697917643, 674260445900196612400442935956116373983588666037⟩
def wholeCLog : DyadicInterval precision := ⟨547523839003961433647041148994703660527741202431, 554433952746197175533793686558852555706518346187⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨664186201691213820714473875448160097398453731531, scale precision, 674260445900196612400442935956116373433832852149, scale precision,
    1, 128, 1, 128, ⟨-1152623745920822271562550500580679309638001747771, -1152623745920822271562550500580679309637999650618⟩, ⟨-1130622417012970672713234291418110374754601776405, -1130622417012970672713234291418110374754599679252⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1308144663050354424586377192523512508722977195420, 1338982582539360470879974385816609223046114525916⟩
def wholeBExp : DyadicInterval precision := ⟨233897172054041643994244457485096478958012437358, 243978938664234210632066399729445591452302116589⟩
def wholeBLog : DyadicInterval precision := ⟨216965140084332544136277106501232773694821326736, 225630288065732009115102913342856964408822700279⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨233897172054041643994244457485096479507768251246, scale precision, 243978938664234210632066399729445590902546302701, scale precision,
    2, 128, 2, 128, ⟨-2677965165078720941759948771633218449527367922191, -2677965165078720941759948771633218449527365825038⟩, ⟨-2616289326100708849172754385047025014152765352889, -2616289326100708849172754385047025014152763255736⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0570StableWitnesses

end


