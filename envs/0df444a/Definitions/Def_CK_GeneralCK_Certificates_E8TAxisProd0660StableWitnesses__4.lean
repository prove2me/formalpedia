-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0660StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0660StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:55:31.830366+00:00
-- url     : https://prove2.me/theorems/0b721f3f-e640-42af-8c49-914a0a8acc96
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0660StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0661StableWitnesses, GeneralCK.Certificates.E8TAxisProd06…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0660StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0661StableWitnesses, GeneralCK.Certificates.E8TAxisProd0662StableWitnesses, GeneralCK.Certificates.E8TAxisProd0663StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0660StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0661StableWitnesses, GeneralCK.Certificates.E8TAxisProd0662StableWitnesses, GeneralCK.Certificates.E8TAxisProd0663StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0660StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0661StableWitnesses, GeneralCK.Certificates.E8TAxisProd0662StableWitnesses, GeneralCK.Certificates.E8TAxisProd0663StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0660StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0661StableWitnesses, GeneralCK/Certificates/E8TAxisProd0662StableWitnesses, GeneralCK/Certificates/E8TAxisProd0663StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0660StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0660StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1741156135795404262119345367673058305863553519, 1741156135795404262119345367673058305863553520⟩
def centerAExp : DyadicInterval precision := ⟨1458023470409865756601312007099833957031930691260, 1458023470409865756601312007099833959230953946813⟩
def centerALog : DyadicInterval precision := ⟨1011295620324512224091084430898450250872009997488, 1011295620324512224091084430898450253071033253041⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458023470409865756601312007099833957581686505148, scale precision, 1458023470409865756601312007099833958681198132925, scale precision,
    0, 128, 0, 128, ⟨-3482312271590808524238690735346117162795431580, -3482312271590808524238690735346117162793334427⟩, ⟨-3482312271590808524238690735346116060660879652, -3482312271590808524238690735346116060658782499⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨546538709428945749870773924191788198118687927157, 546538709428945749870773924191788198118687927158⟩
def centerDExp : DyadicInterval precision := ⟨691806148899640566657527120936512860452889890625, 691806148899640566657527120936512862651913146178⟩
def centerDLog : DyadicInterval precision := ⟨566391424872267910855012963449734473930997225626, 566391424872267910855012963449734476130020481179⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨691806148899640566657527120936512861002645704513, scale precision, 691806148899640566657527120936512862102157332290, scale precision,
    1, 128, 1, 128, ⟨-1093077418857891499741547848383576397398784651881, -1093077418857891499741547848383576397398782554728⟩, ⟨-1093077418857891499741547848383576395075969153903, -1093077418857891499741547848383576395075967056750⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨548550366145150196317813977139868849007286544805, 548550366145150196317813977139868849007286544806⟩
def centerCExp : DyadicInterval precision := ⟨689904320451970416257276583478983631160859095794, 689904320451970416257276583478983633359882351347⟩
def centerCLog : DyadicInterval precision := ⟨565100037924691344158021867063560083068269883805, 565100037924691344158021867063560085267293139358⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨689904320451970416257276583478983631710614909682, scale precision, 689904320451970416257276583478983632810126537459, scale precision,
    1, 128, 1, 128, ⟨-1097100732290300392635627954279737699179183488080, -1097100732290300392635627954279737699179181390927⟩, ⟨-1097100732290300392635627954279737696849964788293, -1097100732290300392635627954279737696849962691140⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1262030173791323061775270330140342410129489632587, 1262030173791323061775270330140342410129489632588⟩
def centerBExp : DyadicInterval precision := ⟨259871566125798882025316147068054432418029128466, 259871566125798882025316147068054434617052384019⟩
def centerBLog : DyadicInterval precision := ⟨239186318802094284604366906832104680520216792208, 239186318802094284604366906832104682719240047761⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨259871566125798882025316147068054432967784942354, scale precision, 259871566125798882025316147068054434067296570131, scale precision,
    2, 128, 2, 128, ⟨-2524060347582646123550540660280684823350773056253, -2524060347582646123550540660280684823350770959100⟩, ⟨-2524060347582646123550540660280684817167187571251, -2524060347582646123550540660280684817167185474098⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1582869063071984205522252427078437298396921978, 1899443256066344012630337314537754309230277492⟩
def wholeAExp : DyadicInterval precision := ⟨1457707683773513925477741956702213444480153619489, 1458339325360928401721230227698749082343136271522⟩
def wholeALog : DyadicInterval precision := ⟨1011137530350683182654731711817158197559546439255, 1011453727394019217297123487654775992957886515170⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1457707683773513925477741956702213445029909433377, scale precision, 1458339325360928401721230227698749081793380457634, scale precision,
    0, 128, 0, 128, ⟨-3798886512132688025260674629075509169648258520, -3798886512132688025260674629075509169646161367⟩, ⟨-3165738126143968411044504854156874045846969675, -3165738126143968411044504854156874045844872522⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨541289809268942399956535792498120861936820641712, 551800421242914454820810459967297938576086292891⟩
def wholeDExp : DyadicInterval precision := ⟨686842745746340006938348233447115251068009001225, 696793203199184192771083052087923261448554764920⟩
def wholeDLog : DyadicInterval precision := ⟨563018755595924057929845042473976395760693996545, 569772344639491636839148332004312891755835414717⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨686842745746340006938348233447115251617764815113, scale precision, 696793203199184192771083052087923260898798951032, scale precision,
    1, 128, 1, 128, ⟨-1103600842485828909641620919934595878321974184929, -1103600842485828909641620919934595878321972087776⟩, ⟨-1082579618537884799913071584996241722720546953858, -1082579618537884799913071584996241722720544856705⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨543114068354268668262588842166456947222240766273, 554000433503825012123662242287602563121434110566⟩
def wholeCExp : DyadicInterval precision := ⟨684778033552071001269599362921260133737500125004, 695055885934021727112508856317500128400898280889⟩
def wholeCLog : DyadicInterval precision := ⟨561613472876357606435164045606356037650420487836, 568595436624694893030246324368141867830961842876⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨684778033552071001269599362921260134287255938892, scale precision, 695055885934021727112508856317500127851142467001, scale precision,
    1, 128, 1, 128, ⟨-1108000867007650024247324484575205127416196950740, -1108000867007650024247324484575205127416194853587⟩, ⟨-1086228136708537336525177684332913893288504999480, -1086228136708537336525177684332913893288502902327⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1247010520844582423370759880370954134460850870370, 1277138660620720490328816060139948074117166135465⟩
def wholeBExp : DyadicInterval precision := ⟨254553808047124850002238322115775941583620238619, 265268165523649043952818121627380415436451145151⟩
def wholeBLog : DyadicInterval precision := ⟨234664381544358065896158973909626125229547346328, 243761039329222190336679001571779741068980462152⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨254553808047124850002238322115775942133376052507, scale precision, 265268165523649043952818121627380414886695331263, scale precision,
    2, 128, 2, 128, ⟨-2554277321241440980657632120279896151390715179570, -2554277321241440980657632120279896151390713082417⟩, ⟨-2494021041689164846741519760741908265892809290004, -2494021041689164846741519760741908265892807192851⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0660StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0661StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0661StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1741156135795404262119345367673058305863553519, 1741156135795404262119345367673058305863553520⟩
def centerAExp : DyadicInterval precision := ⟨1458023470409865756601312007099833957031930691260, 1458023470409865756601312007099833959230953946813⟩
def centerALog : DyadicInterval precision := ⟨1011295620324512224091084430898450250872009997488, 1011295620324512224091084430898450253071033253041⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458023470409865756601312007099833957581686505148, scale precision, 1458023470409865756601312007099833958681198132925, scale precision,
    0, 128, 0, 128, ⟨-3482312271590808524238690735346117162795431580, -3482312271590808524238690735346117162793334427⟩, ⟨-3482312271590808524238690735346116060660879652, -3482312271590808524238690735346116060658782499⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨538055526195232767375495206525415972741527492727, 538055526195232767375495206525415972741527492728⟩
def centerCExp : DyadicInterval precision := ⟨699884025700765353035449847949581955872615286482, 699884025700765353035449847949581958071638542035⟩
def centerCLog : DyadicInterval precision := ⟨571863815485047821267389264866984197739458039102, 571863815485047821267389264866984199938481294655⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨699884025700765353035449847949581956422371100370, scale precision, 699884025700765353035449847949581957521882728147, scale precision,
    1, 128, 1, 128, ⟨-1076111052390465534750990413050831946631059121152, -1076111052390465534750990413050831946631057023999⟩, ⟨-1076111052390465534750990413050831944335052946912, -1076111052390465534750990413050831944335050849759⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1232589004181237640646238105414016181887374700538, 1232589004181237640646238105414016181887374700539⟩
def centerBExp : DyadicInterval precision := ⟨270555286557991678089410585118037104535451101605, 270555286557991678089410585118037106734474357158⟩
def centerBLog : DyadicInterval precision := ⟨248229110543707448580316654058258588474841242845, 248229110543707448580316654058258590673864498398⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨270555286557991678089410585118037105085206915493, scale precision, 270555286557991678089410585118037106184718543270, scale precision,
    2, 128, 2, 128, ⟨-2465178008362475281292476210828032366744454100067, -2465178008362475281292476210828032366744452002914⟩, ⟨-2465178008362475281292476210828032360805046799238, -2465178008362475281292476210828032360805044702085⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1582869063071984205522252427078437298396921978, 1899443256066344012630337314537754309230277492⟩
def wholeAExp : DyadicInterval precision := ⟨1457707683773513925477741956702213444480153619489, 1458339325360928401721230227698749082343136271522⟩
def wholeALog : DyadicInterval precision := ⟨1011137530350683182654731711817158197559546439255, 1011453727394019217297123487654775992957886515170⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1457707683773513925477741956702213445029909433377, scale precision, 1458339325360928401721230227698749081793380457634, scale precision,
    0, 128, 0, 128, ⟨-3798886512132688025260674629075509169648258520, -3798886512132688025260674629075509169646161367⟩, ⟨-3165738126143968411044504854156874045846969675, -3165738126143968411044504854156874045844872522⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨532645449831759162196297561080491466860611335961, 543479104820114982152937417998735313320844945624⟩
def wholeCExp : DyadicInterval precision := ⟨694708767084621674124513518123287224531304063580, 705084809452445858279336861265266597621646235227⟩
def wholeCLog : DyadicInterval precision := ⟨568360174827005297736903883188741740999342798618, 575376295433731289279230414097550835243392047238⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨694708767084621674124513518123287225081059877468, scale precision, 705084809452445858279336861265266597071890421339, scale precision,
    1, 128, 1, 128, ⟨-1086958209640229964305874835997470627798246118337, -1086958209640229964305874835997470627798244021184⟩, ⟨-1065290899663518324392595122160982932581688431470, -1065290899663518324392595122160982932581686334317⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1217744907754159102805678786011387963127298249397, 1247522542888921187994469339366283873242165079069⟩
def wholeBExp : DyadicInterval precision := ⟨265082362686605076784619213339191668769248663509, 276107408102344063593065228501385032168880429797⟩
def wholeBLog : DyadicInterval precision := ⟨243603771255156524408818265845549816608738506524, 252906472413951859664376424936907434307577272250⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨265082362686605076784619213339191669319004477397, scale precision, 276107408102344063593065228501385031619124615909, scale precision,
    2, 128, 2, 128, ⟨-2495045085777842375988938678732567749515347733000, -2495045085777842375988938678732567749515345635847⟩, ⟨-2435489815508318205611357572022775923344610351982, -2435489815508318205611357572022775923344608254829⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0661StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0662StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0662StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1424582033573572438591305530993584070055182816, 1424582033573572438591305530993584070055182817⟩
def centerAExp : DyadicInterval precision := ⟨1458655248650088110751137895023802507105717993838, 1458655248650088110751137895023802509304741249391⟩
def centerALog : DyadicInterval precision := ⟨1011611851563511234375923245561748361600484378174, 1011611851563511234375923245561748363799507633727⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458655248650088110751137895023802507655473807726, scale precision, 1458655248650088110751137895023802508754985435503, scale precision,
    0, 128, 0, 128, ⟨-2849164067147144877182611061987168690940009844, -2849164067147144877182611061987168690937912691⟩, ⟨-2849164067147144877182611061987167589282818573, -2849164067147144877182611061987167589280721420⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨546538709428945749870773924191788198118687927157, 546538709428945749870773924191788198118687927158⟩
def centerDExp : DyadicInterval precision := ⟨691806148899640566657527120936512860452889890625, 691806148899640566657527120936512862651913146178⟩
def centerDLog : DyadicInterval precision := ⟨566391424872267910855012963449734473930997225626, 566391424872267910855012963449734476130020481179⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨691806148899640566657527120936512861002645704513, scale precision, 691806148899640566657527120936512862102157332290, scale precision,
    1, 128, 1, 128, ⟨-1093077418857891499741547848383576397398784651881, -1093077418857891499741547848383576397398782554728⟩, ⟨-1093077418857891499741547848383576395075969153903, -1093077418857891499741547848383576395075967056750⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨548184470564021894512387514941953804791933066325, 548184470564021894512387514941953804791933066326⟩
def centerCExp : DyadicInterval precision := ⟨690249850206347754603718482044273398877553247943, 690249850206347754603718482044273401076576503496⟩
def centerCLog : DyadicInterval precision := ⟨565334745722056997940983659274556681089753644383, 565334745722056997940983659274556683288776899936⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨690249850206347754603718482044273399427309061831, scale precision, 690249850206347754603718482044273400526820689608, scale precision,
    1, 128, 1, 128, ⟨-1096368941128043789024775029883907610747893543408, -1096368941128043789024775029883907610747891446255⟩, ⟨-1096368941128043789024775029883907608419840819050, -1096368941128043789024775029883907608419838721897⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1261515212730188967598312162298199104278273688972, 1261515212730188967598312162298199104278273688973⟩
def centerBExp : DyadicInterval precision := ⟨260054762501350142609741679632833927292121681848, 260054762501350142609741679632833929491144937401⟩
def centerBLog : DyadicInterval precision := ⟨239341850186075047601140695797897707224424408747, 239341850186075047601140695797897709423447664300⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨260054762501350142609741679632833927841877495736, scale precision, 260054762501350142609741679632833928941389123513, scale precision,
    2, 128, 2, 128, ⟨-2523030425460377935196624324596398211646163146135, -2523030425460377935196624324596398211646161048982⟩, ⟨-2523030425460377935196624324596398205466933706904, -2523030425460377935196624324596398205466931609751⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 1582869063071984205522252427078437298396921979⟩
def wholeAExp : DyadicInterval precision := ⟨1458339325360928401721230227698749080144113015969, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1011453727394019217297123487654775990758863259617, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458339325360928401721230227698749080693868829857, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-3165738126143968411044504854156875147742815392, -3165738126143968411044504854156875147740718239⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨541289809268942399956535792498120861936820641712, 551800421242914454820810459967297938576086292891⟩
def wholeDExp : DyadicInterval precision := ⟨686842745746340006938348233447115251068009001225, 696793203199184192771083052087923261448554764920⟩
def wholeDLog : DyadicInterval precision := ⟨563018755595924057929845042473976395760693996545, 569772344639491636839148332004312891755835414717⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨686842745746340006938348233447115251617764815113, scale precision, 696793203199184192771083052087923260898798951032, scale precision,
    1, 128, 1, 128, ⟨-1103600842485828909641620919934595878321974184929, -1103600842485828909641620919934595878321972087776⟩, ⟨-1082579618537884799913071584996241722720546953858, -1082579618537884799913071584996241722720544856705⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨542749093494038944780073393512148392763110327956, 553633607897550914157789526569935476549321922279⟩
def wholeCExp : DyadicInterval precision := ⟨685121867823938455553124774054258053967949946649, 695403119599511953042005088554461632004956729619⟩
def wholeCLog : DyadicInterval precision := ⟨561847586869509954488003537012061231343123291057, 568830738356242015179659741123858552550222384660⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨685121867823938455553124774054258054517705760537, scale precision, 695403119599511953042005088554461631455200915731, scale precision,
    1, 128, 1, 128, ⟨-1107267215795101828315579053139870954271383729630, -1107267215795101828315579053139870954271381632477⟩, ⟨-1085498186988077889560146787024296784370821333849, -1085498186988077889560146787024296784370819236696⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1246498603026250655392578008129787970109182221023, 1276620668557843420799081521959812638844280769427⟩
def wholeBExp : DyadicInterval precision := ⟨254734312253380017210503759009619482476048109689, 265454060733175372864005382688728719096523501950⟩
def wholeBLog : DyadicInterval precision := ⟨234818102288242134203976341290218377919046810346, 243918368655646541605429715408456020939558516621⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨254734312253380017210503759009619483025803923577, scale precision, 265454060733175372864005382688728718546767688062, scale precision,
    2, 128, 2, 128, ⟨-2553241337115686841598163043919625280842707841842, -2553241337115686841598163043919625280842705744689⟩, ⟨-2492997206052501310785156016259575937191593099534, -2492997206052501310785156016259575937191591002381⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0662StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0663StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0663StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1424582033573572438591305530993584070055182816, 1424582033573572438591305530993584070055182817⟩
def centerAExp : DyadicInterval precision := ⟨1458655248650088110751137895023802507105717993838, 1458655248650088110751137895023802509304741249391⟩
def centerALog : DyadicInterval precision := ⟨1011611851563511234375923245561748361600484378174, 1011611851563511234375923245561748363799507633727⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458655248650088110751137895023802507655473807726, scale precision, 1458655248650088110751137895023802508754985435503, scale precision,
    0, 128, 0, 128, ⟨-2849164067147144877182611061987168690940009844, -2849164067147144877182611061987168690937912691⟩, ⟨-2849164067147144877182611061987167589282818573, -2849164067147144877182611061987167589280721420⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨537691401777813747658835575701738643084239573746, 537691401777813747658835575701738643084239573747⟩
def centerCExp : DyadicInterval precision := ⟨700232856465279399580166737315676895289917665847, 700232856465279399580166737315676897488940921400⟩
def centerCLog : DyadicInterval precision := ⟨572099671402117308658897195008076873590317997681, 572099671402117308658897195008076875789341253234⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨700232856465279399580166737315676895839673479735, scale precision, 700232856465279399580166737315676896939185107512, scale precision,
    1, 128, 1, 128, ⟨-1075382803555627495317671151403477287315911389440, -1075382803555627495317671151403477287315909292287⟩, ⟨-1075382803555627495317671151403477285021049002702, -1075382803555627495317671151403477285021046905549⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1232080035570945139195978903704229363413377947203, 1232080035570945139195978903704229363413377947204⟩
def centerBExp : DyadicInterval precision := ⟨270743794201576930992265469009174443763249487322, 270743794201576930992265469009174445962272742875⟩
def centerBLog : DyadicInterval precision := ⟨248388163768140938907335178276606667741715613659, 248388163768140938907335178276606669940738869212⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨270743794201576930992265469009174444313005301210, scale precision, 270743794201576930992265469009174445412516928987, scale precision,
    2, 128, 2, 128, ⟨-2464160071141890278391957807408458729794392912259, -2464160071141890278391957807408458729794390815106⟩, ⟨-2464160071141890278391957807408458723859120973712, -2464160071141890278391957807408458723859118876559⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 1582869063071984205522252427078437298396921979⟩
def wholeAExp : DyadicInterval precision := ⟨1458339325360928401721230227698749080144113015969, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1011453727394019217297123487654775990758863259617, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458339325360928401721230227698749080693868829857, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-3165738126143968411044504854156875147742815392, -3165738126143968411044504854156875147740718239⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨532282228172866116854382691727110279060616762140, 543114068354268668262588842166456947222240766274⟩
def wholeCExp : DyadicInterval precision := ⟨695055885934021727112508856317500126201875025336, 705435360866505781316672671624606264995864481359⟩
def wholeCLog : DyadicInterval precision := ⟨568595436624694893030246324368141865631938587323, 575612745737157315624533178384052512555325538795⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨695055885934021727112508856317500126751630839224, scale precision, 705435360866505781316672671624606264446108667471, scale precision,
    1, 128, 1, 128, ⟨-1086228136708537336525177684332913895600460162770, -1086228136708537336525177684332913895600458065617⟩, ⟨-1064564456345732233708765383454220556982265552162, -1064564456345732233708765383454220556982263455009⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1217239001437486599715214062593104088327201605187, 1247010520844582423370759880370954134460850870371⟩
def wholeBExp : DyadicInterval precision := ⟨265268165523649043952818121627380413237427889598, 276298626287712738569478063235137594687948108097⟩
def wholeBLog : DyadicInterval precision := ⟨243761039329222190336679001571779738869957206599, 253067297034268024660477759355581073793146424089⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨265268165523649043952818121627380413787183703486, scale precision, 276298626287712738569478063235137594138192294209, scale precision,
    2, 128, 2, 128, ⟨-2494021041689164846741519760741908271950596288637, -2494021041689164846741519760741908271950594191484⟩, ⟨-2434478002874973199430428125186208173746430980455, -2434478002874973199430428125186208173746428883302⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0663StableWitnesses

end


