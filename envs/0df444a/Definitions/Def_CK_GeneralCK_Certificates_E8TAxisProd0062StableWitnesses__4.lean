-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0062StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0062StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:59:24.485918+00:00
-- url     : https://prove2.me/theorems/229f2ca8-09eb-4a85-b895-2ec5a818428b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0062StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0063StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0062StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0063StableWitnesses, GeneralCK.Certificates.E8TAxisProd0064StableWitnesses, GeneralCK.Certificates.E8TAxisProd0065StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0062StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0063StableWitnesses, GeneralCK.Certificates.E8TAxisProd0064StableWitnesses, GeneralCK.Certificates.E8TAxisProd0065StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0062StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0063StableWitnesses, GeneralCK.Certificates.E8TAxisProd0064StableWitnesses, GeneralCK.Certificates.E8TAxisProd0065StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0062StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0063StableWitnesses, GeneralCK/Certificates/E8TAxisProd0064StableWitnesses, GeneralCK/Certificates/E8TAxisProd0065StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0062StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0062StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨199272515379397466243712200840066988851184259851, 199272515379397466243712200840066988851184259852⟩
def centerDExp : DyadicInterval precision := ⟨1112677029363765823963422130229284076021359517329, 1112677029363765823963422130229284078220382772882⟩
def centerDLog : DyadicInterval precision := ⟨827306521710622256038181567611853437995191413469, 827306521710622256038181567611853440194214669022⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1112677029363765823963422130229284076571115331217, scale precision, 1112677029363765823963422130229284077670626958994, scale precision,
    0, 128, 0, 128, ⟨-398545030758794932487424401680133978424474007328, -398545030758794932487424401680133978424471910175⟩, ⟨-398545030758794932487424401680133976980265129232, -398545030758794932487424401680133976980263032079⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨203802040624012852586366857882370360086913604468, 203802040624012852586366857882370360086913604469⟩
def centerCExp : DyadicInterval precision := ⟨1105801483010104524876835505205719392959862188974, 1105801483010104524876835505205719395158885444527⟩
def centerCLog : DyadicInterval precision := ⟨823397676494555074992354335814380345069644035678, 823397676494555074992354335814380347268667291231⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1105801483010104524876835505205719393509618002862, scale precision, 1105801483010104524876835505205719394609129630639, scale precision,
    0, 128, 0, 128, ⟨-407604081248025705172733715764740720900422528254, -407604081248025705172733715764740720900420431101⟩, ⟨-407604081248025705172733715764740719447233986775, -407604081248025705172733715764740719447231889622⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨412013103369899024069530913214965111556865971996, 412013103369899024069530913214965111556865971997⟩
def centerBExp : DyadicInterval precision := ⟨831638702309372174108721356206934855037146851301, 831638702309372174108721356206934857236170106854⟩
def centerBLog : DyadicInterval precision := ⟨658344782481043794267062701001445088728988824785, 658344782481043794267062701001445090928012080338⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨831638702309372174108721356206934855586902665189, scale precision, 831638702309372174108721356206934856686414292966, scale precision,
    0, 128, 0, 128, ⟨-824026206739798048139061826429930224079860494691, -824026206739798048139061826429930224079858397538⟩, ⟨-824026206739798048139061826429930222147605490447, -824026206739798048139061826429930222147603393294⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨191194719185872429583518944051791718612165764688, 207364037900146833805279022757379167895402526014⟩
def wholeDExp : DyadicInterval precision := ⟨1100424441361699833197968540687666012888098379856, 1125044909933745912773463128462173915391977363052⟩
def wholeDLog : DyadicInterval precision := ⟨820333450761233184846212780159319756857071966390, 834311627217828832252519695712052890740898632922⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1100424441361699833197968540687666013437854193744, scale precision, 1125044909933745912773463128462173914842221549164, scale precision,
    0, 128, 0, 128, ⟨-414728075800293667610558045514758336520950753820, -414728075800293667610558045514758336520948656667⟩, ⟨-382389438371744859167037888103583436510166401088, -382389438371744859167037888103583436510164303935⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨195070384091725537299207625964822441604096874997, 212550077699428455989854073007082018901742822767⟩
def wholeCExp : DyadicInterval precision := ⟨1092642524092652140066262196305827179357671526605, 1119093832522548353760792784395684186476972512655⟩
def wholeCLog : DyadicInterval precision := ⟨815887345423414633040468176727720343602299791764, 830945157630913290200624245407414190058998920140⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1092642524092652140066262196305827179907427340493, scale precision, 1119093832522548353760792784395684185927216698767, scale precision,
    0, 128, 0, 128, ⟨-425100155398856911979708146014164038538831515873, -425100155398856911979708146014164038538829418720⟩, ⟨-390140768183451074598415251929644882490230854191, -390140768183451074598415251929644882490228757038⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨394131280415088114324880764542299808171984852989, 430020255848871057996723868378530389896812048619⟩
def wholeBExp : DyadicInterval precision := ⟨811395907539575989205372525227068894781030924708, 852240338090969698012242422231538058144447605840⟩
def wholeBLog : DyadicInterval precision := ⟨645386032564338615019803630851229122526109369488, 671416323310479763794961458183140405442526050520⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨811395907539575989205372525227068895330786738596, scale precision, 852240338090969698012242422231538057594691791952, scale precision,
    0, 128, 0, 128, ⟨-860040511697742115993447736757060780783855703627, -860040511697742115993447736757060780783853606474⟩, ⟨-788262560830176228649761529084599615401197940106, -788262560830176228649761529084599615401195842953⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0062StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0063StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0063StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨215469853832861228733019240262249168447508352861, 215469853832861228733019240262249168447508352862⟩
def centerDExp : DyadicInterval precision := ⟨1088285489568234168416510694967649720478852956927, 1088285489568234168416510694967649722677876212480⟩
def centerDLog : DyadicInterval precision := ⟨813392086659747652895796213383370383407954793069, 813392086659747652895796213383370385606978048622⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1088285489568234168416510694967649721028608770815, scale precision, 1088285489568234168416510694967649722128120398592, scale precision,
    0, 128, 0, 128, ⟨-430939707665722457466038480524498337633306585522, -430939707665722457466038480524498337633304488369⟩, ⟨-430939707665722457466038480524498336156728923076, -430939707665722457466038480524498336156726825923⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨218716309774253515715349559598011326794849994989, 218716309774253515715349559598011326794849994990⟩
def centerCExp : DyadicInterval precision := ⟨1083461363001147522481644668816972141344008008553, 1083461363001147522481644668816972143543031264106⟩
def centerCLog : DyadicInterval precision := ⟨810624347003225179965347206965641653964661957660, 810624347003225179965347206965641656163685213213⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1083461363001147522481644668816972141893763822441, scale precision, 1083461363001147522481644668816972142993275450218, scale precision,
    0, 128, 0, 128, ⟨-437432619548507031430699119196022654331277110918, -437432619548507031430699119196022654331275013765⟩, ⟨-437432619548507031430699119196022652848124966194, -437432619548507031430699119196022652848122869041⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨445359177715611993933353881900193063997754999603, 445359177715611993933353881900193063997754999604⟩
def centerBExp : DyadicInterval precision := ⟨794541703289763978788855372038777171274983996626, 794541703289763978788855372038777173474007252179⟩
def centerBLog : DyadicInterval precision := ⟨634508186532076657859391026509774320950359466171, 634508186532076657859391026509774323149382721724⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨794541703289763978788855372038777171824739810514, scale precision, 794541703289763978788855372038777172924251438291, scale precision,
    0, 128, 0, 128, ⟨-890718355431223987866707763800386129006746856809, -890718355431223987866707763800386129006744759656⟩, ⟨-890718355431223987866707763800386126984275238759, -890718355431223987866707763800386126984273141606⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨207364037900146833805279022757379167895402526013, 223590532296792858273138350117122513977217811277⟩
def wholeDExp : DyadicInterval precision := ⟨1076258554488359441934578352032876247847469232020, 1100424441361699833197968540687666015087121635409⟩
def wholeDLog : DyadicInterval precision := ⟨806482109433465224369192354012429699430722065898, 820333450761233184846212780159319759056095221943⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1076258554488359441934578352032876248397225045908, scale precision, 1100424441361699833197968540687666014537365821521, scale precision,
    0, 128, 0, 128, ⟨-447181064593585716546276700234245028700975705620, -447181064593585716546276700234245028700973608467⟩, ⟨-414728075800293667610558045514758335060661447385, -414728075800293667610558045514758335060659350232⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨209956316671997090000842133265351880706535748528, 227493904775828364443481753968725214648101220907⟩
def wholeCExp : DyadicInterval precision := ⟨1070524947694947175059872365104781307820615696770, 1096527691430814070408977739606207489392109661352⟩
def wholeCLog : DyadicInterval precision := ⟨803176377000203245651677875656754746083613733583, 818108780016791024693045805775745556061045574755⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1070524947694947175059872365104781308370371510658, scale precision, 1096527691430814070408977739606207488842353847464, scale precision,
    0, 128, 0, 128, ⟨-454987809551656728886963507937450430046740900901, -454987809551656728886963507937450430046738803748⟩, ⟨-419912633343994180001684266530703760680333164395, -419912633343994180001684266530703760680331067242⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨427241540043944272767980241125254450224304692813, 463612671914032783328998846535993879410036316003⟩
def wholeBExp : DyadicInterval precision := ⟨774940598619922204718906818259703490442086684951, 814487153830654407329274835310961499888476655083⟩
def wholeBLog : DyadicInterval precision := ⟨621754788502250965904765341100031121398808270960, 647372392247794569856006880382232491239115169741⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨774940598619922204718906818259703490991842498839, scale precision, 814487153830654407329274835310961499338720841195, scale precision,
    0, 128, 0, 128, ⟨-927225343828065566657997693071987759856887371285, -927225343828065566657997693071987759856885274132⟩, ⟨-854483080087888545535960482250508899462138126627, -854483080087888545535960482250508899462136029474⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0063StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0064StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0064StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨199272515379397466243712200840066988851184259851, 199272515379397466243712200840066988851184259852⟩
def centerDExp : DyadicInterval precision := ⟨1112677029363765823963422130229284076021359517329, 1112677029363765823963422130229284078220382772882⟩
def centerDLog : DyadicInterval precision := ⟨827306521710622256038181567611853437995191413469, 827306521710622256038181567611853440194214669022⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1112677029363765823963422130229284076571115331217, scale precision, 1112677029363765823963422130229284077670626958994, scale precision,
    0, 128, 0, 128, ⟨-398545030758794932487424401680133978424474007328, -398545030758794932487424401680133978424471910175⟩, ⟨-398545030758794932487424401680133976980265129232, -398545030758794932487424401680133976980263032079⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨202507445516537500012131595254672422594967063253, 202507445516537500012131595254672422594967063254⟩
def centerCExp : DyadicInterval precision := ⟨1107762252645637980489192806237745350742128503631, 1107762252645637980489192806237745352941151759184⟩
def centerCLog : DyadicInterval precision := ⟨824513467709269488069291355952413269384983419907, 824513467709269488069291355952413271584006675460⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1107762252645637980489192806237745351291884317519, scale precision, 1107762252645637980489192806237745352391395945296, scale precision,
    0, 128, 0, 128, ⟨-405014891033075000024263190509344845915243353992, -405014891033075000024263190509344845915241256839⟩, ⟨-405014891033075000024263190509344844464626996174, -405014891033075000024263190509344844464624899021⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨410633201084391467870583087491309252328333438807, 410633201084391467870583087491309252328333438808⟩
def centerBExp : DyadicInterval precision := ⟨833210598374149454201945420759125265341111609227, 833210598374149454201945420759125267540134864780⟩
def centerBLog : DyadicInterval precision := ⟨659346265734723569464142280950708826813191231787, 659346265734723569464142280950708829012214487340⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨833210598374149454201945420759125265890867423115, scale precision, 833210598374149454201945420759125266990379050892, scale precision,
    0, 128, 0, 128, ⟨-821266402168782935741166174982618505620972777447, -821266402168782935741166174982618505620970680294⟩, ⟨-821266402168782935741166174982618503692363074935, -821266402168782935741166174982618503692360977782⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨191194719185872429583518944051791718612165764688, 207364037900146833805279022757379167895402526014⟩
def wholeDExp : DyadicInterval precision := ⟨1100424441361699833197968540687666012888098379856, 1125044909933745912773463128462173915391977363052⟩
def wholeDLog : DyadicInterval precision := ⟨820333450761233184846212780159319756857071966390, 834311627217828832252519695712052890740898632922⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1100424441361699833197968540687666013437854193744, scale precision, 1125044909933745912773463128462173914842221549164, scale precision,
    0, 128, 0, 128, ⟨-414728075800293667610558045514758336520950753820, -414728075800293667610558045514758336520948656667⟩, ⟨-382389438371744859167037888103583436510166401088, -382389438371744859167037888103583436510164303935⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨193778155013554683299889988710244792947684043083, 211253010738814688741513314259447908539070264892⟩
def wholeCExp : DyadicInterval precision := ⟨1094583663264658192859639577095084240099742816761, 1121074541873184918683835318833754696716371101054⟩
def wholeCLog : DyadicInterval precision := ⟨816997658858733881976258143282406435194459036245, 832066487812359628690065743459079147773281772204⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1094583663264658192859639577095084240649498630649, scale precision, 1121074541873184918683835318833754696166615287166, scale precision,
    0, 128, 0, 128, ⟨-422506021477629377483026628518895817812182336590, -422506021477629377483026628518895817812180239437⟩, ⟨-387556310027109366599779977420489585178673685762, -387556310027109366599779977420489585178671588609⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨392760784790180292139123525495050640775660750371, 428630511643972528454174557156597790389313925337⟩
def wholeBExp : DyadicInterval precision := ⟨812940491109497126172575141947222963057498304379, 853840182486705188164996754687631267887724548140⟩
def wholeBLog : DyadicInterval precision := ⟨646378881863236975591500270143725016568888774544, 672426534142843849849723373732993902346578958728⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨812940491109497126172575141947222963607254118267, scale precision, 853840182486705188164996754687631267337968734252, scale precision,
    0, 128, 0, 128, ⟨-857261023287945056908349114313195581766978023100, -857261023287945056908349114313195581766975925947⟩, ⟨-785521569580360584278247050990101280610316212757, -785521569580360584278247050990101280610314115604⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0064StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0065StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0065StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 1899443256066344012630337314537754309230277492⟩
def centerAExp : DyadicInterval precision := ⟨1457707683773513925477741956702213444480153619489, 1457707683773513925477741956702213446679176875042⟩
def centerALog : DyadicInterval precision := ⟨1011137530350683182654731711817158197559546439255, 1011137530350683182654731711817158199758569694808⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457707683773513925477741956702213445029909433377, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-3798886512132688025260674629075509169648258520, -3798886512132688025260674629075509169646161367⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨248047465841179905852080519169529384371630755610, 248047465841179905852080519169529384371630755611⟩
def centerDExp : DyadicInterval precision := ⟨1040834191819245838922303450900148559184359318387, 1040834191819245838922303450900148561383382573940⟩
def centerDLog : DyadicInterval precision := ⟨785937414897454142996966385139071281278247176763, 785937414897454142996966385139071283477270432316⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1040834191819245838922303450900148559734115132275, scale precision, 1040834191819245838922303450900148560833626760052, scale precision,
    0, 128, 0, 128, ⟨-496094931682359811704161038339058769515209742591, -496094931682359811704161038339058769515207645438⟩, ⟨-496094931682359811704161038339058767971315377004, -496094931682359811704161038339058767971313279851⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨250010485980183976055392476858641416483499955009, 250010485980183976055392476858641416483499955010⟩
def centerCExp : DyadicInterval precision := ⟨1038041945019907988417555870178637115729740566111, 1038041945019907988417555870178637117928763821664⟩
def centerCLog : DyadicInterval precision := ⟨784305678760996942073221918091369059578222346533, 784305678760996942073221918091369061777245602086⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1038041945019907988417555870178637116279496379999, scale precision, 1038041945019907988417555870178637117379008007776, scale precision,
    0, 128, 0, 128, ⟨-500020971960367952110784953717282833741024615332, -500020971960367952110784953717282833741022518179⟩, ⟨-500020971960367952110784953717282832192977301859, -500020971960367952110784953717282832192975204706⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨514917795777685095537795947665298298661090422770, 514917795777685095537795947665298298661090422771⟩
def centerBExp : DyadicInterval precision := ⟨722398986344962202368518281249828935445413166130, 722398986344962202368518281249828937644436421683⟩
def centerBLog : DyadicInterval precision := ⟨587009398150422054872458466897927026719725223095, 587009398150422054872458466897927028918748478648⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨722398986344962202368518281249828935995168980018, scale precision, 722398986344962202368518281249828937094680607795, scale precision,
    1, 128, 1, 128, ⟨-1029835591555370191075591895330596598434405246195, -1029835591555370191075591895330596598434403149042⟩, ⟨-1029835591555370191075591895330596596209958542039, -1029835591555370191075591895330596596209956444886⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨239878763828786629732963390089367294542248751090, 256233328382592948799518632260864583083635375284⟩
def wholeDExp : DyadicInterval precision := ⟨1029239839924196772159254586274144058200357824470, 1052534436295863801714746685306812133363569214732⟩
def wholeDLog : DyadicInterval precision := ⟨779149939480909138582665574125961103221748177421, 792755074273575496363197836249071888393767558659⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1029239839924196772159254586274144058750113638358, scale precision, 1052534436295863801714746685306812132813813400844, scale precision,
    0, 128, 0, 128, ⟨-512466656765185897599037264521729166947914940776, -512466656765185897599037264521729166947912843623⟩, ⟨-479757527657573259465926780178734588321132532104, -479757527657573259465926780178734588321130434951⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨241184626806749055639611155786176124284241534580, 258856523389556057576596003104549794743303155872⟩
def wholeCExp : DyadicInterval precision := ⟨1025551774732822142853509456880829104766074972342, 1050655220626468140158581794906027349332101733979⟩
def wholeCLog : DyadicInterval precision := ⟨776984276000630970805974684708486429238247565004, 791662208582552229743762264383106992014978222243⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1025551774732822142853509456880829105315830786230, scale precision, 1050655220626468140158581794906027348782345920091, scale precision,
    0, 128, 0, 128, ⟨-517713046779112115153192006209099590270057832471, -517713046779112115153192006209099590270055735318⟩, ⟨-482369253613498111279222311572352247803752732639, -482369253613498111279222311572352247803750635486⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨496257886122708299080717656232804391559802806573, 533735477367524214415483762183972136785277995954⟩
def wholeBExp : DyadicInterval precision := ⟨704033850755750596856942594226690043290622365314, 741083167255899678520967171438347785922362563630⟩
def wholeBLog : DyadicInterval precision := ⟨574667184328729225728115524796933597341884829664, 599459970066116025774948586559345272802734587937⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨704033850755750596856942594226690043840378179202, scale precision, 741083167255899678520967171438347785372606749742, scale precision,
    1, 128, 0, 128, ⟨-1067470954735048428830967524367944274711793390507, -1067470954735048428830967524367944274711791293354⟩, ⟨-992515772245416598161435312465608782035424672939, -992515772245416598161435312465608782035422575786⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0065StableWitnesses

end


