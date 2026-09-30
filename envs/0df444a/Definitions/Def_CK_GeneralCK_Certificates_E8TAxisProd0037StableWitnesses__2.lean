-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0037StableWitnesses__2
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0037StableWitnesses__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:39:46.645648+00:00
-- url     : https://prove2.me/theorems/bd0e4c40-415f-465a-a850-aa5bc5145bd4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0037StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisProd0038StableWitnesses)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0037StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisProd0038StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0037StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisProd0038StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0037StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisProd0038StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0037StableWitnesses (+1 modules: GeneralCK/Certificates/E8TAxisProd0038StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0037StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0037StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨111526329570936434949156234057414250978987281265, 111526329570936434949156234057414250978987281266⟩
def centerCExp : DyadicInterval precision := ⟨1254636141255587401746891707902001681544737764716, 1254636141255587401746891707902001683743761020269⟩
def centerCLog : DyadicInterval precision := ⟨905760540593975242609047669165684822484118727308, 905760540593975242609047669165684824683141982861⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1254636141255587401746891707902001682094493578604, scale precision, 1254636141255587401746891707902001683194005206381, scale precision,
    0, 128, 0, 128, ⟨-223052659141872869898312468114828502598375640813, -223052659141872869898312468114828502598373543660⟩, ⟨-223052659141872869898312468114828501317575581401, -223052659141872869898312468114828501317573484248⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨220015566163561586175537252383320360307282815723, 220015566163561586175537252383320360307282815724⟩
def centerBExp : DyadicInterval precision := ⟨1081536707726478807316248973790450002371416071496, 1081536707726478807316248973790450004570439327049⟩
def centerBLog : DyadicInterval precision := ⟨809518652732157095875767932892631841705419802721, 809518652732157095875767932892631843904443058274⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1081536707726478807316248973790450002921171885384, scale precision, 1081536707726478807316248973790450004020683513161, scale precision,
    0, 128, 0, 128, ⟨-440031132327123172351074504766640721357462428629, -440031132327123172351074504766640721357460331476⟩, ⟨-440031132327123172351074504766640719871670931419, -440031132327123172351074504766640719871668834266⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨106906222136452251800882146200705633326592822456, 116149005857262799618127819525499179952021385956⟩
def wholeCExp : DyadicInterval precision := ⟨1246724455453277103715617085793914979940220082727, 1262593595962690659632005253813941877889857420580⟩
def wholeCLog : DyadicInterval precision := ⟨901497201987704499724274899662403196323721643119, 910036034438471029983882665499693165399556502883⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1246724455453277103715617085793914980489975896615, scale precision, 1262593595962690659632005253813941877340101606692, scale precision,
    0, 128, 0, 128, ⟨-232298011714525599236255639050998360548507814608, -232298011714525599236255639050998360548505717455⟩, ⟨-213812444272904503601764292401411266016822763957, -213812444272904503601764292401411266016820666804⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨211253010738814688741513314259447908539070264891, 228795830081704859847687774194111259693403688136⟩
def wholeBExp : DyadicInterval precision := ⟨1068619369684015382867667652417372494517590509916, 1094583663264658192859639577095084242298766072314⟩
def wholeBLog : DyadicInterval precision := ⟨802076051312755177186185483652806810775416639633, 816997658858733881976258143282406437393482291798⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1068619369684015382867667652417372495067346323804, scale precision, 1094583663264658192859639577095084241749010258426, scale precision,
    0, 128, 0, 128, ⟨-457591660163409719695375548388222520138684204871, -457591660163409719695375548388222520138682107718⟩, ⟨-422506021477629377483026628518895816344100820128, -422506021477629377483026628518895816344098722975⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0037StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0038StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0038StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨103562170067272545061760203282565258788806140463, 103562170067272545061760203282565258788806140464⟩
def centerCExp : DyadicInterval precision := ⟨1268384700277726817167059658881397942894075782094, 1268384700277726817167059658881397945093099037647⟩
def centerCLog : DyadicInterval precision := ⟨913139716219988531208626394688059328703148713823, 913139716219988531208626394688059330902171969376⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1268384700277726817167059658881397943443831595982, scale precision, 1268384700277726817167059658881397944543343223759, scale precision,
    0, 128, 0, 128, ⟨-207124340134545090123520406565130518211071792029, -207124340134545090123520406565130518211069694876⟩, ⟨-207124340134545090123520406565130516944154866976, -207124340134545090123520406565130516944152769823⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨203802040624012852586366857882370360086913604468, 203802040624012852586366857882370360086913604469⟩
def centerBExp : DyadicInterval precision := ⟨1105801483010104524876835505205719392959862188974, 1105801483010104524876835505205719395158885444527⟩
def centerBLog : DyadicInterval precision := ⟨823397676494555074992354335814380345069644035678, 823397676494555074992354335814380347268667291231⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1105801483010104524876835505205719393509618002862, scale precision, 1105801483010104524876835505205719394609129630639, scale precision,
    0, 128, 0, 128, ⟨-407604081248025705172733715764740720900422528254, -407604081248025705172733715764740720900420431101⟩, ⟨-407604081248025705172733715764740719447233986775, -407604081248025705172733715764740719447231889622⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨98946240501651460655236999370633104625806438931, 108180484096466973298783154526216413755061499936⟩
def wholeCExp : DyadicInterval precision := ⟨1260393840574666853052529216367277878303348449117, 1276422056781884267024825639853428504785486093644⟩
def wholeCLog : DyadicInterval precision := ⟨908855369084211161785347986846822294280864748185, 917436360793557022095544909352086775557434872913⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1260393840574666853052529216367277878853104263005, scale precision, 1276422056781884267024825639853428504235730279756, scale precision,
    0, 128, 0, 128, ⟨-216360968192933946597566309052432828147598618908, -216360968192933946597566309052432828147596521755⟩, ⟨-197892481003302921310473998741266208622144216276, -197892481003302921310473998741266208622142119123⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨195070384091725537299207625964822441604096874997, 212550077699428455989854073007082018901742822767⟩
def wholeBExp : DyadicInterval precision := ⟨1092642524092652140066262196305827179357671526605, 1119093832522548353760792784395684186476972512655⟩
def wholeBLog : DyadicInterval precision := ⟨815887345423414633040468176727720343602299791764, 830945157630913290200624245407414190058998920140⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1092642524092652140066262196305827179907427340493, scale precision, 1119093832522548353760792784395684185927216698767, scale precision,
    0, 128, 0, 128, ⟨-425100155398856911979708146014164038538831515873, -425100155398856911979708146014164038538829418720⟩, ⟨-390140768183451074598415251929644882490230854191, -390140768183451074598415251929644882490228757038⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0038StableWitnesses

end


