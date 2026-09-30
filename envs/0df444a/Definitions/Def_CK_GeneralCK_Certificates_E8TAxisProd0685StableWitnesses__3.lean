-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0685StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0685StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:04:46.325439+00:00
-- url     : https://prove2.me/theorems/d923d1e1-115e-4e01-90dd-2914ccadad07
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0685StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0686StableWitnesses, GeneralCK.Certificates.E8TAxisProd06…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0685StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0686StableWitnesses, GeneralCK.Certificates.E8TAxisProd0687StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0685StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0686StableWitnesses, GeneralCK.Certificates.E8TAxisProd0687StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0685StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0686StableWitnesses, GeneralCK.Certificates.E8TAxisProd0687StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0685StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0686StableWitnesses, GeneralCK/Certificates/E8TAxisProd0687StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0685StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0685StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨474860522247948771940036538063380708083792495, 474860522247948771940036538063380708083792496⟩
def centerAExp : DyadicInterval precision := ⟨1460552224796057874071550301380937639903048136016, 1460552224796057874071550301380937642102071391569⟩
def centerALog : DyadicInterval precision := ⟨1012560955921529836431094652635425273892829583853, 1012560955921529836431094652635425276091852839406⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1460552224796057874071550301380937640452803949904, scale precision, 1460552224796057874071550301380937641552315577681, scale precision,
    0, 128, 0, 128, ⟨-949721044495897543880073076126761966281808906, -949721044495897543880073076126761966279711753⟩, ⟨-949721044495897543880073076126760866055458229, -949721044495897543880073076126760866053361076⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨557626218156733731854265351491921930004406181893, 557626218156733731854265351491921930004406181894⟩
def centerCExp : DyadicInterval precision := ⟨681388768473368520887477975782684823184721518194, 681388768473368520887477975782684825383744773747⟩
def centerCLog : DyadicInterval precision := ⟨559303740501896351925319889885294283505067546195, 559303740501896351925319889885294285704090801748⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨681388768473368520887477975782684823734477332082, scale precision, 681388768473368520887477975782684824833988959859, scale precision,
    1, 128, 1, 128, ⟨-1115252436313467463708530702983843861187977289588, -1115252436313467463708530702983843861187975192435⟩, ⟨-1115252436313467463708530702983843858829649535139, -1115252436313467463708530702983843858829647437986⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1289731580980479605752485912129011047602385042225, 1289731580980479605752485912129011047602385042226⟩
def centerBExp : DyadicInterval precision := ⟨250204701451473274294325042515435881583533248463, 250204701451473274294325042515435883782556504016⟩
def centerBLog : DyadicInterval precision := ⟨230955705025089964702265141892418758984501910907, 230955705025089964702265141892418761183525166460⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨250204701451473274294325042515435882133289062351, scale precision, 250204701451473274294325042515435883232800690128, scale precision,
    2, 128, 2, 128, ⟨-2579463161960959211504971824258022098416017834102, -2579463161960959211504971824258022098416015736949⟩, ⟨-2579463161960959211504971824258022091993524431947, -2579463161960959211504971824258022091993522334794⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨316573674294471837011765157253655004433778636, 633147383168915695688804483341311756669124067⟩
def wholeAExp : DyadicInterval precision := ⟨1460235890986607494244084883518378976785131112043, 1460868627107607697638964738615285410683914502614⟩
def wholeALog : DyadicInterval precision := ⟨1012402729061596953461092784027353937561977270075, 1012719199911638357989124323230052395461166191557⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1460235890986607494244084883518378977334886925931, scale precision, 1460868627107607697638964738615285410134158688726, scale precision,
    0, 128, 0, 128, ⟨-1266294766337831391377608966682624063571644160, -1266294766337831391377608966682624063569547007⟩, ⟨-633147348588943674023530314507309458874576803, -633147348588943674023530314507309458872479650⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨552166933197188683374850990452555196994927225219, 563099503091774669885689056146807227713503443159⟩
def wholeCExp : DyadicInterval precision := ⟨676304267770541349869378554063490937447714237684, 686498342495103149037812478669294550109649522760⟩
def wholeCLog : DyadicInterval precision := ⟨555831870947479867300624657093401304860205304336, 562784442014820528870121302404999932119156442921⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨676304267770541349869378554063490937997470051572, scale precision, 686498342495103149037812478669294549559893708872, scale precision,
    1, 128, 1, 128, ⟨-1126199006183549339771378112293614456615036844986, -1126199006183549339771378112293614456615034747833⟩, ⟨-1104333866394377366749701980905110392819468081604, -1104333866394377366749701980905110392819465984451⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1274549734501976508539636586264995992738465663453, 1305001521227457412018911073404994538084941524380⟩
def wholeBExp : DyadicInterval precision := ⟨245030613164772502550850320785045035275697615230, 255457248406065143391072622331457004926422930305⟩
def wholeBLog : DyadicInterval precision := ⟨226531236644363873940277962562510427227729891420, 235433606177261909204081416755181239508435245014⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨245030613164772502550850320785045035825453429118, scale precision, 255457248406065143391072622331457004376667116417, scale precision,
    2, 128, 2, 128, ⟨-2610003042454914824037822146809989079448939770228, -2610003042454914824037822146809989079448937673075⟩, ⟨-2549099469003953017079273172529991982331713255087, -2549099469003953017079273172529991982331711157934⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0685StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0686StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0686StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨474860522247948771940036538063380708083792495, 474860522247948771940036538063380708083792496⟩
def centerAExp : DyadicInterval precision := ⟨1460552224796057874071550301380937639903048136016, 1460552224796057874071550301380937642102071391569⟩
def centerALog : DyadicInterval precision := ⟨1012560955921529836431094652635425273892829583853, 1012560955921529836431094652635425276091852839406⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1460552224796057874071550301380937640452803949904, scale precision, 1460552224796057874071550301380937641552315577681, scale precision,
    0, 128, 0, 128, ⟨-949721044495897543880073076126761966281808906, -949721044495897543880073076126761966279711753⟩, ⟨-949721044495897543880073076126760866055458229, -949721044495897543880073076126760866053361076⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨547087156785564145999381877673026560118074025060, 547087156785564145999381877673026560118074025061⟩
def centerCExp : DyadicInterval precision := ⟨691287125317854160411394855709861911084427436832, 691287125317854160411394855709861913283450692385⟩
def centerCLog : DyadicInterval precision := ⟨566039108657497931722710181240450651852101654982, 566039108657497931722710181240450654051124910535⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨691287125317854160411394855709861911634183250720, scale precision, 691287125317854160411394855709861912733694878497, scale precision,
    1, 128, 1, 128, ⟨-1094174313571128291998763755346053121398428841374, -1094174313571128291998763755346053121398426744221⟩, ⟨-1094174313571128291998763755346053119073869356020, -1094174313571128291998763755346053119073867258867⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1259970952704626985227890949918873550266058166861, 1259970952704626985227890949918873550266058166862⟩
def centerBExp : DyadicInterval precision := ⟨260604904623057157330816262775113737530966473280, 260604904623057157330816262775113739729989728833⟩
def centerBLog : DyadicInterval precision := ⟨239808814364667122460469340356761302089775200750, 239808814364667122460469340356761304288798456303⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨260604904623057157330816262775113738080722287168, scale precision, 260604904623057157330816262775113739180233914945, scale precision,
    2, 128, 2, 128, ⟨-2519941905409253970455781899837747103615209863972, -2519941905409253970455781899837747103615207766819⟩, ⟨-2519941905409253970455781899837747097449024900628, -2519941905409253970455781899837747097449022803475⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨316573674294471837011765157253655004433778636, 633147383168915695688804483341311756669124067⟩
def wholeAExp : DyadicInterval precision := ⟨1460235890986607494244084883518378976785131112043, 1460868627107607697638964738615285410683914502614⟩
def wholeALog : DyadicInterval precision := ⟨1012402729061596953461092784027353937561977270075, 1012719199911638357989124323230052395461166191557⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1460235890986607494244084883518378977334886925931, scale precision, 1460868627107607697638964738615285410134158688726, scale precision,
    0, 128, 0, 128, ⟨-1266294766337831391377608966682624063571644160, -1266294766337831391377608966682624063569547007⟩, ⟨-633147348588943674023530314507309458874576803, -633147348588943674023530314507309458872479650⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨541654538126871809569398101492862979540654997330, 552533507797717736554719832775524462678230971782⟩
def wholeCExp : DyadicInterval precision := ⟨686154053114796290066834967020706358327478598970, 696445509880808157272503859764899403096506389361⟩
def wholeCLog : DyadicInterval precision := ⟨562550168351969091822187740944373997517377394562, 569536883163217644656607860660718214270741630906⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨686154053114796290066834967020706358877234412858, scale precision, 696445509880808157272503859764899402546750575473, scale precision,
    1, 128, 1, 128, ⟨-1105067015595435473109439665551048926527437671197, -1105067015595435473109439665551048926527435574044⟩, ⟨-1083309076253743619138796202985725957927639993985, -1083309076253743619138796202985725957927637896832⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1244963475049946801553682196125291092267488633169, 1275067312854252478862531191568066790378453330449⟩
def wholeBExp : DyadicInterval precision := ⟨255276376452040019274382557000871006591228905066, 266012300668708602943229969657795118821124387376⟩
def wholeBLog : DyadicInterval precision := ⟨235279637096383053158403622032703134486796629439, 244390723994011558162339590715447090669157864490⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨255276376452040019274382557000871007140984718954, scale precision, 266012300668708602943229969657795118271368573488, scale precision,
    2, 128, 2, 128, ⟨-2550134625708504957725062383136133583904355324081, -2550134625708504957725062383136133583904353226928⟩, ⟨-2489926950099893603107364392250582181514557755002, -2489926950099893603107364392250582181514555657849⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0686StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0687StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0687StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨474860522247948771940036538063380708083792495, 474860522247948771940036538063380708083792496⟩
def centerAExp : DyadicInterval precision := ⟨1460552224796057874071550301380937639903048136016, 1460552224796057874071550301380937642102071391569⟩
def centerALog : DyadicInterval precision := ⟨1012560955921529836431094652635425273892829583853, 1012560955921529836431094652635425276091852839406⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1460552224796057874071550301380937640452803949904, scale precision, 1460552224796057874071550301380937641552315577681, scale precision,
    0, 128, 0, 128, ⟨-949721044495897543880073076126761966281808906, -949721044495897543880073076126761966279711753⟩, ⟨-949721044495897543880073076126760866055458229, -949721044495897543880073076126760866053361076⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨536599394242600065678300952758147288680459786193, 536599394242600065678300952758147288680459786194⟩
def centerCExp : DyadicInterval precision := ⟨701280041306653874347238213353061611021019581303, 701280041306653874347238213353061613220042836856⟩
def centerCLog : DyadicInterval precision := ⟨572807478855781882969324578534583809007097568295, 572807478855781882969324578534583811206120823848⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨701280041306653874347238213353061611570775395191, scale precision, 701280041306653874347238213353061612670287022968, scale precision,
    1, 128, 1, 128, ⟨-1073198788485200131356601905516294578506638415288, -1073198788485200131356601905516294578506636318135⟩, ⟨-1073198788485200131356601905516294576215202826637, -1073198788485200131356601905516294576215200729484⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1230553757125146095167125044126466839972991650425, 1230553757125146095167125044126466839972991650426⟩
def centerBExp : DyadicInterval precision := ⟨271309872614514088794678388640521408769329497780, 271309872614514088794678388640521410968352753333⟩
def centerBLog : DyadicInterval precision := ⟨248865688119802892488656002097640919479506918127, 248865688119802892488656002097640921678530173680⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨271309872614514088794678388640521409319085311668, scale precision, 271309872614514088794678388640521410418596939445, scale precision,
    2, 128, 2, 128, ⟨-2461107514250292190334250088252933682907428451654, -2461107514250292190334250088252933682907426354501⟩, ⟨-2461107514250292190334250088252933676984540247200, -2461107514250292190334250088252933676984538150047⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨316573674294471837011765157253655004433778636, 633147383168915695688804483341311756669124067⟩
def wholeAExp : DyadicInterval precision := ⟨1460235890986607494244084883518378976785131112043, 1460868627107607697638964738615285410683914502614⟩
def wholeALog : DyadicInterval precision := ⟨1012402729061596953461092784027353937561977270075, 1012719199911638357989124323230052395461166191557⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1460235890986607494244084883518378977334886925931, scale precision, 1460868627107607697638964738615285410134158688726, scale precision,
    0, 128, 0, 128, ⟨-1266294766337831391377608966682624063571644160, -1266294766337831391377608966682624063569547007⟩, ⟨-633147348588943674023530314507309458874576803, -633147348588943674023530314507309458872479650⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨531192925168028344773704634130169567373930408526, 542019328422355981835085710408050485812552569198⟩
def wholeCExp : DyadicInterval precision := ⟨696097931534028604717593342577670134100085749177, 706487711216951474549149029906521283096380286611⟩
def wholeCLog : DyadicInterval precision := ⟨569301461624562947380059514219729912562315626808, 576322336474074920862789780747981304913636695265⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨696097931534028604717593342577670134649841563065, scale precision, 706487711216951474549149029906521282546624472723, scale precision,
    1, 128, 1, 128, ⟨-1084038656844711963670171420816100972779353291771, -1084038656844711963670171420816100972779351194618⟩, ⟨-1062385850336056689547409268260339133610589398786, -1062385850336056689547409268260339133610587301633⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1215721911499174935818132268414115567197327255398, 1245475080116736679375251994606852024794267618072⟩
def wholeBExp : DyadicInterval precision := ⟨265826128298517989445850033580327655460744797839, 276872837454465782252837677761281135641983138185⟩
def wholeBLog : DyadicInterval precision := ⟨244233211003568657454976771819525486671593516949, 253550132697702752592258658094778189988061020954⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨265826128298517989445850033580327656010500611727, scale precision, 276872837454465782252837677761281135092227324297, scale precision,
    2, 128, 2, 128, ⟨-2490950160233473358750503989213704052611072208005, -2490950160233473358750503989213704052611070110852⟩, ⟨-2431443822998349871636264536828231131492713174859, -2431443822998349871636264536828231131492711077706⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0687StableWitnesses

end


