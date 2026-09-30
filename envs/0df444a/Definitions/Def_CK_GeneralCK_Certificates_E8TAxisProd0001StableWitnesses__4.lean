-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0001StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0001StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:30:47.491402+00:00
-- url     : https://prove2.me/theorems/97c54e51-54df-4239-a25d-49972f9a50bc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0001StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0002StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0001StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0002StableWitnesses, GeneralCK.Certificates.E8TAxisProd0003StableWitnesses, GeneralCK.Certificates.E8TAxisProd0004StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0001StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0002StableWitnesses, GeneralCK.Certificates.E8TAxisProd0003StableWitnesses, GeneralCK.Certificates.E8TAxisProd0004StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0001StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0002StableWitnesses, GeneralCK.Certificates.E8TAxisProd0003StableWitnesses, GeneralCK.Certificates.E8TAxisProd0004StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0001StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0002StableWitnesses, GeneralCK/Certificates/E8TAxisProd0003StableWitnesses, GeneralCK/Certificates/E8TAxisProd0004StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval
import Definitions.Def_GeneralCK_E8_Prod0001_inputs

-- ===== source module GeneralCK.Certificates.E8TAxisProd0001StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0001StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000





theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide










theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide










theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide










theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide










theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide










theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide










theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide










theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide










theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0001StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0002StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0002StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 3798893981423257492988718450954299577395465181⟩
def centerAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1453923564186661310665317018859587709527417053272⟩
def centerALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009241782561842849966002591658486094460586802138⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨19787261415618956269193137821462137643299660144, 19787261415618956269193137821462137643299660145⟩
def centerDExp : DyadicInterval precision := ⟨1422458110153910514512537297173309437352704550462, 1422458110153910514512537297173309439551727806015⟩
def centerDLog : DyadicInterval precision := ⟨993382423595496802456179790205135829228690482622, 993382423595496802456179790205135831427713738175⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1422458110153910514512537297173309437902460364350, scale precision, 1422458110153910514512537297173309439001971992127, scale precision,
    0, 128, 0, 128, ⟨-39574522831237912538386275642924275851445840514, -39574522831237912538386275642924275851443743361⟩, ⟨-39574522831237912538386275642924274721754897217, -39574522831237912538386275642924274721752800064⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨23587121573163298340330466159925038915762707818, 23587121573163298340330466159925038915762707819⟩
def centerCExp : DyadicInterval precision := ⟨1415080611720820914364265680463283992810521368520, 1415080611720820914364265680463283995009544624073⟩
def centerCLog : DyadicInterval precision := ⟨989638945311409560973256953883409458523119952764, 989638945311409560973256953883409460722143208317⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1415080611720820914364265680463283993360277182408, scale precision, 1415080611720820914364265680463283994459788810185, scale precision,
    0, 128, 0, 128, ⟨-47174243146326596680660932319850078399316748015, -47174243146326596680660932319850078399314650862⟩, ⟨-47174243146326596680660932319850077263736180414, -47174243146326596680660932319850077263734083261⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨43385415673619159303918653523724014002199098407, 43385415673619159303918653523724014002199098408⟩
def centerBExp : DyadicInterval precision := ⟨1377256413094801759155106396529063141071064744374, 1377256413094801759155106396529063143270087999927⟩
def centerBLog : DyadicInterval precision := ⟨970294188078387503961473855714136030946697543141, 970294188078387503961473855714136033145720798694⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1377256413094801759155106396529063141620820558262, scale precision, 1377256413094801759155106396529063142720332186039, scale precision,
    0, 128, 0, 128, ⟨-86770831347238318607837307047448028587783003487, -86770831347238318607837307047448028587780906334⟩, ⟨-86770831347238318607837307047448027421015487299, -86770831347238318607837307047448027421013390146⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨18995665047735116218618892934888584156033732657, 20578871293540181087774692060534010761932455779⟩
def wholeDExp : DyadicInterval precision := ⟨1420918019911383254566844357126927029598135402497, 1423999843327116683343282796578766321720660974834⟩
def wholeDLog : DyadicInterval precision := ⟨992601745007901601457433275450218201286829393502, 994163517538761546318115582447098114172952119197⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1420918019911383254566844357126927030147891216385, scale precision, 1423999843327116683343282796578766321170905160946, scale precision,
    0, 128, 0, 128, ⟨-41157742587080362175549384121068022089323650775, -41157742587080362175549384121068022089321553622⟩, ⟨-37991330095470232437237785869777167747834587957, -37991330095470232437237785869777167747832490804⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨21528821741448843534916460983893935247377312625, 25645530275337861222811727042940313553206465624⟩
def wholeCExp : DyadicInterval precision := ⟨1411100163730250715611675570912580979575688448038, 1419072076386451827323355281724057477324448000978⟩
def wholeCLog : DyadicInterval precision := ⟨987615203460619175063571975429473045677556543604, 991665478244185565170265217796583835419286676148⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1411100163730250715611675570912580980125444261926, scale precision, 1419072076386451827323355281724057476774692187090, scale precision,
    0, 128, 0, 128, ⟨-51291060550675722445623454085880627675805893156, -51291060550675722445623454085880627675803796003⟩, ⟨-43057643482897687069832921967787869928562430018, -43057643482897687069832921967787869928560332865⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨40533518663166560848124822041176720320630938595, 46237696723453030634713590725906446102500922703⟩
def wholeBExp : DyadicInterval precision := ⟨1371891156320640275377461634832536357649059351868, 1382641925933778624162051348417793952658857791773⟩
def wholeBLog : DyadicInterval precision := ⟨967529334281554329962408432162451897746719563587, 973064230117935785593232025639809025714311606104⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1371891156320640275377461634832536358198815165756, scale precision, 1382641925933778624162051348417793952109101977885, scale precision,
    0, 128, 0, 128, ⟨-92475393446906061269427181451812892790668176849, -92475393446906061269427181451812892790666079696⟩, ⟨-81067037326333121696249644082353440060151499114, -81067037326333121696249644082353440060149401961⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0002StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0003StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0003StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨60981562246941182391851692343549914653715634261, 60981562246941182391851692343549914653715634262⟩
def centerDExp : DyadicInterval precision := ⟨1344488804354560387653913977701155507615899604953, 1344488804354560387653913977701155509814922860506⟩
def centerDLog : DyadicInterval precision := ⟨953326044385255946846825783453523246727646501740, 953326044385255946846825783453523248926669757293⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1344488804354560387653913977701155508165655418841, scale precision, 1344488804354560387653913977701155509265167046618, scale precision,
    0, 128, 0, 128, ⟨-121963124493882364783703384687099829905034185949, -121963124493882364783703384687099829905032088796⟩, ⟨-121963124493882364783703384687099828709830448249, -121963124493882364783703384687099828709828351096⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨65423239729953941592341983218016420479652542440, 65423239729953941592341983218016420479652542441⟩
def centerCExp : DyadicInterval precision := ⟨1336341467062228111088745819872598906252220300437, 1336341467062228111088745819872598908451243555990⟩
def centerCLog : DyadicInterval precision := ⟨949076326728730160431345514648061799479504624794, 949076326728730160431345514648061801678527880347⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1336341467062228111088745819872598906801976114325, scale precision, 1336341467062228111088745819872598907901487742102, scale precision,
    0, 128, 0, 128, ⟨-130846479459907883184683966436032841560551430362, -130846479459907883184683966436032841560549333209⟩, ⟨-130846479459907883184683966436032840358060836552, -130846479459907883184683966436032840358058739399⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨126679724792444906829094057492586161245362209646, 126679724792444906829094057492586161245362209647⟩
def centerBExp : DyadicInterval precision := ⟨1228886968124097995678328532808995163696346098422, 1228886968124097995678328532808995165895369353975⟩
def centerBLog : DyadicInterval precision := ⟨891839312598626456394836566050469658740182651592, 891839312598626456394836566050469660939205907145⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1228886968124097995678328532808995164246101912310, scale precision, 1228886968124097995678328532808995165345613540087, scale precision,
    0, 128, 0, 128, ⟨-253359449584889813658188114985172323144543958073, -253359449584889813658188114985172323144541860920⟩, ⟨-253359449584889813658188114985172321836906977665, -253359449584889813658188114985172321836904880512⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨58602635770181898821662589353151101542136562992, 63360863746962342702697993485127651995684952634⟩
def wholeDExp : DyadicInterval precision := ⟨1340118310385255731396483422015350658626993302998, 1348872859460053731599279250908956040444361819487⟩
def wholeDLog : DyadicInterval precision := ⟨951047895604627342379828868169897140353010055619, 955607699899585814401544643147774225289199821907⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1340118310385255731396483422015350659176749116886, scale precision, 1348872859460053731599279250908956039894606005599, scale precision,
    0, 128, 0, 128, ⟨-126721727493924685405395986970255304590921766561, -126721727493924685405395986970255304590919669408⟩, ⟨-117205271540363797643325178706302202488614608506, -117205271540363797643325178706302202488612511353⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨62409097206069606708408168815139972464900235695, 68438027870394084921299803443842121697156389362⟩
def wholeCExp : DyadicInterval precision := ⟨1330839609064849834387863226209648406986378997955, 1341864884896329694947165175434287950304501715613⟩
def wholeCLog : DyadicInterval precision := ⟨946199506730229910396969348837562152290078579587, 951958735123675020100840869810752678907829139428⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1330839609064849834387863226209648407536134811843, scale precision, 1341864884896329694947165175434287949754745901725, scale precision,
    0, 128, 0, 128, ⟨-136876055740788169842599606887684243998044747732, -136876055740788169842599606887684243998042650579⟩, ⟨-124818194412139213416816337630279944331031084005, -124818194412139213416816337630279944331028986852⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨121252999859680607281913286376018482511954730469, 132110463846210516044711664841215322615024907154⟩
def wholeBExp : DyadicInterval precision := ⟨1219788070376012291331212345706861179026867056585, 1238046937477863287537128374947874710563698058428⟩
def wholeBLog : DyadicInterval precision := ⟨886888134996521783257090466047055991317612458814, 896806837320689770602186504796947362731308911748⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1219788070376012291331212345706861179576622870473, scale precision, 1238046937477863287537128374947874710013942244540, scale precision,
    0, 128, 0, 128, ⟨-264220927692421032089423329682430645888746452424, -264220927692421032089423329682430645888744355271⟩, ⟨-242505999719361214563826572752036964374929442799, -242505999719361214563826572752036964374927345646⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0003StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0004StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0004StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨56224069662401947129176131245290424868351320698, 56224069662401947129176131245290424868351320699⟩
def centerDExp : DyadicInterval precision := ⟨1353270542552318619031293173544076935377002222510, 1353270542552318619031293173544076937576025478063⟩
def centerDLog : DyadicInterval precision := ⟨957892874924759606731049484620710570189124178339, 957892874924759606731049484620710572388147433892⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1353270542552318619031293173544076935926758036398, scale precision, 1353270542552318619031293173544076937026269664175, scale precision,
    0, 128, 0, 128, ⟨-112448139324803894258352262490580850330427558828, -112448139324803894258352262490580850330425461675⟩, ⟨-112448139324803894258352262490580849142979821120, -112448139324803894258352262490580849142977723967⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨60664350701943895908274812532193838400488968342, 60664350701943895908274812532193838400488968343⟩
def centerCExp : DyadicInterval precision := ⟨1345072560048415338197584206881288726431064297522, 1345072560048415338197584206881288728630087553075⟩
def centerCLog : DyadicInterval precision := ⟨953630062231040205313701479787567000636983336588, 953630062231040205313701479787567002836006592141⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1345072560048415338197584206881288726980820111410, scale precision, 1345072560048415338197584206881288728080331739187, scale precision,
    0, 128, 0, 128, ⟨-121328701403887791816549625064387677398321497476, -121328701403887791816549625064387677398319400323⟩, ⟨-121328701403887791816549625064387676203636473047, -121328701403887791816549625064387676203634375894⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨117105752201681545165834830016706114467703807692, 117105752201681545165834830016706114467703807693⟩
def centerBExp : DyadicInterval precision := ⟨1245093231059763170750164573821199928501784274980, 1245093231059763170750164573821199930700807530533⟩
def centerBLog : DyadicInterval precision := ⟨900616642053705619557786953461501342690718171671, 900616642053705619557786953461501344889741427224⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1245093231059763170750164573821199929051540088868, scale precision, 1245093231059763170750164573821199930151051716645, scale precision,
    0, 128, 0, 128, ⟨-234211504403363090331669660033412229580716984727, -234211504403363090331669660033412229580714887574⟩, ⟨-234211504403363090331669660033412228290100343198, -234211504403363090331669660033412228290098246045⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨53845849274430363340356920789158241656378561384, 58602635770181898821662589353151101542136562993⟩
def wholeDExp : DyadicInterval precision := ⟨1348872859460053731599279250908956038245338563934, 1357681920934804568838490939788917163911062976792⟩
def wholeDLog : DyadicInterval precision := ⟨955607699899585814401544643147774223090176566354, 960181582307675404146178190201383839808765855727⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1348872859460053731599279250908956038795094377822, scale precision, 1357681920934804568838490939788917163361307162904, scale precision,
    0, 128, 0, 128, ⟨-117205271540363797643325178706302203679933740618, -117205271540363797643325178706302203679931643465⟩, ⟨-107691698548860726680713841578316482720963429336, -107691698548860726680713841578316482720961332183⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨57651166903258272846568912508060285708089093757, 63678133069629385946223510141068352443280596131⟩
def wholeCExp : DyadicInterval precision := ⟨1339536598902366963770989131506206354893424047215, 1350630293579732954838529998654005145014173668864⟩
def wholeCLog : DyadicInterval precision := ⟨950744406703524391972600044754262256134730645656, 956521346850492119777299553570157693451628120442⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1339536598902366963770989131506206355443179861103, scale precision, 1350630293579732954838529998654005144464417854976, scale precision,
    0, 128, 0, 128, ⟨-127356266139258771892447020282136705486373416425, -127356266139258771892447020282136705486371319272⟩, ⟨-115302333806516545693137825016120570821294739610, -115302333806516545693137825016120570821292642457⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨111685688823663682104164597513308723070171042184, 122529524349534149185465417549696152859615174423⟩
def wholeBExp : DyadicInterval precision := ⟨1235886122017267861038260021348983644245296257024, 1254362564991884505726197553118043780144396161571⟩
def wholeBLog : DyadicInterval precision := ⟨895636530573733989776573437297737868724720843920, 905613327040268922296823991053019244681353657618⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1235886122017267861038260021348983644795052070912, scale precision, 1254362564991884505726197553118043779594640347683, scale precision,
    0, 128, 0, 128, ⟨-245059048699068298370930835099392306369347138520, -245059048699068298370930835099392306369345041367⟩, ⟨-223371377647327364208329195026617445499803432101, -223371377647327364208329195026617445499801334948⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0004StableWitnesses

end


