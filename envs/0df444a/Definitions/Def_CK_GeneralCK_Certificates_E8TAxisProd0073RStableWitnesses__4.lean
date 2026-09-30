-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0073RStableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0073RStableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:03:24.598304+00:00
-- url     : https://prove2.me/theorems/966fb248-8c1c-4417-82e5-bf4677ffd241
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0073RStableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0074RStableWitnesses, GeneralCK.Certificates.E8TAxisProd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0073RStableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0074RStableWitnesses, GeneralCK.Certificates.E8TAxisProd0079RStableWitnesses, GeneralCK.Certificates.E8TAxisProd0080RStableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0073RStableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0074RStableWitnesses, GeneralCK.Certificates.E8TAxisProd0079RStableWitnesses, GeneralCK.Certificates.E8TAxisProd0080RStableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0073RStableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0074RStableWitnesses, GeneralCK.Certificates.E8TAxisProd0079RStableWitnesses, GeneralCK.Certificates.E8TAxisProd0080RStableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0073RStableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0074RStableWitnesses, GeneralCK/Certificates/E8TAxisProd0079RStableWitnesses, GeneralCK/Certificates/E8TAxisProd0080RStableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0073RStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0073RStableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨154999391481232912176531096462725419644778483979, 154999391481232912176531096462725419644778483980⟩
def centerDExp : DyadicInterval precision := ⟨1182173450222225673505629770194260121401539327798, 1182173450222225673505629770194260123600562583351⟩
def centerDLog : DyadicInterval precision := ⟨866240207568659899353028711382600099926261785804, 866240207568659899353028711382600102125285041357⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1182173450222225673505629770194260121951295141686, scale precision, 1182173450222225673505629770194260123050806769463, scale precision,
    0, 128, 0, 128, ⟨-309998782962465824353062192925450839969212107887, -309998782962465824353062192925450839969210010734⟩, ⟨-309998782962465824353062192925450838609903925185, -309998782962465824353062192925450838609901828032⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨159811875404845412332835849570915332159904557127, 159811875404845412332835849570915332159904557128⟩
def centerCExp : DyadicInterval precision := ⟨1174413625574775140740960988166041736552527427605, 1174413625574775140740960988166041738751550683158⟩
def centerCLog : DyadicInterval precision := ⟨861944039176305392814570378622733955396106719554, 861944039176305392814570378622733957595129975107⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1174413625574775140740960988166041737102283241493, scale precision, 1174413625574775140740960988166041738201794869270, scale precision,
    0, 128, 0, 128, ⟨-319623750809690824665671699141830665003955002973, -319623750809690824665671699141830665003952905820⟩, ⟨-319623750809690824665671699141830663635665322688, -319623750809690824665671699141830663635663225535⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨319067775302505002942167197477318956392189084598, 319067775302505002942167197477318956392189084599⟩
def centerBExp : DyadicInterval precision := ⟨944437623369668716532295615577670201364561462342, 944437623369668716532295615577670203563584717895⟩
def centerBLog : DyadicInterval precision := ⟨728523411874105531042506919726053314031235703942, 728523411874105531042506919726053316230258959495⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨944437623369668716532295615577670201914317276230, scale precision, 944437623369668716532295615577670203013828904007, scale precision,
    0, 128, 0, 128, ⟨-638135550605010005884334394954637913635117267856, -638135550605010005884334394954637913635115170703⟩, ⟨-638135550605010005884334394954637911933641167691, -638135550605010005884334394954637911933639070538⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨150991919513477176104051187712444417195036210428, 159009523631476834293416684122073812609720086985⟩
def wholeDExp : DyadicInterval precision := ⟨1175703819620526499056916402241341505278943686883, 1188674354540648287330851150581954943606665789757⟩
def wholeDLog : DyadicInterval precision := ⟨862659221266056220624571274243273530090398223223, 869829687869058094079061307765923603360191874427⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1175703819620526499056916402241341505828699500771, scale precision, 1188674354540648287330851150581954943056909975869, scale precision,
    0, 128, 0, 128, ⟨-318019047262953668586833368244147625902835295714, -318019047262953668586833368244147625902833198561⟩, ⟨-301983839026954352208102375424888833714136431622, -301983839026954352208102375424888833714134334469⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨155480465510961978161806974473057541859913965829, 164146485543706911380212608705974937802842585670⟩
def wholeCExp : DyadicInterval precision := ⟨1167467951615164010714111386766126676457788552734, 1181395447964627495733780322911049527088212055489⟩
def wholeCLog : DyadicInterval precision := ⟨858087878960455589474575508211226886006542865453, 865810041652312317067648650979185488726511492207⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1167467951615164010714111386766126677007544366622, scale precision, 1181395447964627495733780322911049526538456241601, scale precision,
    0, 128, 0, 128, ⟨-328292971087413822760425217411949876293901276284, -328292971087413822760425217411949876293899179131⟩, ⟨-310960931021923956323613948946115083039727305970, -310960931021923956323613948946115083039725208817⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨310399396699256950984041451612067022294184943489, 327760197752559038439133554083214572857831243690⟩
def wholeBExp : DyadicInterval precision := ⟨933269907762331493937873102670555718357930866115, 955707528249466688044958580985006769096163752102⟩
def wholeBLog : DyadicInterval precision := ⟨721723725432976317515070165492696006907252905980, 735353396338611872578012864905443975754921531117⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨933269907762331493937873102670555718907686680003, scale precision, 955707528249466688044958580985006768546407938214, scale precision,
    0, 128, 0, 128, ⟨-655520395505118076878267108166429146576581707053, -655520395505118076878267108166429146576579609900⟩, ⟨-620798793398513901968082903224134043747664968112, -620798793398513901968082903224134043747662870959⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0073RStableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0074RStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0074RStableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨154999391481232912176531096462725419644778483979, 154999391481232912176531096462725419644778483980⟩
def centerDExp : DyadicInterval precision := ⟨1182173450222225673505629770194260121401539327798, 1182173450222225673505629770194260123600562583351⟩
def centerDLog : DyadicInterval precision := ⟨866240207568659899353028711382600099926261785804, 866240207568659899353028711382600102125285041357⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1182173450222225673505629770194260121951295141686, scale precision, 1182173450222225673505629770194260123050806769463, scale precision,
    0, 128, 0, 128, ⟨-309998782962465824353062192925450839969212107887, -309998782962465824353062192925450839969210010734⟩, ⟨-309998782962465824353062192925450838609903925185, -309998782962465824353062192925450838609901828032⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨159169985233104730880262620939575215045422974914, 159169985233104730880262620939575215045422974915⟩
def centerCExp : DyadicInterval precision := ⟨1175445681549742332239505391514667718164472289728, 1175445681549742332239505391514667720363495545281⟩
def centerCLog : DyadicInterval precision := ⟨862516157828402869063727593395129987735853566533, 862516157828402869063727593395129989934876822086⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1175445681549742332239505391514667718714228103616, scale precision, 1175445681549742332239505391514667719813739731393, scale precision,
    0, 128, 0, 128, ⟨-318339970466209461760525241879150430774391150843, -318339970466209461760525241879150430774389053690⟩, ⟨-318339970466209461760525241879150429407302845969, -318339970466209461760525241879150429407300748816⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨318400131926743274789312092208504137548932536123, 318400131926743274789312092208504137548932536124⟩
def centerBExp : DyadicInterval precision := ⟨945300893914836998357902081669710585621452481639, 945300893914836998357902081669710587820475737192⟩
def centerBLog : DyadicInterval precision := ⟨729047716473560833944230808607896295606555554959, 729047716473560833944230808607896297805578810512⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨945300893914836998357902081669710586171208295527, scale precision, 945300893914836998357902081669710587270719923304, scale precision,
    0, 128, 0, 128, ⟨-636800263853486549578624184417008275947827257329, -636800263853486549578624184417008275947825160176⟩, ⟨-636800263853486549578624184417008274247904984320, -636800263853486549578624184417008274247902887167⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨150991919513477176104051187712444417195036210428, 159009523631476834293416684122073812609720086985⟩
def wholeDExp : DyadicInterval precision := ⟨1175703819620526499056916402241341505278943686883, 1188674354540648287330851150581954943606665789757⟩
def wholeDLog : DyadicInterval precision := ⟨862659221266056220624571274243273530090398223223, 869829687869058094079061307765923603360191874427⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1175703819620526499056916402241341505828699500771, scale precision, 1188674354540648287330851150581954943056909975869, scale precision,
    0, 128, 0, 128, ⟨-318019047262953668586833368244147625902835295714, -318019047262953668586833368244147625902833198561⟩, ⟨-301983839026954352208102375424888833714136431622, -301983839026954352208102375424888833714134334469⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨154839041989814261300191813798023029202199323050, 163504115724003826455727092964752187077115116187⟩
def wholeCExp : DyadicInterval precision := ⟨1168494670815230410130443240817123223296884575568, 1182432884363077636122480154710369183259614772059⟩
def wholeCLog : DyadicInterval precision := ⟨858658543171026193409523755100524291209804259655, 866383623384107335437155153607563630150647298134⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1168494670815230410130443240817123223846640389456, scale precision, 1182432884363077636122480154710369182709858958171, scale precision,
    0, 128, 0, 128, ⟨-327008231448007652911454185929504374841841624581, -327008231448007652911454185929504374841839527428⟩, ⟨-309678083979628522600383627596046057724894724243, -309678083979628522600383627596046057724892627090⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨309733574902450231722473605348773919922730774135, 327090680858758583373932802371003276516688738836⟩
def wholeBExp : DyadicInterval precision := ⟨934125365302252464635631009739543171538932793379, 956578715624353311846366700153450027496848179143⟩
def wholeBLog : DyadicInterval precision := ⟨722245708143222885807268476168971919129511248401, 735880041861580198236598054257202697746267990456⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨934125365302252464635631009739543172088688607267, scale precision, 956578715624353311846366700153450026947092365255, scale precision,
    0, 128, 0, 128, ⟨-654181361717517166747865604742006553893508281819, -654181361717517166747865604742006553893506184666⟩, ⟨-619467149804900463444947210697547839005522287695, -619467149804900463444947210697547839005520190542⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0074RStableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0079RStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0079RStableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3482318024844347500022322904444928295572395252, 3482318024844347500022322904444928295572395253⟩
def centerAExp : DyadicInterval precision := ⟨1454553569581723058392238696431353224119669669100, 1454553569581723058392238696431353226318692924653⟩
def centerALog : DyadicInterval precision := ⟨1009557569928173087760872372803888449827653659813, 1009557569928173087760872372803888452026676915366⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454553569581723058392238696431353224669425482988, scale precision, 1454553569581723058392238696431353225768937110765, scale precision,
    0, 128, 0, 128, ⟨-6964636049688695000044645808889857143527710010, -6964636049688695000044645808889857143525612857⟩, ⟨-6964636049688695000044645808889856038763968154, -6964636049688695000044645808889856038761871001⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨154999391481232912176531096462725419644778483979, 154999391481232912176531096462725419644778483980⟩
def centerDExp : DyadicInterval precision := ⟨1182173450222225673505629770194260121401539327798, 1182173450222225673505629770194260123600562583351⟩
def centerDLog : DyadicInterval precision := ⟨866240207568659899353028711382600099926261785804, 866240207568659899353028711382600102125285041357⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1182173450222225673505629770194260121951295141686, scale precision, 1182173450222225673505629770194260123050806769463, scale precision,
    0, 128, 0, 128, ⟨-309998782962465824353062192925450839969212107887, -309998782962465824353062192925450839969210010734⟩, ⟨-309998782962465824353062192925450838609903925185, -309998782962465824353062192925450838609901828032⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨158528165014424078234857943975146549253327435378, 158528165014424078234857943975146549253327435379⟩
def centerCExp : DyadicInterval precision := ⟨1176478531857517390277184964112166953910992158352, 1176478531857517390277184964112166956110015413905⟩
def centerCLog : DyadicInterval precision := ⟨863088492685568708565274006874076763150459959307, 863088492685568708565274006874076765349483214860⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1176478531857517390277184964112166954460747972240, scale precision, 1176478531857517390277184964112166955560259600017, scale precision,
    0, 128, 0, 128, ⟨-317056330028848156469715887950293099189599976851, -317056330028848156469715887950293099189597879698⟩, ⟨-317056330028848156469715887950293097823711861814, -317056330028848156469715887950293097823709764661⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨317732630513434704967453952884466923458080761012, 317732630513434704967453952884466923458080761013⟩
def centerBExp : DyadicInterval precision := ⟨946164769728362764799933754019820743928033313662, 946164769728362764799933754019820746127056569215⟩
def centerBLog : DyadicInterval precision := ⟨729572200459498790870213889183536750846577658467, 729572200459498790870213889183536753045600914020⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨946164769728362764799933754019820744477789127550, scale precision, 946164769728362764799933754019820745577300755327, scale precision,
    0, 128, 0, 128, ⟨-635465261026869409934907905768933847765347667994, -635465261026869409934907905768933847765345570841⟩, ⟨-635465261026869409934907905768933846066977473211, -635465261026869409934907905768933846066975376058⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1455183847209450510423929547351191477780877052172⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009873425488092576137085252579843092274389747387⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨150991919513477176104051187712444417195036210428, 159009523631476834293416684122073812609720086985⟩
def wholeDExp : DyadicInterval precision := ⟨1175703819620526499056916402241341505278943686883, 1188674354540648287330851150581954943606665789757⟩
def wholeDLog : DyadicInterval precision := ⟨862659221266056220624571274243273530090398223223, 869829687869058094079061307765923603360191874427⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1175703819620526499056916402241341505828699500771, scale precision, 1188674354540648287330851150581954943056909975869, scale precision,
    0, 128, 0, 128, ⟨-318019047262953668586833368244147625902835295714, -318019047262953668586833368244147625902833198561⟩, ⟨-301983839026954352208102375424888833714136431622, -301983839026954352208102375424888833714134334469⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨154197686497932961536819931575887586175858849817, 162861817784200237565871966520572794999609887196⟩
def wholeCExp : DyadicInterval precision := ⟨1169522177914865128352659833859980547197351443196, 1183471121605739864066405757523309464057096602686⟩
def wholeCLog : DyadicInterval precision := ⟨859229422313229852746433528080764615766696322391, 866957422609189959781681149222032681615423866056⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1169522177914865128352659833859980547747107257084, scale precision, 1183471121605739864066405757523309463507340788798, scale precision,
    0, 128, 0, 128, ⟨-325723635568400475131743933041145590686227052780, -325723635568400475131743933041145590686224955627⟩, ⟨-308395372995865923073639863151775171672809894872, -308395372995865923073639863151775171672807797719⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨309067891082506609001259954034646670914709424586, 326421309931081011329908709873818033517884938469⟩
def wholeBExp : DyadicInterval precision := ⟨934981420214208148924752773574616555275528441997, 957450516359962807439347788495256247582058839168⟩
def wholeBLog : DyadicInterval precision := ⟨722767868800246844242748713431166334776712265638, 736406868263745359049599811702686317853918479869⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨934981420214208148924752773574616555825284255885, scale precision, 957450516359962807439347788495256247032303025280, scale precision,
    0, 128, 0, 128, ⟨-652842619862162022659817419747636067895113159229, -652842619862162022659817419747636067895111062076⟩, ⟨-618135782165013218002519908069293340990244391129, -618135782165013218002519908069293340990242293976⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0079RStableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0080RStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0080RStableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨154999391481232912176531096462725419644778483979, 154999391481232912176531096462725419644778483980⟩
def centerDExp : DyadicInterval precision := ⟨1182173450222225673505629770194260121401539327798, 1182173450222225673505629770194260123600562583351⟩
def centerDLog : DyadicInterval precision := ⟨866240207568659899353028711382600099926261785804, 866240207568659899353028711382600102125285041357⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1182173450222225673505629770194260121951295141686, scale precision, 1182173450222225673505629770194260123050806769463, scale precision,
    0, 128, 0, 128, ⟨-309998782962465824353062192925450839969212107887, -309998782962465824353062192925450839969210010734⟩, ⟨-309998782962465824353062192925450838609903925185, -309998782962465824353062192925450838609901828032⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨157886414463606561778317351405253986730691759120, 157886414463606561778317351405253986730691759121⟩
def centerCExp : DyadicInterval precision := ⟨1177512177457798268318717144017281214970551156601, 1177512177457798268318717144017281217169574412154⟩
def centerCLog : DyadicInterval precision := ⟨863661043937716394471097276096471115864317161613, 863661043937716394471097276096471118063340417166⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1177512177457798268318717144017281215520306970489, scale precision, 1177512177457798268318717144017281216619818598266, scale precision,
    0, 128, 0, 128, ⟨-315772828927213123556634702810507974143729121306, -315772828927213123556634702810507974143727024153⟩, ⟨-315772828927213123556634702810507972779040012332, -315772828927213123556634702810507972779037915179⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨317065270755355282202997681696928277565512072744, 317065270755355282202997681696928277565512072745⟩
def centerBExp : DyadicInterval precision := ⟨947029251425728432434882935138905507314487525081, 947029251425728432434882935138905509513510780634⟩
def centerBLog : DyadicInterval precision := ⟨730096863944862566735825393324281300164269078371, 730096863944862566735825393324281302363292333924⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨947029251425728432434882935138905507864243338969, scale precision, 947029251425728432434882935138905508963754966746, scale precision,
    0, 128, 0, 128, ⟨-634130541510710564405995363393856555979435125354, -634130541510710564405995363393856555979433028201⟩, ⟨-634130541510710564405995363393856554282615262777, -634130541510710564405995363393856554282613165624⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨150991919513477176104051187712444417195036210428, 159009523631476834293416684122073812609720086985⟩
def wholeDExp : DyadicInterval precision := ⟨1175703819620526499056916402241341505278943686883, 1188674354540648287330851150581954943606665789757⟩
def wholeDLog : DyadicInterval precision := ⟨862659221266056220624571274243273530090398223223, 869829687869058094079061307765923603360191874427⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1175703819620526499056916402241341505828699500771, scale precision, 1188674354540648287330851150581954943056909975869, scale precision,
    0, 128, 0, 128, ⟨-318019047262953668586833368244147625902835295714, -318019047262953668586833368244147625902833198561⟩, ⟨-301983839026954352208102375424888833714136431622, -301983839026954352208102375424888833714134334469⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨153556398750566205741514519544252603104850649526, 162219591438643417424467576812270848912236909425⟩
def wholeCExp : DyadicInterval precision := ⟨1170550473862244348970197146289319940669121975814, 1184510160663970923559104633505172251895935606217⟩
def wholeCLog : DyadicInterval precision := ⟨859800516574792290222578233182037981439534396491, 867531439519667230961090412510273877413075964111⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1170550473862244348970197146289319941218877789702, scale precision, 1184510160663970923559104633505172251346179792329, scale precision,
    0, 128, 0, 128, ⟨-324439182877286834848935153624541698510877581423, -324439182877286834848935153624541698510875484270⟩, ⟨-307112797501132411483029039088505205531389025539, -307112797501132411483029039088505205531386928386⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨308402344933586987341878295350818749064874893139, 325752084660906962361547582823826438291185354524⟩
def wholeBExp : DyadicInterval precision := ⟨935838073098731428091206743465742973812004580356, 958322931087011801974061944595498988366705580372⟩
def wholeBLog : DyadicInterval precision := ⟨723290207512910948896569197677397721045942770011, 736933875662125097118239462317175086821229006121⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨935838073098731428091206743465742974361760394244, scale precision, 958322931087011801974061944595498987816949766484, scale precision,
    0, 128, 0, 128, ⟨-651504169321813924723095165647652877440927361662, -651504169321813924723095165647652877440925264509⟩, ⟨-616804689867173974683756590701637497291339276427, -616804689867173974683756590701637497291337179274⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0080RStableWitnesses

end


