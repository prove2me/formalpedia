-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0277StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0277StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T23:35:40.939976+00:00
-- url     : https://prove2.me/theorems/40a420b8-9359-436d-bc90-f6289f8748f3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0277StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0278StableWitnesses, GeneralCK.Certificates.E8TAxisProd02…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0277StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0278StableWitnesses, GeneralCK.Certificates.E8TAxisProd0279StableWitnesses, GeneralCK.Certificates.E8TAxisProd0280StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0277StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0278StableWitnesses, GeneralCK.Certificates.E8TAxisProd0279StableWitnesses, GeneralCK.Certificates.E8TAxisProd0280StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0277StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0278StableWitnesses, GeneralCK.Certificates.E8TAxisProd0279StableWitnesses, GeneralCK.Certificates.E8TAxisProd0280StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0277StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0278StableWitnesses, GeneralCK/Certificates/E8TAxisProd0279StableWitnesses, GeneralCK/Certificates/E8TAxisProd0280StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0277StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0277StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4906913324212444341793886191975635191530054563, 4906913324212444341793886191975635191530054564⟩
def centerAExp : DyadicInterval precision := ⟨1451720686451934407431403951699999116082005297895, 1451720686451934407431403951699999118281028553448⟩
def centerALog : DyadicInterval precision := ⟨1008137063309063130766142500412726798681612460495, 1008137063309063130766142500412726800880635716048⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1451720686451934407431403951699999116631761111783, scale precision, 1451720686451934407431403951699999117731272739560, scale precision,
    0, 128, 0, 128, ⟨-9813826648424888683587772383951270936520944858, -9813826648424888683587772383951270936518847705⟩, ⟨-9813826648424888683587772383951269829601370550, -9813826648424888683587772383951269829599273397⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨756629458111635987963421694655899447515956153847, 756629458111635987963421694655899447515956153848⟩
def centerDExp : DyadicInterval precision := ⟨518949168719742299502489786080534463489111235356, 518949168719742299502489786080534465688134490909⟩
def centerDLog : DyadicInterval precision := ⟨444091993825822657919630218920559695762275777424, 444091993825822657919630218920559697961299032977⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨518949168719742299502489786080534464038867049244, scale precision, 518949168719742299502489786080534465138378677021, scale precision,
    1, 128, 1, 128, ⟨-1513258916223271975926843389311798896580174863487, -1513258916223271975926843389311798896580172766334⟩, ⟨-1513258916223271975926843389311798893483651849057, -1513258916223271975926843389311798893483649751904⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨762927784361834418407987279407994337098460666583, 762927784361834418407987279407994337098460666584⟩
def centerCExp : DyadicInterval precision := ⟨514495576805314348432572317133760263004713236112, 514495576805314348432572317133760265203736491665⟩
def centerCLog : DyadicInterval precision := ⟨440801701831143829108222757573261963546077818515, 440801701831143829108222757573261965745101074068⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨514495576805314348432572317133760263554469050000, scale precision, 514495576805314348432572317133760264653980677777, scale precision,
    1, 128, 1, 128, ⟨-1525855568723668836815974558815988675758585996269, -1525855568723668836815974558815988675758583899116⟩, ⟨-1525855568723668836815974558815988672635258767221, -1525855568723668836815974558815988672635256670068⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1886084281562207335757793096441141692879078805211, 1886084281562207335757793096441141692879078805212⟩
def centerBExp : DyadicInterval precision := ⟨110630656779802414553057115247091935507037441069, 110630656779802414553057115247091937706060696622⟩
def centerBLog : DyadicInterval precision := ⟨106643466981203834110065329174321395145105243316, 106643466981203834110065329174321397344128498869⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨110630656779802414553057115247091936056793254957, scale precision, 110630656779802414553057115247091937156304882734, scale precision,
    3, 128, 3, 128, ⟨-3772168563124414671515586192882283393020784096804, -3772168563124414671515586192882283393020781999651⟩, ⟨-3772168563124414671515586192882283378495533221191, -3772168563124414671515586192882283378495531124038⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4748624479255801076876082777124010865681651338, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1452035179538035812075122148102075718654446240893⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1008294829281404787796718047455216465384960373552⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1452035179538035812075122148102075718104690427005, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-9497248958511602153752165554248021178024436730, -9497248958511602153752165554248021178022339577⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨750806424999049798752938234956163650116084001297, 762469961061176672454638714549067897721941573493⟩
def wholeDExp : DyadicInterval precision := ⟨514818014850194000087183801285808384916278939514, 523100967242339682629524513379347097451596710168⟩
def wholeDLog : DyadicInterval precision := ⟨441040166381185817721359138930122616152471066865, 447152665109602019123525890115620511802318039062⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨514818014850194000087183801285808385466034753402, scale precision, 523100967242339682629524513379347096901840896280, scale precision,
    1, 128, 1, 128, ⟨-1524939922122353344909277429098135797004569717344, -1524939922122353344909277429098135797004567620191⟩, ⟨-1501612849998099597505876469912327298696195936143, -1501612849998099597505876469912327298696193838990⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨756883028922881915174985275614420312561635289775, 768991378531425944311427866808425478226721721175⟩
def wholeCExp : DyadicInterval precision := ⟨510244079853831118783388651347226677950805952260, 518769124400892565552871376066334004300491890640⟩
def wholeCLog : DyadicInterval precision := ⟨437653790598836308430548153319451526028158743416, 443959121538554262481971064280810509659301443912⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨510244079853831118783388651347226678500561766148, scale precision, 518769124400892565552871376066334003750736076752, scale precision,
    1, 128, 1, 128, ⟨-1537982757062851888622855733616850958028120325206, -1537982757062851888622855733616850958028118228053⟩, ⟨-1513766057845763830349970551228840623574472780359, -1513766057845763830349970551228840623574470683206⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1868315118000739887943271174858272651442820314637, 1903903322113399698837077367278650588864392479757⟩
def wholeBExp : DyadicInterval precision := ⟨107965601541320347416630992185635812010433849881, 113353759878106356024947584002474056534303661368⟩
def wholeBLog : DyadicInterval precision := ⟨104163848883451126517891512619375745616745803105, 109172755952412386433230411591559991044775527652⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨107965601541320347416630992185635812560189663769, scale precision, 113353759878106356024947584002474055984547847480, scale precision,
    3, 128, 3, 128, ⟨-3807806644226799397674154734557301185170684266984, -3807806644226799397674154734557301185170682169831⟩, ⟨-3736630236001479775886542349716545295797486657723, -3736630236001479775886542349716545295797484560570⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0277StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0278StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0278StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4590335763975281399345081579386246932603875055, 4590335763975281399345081579386246932603875056⟩
def centerAExp : DyadicInterval precision := ⟨1452349740496526708002027977982130829907047701826, 1452349740496526708002027977982130832106070957379⟩
def centerALog : DyadicInterval precision := ⟨1008452612267868520487407126245153689838327381286, 1008452612267868520487407126245153692037350636839⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452349740496526708002027977982130830456803515714, scale precision, 1452349740496526708002027977982130831556315143491, scale precision,
    0, 128, 0, 128, ⟨-9180671527950562798690163158772494418428866641, -9180671527950562798690163158772494418426769488⟩, ⟨-9180671527950562798690163158772493311988730734, -9180671527950562798690163158772493311986633581⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨768328048611850508777866556237345596219489900939, 768328048611850508777866556237345596219489900940⟩
def centerDExp : DyadicInterval precision := ⟨510707457819051547382306257729904114775482130573, 510707457819051547382306257729904116974505386126⟩
def centerDLog : DyadicInterval precision := ⟨437997216266833750200638020923159195569100090572, 437997216266833750200638020923159197768123346125⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨510707457819051547382306257729904115325237944461, scale precision, 510707457819051547382306257729904116424749572238, scale precision,
    1, 128, 1, 128, ⟨-1536656097223701017555733112474691194012227940995, -1536656097223701017555733112474691194012225843842⟩, ⟨-1536656097223701017555733112474691190865733759918, -1536656097223701017555733112474691190865731662765⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨774255006513559823730231453333758862314642031514, 774255006513559823730231453333758862314642031515⟩
def centerCExp : DyadicInterval precision := ⟨506581975890089807110663730723165176169978225433, 506581975890089807110663730723165178369001480986⟩
def centerCLog : DyadicInterval precision := ⟨434936834085426554595950017198577378454764684330, 434936834085426554595950017198577380653787939883⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨506581975890089807110663730723165176719734039321, scale precision, 506581975890089807110663730723165177819245667098, scale precision,
    1, 128, 1, 128, ⟨-1548510013027119647460462906667517726215344348550, -1548510013027119647460462906667517726215342251397⟩, ⟨-1548510013027119647460462906667517723043225874661, -1548510013027119647460462906667517723043223777508⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1920547697980714738861627957756747815545804980880, 1920547697980714738861627957756747815545804980881⟩
def centerBExp : DyadicInterval precision := ⟨105534254130460729507562389681752602227078216809, 105534254130460729507562389681752604426101472362⟩
def centerBLog : DyadicInterval precision := ⟨101898001354541306009992941420797363673834401833, 101898001354541306009992941420797365872857657386⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨105534254130460729507562389681752602776834030697, scale precision, 105534254130460729507562389681752603876345658474, scale precision,
    3, 128, 3, 128, ⟨-3841095395961429477723255915513495638704959195257, -3841095395961429477723255915513495638704957098104⟩, ⟨-3841095395961429477723255915513495623478262825432, -3841095395961429477723255915513495623478260728279⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 4748624479255801076876082777124010865681651339⟩
def wholeAExp : DyadicInterval precision := ⟨1452035179538035812075122148102075716455422985340, 1452664369350591901250217311774540050861815457867⟩
def wholeALog : DyadicInterval precision := ⟨1008294829281404787796718047455216463185937117999, 1008610412272733567070593870872814922068705325217⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452035179538035812075122148102075717005178799228, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-9497248958511602153752165554248022284704265776, -9497248958511602153752165554248022284702168623⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨762469961061176672454638714549067897721941573492, 774203834768265108571628471566363912561698867071⟩
def wholeDExp : DyadicInterval precision := ⟨506617451172271417683927781753795729433033108588, 514818014850194000087183801285808387115302195067⟩
def wholeDLog : DyadicInterval precision := ⟨434963177842048586751554818318029031715400615655, 441040166381185817721359138930122618351494322418⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨506617451172271417683927781753795729982788922476, scale precision, 514818014850194000087183801285808386565546381179, scale precision,
    1, 128, 1, 128, ⟨-1548407669536530217143256943132727826709346957757, -1548407669536530217143256943132727826709344860604⟩, ⟨-1524939922122353344909277429098135793883198673776, -1524939922122353344909277429098135793883196576623⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨768175004601111508805576807505928586677554639557, 780354081921873303697987664330433619691437969040⟩
def wholeCExp : DyadicInterval precision := ⟨502371479419976992531597308946334669879476758944, 510814428486735487400488284538229117085508014526⟩
def wholeCLog : DyadicInterval precision := ⟨431806764117837091476095028392722248463207552184, 438076484518207476305631270601929960108187619610⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨502371479419976992531597308946334670429232572832, scale precision, 510814428486735487400488284538229116535752200638, scale precision,
    1, 128, 1, 128, ⟨-1560708163843746607395975328660867240982229368398, -1560708163843746607395975328660867240982227271245⟩, ⟨-1536350009202223017611153615011857171782192693962, -1536350009202223017611153615011857171782190596809⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1902683364366205758745751601618170960911474691520, 1938459397727976043997493853891485963872162528560⟩
def wholeBExp : DyadicInterval precision := ⟨102978910961562032211032605471059213680397882493, 108145996109375667402280847961522199929510245882⟩
def wholeBLog : DyadicInterval precision := ⟨99512806113791536418494733500327884331540958773, 104331824231657771760808035344178931150606603531⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨102978910961562032211032605471059214230153696381, scale precision, 108145996109375667402280847961522199379754431994, scale precision,
    3, 128, 3, 128, ⟨-3876918795455952087994987707782971935546593721730, -3876918795455952087994987707782971935546591624577⟩, ⟨-3805366728732411517491503203236341914393465743925, -3805366728732411517491503203236341914393463646772⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0278StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0279StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0279StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4590335763975281399345081579386246932603875055, 4590335763975281399345081579386246932603875056⟩
def centerAExp : DyadicInterval precision := ⟨1452349740496526708002027977982130829907047701826, 1452349740496526708002027977982130832106070957379⟩
def centerALog : DyadicInterval precision := ⟨1008452612267868520487407126245153689838327381286, 1008452612267868520487407126245153692037350636839⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452349740496526708002027977982130830456803515714, scale precision, 1452349740496526708002027977982130831556315143491, scale precision,
    0, 128, 0, 128, ⟨-9180671527950562798690163158772494418428866641, -9180671527950562798690163158772494418426769488⟩, ⟨-9180671527950562798690163158772493311988730734, -9180671527950562798690163158772493311986633581⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨756629458111635987963421694655899447515956153847, 756629458111635987963421694655899447515956153848⟩
def centerDExp : DyadicInterval precision := ⟨518949168719742299502489786080534463489111235356, 518949168719742299502489786080534465688134490909⟩
def centerDLog : DyadicInterval precision := ⟨444091993825822657919630218920559695762275777424, 444091993825822657919630218920559697961299032977⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨518949168719742299502489786080534464038867049244, scale precision, 518949168719742299502489786080534465138378677021, scale precision,
    1, 128, 1, 128, ⟨-1513258916223271975926843389311798896580174863487, -1513258916223271975926843389311798896580172766334⟩, ⟨-1513258916223271975926843389311798893483651849057, -1513258916223271975926843389311798893483649751904⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨762520824997189519172425694723105925652387616600, 762520824997189519172425694723105925652387616601⟩
def centerCExp : DyadicInterval precision := ⟨514782182171542592418531514811924130234270116967, 514782182171542592418531514811924132433293372520⟩
def centerCLog : DyadicInterval precision := ⟨441013667634779508880382047781170544218936032726, 441013667634779508880382047781170546417959288279⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨514782182171542592418531514811924130784025930855, scale precision, 514782182171542592418531514811924131883537558632, scale precision,
    1, 128, 1, 128, ⟨-1525041649994379038344851389446211852865570438913, -1525041649994379038344851389446211852865568341760⟩, ⟨-1525041649994379038344851389446211849743982124644, -1525041649994379038344851389446211849743980027491⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1885475957895832827535748806904519162208272021696, 1885475957895832827535748806904519162208272021697⟩
def centerBExp : DyadicInterval precision := ⟨110722791150229187056455637898440579560101978440, 110722791150229187056455637898440581759125233993⟩
def centerBLog : DyadicInterval precision := ⟨106729115363465452142857774798860697033869512133, 106729115363465452142857774798860699232892767686⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨110722791150229187056455637898440580109857792328, scale precision, 110722791150229187056455637898440581209369420105, scale precision,
    3, 128, 3, 128, ⟨-3770951915791665655071497613809038331673127172166, -3770951915791665655071497613809038331673125075013⟩, ⟨-3770951915791665655071497613809038317159963011770, -3770951915791665655071497613809038317159960914617⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 4748624479255801076876082777124010865681651339⟩
def wholeAExp : DyadicInterval precision := ⟨1452035179538035812075122148102075716455422985340, 1452664369350591901250217311774540050861815457867⟩
def wholeALog : DyadicInterval precision := ⟨1008294829281404787796718047455216463185937117999, 1008610412272733567070593870872814922068705325217⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452035179538035812075122148102075717005178799228, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-9497248958511602153752165554248022284704265776, -9497248958511602153752165554248022284702168623⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨750806424999049798752938234956163650116084001297, 762469961061176672454638714549067897721941573493⟩
def wholeDExp : DyadicInterval precision := ⟨514818014850194000087183801285808384916278939514, 523100967242339682629524513379347097451596710168⟩
def wholeDLog : DyadicInterval precision := ⟨441040166381185817721359138930122616152471066865, 447152665109602019123525890115620511802318039062⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨514818014850194000087183801285808385466034753402, scale precision, 523100967242339682629524513379347096901840896280, scale precision,
    1, 128, 1, 128, ⟨-1524939922122353344909277429098135797004569717344, -1524939922122353344909277429098135797004567620191⟩, ⟨-1501612849998099597505876469912327298696195936143, -1501612849998099597505876469912327298696193838990⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨756477331477196904987707623019285920506989327038, 768583148729555186523227397183684354683615218325⟩
def wholeCExp : DyadicInterval precision := ⟨510529204450427640340123701123111364679906832615, 519057214043081169049897021766264638959001014647⟩
def wholeCLog : DyadicInterval precision := ⟨437865115991776121813261947848008190288071716918, 444171725222947065515678732007859073554049663143⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨510529204450427640340123701123111365229662646503, scale precision, 519057214043081169049897021766264638409245200759, scale precision,
    1, 128, 1, 128, ⟨-1537166297459110373046454794367368710941027881446, -1537166297459110373046454794367368710941025784293⟩, ⟨-1512954662954393809975415246038571839466040476701, -1512954662954393809975415246038571839466038379548⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1867708522680053326505056059127813391834353866137, 1903293314827719281407291856171675824888649965830⟩
def wholeBExp : DyadicInterval precision := ⟨108055765381488251809219228729243697620099087087, 113447893754116648262125943143452518263158757134⟩
def wholeBLog : DyadicInterval precision := ⟨104247807829375904365137458252592323972381724136, 109260111720207707297057212437927675389899929562⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨108055765381488251809219228729243698169854900975, scale precision, 113447893754116648262125943143452517713402943246, scale precision,
    3, 128, 3, 128, ⟨-3806586629655438562814583712343351657212989573930, -3806586629655438562814583712343351657212987476777⟩, ⟨-3735417045360106653010112118255626776586435187734, -3735417045360106653010112118255626776586433090581⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0279StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0280StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0280StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4273758705152157645723775860095423839948701825, 4273758705152157645723775860095423839948701826⟩
def centerAExp : DyadicInterval precision := ⟨1452979066123426753084482090982379267943336487380, 1452979066123426753084482090982379270142359742933⟩
def centerALog : DyadicInterval precision := ⟨1008768229300280628272830658947964075013109562599, 1008768229300280628272830658947964077212132818152⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452979066123426753084482090982379268493092301268, scale precision, 1452979066123426753084482090982379269592603929045, scale precision,
    0, 128, 0, 128, ⟨-8547517410304315291447551720190848232878905189, -8547517410304315291447551720190848232876808036⟩, ⟨-8547517410304315291447551720190847126917999264, -8547517410304315291447551720190847126915902111⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨791938512842554261609794269869582385953292906566, 791938512842554261609794269869582385953292906567⟩
def centerDExp : DyadicInterval precision := ⟨494470288976765335249663465240012275930998297549, 494470288976765335249663465240012278130021553102⟩
def centerDLog : DyadicInterval precision := ⟨425914889167615021373493039688154777291425506011, 425914889167615021373493039688154779490448761564⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨494470288976765335249663465240012276480754111437, scale precision, 494470288976765335249663465240012277580265739214, scale precision,
    1, 128, 1, 128, ⟨-1583877025685108523219588539739164773531495455899, -1583877025685108523219588539739164773531493358746⟩, ⟨-1583877025685108523219588539739164770281678267518, -1583877025685108523219588539739164770281676170365⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨797523662265743918357736698010976211027438319915, 797523662265743918357736698010976211027438319916⟩
def centerCExp : DyadicInterval precision := ⟨490705444140627766790542842932403231784500171785, 490705444140627766790542842932403233983523427338⟩
def centerCLog : DyadicInterval precision := ⟨423099087443383370181073463999436360429365469069, 423099087443383370181073463999436362628388724622⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨490705444140627766790542842932403232334255985673, scale precision, 490705444140627766790542842932403233433767613450, scale precision,
    1, 128, 1, 128, ⟨-1595047324531487836715473396021952423692253086877, -1595047324531487836715473396021952423692250989724⟩, ⟨-1595047324531487836715473396021952420417502289940, -1595047324531487836715473396021952420417500192787⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1990613044735305892511790264898745275437073148543, 1990613044735305892511790264898745275437073148544⟩
def centerBExp : DyadicInterval precision := ⟨95885452180904482327173193241455507385168680928, 95885452180904482327173193241455509584191936481⟩
def centerBLog : DyadicInterval precision := ⟨92871192396444506014656794545514032144470380006, 92871192396444506014656794545514034343493635559⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨95885452180904482327173193241455507934924494816, scale precision, 95885452180904482327173193241455509034436122593, scale precision,
    3, 128, 3, 128, ⟨-3981226089470611785023580529797490559253614760746, -3981226089470611785023580529797490559253612663593⟩, ⟨-3981226089470611785023580529797490542494679930583, -3981226089470611785023580529797490542494677833430⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4115470352964345628383522602588716836376905846, 4432047174048269527644776165804031130864675905⟩
def wholeAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1453293830838237185210198542808669484539789010133⟩
def wholeALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1008926063354791867585944205900164502304869828050⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1453293830838237185210198542808669483990033196245, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-8230940705928691256767045205177433119894175747, -8230940705928691256767045205177433119892078594⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨786008954924549138888839394711577924172029077196, 797886217135535601213561462349015058648188303748⟩
def wholeDExp : DyadicInterval precision := ⟨490462045819898463991457369988920386537963137363, 498498909896069833132911032342083545771079714894⟩
def wholeDLog : DyadicInterval precision := ⟨422916858198723400101802834922666846616439225893, 428921977795889549222947679819138374779521683823⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨490462045819898463991457369988920387087718951251, scale precision, 498498909896069833132911032342083545221323901006, scale precision,
    1, 128, 1, 128, ⟨-1595772434271071202427122924698030118934565623881, -1595772434271071202427122924698030118934563526728⟩, ⟨-1572017909849098277777678789423155846732282314032, -1572017909849098277777678789423155846732280216879⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨791370554621716418654315272559769045398297445580, 803696310944812440969022459738225718904065351190⟩
def wholeCExp : DyadicInterval precision := ⟨486577914747696709790903248729443372711909107793, 494854753316875008028661859966649692212072059848⟩
def wholeCLog : DyadicInterval precision := ⟨420005779804942359384841535882528920403182293414, 426202132578112652564666822207894721531212584762⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨486577914747696709790903248729443373261664921681, scale precision, 494854753316875008028661859966649691662316245960, scale precision,
    1, 128, 1, 128, ⟨-1607392621889624881938044919476451439459396631211, -1607392621889624881938044919476451439459394534058⟩, ⟨-1582741109243432837308630545119538089172949775394, -1582741109243432837308630545119538089172947678241⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1972571320794985487516278294458037721104916739529, 2008697193698693596943215232503748635648535803243⟩
def wholeBExp : DyadicInterval precision := ⟨93541661902616612035010359993628655954859751287, 98282262613805823702334782365487546223658604629⟩
def wholeBLog : DyadicInterval precision := ⟨90670048242886782630462508916152539945077098129, 95118706616381383620510330541910812425970640802⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨93541661902616612035010359993628656504615565175, scale precision, 98282262613805823702334782365487545673902790741, scale precision,
    3, 128, 3, 128, ⟨-4017394387397387193886430465007497279886496937124, -4017394387397387193886430465007497279886494839971⟩, ⟨-3945142641589970975032556588916075434034717260673, -3945142641589970975032556588916075434034715163520⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0280StableWitnesses

end


