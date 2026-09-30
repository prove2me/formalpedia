-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0156StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0156StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:19:25.448478+00:00
-- url     : https://prove2.me/theorems/8115ac5b-62a3-4b34-885d-c144418926a7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0156StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0157StableWitnesses, GeneralCK.Certificates.E8TAxisProd01…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0156StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0157StableWitnesses, GeneralCK.Certificates.E8TAxisProd0158StableWitnesses, GeneralCK.Certificates.E8TAxisProd0159StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0156StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0157StableWitnesses, GeneralCK.Certificates.E8TAxisProd0158StableWitnesses, GeneralCK.Certificates.E8TAxisProd0159StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0156StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0157StableWitnesses, GeneralCK.Certificates.E8TAxisProd0158StableWitnesses, GeneralCK.Certificates.E8TAxisProd0159StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0156StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0157StableWitnesses, GeneralCK/Certificates/E8TAxisProd0158StableWitnesses, GeneralCK/Certificates/E8TAxisProd0159StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0156StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0156StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨347578074592523924908318039364714024927705871997, 347578074592523924908318039364714024927705871998⟩
def centerDExp : DyadicInterval precision := ⟨908299859688922494739995341064431377288246704711, 908299859688922494739995341064431379487269960264⟩
def centerDLog : DyadicInterval precision := ⟨706404787120776184926021840452869055161422984619, 706404787120776184926021840452869057360446240172⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨908299859688922494739995341064431377838002518599, scale precision, 908299859688922494739995341064431378937514146376, scale precision,
    0, 128, 0, 128, ⟨-695156149185047849816636078729428050739998442960, -695156149185047849816636078729428050739996345807⟩, ⟨-695156149185047849816636078729428048970827142184, -695156149185047849816636078729428048970825045031⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨352637767346947535742909112004860703217320900032, 352637767346947535742909112004860703217320900033⟩
def centerCExp : DyadicInterval precision := ⟨902032546038030360232638297370881794679365690226, 902032546038030360232638297370881796878388945779⟩
def centerCLog : DyadicInterval precision := ⟨702534495582703292611958958802778079541099476047, 702534495582703292611958958802778081740122731600⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨902032546038030360232638297370881795229121504114, scale precision, 902032546038030360232638297370881796328633131891, scale precision,
    0, 128, 0, 128, ⟨-705275534693895071485818224009721407325374591813, -705275534693895071485818224009721407325372494660⟩, ⟨-705275534693895071485818224009721405543911105469, -705275534693895071485818224009721405543909008316⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨746765861749167066036712365222262773594882131821, 746765861749167066036712365222262773594882131822⟩
def centerBExp : DyadicInterval precision := ⟨526001376977902856779696608708427188217383762916, 526001376977902856779696608708427190416407018469⟩
def centerBLog : DyadicInterval precision := ⟨449287026447168944552217909928056038020331483030, 449287026447168944552217909928056040219354738583⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨526001376977902856779696608708427188767139576804, scale precision, 526001376977902856779696608708427189866651204581, scale precision,
    1, 128, 1, 128, ⟨-1493531723498334132073424730444525548717268960113, -1493531723498334132073424730444525548717266862960⟩, ⟨-1493531723498334132073424730444525545662261664328, -1493531723498334132073424730444525545662259567175⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨339164617338553850423871699333891257707773909588, 356015818146773315735630103594046256346147492781⟩
def wholeDExp : DyadicInterval precision := ⟨897872332234039104779267097055247454328309327909, 918817951079152880960489128094785338008821185250⟩
def wholeDLog : DyadicInterval precision := ⟨699959742628865241142888209739517589777680401458, 712877141250487397629906767735900639146197088161⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨897872332234039104779267097055247454878065141797, scale precision, 918817951079152880960489128094785337459065371362, scale precision,
    0, 128, 0, 128, ⟨-712031636293546631471260207188092513587154905811, -712031636293546631471260207188092513587152808658⟩, ⟨-678329234677107700847743398667782514541089437367, -678329234677107700847743398667782514541087340214⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨343873197344268921505429276325898414392065692615, 361429001373380832629520534349533653251055519395⟩
def wholeCExp : DyadicInterval precision := ⟨891245737101262683231821777009961823640143117119, 912916596877989280495260089158425709861359629215⟩
def wholeCLog : DyadicInterval precision := ⟨695849158323487264058235982453080193899714236712, 709249246894175130239058694383132544665460851704⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨891245737101262683231821777009961824189898931007, scale precision, 912916596877989280495260089158425709311603815327, scale precision,
    0, 128, 0, 128, ⟨-722858002746761665259041068699067307403624418569, -722858002746761665259041068699067307403622321416⟩, ⟨-687746394688537843010858552651796827904020247351, -687746394688537843010858552651796827904018150198⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨726288180767488699553185446149232667360050618900, 767460958412969991251375042258287869919968239989⟩
def wholeBExp : DyadicInterval precision := ⟨511313809873439990011253137188545905656296841669, 540949877335522584512979002265394063834079784818⟩
def wholeBLog : DyadicInterval precision := ⟨438446483194201035413046796348184463170397646907, 460238208878101254730588953664250212432840887238⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨511313809873439990011253137188545906206052655557, scale precision, 540949877335522584512979002265394063284323970930, scale precision,
    1, 128, 1, 128, ⟨-1534921916825939982502750084516575741411318951496, -1534921916825939982502750084516575741411316854343⟩, ⟨-1452576361534977399106370892298465333234809367766, -1452576361534977399106370892298465333234807270613⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0156StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0157StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0157StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨330774838385704024446645164332729497941801346231, 330774838385704024446645164332729497941801346232⟩
def centerDExp : DyadicInterval precision := ⟨929427725267003858605636529731753968326593265085, 929427725267003858605636529731753970525616520638⟩
def centerDLog : DyadicInterval precision := ⟨719377002425149550154397054915826075326505911594, 719377002425149550154397054915826077525529167147⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨929427725267003858605636529731753968876349078973, scale precision, 929427725267003858605636529731753969975860706750, scale precision,
    0, 128, 0, 128, ⟨-661549676771408048893290328665458996748080881422, -661549676771408048893290328665458996748078784269⟩, ⟨-661549676771408048893290328665458995019126600658, -661549676771408048893290328665458995019124503505⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨335805898320327040663504506855926472520468267707, 335805898320327040663504506855926472520468267708⟩
def centerCExp : DyadicInterval precision := ⟨923050795257088086822732066019715148142802390983, 923050795257088086822732066019715150341825646536⟩
def centerCLog : DyadicInterval precision := ⟨715473773561565427855065802759262105494401721409, 715473773561565427855065802759262107693424976962⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨923050795257088086822732066019715148692558204871, scale precision, 923050795257088086822732066019715149792069832648, scale precision,
    0, 128, 0, 128, ⟨-671611796640654081327009013711852945911386996158, -671611796640654081327009013711852945911384899005⟩, ⟨-671611796640654081327009013711852944170488171827, -671611796640654081327009013711852944170486074674⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨706813465730154586771337198982012246864890807771, 706813465730154586771337198982012246864890807772⟩
def centerBExp : DyadicInterval precision := ⟨555560163249418285350093389752035198137621009346, 555560163249418285350093389752035200336644264899⟩
def centerBLog : DyadicInterval precision := ⟨470862903536341784793116763192709905705953610098, 470862903536341784793116763192709907904976865651⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨555560163249418285350093389752035198687376823234, scale precision, 555560163249418285350093389752035199786888451011, scale precision,
    1, 128, 1, 128, ⟨-1413626931460309173542674397964024495176014909122, -1413626931460309173542674397964024495176012811969⟩, ⟨-1413626931460309173542674397964024492283550419117, -1413626931460309173542674397964024492283548321964⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨322408132378444526209018649139695484921606350582, 339164617338553850423871699333891257707773909589⟩
def wholeDExp : DyadicInterval precision := ⟨918817951079152880960489128094785335809797929697, 940130328208408204655831711119657711878645153902⟩
def wholeDLog : DyadicInterval precision := ⟨712877141250487397629906767735900636947173832608, 725904575743015811666185701912516251881166002297⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨918817951079152880960489128094785336359553743585, scale precision, 940130328208408204655831711119657711328889340014, scale precision,
    0, 128, 0, 128, ⟨-678329234677107700847743398667782516290008298142, -678329234677107700847743398667782516290006200989⟩, ⟨-644816264756889052418037298279390968988577963593, -644816264756889052418037298279390968988575866440⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨327090680858758583373932802371003276516688738835, 344546464008129346091878105779578884429905982105⟩
def wholeCExp : DyadicInterval precision := ⟨912075881767334120094256239395639958508841862537, 934125365302252464635631009739543173737956048932⟩
def wholeCLog : DyadicInterval precision := ⟨708731678392671451820057937515112134201479069089, 722245708143222885807268476168971921328534503954⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨912075881767334120094256239395639959058597676425, scale precision, 934125365302252464635631009739543173188200235044, scale precision,
    0, 128, 0, 128, ⟨-689092928016258692183756211559157769740736451495, -689092928016258692183756211559157769740734354342⟩, ⟨-654181361717517166747865604742006552173248770677, -654181361717517166747865604742006552173246673524⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨686746784135662041361783775179230530642546345197, 727087195464729964811335267510126589391029154203⟩
def wholeBExp : DyadicInterval precision := ⟨540358717290803630500603264005556785802569439428, 571027442729152088477736821499906456147927434383⟩
def wholeBLog : DyadicInterval precision := ⟨459806683358730684789292325484676888823263074369, 482027272914487729614436700641673715826584760900⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨540358717290803630500603264005556786352325253316, scale precision, 571027442729152088477736821499906455598171620495, scale precision,
    1, 128, 1, 128, ⟨-1454174390929459929622670535020253180268977206959, -1454174390929459929622670535020253180268975109806⟩, ⟨-1373493568271324082723567550358461059878035230032, -1373493568271324082723567550358461059878033132879⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0157StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0158StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0158StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨347578074592523924908318039364714024927705871997, 347578074592523924908318039364714024927705871998⟩
def centerDExp : DyadicInterval precision := ⟨908299859688922494739995341064431377288246704711, 908299859688922494739995341064431379487269960264⟩
def centerDLog : DyadicInterval precision := ⟨706404787120776184926021840452869055161422984619, 706404787120776184926021840452869057360446240172⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨908299859688922494739995341064431377838002518599, scale precision, 908299859688922494739995341064431378937514146376, scale precision,
    0, 128, 0, 128, ⟨-695156149185047849816636078729428050739998442960, -695156149185047849816636078729428050739996345807⟩, ⟨-695156149185047849816636078729428048970827142184, -695156149185047849816636078729428048970825045031⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨351962631759981556280962456265113090278767507621, 351962631759981556280962456265113090278767507622⟩
def centerCExp : DyadicInterval precision := ⟨902866312715135512766893692393849513024755617214, 902866312715135512766893692393849515223778872767⟩
def centerCLog : DyadicInterval precision := ⟨703049967917784408271442311339212209473374639499, 703049967917784408271442311339212211672397895052⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨902866312715135512766893692393849513574511431102, scale precision, 902866312715135512766893692393849514674023058879, scale precision,
    0, 128, 0, 128, ⟨-703925263519963112561924912530226181447445246180, -703925263519963112561924912530226181447443149027⟩, ⟨-703925263519963112561924912530226179667626881457, -703925263519963112561924912530226179667624784304⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨745958753463314230711506589196840900544859389630, 745958753463314230711506589196840900544859389631⟩
def centerBExp : DyadicInterval precision := ⟨526582662137948553892087416150623738933844712116, 526582662137948553892087416150623741132867967669⟩
def centerBLog : DyadicInterval precision := ⟨449714409448554820072772359482588594687673685245, 449714409448554820072772359482588596886696940798⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨526582662137948553892087416150623739483600526004, scale precision, 526582662137948553892087416150623740583112153781, scale precision,
    1, 128, 1, 128, ⟨-1491917506926628461423013178393681802615537291839, -1491917506926628461423013178393681802615535194686⟩, ⟨-1491917506926628461423013178393681799563902363837, -1491917506926628461423013178393681799563900266684⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨339164617338553850423871699333891257707773909588, 356015818146773315735630103594046256346147492781⟩
def wholeDExp : DyadicInterval precision := ⟨897872332234039104779267097055247454328309327909, 918817951079152880960489128094785338008821185250⟩
def wholeDLog : DyadicInterval precision := ⟨699959742628865241142888209739517589777680401458, 712877141250487397629906767735900639146197088161⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨897872332234039104779267097055247454878065141797, scale precision, 918817951079152880960489128094785337459065371362, scale precision,
    0, 128, 0, 128, ⟨-712031636293546631471260207188092513587154905811, -712031636293546631471260207188092513587152808658⟩, ⟨-678329234677107700847743398667782514541089437367, -678329234677107700847743398667782514541087340214⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨343200084397114651700616511900199179081958739590, 360751790294758116634357805075516741583889296052⟩
def wholeCExp : DyadicInterval precision := ⟨892072066991257785754281552593305036253190633266, 913757894713163016505213102396506446860385206096⟩
def wholeCLog : DyadicInterval precision := ⟨696362375538974423103809126688934699563274230813, 709766990723107812917057116339658854868648811399⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨892072066991257785754281552593305036802946447154, scale precision, 913757894713163016505213102396506446310629392208, scale precision,
    0, 128, 0, 128, ⟨-721503580589516233268715610151033484068456897439, -721503580589516233268715610151033484068454800286⟩, ⟨-686400168794229303401233023800398357284616661499, -686400168794229303401233023800398357284614564346⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨725489492374379835709792374714335031090376306718, 766645226495309387918731185011730320819877664150⟩
def wholeBExp : DyadicInterval precision := ⟨511884904521197338754882311587328657031762965577, 541541442301640071515188763044860578340455677384⟩
def wholeBLog : DyadicInterval precision := ⟨438869500450241106105566329066449653465557562315, 460669902469242203068314936618513433220757871358⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨511884904521197338754882311587328657581518779465, scale precision, 541541442301640071515188763044860577790699863496, scale precision,
    1, 128, 1, 128, ⟨-1533290452990618775837462370023460643209384656656, -1533290452990618775837462370023460643209382559503⟩, ⟨-1450978984748759671419584749428670060697083236506, -1450978984748759671419584749428670060697081139353⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0158StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0159StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0159StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨330774838385704024446645164332729497941801346231, 330774838385704024446645164332729497941801346232⟩
def centerDExp : DyadicInterval precision := ⟨929427725267003858605636529731753968326593265085, 929427725267003858605636529731753970525616520638⟩
def centerDLog : DyadicInterval precision := ⟨719377002425149550154397054915826075326505911594, 719377002425149550154397054915826077525529167147⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨929427725267003858605636529731753968876349078973, scale precision, 929427725267003858605636529731753969975860706750, scale precision,
    0, 128, 0, 128, ⟨-661549676771408048893290328665458996748080881422, -661549676771408048893290328665458996748078784269⟩, ⟨-661549676771408048893290328665458995019126600658, -661549676771408048893290328665458995019124503505⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨335134605721498841594280831922832390595255708313, 335134605721498841594280831922832390595255708314⟩
def centerCExp : DyadicInterval precision := ⟨923899130761395807892753291547976711101414155281, 923899130761395807892753291547976713300437410834⟩
def centerCLog : DyadicInterval precision := ⟨715993629287381424471997271167548919883841904912, 715993629287381424471997271167548922082865160465⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨923899130761395807892753291547976711651169969169, scale precision, 923899130761395807892753291547976712750681596946, scale precision,
    0, 128, 0, 128, ⟨-670269211442997683188561663845664782060162620052, -670269211442997683188561663845664782060160522899⟩, ⟨-670269211442997683188561663845664780320862310357, -670269211442997683188561663845664780320860213204⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨706022671539624411025582194983808140774018978396, 706022671539624411025582194983808140774018978397⟩
def centerBExp : DyadicInterval precision := ⟨556161697370634439402834409758232786911677666700, 556161697370634439402834409758232789110700922253⟩
def centerBLog : DyadicInterval precision := ⟨471298691888759574764440945023705766982412055106, 471298691888759574764440945023705769181435310659⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨556161697370634439402834409758232787461433480588, scale precision, 556161697370634439402834409758232788560945108365, scale precision,
    1, 128, 1, 128, ⟨-1412045343079248822051164389967616282992707032545, -1412045343079248822051164389967616282992704935392⟩, ⟨-1412045343079248822051164389967616280103370978196, -1412045343079248822051164389967616280103368881043⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨322408132378444526209018649139695484921606350582, 339164617338553850423871699333891257707773909589⟩
def wholeDExp : DyadicInterval precision := ⟨918817951079152880960489128094785335809797929697, 940130328208408204655831711119657711878645153902⟩
def wholeDLog : DyadicInterval precision := ⟨712877141250487397629906767735900636947173832608, 725904575743015811666185701912516251881166002297⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨918817951079152880960489128094785336359553743585, scale precision, 940130328208408204655831711119657711328889340014, scale precision,
    0, 128, 0, 128, ⟨-678329234677107700847743398667782516290008298142, -678329234677107700847743398667782516290006200989⟩, ⟨-644816264756889052418037298279390968988577963593, -644816264756889052418037298279390968988575866440⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨326421309931081011329908709873818033517884938468, 343873197344268921505429276325898414392065692616⟩
def wholeCExp : DyadicInterval precision := ⟨912916596877989280495260089158425707662336373662, 934981420214208148924752773574616557474551697550⟩
def wholeCLog : DyadicInterval precision := ⟨709249246894175130239058694383132542466437596151, 722767868800246844242748713431166336975735521191⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨912916596877989280495260089158425708212092187550, scale precision, 934981420214208148924752773574616556924795883662, scale precision,
    0, 128, 0, 128, ⟨-687746394688537843010858552651796829664244620263, -687746394688537843010858552651796829664242523110⟩, ⟨-652842619862162022659817419747636066176428691796, -652842619862162022659817419747636066176426594643⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨685963999756797209752584202718138649636232751542, 726288180767488699553185446149232667360050618901⟩
def wholeBExp : DyadicInterval precision := ⟨540949877335522584512979002265394061635056529265, 571639458269859880067295969679856100962578123521⟩
def wholeBLog : DyadicInterval precision := ⟨460238208878101254730588953664250210233817631685, 482467279940599822739468415949780310166247788826⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨540949877335522584512979002265394062184812343153, scale precision, 571639458269859880067295969679856100412822309633, scale precision,
    1, 128, 1, 128, ⟨-1452576361534977399106370892298465336205395204989, -1452576361534977399106370892298465336205393107836⟩, ⟨-1371927999513594419505168405436277297866914484696, -1371927999513594419505168405436277297866912387543⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0159StableWitnesses

end


