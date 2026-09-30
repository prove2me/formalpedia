-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0449StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0449StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:56:57.878531+00:00
-- url     : https://prove2.me/theorems/bfc699fd-ff94-457b-8b4b-15142145fc9e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0449StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0450StableWitnesses, GeneralCK.Certificates.E8TAxisProd04…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0449StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0450StableWitnesses, GeneralCK.Certificates.E8TAxisProd0451StableWitnesses, GeneralCK.Certificates.E8TAxisProd0452StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0449StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0450StableWitnesses, GeneralCK.Certificates.E8TAxisProd0451StableWitnesses, GeneralCK.Certificates.E8TAxisProd0452StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0449StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0450StableWitnesses, GeneralCK.Certificates.E8TAxisProd0451StableWitnesses, GeneralCK.Certificates.E8TAxisProd0452StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0449StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0450StableWitnesses, GeneralCK/Certificates/E8TAxisProd0451StableWitnesses, GeneralCK/Certificates/E8TAxisProd0452StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0449StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0449StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨687872580056255843160164202748380391008755458653, 687872580056255843160164202748380391008755458654⟩
def centerDExp : DyadicInterval precision := ⟨570148394211525905172999746249825252784123887881, 570148394211525905172999746249825254983147143434⟩
def centerDLog : DyadicInterval precision := ⟨481395051335389284017617212273304505633359993607, 481395051335389284017617212273304507832383249160⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨570148394211525905172999746249825253333879701769, scale precision, 570148394211525905172999746249825254433391329546, scale precision,
    1, 128, 1, 128, ⟨-1375745160112511686320328405496760783426739862143, -1375745160112511686320328405496760783426737764990⟩, ⟨-1375745160112511686320328405496760780608284069625, -1375745160112511686320328405496760780608281972472⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨693953170102350195040475811154054585128760209282, 693953170102350195040475811154054585128760209283⟩
def centerCExp : DyadicInterval precision := ⟨565423863394075722663182195118680616760905877889, 565423863394075722663182195118680618959929133442⟩
def centerCLog : DyadicInterval precision := ⟨477992422708981805761906920246560188109514043905, 477992422708981805761906920246560190308537299458⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨565423863394075722663182195118680617310661691777, scale precision, 565423863394075722663182195118680618410173319554, scale precision,
    1, 128, 1, 128, ⟨-1387906340204700390080951622308109171678524495397, -1387906340204700390080951622308109171678522398244⟩, ⟨-1387906340204700390080951622308109168836518438889, -1387906340204700390080951622308109168836516341736⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1680032951862440541127179308444651812156059641529, 1680032951862440541127179308444651812156059641530⟩
def centerBExp : DyadicInterval precision := ⟨146667675798941958101908974289133152236090589918, 146667675798941958101908974289133154435113845471⟩
def centerBLog : DyadicInterval precision := ⟨139766373646246328385880360132257938592708971264, 139766373646246328385880360132257940791732226817⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨146667675798941958101908974289133152785846403806, scale precision, 146667675798941958101908974289133153885358031583, scale precision,
    3, 128, 3, 128, ⟨-3360065903724881082254358616889303629790280517604, -3360065903724881082254358616889303629790278420451⟩, ⟨-3360065903724881082254358616889303618833960145668, -3360065903724881082254358616889303618833958048515⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨682249998762477519670394645145297230397519416513, 693511205829020257423882496604739492695821414415⟩
def wholeDExp : DyadicInterval precision := ⟨565765939962058116901418666290376202748638649045, 574552180098098577953261580846255154870927737058⟩
def wholeDLog : DyadicInterval precision := ⟨478239054014281969770673762969782321702426146976, 484559560373994267607098493867261018654665103074⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨565765939962058116901418666290376203298394462933, scale precision, 574552180098098577953261580846255154321171923170, scale precision,
    1, 128, 1, 128, ⟨-1387022411658040514847764993209478986811787730860, -1387022411658040514847764993209478986811785633707⟩, ⟨-1364499997524955039340789290290594459396613333134, -1364499997524955039340789290290594459396611235981⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨688117403189925269023413300262066776374484662458, 699806257356875677533443481737167955641447730265⟩
def wholeCExp : DyadicInterval precision := ⟨560913082830714205703567430471177357528095599478, 569957409633834276386638279927268713405592364409⟩
def wholeCLog : DyadicInterval precision := ⟨474736328853562051563390858983507676169942765407, 481257656907716479197718191967027872353618193093⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨560913082830714205703567430471177358077851413366, scale precision, 569957409633834276386638279927268712855836550521, scale precision,
    1, 128, 1, 128, ⟨-1399612514713751355066886963474335912715327034840, -1399612514713751355066886963474335912715324937687⟩, ⟨-1376234806379850538046826600524133551339270265117, -1376234806379850538046826600524133551339268167964⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1662951662317545377766557686605882154116823010173, 1697179641826103933915969760994929555110868679197⟩
def wholeBExp : DyadicInterval precision := ⟨143266256981708350449706378941595763067412050399, 150136413451526906436248704935433689312036799826⟩
def wholeBLog : DyadicInterval precision := ⟨136671896096980406025400834381416061252134738762, 142915361860133957721580706332300454378100869734⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨143266256981708350449706378941595763617167864287, scale precision, 150136413451526906436248704935433688762280985938, scale precision,
    3, 128, 3, 128, ⟨-3394359283652207867831939521989859115829960741090, -3394359283652207867831939521989859115829958643937⟩, ⟨-3325903324635090755533115373211764302882053783460, -3325903324635090755533115373211764302882051686307⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0449StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0450StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0450StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨699165997627898866254694872768746753397359927635, 699165997627898866254694872768746753397359927636⟩
def centerDExp : DyadicInterval precision := ⟨561404751706234480105216227684808901745528779369, 561404751706234480105216227684808903944552034922⟩
def centerDLog : DyadicInterval precision := ⟨475091591069212524269724099885343165971571379074, 475091591069212524269724099885343168170594634627⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨561404751706234480105216227684808902295284593257, scale precision, 561404751706234480105216227684808903394796221034, scale precision,
    1, 128, 1, 128, ⟨-1398331995255797732509389745537493508225896930926, -1398331995255797732509389745537493508225894833773⟩, ⟨-1398331995255797732509389745537493505363544876768, -1398331995255797732509389745537493505363542779615⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨704886462101827030359916663069019978249385236586, 704886462101827030359916663069019978249385236587⟩
def centerCExp : DyadicInterval precision := ⟨557027119175365027230672140175094603465492923349, 557027119175365027230672140175094605664516178902⟩
def centerCLog : DyadicInterval precision := ⟨471925428860339137607882105766970748714786475804, 471925428860339137607882105766970750913809731357⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨557027119175365027230672140175094604015248737237, scale precision, 557027119175365027230672140175094605114760365014, scale precision,
    1, 128, 1, 128, ⟨-1409772924203654060719833326138039957941195049206, -1409772924203654060719833326138039957941192952053⟩, ⟨-1409772924203654060719833326138039955056347994291, -1409772924203654060719833326138039955056345897138⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1713211620608840422771596309974653699676551190462, 1713211620608840422771596309974653699676551190463⟩
def centerBExp : DyadicInterval precision := ⟨140157359228792704004035552312147549571505875871, 140157359228792704004035552312147551770529131424⟩
def centerBLog : DyadicInterval precision := ⟨133837800242224174636411853170653776814421352558, 133837800242224174636411853170653779013444608111⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨140157359228792704004035552312147550121261689759, scale precision, 140157359228792704004035552312147551220773317536, scale precision,
    3, 128, 3, 128, ⟨-3426423241217680845543192619949307405085724438853, -3426423241217680845543192619949307405085722341700⟩, ⟨-3426423241217680845543192619949307393620482420149, -3426423241217680845543192619949307393620480322996⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨693511205829020257423882496604739492695821414414, 704837076587479092158941059188951191105662022839⟩
def wholeDExp : DyadicInterval precision := ⟨557064765387537285209117120927584102725232557331, 565765939962058116901418666290376204947661904598⟩
def wholeDLog : DyadicInterval precision := ⟨471952686082951260798866870121334518051885287659, 478239054014281969770673762969782323901449402529⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨557064765387537285209117120927584103274988371219, scale precision, 565765939962058116901418666290376204397906090710, scale precision,
    1, 128, 1, 128, ⟨-1409674153174958184317882118377902383653651143312, -1409674153174958184317882118377902383653649046159⟩, ⟨-1387022411658040514847764993209478983971500023954, -1387022411658040514847764993209478983971497926801⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨699018274946216839467202719819796045222121051365, 710772219499800002539550232633061131065685412855⟩
def wholeCExp : DyadicInterval precision := ⟨552558621154368501616986397782311831674376840684, 561518252226973885127647258841657517196832520275⟩
def wholeCLog : DyadicInterval precision := ⟨468686457657077742530140922151493327041519892158, 475173590189077688502320697137834447850808780929⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨552558621154368501616986397782311832224132654572, scale precision, 561518252226973885127647258841657516647076706387, scale precision,
    1, 128, 1, 128, ⟨-1421544438999600005079100465266122263585460167128, -1421544438999600005079100465266122263585458069975⟩, ⟨-1398036549892433678934405439639592089013356409971, -1398036549892433678934405439639592089013354312818⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1696005161928035909525083653275876691580547963276, 1730480979171308863079045827616715137963238279929⟩
def wholeBExp : DyadicInterval precision := ⟨136883943166681602440876159476332480627922426187, 143496703018118585762422141401556519442682892276⟩
def wholeBLog : DyadicInterval precision := ⟨130847776517299761396889421162079513400864278473, 136881753909347954311105295699260300092149884357⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨136883943166681602440876159476332481177678240075, scale precision, 143496703018118585762422141401556518892927078388, scale precision,
    3, 128, 3, 128, ⟨-3460961958342617726158091655233430281796187404504, -3460961958342617726158091655233430281796185307351⟩, ⟨-3392010323856071819050167306551753377561881068209, -3392010323856071819050167306551753377561878971056⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0450StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0451StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0451StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨687872580056255843160164202748380391008755458653, 687872580056255843160164202748380391008755458654⟩
def centerDExp : DyadicInterval precision := ⟨570148394211525905172999746249825252784123887881, 570148394211525905172999746249825254983147143434⟩
def centerDLog : DyadicInterval precision := ⟨481395051335389284017617212273304505633359993607, 481395051335389284017617212273304507832383249160⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨570148394211525905172999746249825253333879701769, scale precision, 570148394211525905172999746249825254433391329546, scale precision,
    1, 128, 1, 128, ⟨-1375745160112511686320328405496760783426739862143, -1375745160112511686320328405496760783426737764990⟩, ⟨-1375745160112511686320328405496760780608284069625, -1375745160112511686320328405496760780608281972472⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨693560308079891890998028330637341438090707017715, 693560308079891890998028330637341438090707017716⟩
def centerCExp : DyadicInterval precision := ⟨565727925023054165807504696264180603842492563720, 565727925023054165807504696264180606041515819273⟩
def centerCLog : DyadicInterval precision := ⟨478211647954449960484269144943580687151897471471, 478211647954449960484269144943580689350920727024⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨565727925023054165807504696264180604392248377608, scale precision, 565727925023054165807504696264180605491760005385, scale precision,
    1, 128, 1, 128, ⟨-1387120616159783781996056661274682877601654366164, -1387120616159783781996056661274682877601652269011⟩, ⟨-1387120616159783781996056661274682874761175801853, -1387120616159783781996056661274682874761173704700⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1679447889113805195677159679330364232516576223989, 1679447889113805195677159679330364232516576223990⟩
def centerBExp : DyadicInterval precision := ⟨146785149706003115935910173269716331031637875546, 146785149706003115935910173269716333230661131099⟩
def centerBLog : DyadicInterval precision := ⟨139873129841414655878780935028689782423114079898, 139873129841414655878780935028689784622137335451⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨146785149706003115935910173269716331581393689434, scale precision, 146785149706003115935910173269716332680905317211, scale precision,
    3, 128, 3, 128, ⟨-3358895778227610391354319358660728470506929445554, -3358895778227610391354319358660728470506927348401⟩, ⟨-3358895778227610391354319358660728459559377547566, -3358895778227610391354319358660728459559375450413⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨682249998762477519670394645145297230397519416513, 693511205829020257423882496604739492695821414415⟩
def wholeDExp : DyadicInterval precision := ⟨565765939962058116901418666290376202748638649045, 574552180098098577953261580846255154870927737058⟩
def wholeDLog : DyadicInterval precision := ⟨478239054014281969770673762969782321702426146976, 484559560373994267607098493867261018654665103074⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨565765939962058116901418666290376203298394462933, scale precision, 574552180098098577953261580846255154321171923170, scale precision,
    1, 128, 1, 128, ⟨-1387022411658040514847764993209478986811787730860, -1387022411658040514847764993209478986811785633707⟩, ⟨-1364499997524955039340789290290594459396613333134, -1364499997524955039340789290290594459396611235981⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨687725700735041234130853821378029194186295533812, 699412226729351037223251834141358780805047251837⟩
def wholeCExp : DyadicInterval precision := ⟨561215616234337660797995178659569170848891162893, 570263004313409008720751178422727456988272597554⟩
def wholeCLog : DyadicInterval precision := ⟨474954938811624802399157458689696645450129917738, 481477495715337280592891852574908626833406903728⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨561215616234337660797995178659569171398646976781, scale precision, 570263004313409008720751178422727456438516783666, scale precision,
    1, 128, 1, 128, ⟨-1398824453458702074446503668282717563041753900465, -1398824453458702074446503668282717563041751803312⟩, ⟨-1375451401470082468261707642756058386963647443211, -1375451401470082468261707642756058386963645346058⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1662368858123314123245758132647461198576942678621, 1696592364383445283685959180461638427222092120207⟩
def wholeBExp : DyadicInterval precision := ⟨143381441059296053248962342673329569932810602126, 150256201251973880649267538755360220585789685146⟩
def wholeBLog : DyadicInterval precision := ⟨136776793308230379246279946956164845369549057884, 143023986473786724590467701560892341434209934548⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨143381441059296053248962342673329570482566416014, scale precision, 150256201251973880649267538755360220036033871258, scale precision,
    3, 128, 3, 128, ⟨-3393184728766890567371918360923276860047902312578, -3393184728766890567371918360923276860047900215425⟩, ⟨-3324737716246628246491516265294922391806559537205, -3324737716246628246491516265294922391806557440052⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0451StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0452StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0452StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨676643340013426075185609328596269506214112195118, 676643340013426075185609328596269506214112195119⟩
def centerDExp : DyadicInterval precision := ⟨578977364869803800462989438501500576320691752033, 578977364869803800462989438501500578519715007586⟩
def centerDLog : DyadicInterval precision := ⟨487732559398326774108745629110692920177628439235, 487732559398326774108745629110692922376651694788⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨578977364869803800462989438501500576870447565921, scale precision, 578977364869803800462989438501500577969959193698, scale precision,
    1, 128, 1, 128, ⟨-1353286680026852150371218657192539013815963666390, -1353286680026852150371218657192539013815961569237⟩, ⟨-1353286680026852150371218657192539011040487211240, -1353286680026852150371218657192539011040485114087⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨682689450985518055977446966268082448940349368721, 682689450985518055977446966268082448940349368722⟩
def centerCExp : DyadicInterval precision := ⟨574206765050947912446896833561260108317480004370, 574206765050947912446896833561260110516503259923⟩
def centerCLog : DyadicInterval precision := ⟨484311596651690336206517271104793076458651431488, 484311596651690336206517271104793078657674687041⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨574206765050947912446896833561260108867235818258, scale precision, 574206765050947912446896833561260109966747446035, scale precision,
    1, 128, 1, 128, ⟨-1365378901971036111954893932536164899279967560336, -1365378901971036111954893932536164899279965463183⟩, ⟨-1365378901971036111954893932536164896481432011703, -1365378901971036111954893932536164896481429914550⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1646517631133051021181716628111674714560935735173, 1646517631133051021181716628111674714560935735174⟩
def centerBExp : DyadicInterval precision := ⟨153551120585180497796242564466749997186869923111, 153551120585180497796242564466749999385893178664⟩
def centerBLog : DyadicInterval precision := ⟨146008687019417574216281434408300149636446329100, 146008687019417574216281434408300151835469584653⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨153551120585180497796242564466749997736625736999, scale precision, 153551120585180497796242564466749998836137364776, scale precision,
    3, 128, 3, 128, ⟨-3293035262266102042363433256223349434354455772424, -3293035262266102042363433256223349434354453675271⟩, ⟨-3293035262266102042363433256223349423889289265424, -3293035262266102042363433256223349423889287168271⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨671052481512572809340093335645151882932874114537, 682249998762477519670394645145297230397519416514⟩
def wholeDExp : DyadicInterval precision := ⟨574552180098098577953261580846255152671904481505, 583424017396714902499808941799093865790753691861⟩
def wholeDLog : DyadicInterval precision := ⟨484559560373994267607098493867261016455641847521, 490914027605645316992013980560028282815828884161⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨574552180098098577953261580846255153221660295393, scale precision, 583424017396714902499808941799093865240997877973, scale precision,
    1, 128, 1, 128, ⟨-1364499997524955039340789290290594462193466430073, -1364499997524955039340789290290594462193464332920⟩, ⟨-1342104963025145618680186671290303764488587902438, -1342104963025145618680186671290303764488585805285⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨676886778349777664619303492649313482610181178240, 688509183314938616996838045356376332131953665847⟩
def wholeCExp : DyadicInterval precision := ⟨569651918170250097134241553068733734975339469782, 578784519636346772256564170159193951215868690710⟩
def wholeCLog : DyadicInterval precision := ⟨481037859295318283248263055497744137625062154199, 487594426664064662860821143617928002470712912101⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨569651918170250097134241553068733735525095283670, scale precision, 578784519636346772256564170159193950666112876822, scale precision,
    1, 128, 1, 128, ⟨-1377018366629877233993676090712752665674364478988, -1377018366629877233993676090712752665674362381835⟩, ⟨-1353773556699555329238606985298626963832162796936, -1353773556699555329238606985298626963832160699783⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1629568612854644677560044379834200368999050304567, 1663534544446404090279176869532917308474765413942⟩
def wholeBExp : DyadicInterval precision := ⟨150016705149456755418414277874292937901029785535, 157154205278119926711519446275219570808897273479⟩
def wholeBLog : DyadicInterval precision := ⟨142806801270319719248581834561923533700476978874, 149265576868139565289363747102420810511992503402⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨150016705149456755418414277874292938450785599423, scale precision, 157154205278119926711519446275219570259141459591, scale precision,
    3, 128, 3, 128, ⟨-3327069088892808180558353739065834622305395553975, -3327069088892808180558353739065834622305393456822⟩, ⟨-3259137225709289355120088759668400732885486181026, -3259137225709289355120088759668400732885484083873⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0452StableWitnesses

end


