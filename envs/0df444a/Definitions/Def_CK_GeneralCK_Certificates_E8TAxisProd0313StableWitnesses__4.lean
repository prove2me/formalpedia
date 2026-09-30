-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0313StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0313StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T20:01:19.37393+00:00
-- url     : https://prove2.me/theorems/b33f4dc2-c5e9-4d1e-b261-586384ce9fd4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0313StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0314StableWitnesses, GeneralCK.Certificates.E8TAxisProd03…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0313StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0314StableWitnesses, GeneralCK.Certificates.E8TAxisProd0315StableWitnesses, GeneralCK.Certificates.E8TAxisProd0316StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0313StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0314StableWitnesses, GeneralCK.Certificates.E8TAxisProd0315StableWitnesses, GeneralCK.Certificates.E8TAxisProd0316StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0313StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0314StableWitnesses, GeneralCK.Certificates.E8TAxisProd0315StableWitnesses, GeneralCK.Certificates.E8TAxisProd0316StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0313StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0314StableWitnesses, GeneralCK/Certificates/E8TAxisProd0315StableWitnesses, GeneralCK/Certificates/E8TAxisProd0316StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0313StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0313StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨780097432743148472065827322615976914715321380242, 780097432743148472065827322615976914715321380243⟩
def centerDExp : DyadicInterval precision := ⟨502547949796029941349747428157944022560728851116, 502547949796029941349747428157944024759752106669⟩
def centerDLog : DyadicInterval precision := ⟨431938086327136521229594192068681255335127784667, 431938086327136521229594192068681257534151040220⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨502547949796029941349747428157944023110484665004, scale precision, 502547949796029941349747428157944024209996292781, scale precision,
    1, 128, 1, 128, ⟨-1560194865486296944131654645231953831029434576104, -1560194865486296944131654645231953831029432478951⟩, ⟨-1560194865486296944131654645231953827831853042018, -1560194865486296944131654645231953827831850944865⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨784002162304114043099317321803255252349862449714, 784002162304114043099317321803255252349862449715⟩
def centerCExp : DyadicInterval precision := ⟨499869772297843797504455619550444785579872778488, 499869772297843797504455619550444787778896034041⟩
def centerCLog : DyadicInterval precision := ⟨429943823082900815625458228337849656794070049314, 429943823082900815625458228337849658993093304867⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨499869772297843797504455619550444786129628592376, scale precision, 499869772297843797504455619550444787229140220153, scale precision,
    1, 128, 1, 128, ⟨-1568004324608228086198634643606510506307082637003, -1568004324608228086198634643606510506307080539850⟩, ⟨-1568004324608228086198634643606510503092369259009, -1568004324608228086198634643606510503092367161856⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1952729836462571730707011752159487108300541861020, 1952729836462571730707011752159487108300541861021⟩
def centerBExp : DyadicInterval precision := ⟨100987400193076882696392276615758692790839479073, 100987400193076882696392276615758694989862734626⟩
def centerBLog : DyadicInterval precision := ⟨97651197573922029763223680347709210602585632953, 97651197573922029763223680347709212801608888506⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨100987400193076882696392276615758693340595292961, scale precision, 100987400193076882696392276615758694440106920738, scale precision,
    3, 128, 3, 128, ⟨-3905459672925143461414023504318974224557216135457, -3905459672925143461414023504318974224557214038304⟩, ⟨-3905459672925143461414023504318974208644953405768, -3905459672925143461414023504318974208644951308615⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨774203834768265108571628471566363912561698867070, 786008954924549138888839394711577924172029077197⟩
def wholeDExp : DyadicInterval precision := ⟨498498909896069833132911032342083543572056459341, 506617451172271417683927781753795731632056364141⟩
def wholeDLog : DyadicInterval precision := ⟨428921977795889549222947679819138372580498428270, 434963177842048586751554818318029033914423871208⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨498498909896069833132911032342083544121812273229, scale precision, 506617451172271417683927781753795731082300550253, scale precision,
    1, 128, 1, 128, ⟨-1572017909849098277777678789423155849955836091904, -1572017909849098277777678789423155849955833994751⟩, ⟨-1548407669536530217143256943132727823537450607677, -1548407669536530217143256943132727823537448510524⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨777891647546635597138833563221306289939779184489, 790131948877739904083861773233963986865884366676⟩
def wholeCExp : DyadicInterval precision := ⟨495694231931024301246504577872503231582650368558, 504067192084870322198404859237889766919414971585⟩
def wholeCLog : DyadicInterval precision := ⟨426829132963654659859399313733114143151960946144, 433068157986980978319671954459641925956470516151⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨495694231931024301246504577872503232132406182446, scale precision, 504067192084870322198404859237889766369659157697, scale precision,
    1, 128, 1, 128, ⟨-1580263897755479808167723546467927975352666234566, -1580263897755479808167723546467927975352664137413⟩, ⟨-1555783295093271194277667126442612578285587354411, -1555783295093271194277667126442612578285585257258⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1934781404229217960038886135093835683716979535040, 1970723335728780996836052704795570134840517461369⟩
def wholeBExp : DyadicInterval precision := ⟨98531121726903411418133211754806366637918572123, 103498527946832056235430089184964059785102036858⟩
def wholeBLog : DyadicInterval precision := ⟨95351866472733025226206155970015231708520164456, 99998139721020937227686094386315155175029942334⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨98531121726903411418133211754806367187674386011, scale precision, 103498527946832056235430089184964059235346222970, scale precision,
    3, 128, 3, 128, ⟨-3941446671457561993672105409591140277835505422675, -3941446671457561993672105409591140277835503325522⟩, ⟨-3869562808458435920077772270187671359670863985133, -3869562808458435920077772270187671359670861887980⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0313StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0314StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0314StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨795453216539044351832352221798446016419836097590, 795453216539044351832352221798446016419836097591⟩
def centerCExp : DyadicInterval precision := ⟨492097737679520023701406583584776964797872388060, 492097737679520023701406583584776966996895643613⟩
def centerCLog : DyadicInterval precision := ⟨424141043513453235036834171449965259424631408549, 424141043513453235036834171449965261623654664102⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨492097737679520023701406583584776965347628201948, scale precision, 492097737679520023701406583584776966447139829725, scale precision,
    1, 128, 1, 128, ⟨-1590906433078088703664704443596892034472416011321, -1590906433078088703664704443596892034472413914168⟩, ⟨-1590906433078088703664704443596892031206930476196, -1590906433078088703664704443596892031206928379043⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1987525948764759247689004093242527611585254544868, 1987525948764759247689004093242527611585254544869⟩
def centerBExp : DyadicInterval precision := ⟨96291382241943057493808038511355004069386308928, 96291382241943057493808038511355006268409564481⟩
def centerBLog : DyadicInterval precision := ⟨93252080455197497247109385154676288194816658674, 93252080455197497247109385154676290393839914227⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨96291382241943057493808038511355004619142122816, scale precision, 96291382241943057493808038511355005718653750593, scale precision,
    3, 128, 3, 128, ⟨-3975051897529518495378008186485055231514652712895, -3975051897529518495378008186485055231514650615742⟩, ⟨-3975051897529518495378008186485055214826367563734, -3975051897529518495378008186485055214826365466581⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨789306650046952486889940289746852556386041921506, 801619283297715594379972822490439431071660319425⟩
def wholeCExp : DyadicInterval precision := ⟨487962892215298326112682608645603772328537071891, 496254377687821368268838233217146085732222406686⟩
def wholeCLog : DyadicInterval precision := ⟨421044457946547528686139642548226300998502014631, 427247352124700439373871515163771055698825656961⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨487962892215298326112682608645603772878292885779, scale precision, 496254377687821368268838233217146085182466592798, scale precision,
    1, 128, 1, 128, ⟨-1603238566595431188759945644980878863789899808320, -1603238566595431188759945644980878863789897711167⟩, ⟨-1578613300093904973779880579493705111153018021342, -1578613300093904973779880579493705111153015924189⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1969491601583864251457289075399537866306566670143, 2005602933477353093108762255081303780498199039842⟩
def wholeBExp : DyadicInterval precision := ⟨93938590517514989677769095586087999429618360390, 98697343215060360165536763710699102360480029730⟩
def wholeBLog : DyadicInterval precision := ⟨91043052516129531878635520564270627792595877023, 95507581174463235627546562258218643047410541685⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨93938590517514989677769095586087999979374174278, scale precision, 98697343215060360165536763710699101810724215842, scale precision,
    3, 128, 3, 128, ⟨-4011205866954706186217524510162607569549529611742, -4011205866954706186217524510162607569549527514589⟩, ⟨-3938983203167728502914578150799075724472398316776, -3938983203167728502914578150799075724472396219623⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0314StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0315StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0315StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨780097432743148472065827322615976914715321380242, 780097432743148472065827322615976914715321380243⟩
def centerDExp : DyadicInterval precision := ⟨502547949796029941349747428157944022560728851116, 502547949796029941349747428157944024759752106669⟩
def centerDLog : DyadicInterval precision := ⟨431938086327136521229594192068681255335127784667, 431938086327136521229594192068681257534151040220⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨502547949796029941349747428157944023110484665004, scale precision, 502547949796029941349747428157944024209996292781, scale precision,
    1, 128, 1, 128, ⟨-1560194865486296944131654645231953831029434576104, -1560194865486296944131654645231953831029432478951⟩, ⟨-1560194865486296944131654645231953827831853042018, -1560194865486296944131654645231953827831850944865⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨783590768529798764441452006667171936717559035120, 783590768529798764441452006667171936717559035121⟩
def centerCExp : DyadicInterval precision := ⟨500151265255264747787803955228372342651808113072, 500151265255264747787803955228372344850831368625⟩
def centerCLog : DyadicInterval precision := ⟨430153560462092134992230687988874096718736197685, 430153560462092134992230687988874098917759453238⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨500151265255264747787803955228372343201563926960, scale precision, 500151265255264747787803955228372344301075554737, scale precision,
    1, 128, 1, 128, ⟨-1567181537059597528882904013334343875041571162322, -1567181537059597528882904013334343875041569065169⟩, ⟨-1567181537059597528882904013334343871828667075315, -1567181537059597528882904013334343871828664978162⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1952115463577566131769614501276306850552347114218, 1952115463577566131769614501276306850552347114219⟩
def centerBExp : DyadicInterval precision := ⟨101072340240484581107539383033960585431039732609, 101072340240484581107539383033960587630062988162⟩
def centerBLog : DyadicInterval precision := ⟨97730645583637185892574271766289711669739490530, 97730645583637185892574271766289713868762746083⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨101072340240484581107539383033960585980795546497, scale precision, 101072340240484581107539383033960587080307174274, scale precision,
    3, 128, 3, 128, ⟨-3904230927155132263539229002552613709054140399377, -3904230927155132263539229002552613709054138302224⟩, ⟨-3904230927155132263539229002552613693155250154657, -3904230927155132263539229002552613693155248057504⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨774203834768265108571628471566363912561698867070, 786008954924549138888839394711577924172029077197⟩
def wholeDExp : DyadicInterval precision := ⟨498498909896069833132911032342083543572056459341, 506617451172271417683927781753795731632056364141⟩
def wholeDLog : DyadicInterval precision := ⟨428921977795889549222947679819138372580498428270, 434963177842048586751554818318029033914423871208⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨498498909896069833132911032342083544121812273229, scale precision, 506617451172271417683927781753795731082300550253, scale precision,
    1, 128, 1, 128, ⟨-1572017909849098277777678789423155849955836091904, -1572017909849098277777678789423155849955833994751⟩, ⟨-1548407669536530217143256943132727823537450607677, -1548407669536530217143256943132727823537448510524⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨777481544922208521741875213762229092139903749016, 789719255653951548822230430713390385501532680033⟩
def wholeCExp : DyadicInterval precision := ⟨495974255465491844759123076081273877330358173710, 504350157618547194099449345982391659609258465770⟩
def wholeCLog : DyadicInterval precision := ⟨427038220662286302690951182009306298519248153201, 433278542288741041682971195343304875326616237472⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨495974255465491844759123076081273877880113987598, scale precision, 504350157618547194099449345982391659059502651882, scale precision,
    1, 128, 1, 128, ⟨-1579438511307903097644460861426780772623047714680, -1579438511307903097644460861426780772623045617527⟩, ⟨-1554963089844417043483750427524458182686730781107, -1554963089844417043483750427524458182686728683954⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1934168594595516678001016949637548541861434104709, 1970107443032899946045237766792141542604738794845⟩
def wholeBExp : DyadicInterval precision := ⟨98614200906528023923283228289019029021703424359, 103585358498313719103595477319667826275171728276⟩
def wholeBLog : DyadicInterval precision := ⟨95429696328133777529932636628055567313340851427, 100079225637585937185206342701861835049213413601⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨98614200906528023923283228289019029571459238247, scale precision, 103585358498313719103595477319667825725415914388, scale precision,
    3, 128, 3, 128, ⟨-3940214886065799892090475533584283093357078220726, -3940214886065799892090475533584283093357076123573⟩, ⟨-3868337189191033356002033899275097075966280549151, -3868337189191033356002033899275097075966278451998⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0315StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0316StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0316StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨772209186499448132067305381638357686236332773817, 772209186499448132067305381638357686236332773818⟩
def centerCExp : DyadicInterval precision := ⟨508002196844923980799088765233713471863513776395, 508002196844923980799088765233713474062537031948⟩
def centerCLog : DyadicInterval precision := ⟨435991111796639257486570232268257626039737018682, 435991111796639257486570232268257628238760274235⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨508002196844923980799088765233713472413269590283, scale precision, 508002196844923980799088765233713473512781218060, scale precision,
    1, 128, 1, 128, ⟨-1544418372998896264134610763276715374054291689802, -1544418372998896264134610763276715374054289592649⟩, ⟨-1544418372998896264134610763276715370891041502617, -1544418372998896264134610763276715370891039405464⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1917490573670338960099416660459509937771962584592, 1917490573670338960099416660459509937771962584593⟩
def centerBExp : DyadicInterval precision := ⟨105976685583225697339983553917290031402131594483, 105976685583225697339983553917290033601154850036⟩
def centerBLog : DyadicInterval precision := ⟨102310578393720981819988182749093766449261443885, 102310578393720981819988182749093768648284699438⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨105976685583225697339983553917290031951887408371, scale precision, 105976685583225697339983553917290033051399036148, scale precision,
    3, 128, 3, 128, ⟨-3834981147340677920198833320919019883125490197688, -3834981147340677920198833320919019883125488100535⟩, ⟨-3834981147340677920198833320919019867962362237827, -3834981147340677920198833320919019867962360140674⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨766135567721021778181278960307768552870433322902, 778301836709476402480898380936913162630577459495⟩
def wholeCExp : DyadicInterval precision := ⟨503784325648793644324816973487962261438204053827, 512242040804304655323460144559117787010399779975⟩
def wholeCLog : DyadicInterval precision := ⟨432857817090652076519115336024368111214159638398, 439133973743416442773927028379977704535099683961⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨503784325648793644324816973487962261987959867715, scale precision, 512242040804304655323460144559117786460643966087, scale precision,
    1, 128, 1, 128, ⟨-1556603673418952804961796761873826326856023019246, -1556603673418952804961796761873826326856020922093⟩, ⟨-1532271135442043556362557920615537104172333762905, -1532271135442043556362557920615537104172331665752⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1899634466240213433072015561106460669947467232106, 1935394268029072592499156280915193182704500962532⟩
def wholeBExp : DyadicInterval precision := ⟨103411762515873828440410049293994769804673319600, 108598154258471743876933062012947096172950937737⟩
def wholeBLog : DyadicInterval precision := ⟨99917110122724915545263899600679893219235747485, 104752768843021559259667036334154946272935965667⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨103411762515873828440410049293994770354429133488, scale precision, 108598154258471743876933062012947095623195123849, scale precision,
    3, 128, 3, 128, ⟨-3870788536058145184998312561830386373178612567203, -3870788536058145184998312561830386373178610470050⟩, ⟨-3799268932480426866144031122212921332496384150503, -3799268932480426866144031122212921332496382053350⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0316StableWitnesses

end


