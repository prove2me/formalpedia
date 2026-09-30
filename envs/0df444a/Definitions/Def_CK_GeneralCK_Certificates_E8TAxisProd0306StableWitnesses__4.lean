-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0306StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0306StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:53:27.651471+00:00
-- url     : https://prove2.me/theorems/30e099d3-106b-47d8-8196-1525db53db62
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0306StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0307StableWitnesses, GeneralCK.Certificates.E8TAxisProd03…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0306StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0307StableWitnesses, GeneralCK.Certificates.E8TAxisProd0308StableWitnesses, GeneralCK.Certificates.E8TAxisProd0309StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0306StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0307StableWitnesses, GeneralCK.Certificates.E8TAxisProd0308StableWitnesses, GeneralCK.Certificates.E8TAxisProd0309StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0306StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0307StableWitnesses, GeneralCK.Certificates.E8TAxisProd0308StableWitnesses, GeneralCK.Certificates.E8TAxisProd0309StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0306StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0307StableWitnesses, GeneralCK/Certificates/E8TAxisProd0308StableWitnesses, GeneralCK/Certificates/E8TAxisProd0309StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0306StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0306StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3324030191359282881556817859241043973740987770, 3324030191359282881556817859241043973740987771⟩
def centerAExp : DyadicInterval precision := ⟨1454868674354870198336951421367206718659928330939, 1454868674354870198336951421367206720858951586492⟩
def centerALog : DyadicInterval precision := ⟨1009715489181788885783740077569471416073335956070, 1009715489181788885783740077569471418272359211623⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454868674354870198336951421367206719209684144827, scale precision, 1454868674354870198336951421367206720309195772604, scale precision,
    0, 128, 0, 128, ⟨-6648060382718565763113635718482088499745256643, -6648060382718565763113635718482088499743159490⟩, ⟨-6648060382718565763113635718482087395220791593, -6648060382718565763113635718482087395218694440⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨796281130178643850396140406866846852948562149213, 796281130178643850396140406866846852948562149214⟩
def centerCExp : DyadicInterval precision := ⟨491540524860815398883215111264883420571913436876, 491540524860815398883215111264883422770936692429⟩
def centerCLog : DyadicInterval precision := ⟨423724129166617977960514280964702616757221626148, 423724129166617977960514280964702618956244881701⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨491540524860815398883215111264883421121669250764, scale precision, 491540524860815398883215111264883422221180878541, scale precision,
    1, 128, 1, 128, ⟨-1592562260357287700792280813733693707531719000004, -1592562260357287700792280813733693707531716902851⟩, ⟨-1592562260357287700792280813733693704262531694002, -1592562260357287700792280813733693704262529596849⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1988760637998108302266751652801672954219358666829, 1988760637998108302266751652801672954219358666830⟩
def centerBExp : DyadicInterval precision := ⟨96128824024854703071258766886650426950617121156, 96128824024854703071258766886650429149640376709⟩
def centerBLog : DyadicInterval precision := ⟨93099562441446751018020771032495387511228084848, 93099562441446751018020771032495389710251340401⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨96128824024854703071258766886650427500372935044, scale precision, 96128824024854703071258766886650428599884562821, scale precision,
    3, 128, 3, 128, ⟨-3977521275996216604533503305603345916796971281728, -3977521275996216604533503305603345916796969184575⟩, ⟨-3977521275996216604533503305603345900080465482749, -3977521275996216604533503305603345900080463385596⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3482318024844347500022322904444928295572395253⟩
def wholeAExp : DyadicInterval precision := ⟨1454553569581723058392238696431353224119669669100, 1455183847209450510423929547351191477780877052172⟩
def wholeALog : DyadicInterval precision := ⟨1009557569928173087760872372803888449827653659813, 1009873425488092576137085252579843092274389747387⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1454553569581723058392238696431353224669425482988, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-6964636049688695000044645808889857143527710010, -6964636049688695000044645808889857143525612857⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨790131948877739904083861773233963986865884366675, 802449828068310820313022285246700462607886380914⟩
def wholeCExp : DyadicInterval precision := ⟨487408606411112256842506512413820889060958019062, 495694231931024301246504577872503233781673624111⟩
def wholeCLog : DyadicInterval precision := ⟨420628854181934150052585729135735080083534957150, 426829132963654659859399313733114145350984201697⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨487408606411112256842506512413820889610713832950, scale precision, 495694231931024301246504577872503233231917810223, scale precision,
    1, 128, 1, 128, ⟨-1604899656136621640626044570493400926864224435939, -1604899656136621640626044570493400926864222338786⟩, ⟨-1580263897755479808167723546467927972110873329290, -1580263897755479808167723546467927972110871232137⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1970723335728780996836052704795570134840517461368, 2006840492744667837812694984015978146311927742217⟩
def wholeBExp : DyadicInterval precision := ⟨93779635940018793520398849571650913357599541317, 98531121726903411418133211754806368836941827676⟩
def wholeBLog : DyadicInterval precision := ⟨90893690141265349366758964042710365898198662479, 95351866472733025226206155970015233907543420009⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨93779635940018793520398849571650913907355355205, scale precision, 98531121726903411418133211754806368287186013788, scale precision,
    3, 128, 3, 128, ⟨-4013680985489335675625389968031956301191484398871, -4013680985489335675625389968031956301191482301718⟩, ⟨-3941446671457561993672105409591140261526566519956, -3941446671457561993672105409591140261526564422803⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0306StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0307StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0307StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3324030191359282881556817859241043973740987770, 3324030191359282881556817859241043973740987771⟩
def centerAExp : DyadicInterval precision := ⟨1454868674354870198336951421367206718659928330939, 1454868674354870198336951421367206720858951586492⟩
def centerALog : DyadicInterval precision := ⟨1009715489181788885783740077569471416073335956070, 1009715489181788885783740077569471418272359211623⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454868674354870198336951421367206719209684144827, scale precision, 1454868674354870198336951421367206720309195772604, scale precision,
    0, 128, 0, 128, ⟨-6648060382718565763113635718482088499745256643, -6648060382718565763113635718482088499743159490⟩, ⟨-6648060382718565763113635718482087395220791593, -6648060382718565763113635718482087395218694440⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨784413643176910449102457963069937601769214483584, 784413643176910449102457963069937601769214483585⟩
def centerCExp : DyadicInterval precision := ⟨499588378222922174848212728241069860409535049639, 499588378222922174848212728241069862608558305192⟩
def centerCLog : DyadicInterval precision := ⟨429734129292517886350597291914310274462810395216, 429734129292517886350597291914310276661833650769⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨499588378222922174848212728241069860959290863527, scale precision, 499588378222922174848212728241069862058802491304, scale precision,
    1, 128, 1, 128, ⟨-1568827286353820898204915926139875205146692051360, -1568827286353820898204915926139875205146689954207⟩, ⟨-1568827286353820898204915926139875201930167980130, -1568827286353820898204915926139875201930165882977⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1953344262021694905834396522179105711026662986476, 1953344262021694905834396522179105711026662986477⟩
def centerBExp : DyadicInterval precision := ⟨100902524255045880737661521605337997567289025897, 100902524255045880737661521605337999766312281450⟩
def centerBLog : DyadicInterval precision := ⟨97571805214229133777591432587733380488778036505, 97571805214229133777591432587733382687801292058⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨100902524255045880737661521605337998117044839785, scale precision, 100902524255045880737661521605337999216556467562, scale precision,
    3, 128, 3, 128, ⟨-3906688524043389811668793044358211430016150826603, -3906688524043389811668793044358211430016148729450⟩, ⟨-3906688524043389811668793044358211414090503216453, -3906688524043389811668793044358211414090501119300⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3482318024844347500022322904444928295572395253⟩
def wholeAExp : DyadicInterval precision := ⟨1454553569581723058392238696431353224119669669100, 1455183847209450510423929547351191477780877052172⟩
def wholeALog : DyadicInterval precision := ⟨1009557569928173087760872372803888449827653659813, 1009873425488092576137085252579843092274389747387⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1454553569581723058392238696431353224669425482988, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-6964636049688695000044645808889857143527710010, -6964636049688695000044645808889857143525612857⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨778301836709476402480898380936913162630577459494, 790544729755515845959006727606100906630576870318⟩
def wholeCExp : DyadicInterval precision := ⟨495414307070612103505849426500932781945535822346, 503784325648793644324816973487962263637227309380⟩
def wholeCLog : DyadicInterval precision := ⟨426620089041561576829752774202709544813893950755, 432857817090652076519115336024368113413182893951⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨495414307070612103505849426500932782495291636234, scale precision, 503784325648793644324816973487962263087471495492, scale precision,
    1, 128, 1, 128, ⟨-1581089459511031691918013455212201814882967099965, -1581089459511031691918013455212201814882965002812⟩, ⟨-1556603673418952804961796761873826323666288915885, -1556603673418952804961796761873826323666286818732⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1935394268029072592499156280915193182704500962531, 1971339279621247086412252159443639087270337031535⟩
def wholeBExp : DyadicInterval precision := ⟨98448105641421299325358424932461886397826625347, 103411762515873828440410049293994772003696575153⟩
def wholeBLog : DyadicInterval precision := ⟨95274091584696573089005939062121996861075877642, 99917110122724915545263899600679895418259003038⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨98448105641421299325358424932461886947582439235, scale precision, 103411762515873828440410049293994771453940761265, scale precision,
    3, 128, 3, 128, ⟨-3942678559242494172824504318887278182702020796214, -3942678559242494172824504318887278182702018699061⟩, ⟨-3870788536058145184998312561830386357639393380084, -3870788536058145184998312561830386357639391282931⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0307StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0308StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0308StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3640605953424817106904235978836837760282897367, 3640605953424817106904235978836837760282897368⟩
def centerAExp : DyadicInterval precision := ⟨1454238532866739696576544033316540574868034513622, 1454238532866739696576544033316540577067057769175⟩
def centerALog : DyadicInterval precision := ⟨1009399667722954236284698895375438337347134637797, 1009399667722954236284698895375438339546157893350⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454238532866739696576544033316540575417790327510, scale precision, 1454238532866739696576544033316540576517301955287, scale precision,
    0, 128, 0, 128, ⟨-7281211906849634213808471957673676073068378631, -7281211906849634213808471957673676073066281478⟩, ⟨-7281211906849634213808471957673674968065307991, -7281211906849634213808471957673674968063210838⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨773027256202645857488989064029974938467238771761, 773027256202645857488989064029974938467238771762⟩
def centerCExp : DyadicInterval precision := ⟨507433810655475431905867768624819965941247026640, 507433810655475431905867768624819968140270282193⟩
def centerCLog : DyadicInterval precision := ⟨435569270913604792573245613331299500680505265543, 435569270913604792573245613331299502879528521096⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨507433810655475431905867768624819966491002840528, scale precision, 507433810655475431905867768624819967590514468305, scale precision,
    1, 128, 1, 128, ⟨-1546054512405291714977978128059949878517875293815, -1546054512405291714977978128059949878517873196662⟩, ⟨-1546054512405291714977978128059949875351081890386, -1546054512405291714977978128059949875351079793233⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1918713256896954926527240678927099009332714066950, 1918713256896954926527240678927099009332714066951⟩
def centerBExp : DyadicInterval precision := ⟨105799514965564457679380294868447001946868439629, 105799514965564457679380294868447004145891695182⟩
def centerBLog : DyadicInterval precision := ⟨102145376885849596205267310046086104858957033041, 102145376885849596205267310046086107057980288594⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨105799514965564457679380294868447002496624253517, scale precision, 105799514965564457679380294868447003596135881294, scale precision,
    3, 128, 3, 128, ⟨-3837426513793909853054481357854198026259689159864, -3837426513793909853054481357854198026259687062711⟩, ⟨-3837426513793909853054481357854198011071169205084, -3837426513793909853054481357854198011071167107931⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3482318024844347500022322904444928295572395252, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1454553569581723058392238696431353226318692924653⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009557569928173087760872372803888452026676915366⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1454553569581723058392238696431353225768937110765, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-6964636049688695000044645808889856038763968154, -6964636049688695000044645808889856038761871001⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨766951085873784580849996981851196430098060948879, 779122474801543110738677294130326175942034954140⟩
def wholeCExp : DyadicInterval precision := ⟨503218890010785127641299228350912440635338158160, 511670697388158399334391840273658289372977208945⟩
def wholeCLog : DyadicInterval precision := ⟨432437265563069589910261180060150586100094468882, 438710848781401039820434191310281858472400913671⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨503218890010785127641299228350912441185093972048, scale precision, 511670697388158399334391840273658288823221395057, scale precision,
    1, 128, 1, 128, ⟨-1558244949603086221477354588260652353480730061033, -1558244949603086221477354588260652353480727963880⟩, ⟨-1533902171747569161699993963702392858625837553343, -1533902171747569161699993963702392858625835456190⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1900853854446340605990425969242132023366817734084, 1936620157922318974929584999955748619086501857021⟩
def wholeBExp : DyadicInterval precision := ⟨103238426877560037156283091764691320115640409312, 108417089960500950192122432288490336403435060128⟩
def wholeBLog : DyadicInterval precision := ⟨99755219790538309462172128736144983909981075534, 104584218392348352322224546440265340895881775430⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨103238426877560037156283091764691320665396223200, scale precision, 108417089960500950192122432288490335853679246240, scale precision,
    3, 128, 3, 128, ⟨-3873240315844637949859169999911497245955659404220, -3873240315844637949859169999911497245955657307067⟩, ⟨-3801707708892681211980851938484264039322729044294, -3801707708892681211980851938484264039322726947141⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0308StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0309StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0309StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3640605953424817106904235978836837760282897367, 3640605953424817106904235978836837760282897368⟩
def centerAExp : DyadicInterval precision := ⟨1454238532866739696576544033316540574868034513622, 1454238532866739696576544033316540577067057769175⟩
def centerALog : DyadicInterval precision := ⟨1009399667722954236284698895375438337347134637797, 1009399667722954236284698895375438339546157893350⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454238532866739696576544033316540575417790327510, scale precision, 1454238532866739696576544033316540576517301955287, scale precision,
    0, 128, 0, 128, ⟨-7281211906849634213808471957673676073068378631, -7281211906849634213808471957673676073066281478⟩, ⟨-7281211906849634213808471957673674968065307991, -7281211906849634213808471957673674968063210838⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨761300457364896806672613795289074367766581852326, 761300457364896806672613795289074367766581852327⟩
def centerCExp : DyadicInterval precision := ⟨515642596366683462829752023752910470450488445049, 515642596366683462829752023752910472649511700602⟩
def centerCLog : DyadicInterval precision := ⟨441649822767951848475464577113426108130726263485, 441649822767951848475464577113426110329749519038⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨515642596366683462829752023752910471000244258937, scale precision, 515642596366683462829752023752910472099755886714, scale precision,
    1, 128, 1, 128, ⟨-1522600914729793613345227590578148737091354530008, -1522600914729793613345227590578148737091352432855⟩, ⟨-1522600914729793613345227590578148733974974976450, -1522600914729793613345227590578148733974972879297⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1883651337198952374223349566458663388826991887981, 1883651337198952374223349566458663388826991887982⟩
def centerBExp : DyadicInterval precision := ⟨110999601689756788207614950979350338189246132795, 110999601689756788207614950979350340388269388348⟩
def centerBLog : DyadicInterval precision := ⟨106986409067635388097916259732278124404168562295, 106986409067635388097916259732278126603191817848⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨110999601689756788207614950979350338739001946683, scale precision, 110999601689756788207614950979350339838513574460, scale precision,
    3, 128, 3, 128, ⟨-3767302674397904748446699132917326784892470457806, -3767302674397904748446699132917326784892468360653⟩, ⟨-3767302674397904748446699132917326770415499191262, -3767302674397904748446699132917326770415497094109⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3482318024844347500022322904444928295572395252, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1454553569581723058392238696431353226318692924653⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009557569928173087760872372803888452026676915366⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1454553569581723058392238696431353225768937110765, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-6964636049688695000044645808889856038763968154, -6964636049688695000044645808889856038761871001⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨755260746152291163860170870995844609651218718819, 767358973211500545538712928359387946918017972498⟩
def wholeCExp : DyadicInterval precision := ⟨511385174940146311547669422936068774848217052353, 519922082504956804614508079898252110202736646237⟩
def wholeCLog : DyadicInterval precision := ⟨438499350924704734769794268858068550995454129608, 444809792993547236939148976338631927851381387100⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨511385174940146311547669422936068775397972866241, scale precision, 519922082504956804614508079898252109652980832349, scale precision,
    1, 128, 1, 128, ⟨-1534717946423001091077425856718775895407199126349, -1534717946423001091077425856718775895407197029196⟩, ⟨-1510521492304582327720341741991689217757074191900, -1510521492304582327720341741991689217757072094747⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1865889096222728188412355876142391027903805484195, 1901463634123536824162919442570279331410929518190⟩
def wholeBExp : DyadicInterval precision := ⟨108326658364775654627891049025127641912623265182, 113730708727298394244534889706248047615840846218⟩
def wholeBLog : DyadicInterval precision := ⟨104500029491594320902401731788442630742899787739, 109522531201747066994668216297727469927717394027⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨108326658364775654627891049025127642462379079070, scale precision, 113730708727298394244534889706248047066085032330, scale precision,
    3, 128, 3, 128, ⟨-3802927268247073648325838885140558670238954217261, -3802927268247073648325838885140558670238952120108⟩, ⟨-3731778192445456376824711752284782048742949964637, -3731778192445456376824711752284782048742947867484⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0309StableWitnesses

end


