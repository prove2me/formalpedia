-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0044StableWitnesses__5
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0044StableWitnesses__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:29:17.26545+00:00
-- url     : https://prove2.me/theorems/1ed9ef9e-73e6-474d-a4cf-118b62d10dcc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0044StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0045StableWitnesses, GeneralCK.Certificates.E8TAxisZero00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0044StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0045StableWitnesses, GeneralCK.Certificates.E8TAxisZero0046StableWitnesses, GeneralCK.Certificates.E8TAxisZero0047StableWitnesses, GeneralCK.Certificates.E8TAxisZero0048StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0044StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0045StableWitnesses, GeneralCK.Certificates.E8TAxisZero0046StableWitnesses, GeneralCK.Certificates.E8TAxisZero0047StableWitnesses, GeneralCK.Certificates.E8TAxisZero0048StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0044StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0045StableWitnesses, GeneralCK.Certificates.E8TAxisZero0046StableWitnesses, GeneralCK.Certificates.E8TAxisZero0047StableWitnesses, GeneralCK.Certificates.E8TAxisZero0048StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0044StableWitnesses (+4 modules: GeneralCK/Certificates/E8TAxisZero0045StableWitnesses, GeneralCK/Certificates/E8TAxisZero0046StableWitnesses, GeneralCK/Certificates/E8TAxisZero0047StableWitnesses, GeneralCK/Certificates/E8TAxisZero0048StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0044StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0044StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨364478458648618710654128585069611790600183100243, 364478458648618710654128585069611790600183100244⟩
def centerDExp : DyadicInterval precision := ⟨887534276475298848733503786031227102092850438854, 887534276475298848733503786031227104291873694407⟩
def centerDLog : DyadicInterval precision := ⟨693541818075819702070900853962455106453799173953, 693541818075819702070900853962455108652822429506⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨887534276475298848733503786031227102642606252742, scale precision, 887534276475298848733503786031227103742117880519, scale precision,
    0, 128, 0, 128, ⟨-728956917297237421308257170139223582105649493848, -728956917297237421308257170139223582105647396695⟩, ⟨-728956917297237421308257170139223580295085004280, -728956917297237421308257170139223580295082907127⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨364817490790666071429102057067511365107635660194, 364817490790666071429102057067511365107635660195⟩
def centerCExp : DyadicInterval precision := ⟨887122600089792112017098376886192724466863199341, 887122600089792112017098376886192726665886454894⟩
def centerCLog : DyadicInterval precision := ⟨693285662588347222635541845066256463955200718175, 693285662588347222635541845066256466154223973728⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨887122600089792112017098376886192725016619013229, scale precision, 887122600089792112017098376886192726116130641006, scale precision,
    0, 128, 0, 128, ⟨-729634981581332142858204114135022731120974717264, -729634981581332142858204114135022731120972620111⟩, ⟨-729634981581332142858204114135022729309570020667, -729634981581332142858204114135022729309567923514⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨781791943917130949835805859179926105732699665897, 781791943917130949835805859179926105732699665898⟩
def centerBExp : DyadicInterval precision := ⟨501383959942558930062334769432607254818767589665, 501383959942558930062334769432607257017790845218⟩
def centerBLog : DyadicInterval precision := ⟨431071673694066361011726960588669498070217055341, 431071673694066361011726960588669500269240310894⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨501383959942558930062334769432607255368523403553, scale precision, 501383959942558930062334769432607256468035031330, scale precision,
    0, 128, 0, 128, ⟨-1563583887834261899671611718359852213067902826247, -1563583887834261899671611718359852213067900729094⟩, ⟨-1563583887834261899671611718359852209862897934498, -1563583887834261899671611718359852209862895837345⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨356015818146773315735630103594046256346147492780, 372966609392870424646531471060848444542040850581⟩
def wholeDExp : DyadicInterval precision := ⟨877284626339432933560204346302551150236929118789, 897872332234039104779267097055247456527332583462⟩
def wholeDLog : DyadicInterval precision := ⟨687150831490084437187371430673459275775078265310, 699959742628865241142888209739517591976703657011⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨877284626339432933560204346302551150786684932677, scale precision, 897872332234039104779267097055247455977576769574, scale precision,
    0, 128, 0, 128, ⟨-745933218785740849293062942121696889999941751488, -745933218785740849293062942121696889999939654335⟩, ⟨-712031636293546631471260207188092511797437162463, -712031636293546631471260207188092511797435065310⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨356015818146773315735630103594046256346147492780, 373646781925249351030950326683961254976679459702⟩
def wholeCExp : DyadicInterval precision := ⟨876468442115516198200232507263586159353508440903, 897872332234039104779267097055247456527332583462⟩
def wholeCLog : DyadicInterval precision := ⟨686640711011610567336990065024320224698217460537, 699959742628865241142888209739517591976703657011⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨876468442115516198200232507263586159903264254791, scale precision, 897872332234039104779267097055247455977576769574, scale precision,
    0, 128, 0, 128, ⟨-747293563850498702061900653367922510870071835200, -747293563850498702061900653367922510870069738047⟩, ⟨-712031636293546631471260207188092511797437162463, -712031636293546631471260207188092511797435065310⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨760944660931322281521295401195740766144999036587, 802865233561216913142342731263416338063221001902⟩
def wholeBExp : DyadicInterval precision := ⟨487131610930505629454859937688780156030152787852, 515893719544159630734460663670102680599115471915⟩
def wholeBLog : DyadicInterval precision := ⟨420421118540265489243162511406115268459587697128, 441835440803700658174606167374441227252016689931⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨487131610930505629454859937688780156579908601740, scale precision, 515893719544159630734460663670102680049359658027, scale precision,
    0, 128, 0, 128, ⟨-1605730467122433826284685462526832677775831029061, -1605730467122433826284685462526832677775828931908⟩, ⟨-1521889321862644563042590802391481530732567829816, -1521889321862644563042590802391481530732565732663⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0044StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0045StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0045StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

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

def centerCAlpha : DyadicInterval precision := ⟨347915113981899398123194578678683054927111253088, 347915113981899398123194578678683054927111253089⟩
def centerCExp : DyadicInterval precision := ⟨907881027119325189179178790801918413160815465768, 907881027119325189179178790801918415359838721321⟩
def centerCLog : DyadicInterval precision := ⟨706146462283854151030126041099700614359111705283, 706146462283854151030126041099700616558134960836⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨907881027119325189179178790801918413710571279656, scale precision, 907881027119325189179178790801918414810082907433, scale precision,
    0, 128, 0, 128, ⟨-695830227963798796246389157357366110739217290858, -695830227963798796246389157357366110739215193705⟩, ⟨-695830227963798796246389157357366108969229818646, -695830227963798796246389157357366108969227721493⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨741123107965505982403043075358780307183967797121, 741123107965505982403043075358780307183967797122⟩
def centerBExp : DyadicInterval precision := ⟨530078807130477908684262538652785977507483388065, 530078807130477908684262538652785979706506643618⟩
def centerBLog : DyadicInterval precision := ⟨452282275474556058948910478740371442540816896849, 452282275474556058948910478740371444739840152402⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨530078807130477908684262538652785978057239201953, scale precision, 530078807130477908684262538652785979156750829730, scale precision,
    0, 128, 0, 128, ⟨-1482246215931011964806086150717560615883690548318, -1482246215931011964806086150717560615883688451165⟩, ⟨-1482246215931011964806086150717560612852182737320, -1482246215931011964806086150717560612852180640167⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

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

def wholeCAlpha : DyadicInterval precision := ⟨339164617338553850423871699333891257707773909588, 356691905071146287929656593976527943665705888940⟩
def wholeCExp : DyadicInterval precision := ⟨897042009503459323947563467667192976019023874306, 918817951079152880960489128094785338008821185250⟩
def wholeCLog : DyadicInterval precision := ⟨699445313110822652797813327213962720802298964653, 712877141250487397629906767735900639146197088161⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨897042009503459323947563467667192976568779688194, scale precision, 918817951079152880960489128094785337459065371362, scale precision,
    0, 128, 0, 128, ⟨-713383810142292575859313187953055888227100000097, -713383810142292575859313187953055888227097902944⟩, ⟨-678329234677107700847743398667782514541089437367, -678329234677107700847743398667782514541087340214⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨720704196505286588019868846031388543413144411183, 761758005536359898319332737195518341687286453511⟩
def wholeBExp : DyadicInterval precision := ⟨515319835893299332300907623465546830292466283411, 545099343949433536476932882034095507793198241798⟩
def wholeBLog : DyadicInterval precision := ⟨441411219301797065124766232562135554551420677661, 463263589275079984718213348503670523103949503359⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨515319835893299332300907623465546830842222097299, scale precision, 545099343949433536476932882034095507243442427910, scale precision,
    0, 128, 0, 128, ⟨-1523516011072719796638665474391036684933739673986, -1523516011072719796638665474391036684933737576833⟩, ⟨-1441408393010573176039737692062777085352303466357, -1441408393010573176039737692062777085352301369204⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0045StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0046StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0046StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

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

def centerCAlpha : DyadicInterval precision := ⟨331109982522623167416964697141634972790463510855, 331109982522623167416964697141634972790463510856⟩
def centerCExp : DyadicInterval precision := ⟨929001559704194798821483186381148491897814227485, 929001559704194798821483186381148494096837483038⟩
def centerCLog : DyadicInterval precision := ⟨719116477295201222508738268550921233794607045529, 719116477295201222508738268550921235993630301082⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨929001559704194798821483186381148492447570041373, scale precision, 929001559704194798821483186381148493547081669150, scale precision,
    0, 128, 0, 128, ⟨-662219965045246334833929394283269946445801776620, -662219965045246334833929394283269946445799679467⟩, ⟨-662219965045246334833929394283269944716054363955, -662219965045246334833929394283269944716052266802⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨701284575112527128138461301098180738988902748940, 701284575112527128138461301098180738988902748941⟩
def centerBExp : DyadicInterval precision := ⟨559779495888078522276812949693001262470705076824, 559779495888078522276812949693001264669728332377⟩
def centerBLog : DyadicInterval precision := ⟨473916910541112310866287832301835709473914633100, 473916910541112310866287832301835711672937888653⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨559779495888078522276812949693001263020460890712, scale precision, 559779495888078522276812949693001264119972518489, scale precision,
    0, 128, 0, 128, ⟨-1402569150225054256276922602196361479413137829637, -1402569150225054256276922602196361479413135732484⟩, ⟨-1402569150225054256276922602196361476542475263279, -1402569150225054256276922602196361476542473166126⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

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

def wholeCAlpha : DyadicInterval precision := ⟨322408132378444526209018649139695484921606350582, 339836814519446808266072208879269812676505942048⟩
def wholeCExp : DyadicInterval precision := ⟨917973144834696536071405984720458804174720225603, 940130328208408204655831711119657711878645153902⟩
def wholeCLog : DyadicInterval precision := ⟨712358343325056846011863535961593443757137395038, 725904575743015811666185701912516251881166002297⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨917973144834696536071405984720458804724476039491, scale precision, 940130328208408204655831711119657711328889340014, scale precision,
    0, 128, 0, 128, ⟨-679673629038893616532144417758539626228277123843, -679673629038893616532144417758539626228275026690⟩, ⟨-644816264756889052418037298279390968988577963593, -644816264756889052418037298279390968988575866440⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨681273787334305856660267375789750483251878863978, 721500933786891363258516424855352478148115322625⟩
def wholeBExp : DyadicInterval precision := ⟨544505346261898258134883714993416963978775067950, 575320238374764109725867322323760760159379433455⟩
def wholeBLog : DyadicInterval precision := ⟨462830888843418286505400456946458966103317278391, 485110777021293716605136538083068283882442095112⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨544505346261898258134883714993416964528530881838, scale precision, 575320238374764109725867322323760759609623619567, scale precision,
    0, 128, 0, 128, ⟨-1443001867573782726517032849710704957771826061531, -1443001867573782726517032849710704957771823964378⟩, ⟨-1362547574668611713320534751579500965107199141503, -1362547574668611713320534751579500965107197044350⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0046StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0047StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0047StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨314063896595388511688731668307850747220145675387, 314063896595388511688731668307850747220145675388⟩
def centerDExp : DyadicInterval precision := ⟨950926933437474332245963667891130159890397626751, 950926933437474332245963667891130162089420882304⟩
def centerDLog : DyadicInterval precision := ⟨732460073978448216291062163497299207879791564564, 732460073978448216291062163497299210078814820117⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨950926933437474332245963667891130160440153440639, scale precision, 950926933437474332245963667891130161539665068416, scale precision,
    0, 128, 0, 128, ⟨-628127793190777023377463336615701495285224847764, -628127793190777023377463336615701495285222750611⟩, ⟨-628127793190777023377463336615701493595359950940, -628127793190777023377463336615701493595357853787⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨314397242134590218325088087467422076356226119954, 314397242134590218325088087467422076356226119955⟩
def centerCExp : DyadicInterval precision := ⟨950493249403931478792492530656457401907922158490, 950493249403931478792492530656457404106945414043⟩
def centerCLog : DyadicInterval precision := ⟨732197315150415128172888168055822346999131260552, 732197315150415128172888168055822349198154516105⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨950493249403931478792492530656457402457677972378, scale precision, 950493249403931478792492530656457403557189600155, scale precision,
    0, 128, 0, 128, ⟨-628794484269180436650176174934844153557771256428, -628794484269180436650176174934844153557769159275⟩, ⟨-628794484269180436650176174934844151867135320541, -628794484269180436650176174934844151867133223388⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨662236330683274623589955049087650803598765686211, 662236330683274623589955049087650803598765686212⟩
def centerBExp : DyadicInterval precision := ⟨590505373157246669609870666336405916679286296531, 590505373157246669609870666336405918878309552084⟩
def centerBLog : DyadicInterval precision := ⟨495966306561992773809056193212456869659382522288, 495966306561992773809056193212456871858405777841⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨590505373157246669609870666336405917229042110419, scale precision, 590505373157246669609870666336405918328553738196, scale precision,
    0, 128, 0, 128, ⟨-1324472661366549247179910098175301608558178841258, -1324472661366549247179910098175301608558176744105⟩, ⟨-1324472661366549247179910098175301605836886000739, -1324472661366549247179910098175301605836883903586⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨305741530935075953839244385929164159203164552709, 322408132378444526209018649139695484921606350583⟩
def wholeDExp : DyadicInterval precision := ⟨940130328208408204655831711119657709679621898349, 961818742565408613466907997915298000639465600973⟩
def wholeDLog : DyadicInterval precision := ⟨725904575743015811666185701912516249682142746744, 739043717569107002066769324458966200204494229375⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨940130328208408204655831711119657710229377712237, scale precision, 961818742565408613466907997915298000089709787085, scale precision,
    0, 128, 0, 128, ⟨-644816264756889052418037298279390970697849535889, -644816264756889052418037298279390970697847438736⟩, ⟨-611483061870151907678488771858328317570965873209, -611483061870151907678488771858328317570963776056⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨305741530935075953839244385929164159203164552709, 323076633986625420554114277919708384865414881160⟩
def wholeCExp : DyadicInterval precision := ⟨939270676413094436586014141796240664978946895696, 961818742565408613466907997915298000639465600973⟩
def wholeCLog : DyadicInterval precision := ⟨725381345108217079989914971185021320376069454424, 739043717569107002066769324458966200204494229375⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨939270676413094436586014141796240665528702709584, scale precision, 961818742565408613466907997915298000089709787085, scale precision,
    0, 128, 0, 128, ⟨-646153267973250841108228555839416770586248788170, -646153267973250841108228555839416770586246691017⟩, ⟨-611483061870151907678488771858328317570965873209, -611483061870151907678488771858328317570963776056⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨642612824345374600027155532461264648836387535057, 682054717970188532116141867701296260795220172348⟩
def wholeBExp : DyadicInterval precision := ⟨574705739964270496948184990299961286958367557352, 606577577732496925025204106451473991694560266102⟩
def wholeBLog : DyadicInterval precision := ⟨484669783164337729427336721435496904112498574707, 507368821541917246832108630759351839188774810063⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨574705739964270496948184990299961287508123371240, scale precision, 606577577732496925025204106451473991144804452214, scale precision,
    0, 128, 0, 128, ⟨-1364109435940377064232283735402592522988494285835, -1364109435940377064232283735402592522988492188682⟩, ⟨-1285225648690749200054311064922529296348182115178, -1285225648690749200054311064922529296348180018025⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0047StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0048StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0048StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨297440437897247181273022509268442947544064301498, 297440437897247181273022509268442947544064301499⟩
def centerDExp : DyadicInterval precision := ⟨972806985794329725044362385369131888111738659096, 972806985794329725044362385369131890310761914649⟩
def centerDLog : DyadicInterval precision := ⟨745655734605380757184922339086747309072128874695, 745655734605380757184922339086747311271152130248⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨972806985794329725044362385369131888661494472984, scale precision, 972806985794329725044362385369131889761006100761, scale precision,
    0, 128, 0, 128, ⟨-594880875794494362546045018536885895914058159347, -594880875794494362546045018536885895914056062194⟩, ⟨-594880875794494362546045018536885894262201143797, -594880875794494362546045018536885894262199046644⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨297772080655470080886655242884286810656065954419, 297772080655470080886655242884286810656065954420⟩
def centerCExp : DyadicInterval precision := ⟨972365588829511186945740568321555181717282345971, 972365588829511186945740568321555183916305601524⟩
def centerCLog : DyadicInterval precision := ⟨745390706221635068087184311689716868610987276159, 745390706221635068087184311689716870810010531712⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨972365588829511186945740568321555182267038159859, scale precision, 972365588829511186945740568321555183366549787636, scale precision,
    0, 128, 0, 128, ⟨-595544161310940161773310485768573622138436388308, -595544161310940161773310485768573622138434291155⟩, ⟨-595544161310940161773310485768573620485829526525, -595544161310940161773310485768573620485827429372⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨623937299947084251586086167413394990938096185160, 623937299947084251586086167413394990938096185161⟩
def centerBExp : DyadicInterval precision := ⟨622279441924972261435196078960025720695801641657, 622279441924972261435196078960025722894824897210⟩
def centerBLog : DyadicInterval precision := ⟨518423340725075877235675801320073371579926596996, 518423340725075877235675801320073373778949852549⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨622279441924972261435196078960025721245557455545, scale precision, 622279441924972261435196078960025722345069083322, scale precision,
    0, 128, 0, 128, ⟨-1247874599894168503172172334826789983167364182381, -1247874599894168503172172334826789983167362085228⟩, ⟨-1247874599894168503172172334826789980585022655414, -1247874599894168503172172334826789980585020558261⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨289160022559818845156424937767397025574157886773, 305741530935075953839244385929164159203164552710⟩
def wholeDExp : DyadicInterval precision := ⟨961818742565408613466907997915297998440442345420, 983892922446469118853387927975743981788878518423⟩
def wholeDLog : DyadicInterval precision := ⟨739043717569107002066769324458966198005470973822, 752296360822110031467471195763059032944457639560⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨961818742565408613466907997915297998990198159308, scale precision, 983892922446469118853387927975743981239122704535, scale precision,
    0, 128, 0, 128, ⟨-611483061870151907678488771858328319241694434782, -611483061870151907678488771858328319241692337629⟩, ⟨-578320045119637690312849875534794050331694399297, -578320045119637690312849875534794050331692302144⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨289160022559818845156424937767397025574157886773, 306406529456171130952351701227325511683437947575⟩
def wholeCExp : DyadicInterval precision := ⟨960943865541731091515367813263173041684974167016, 983892922446469118853387927975743981788878518423⟩
def wholeCLog : DyadicInterval precision := ⟨738515985009427417807501760964090830831513406708, 752296360822110031467471195763059032944457639560⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨960943865541731091515367813263173042234729980904, scale precision, 983892922446469118853387927975743981239122704535, scale precision,
    0, 128, 0, 128, ⟨-612813058912342261904703402454651024203001769474, -612813058912342261904703402454651024202999672321⟩, ⟨-578320045119637690312849875534794050331694399297, -578320045119637690312849875534794050331692302144⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨604679849961205198335909874377542917260664182755, 643378770163079788231508868756731049805577603093⟩
def wholeBExp : DyadicInterval precision := ⟨605942118775985779112476417271788411273414889770, 638896340227888384423138544913482996991222897769⟩
def wholeBLog : DyadicInterval precision := ⟨506919676744907847991388293288181496079629564907, 530031711888916372989286597902256519678326454894⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨605942118775985779112476417271788411823170703658, scale precision, 638896340227888384423138544913482996441467083881, scale precision,
    0, 128, 0, 128, ⟨-1286757540326159576463017737513462100937139376307, -1286757540326159576463017737513462100937137279154⟩, ⟨-1209359699922410396671819748755085833263740394493, -1209359699922410396671819748755085833263738297340⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0048StableWitnesses

end


