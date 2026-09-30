-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0164StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0164StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:40:22.849188+00:00
-- url     : https://prove2.me/theorems/88c9ddbc-5df0-4133-b532-10f652320542
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0164StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0165StableWitnesses, GeneralCK.Certificates.E8TAxisProd01…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0164StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0165StableWitnesses, GeneralCK.Certificates.E8TAxisProd0166StableWitnesses, GeneralCK.Certificates.E8TAxisProd0167StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0164StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0165StableWitnesses, GeneralCK.Certificates.E8TAxisProd0166StableWitnesses, GeneralCK.Certificates.E8TAxisProd0167StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0164StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0165StableWitnesses, GeneralCK.Certificates.E8TAxisProd0166StableWitnesses, GeneralCK.Certificates.E8TAxisProd0167StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0164StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0165StableWitnesses, GeneralCK/Certificates/E8TAxisProd0166StableWitnesses, GeneralCK/Certificates/E8TAxisProd0167StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0164StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0164StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨351287653634052115918640421955932629673342410616, 351287653634052115918640421955932629673342410617⟩
def centerCExp : DyadicInterval precision := ⟨903700655331397088320373596889310468933147440557, 903700655331397088320373596889310471132170696110⟩
def centerCLog : DyadicInterval precision := ⟨703565614392975487216357197755279877052223031998, 703565614392975487216357197755279879251246287551⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨903700655331397088320373596889310469482903254445, scale precision, 903700655331397088320373596889310470582414882222, scale precision,
    0, 128, 0, 128, ⟨-702575307268104231837280843911865260235773442549, -702575307268104231837280843911865260235771345396⟩, ⟨-702575307268104231837280843911865258457598297073, -702575307268104231837280843911865258457596199920⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨745151979234803432679121772194049066083719005680, 745151979234803432679121772194049066083719005681⟩
def centerBExp : DyadicInterval precision := ⟨527164348688026764381517418311120294512062173774, 527164348688026764381517418311120296711085429327⟩
def centerBLog : DyadicInterval precision := ⟨450141962495834682390445217902862778277557586305, 450141962495834682390445217902862780476580841858⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨527164348688026764381517418311120295061817987662, scale precision, 527164348688026764381517418311120296161329615439, scale precision,
    1, 128, 1, 128, ⟨-1490303958469606865358243544388098133691572898142, -1490303958469606865358243544388098133691570800989⟩, ⟨-1490303958469606865358243544388098130643305221734, -1490303958469606865358243544388098130643303124581⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨342527124855344147975691026216652607152220235330, 360074740751160892894090487962528567327495184604⟩
def wholeCExp : DyadicInterval precision := ⟨892898965645121959397532364804649247711416359290, 914599775845407951141658852493733686977091910101⟩
def wholeCLog : DyadicInterval precision := ⟨696875765659682097297052894707441000419020320750, 710284909980464209864602503695014412508794783280⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨892898965645121959397532364804649248261172173178, scale precision, 914599775845407951141658852493733686427336096213, scale precision,
    0, 128, 0, 128, ⟨-720149481502321785788180975925057135554834572546, -720149481502321785788180975925057135554832475393⟩, ⟨-685054249710688295951382052433305213425949042693, -685054249710688295951382052433305213425946945540⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨724691129966073447455472889180408340633634944757, 765829836543995576408455012925101753097866819758⟩
def wholeBExp : DyadicInterval precision := ⟨512456397221692565833276317058782590818307423562, 542133412340276077046867046612134316595239631280⟩
def wholeBLog : DyadicInterval precision := ⟨439292690018400355333875668480905793431914294656, 461101764055869272767539320246624534387418350691⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨512456397221692565833276317058782591368063237450, scale precision, 542133412340276077046867046612134316045483817392, scale precision,
    1, 128, 1, 128, ⟨-1531659673087991152816910025850203507763612514354, -1531659673087991152816910025850203507763610417201⟩, ⟨-1449382259932146894910945778360816679785220572181, -1449382259932146894910945778360816679785218475028⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0164StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0165StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0165StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨334463462800637956082555704524588433407429939611, 334463462800637956082555704524588433407429939612⟩
def centerCExp : DyadicInterval precision := ⟨924748056519677103781825935794874859857985381903, 924748056519677103781825935794874862057008637456⟩
def centerCLog : DyadicInterval precision := ⟨716513661678138572603740466045892569491524391413, 716513661678138572603740466045892571690547646966⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨924748056519677103781825935794874860407741195791, scale precision, 924748056519677103781825935794874861507252823568, scale precision,
    0, 128, 0, 128, ⟨-668926925601275912165111409049176867683712737182, -668926925601275912165111409049176867683710640029⟩, ⟨-668926925601275912165111409049176865946009118417, -668926925601275912165111409049176865946007021264⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨705232195447749529846185115854158530882609513902, 705232195447749529846185115854158530882609513903⟩
def centerBExp : DyadicInterval precision := ⟨556763640442969877903307630244600432196176329900, 556763640442969877903307630244600434395199585453⟩
def centerBLog : DyadicInterval precision := ⟨471734646474082036318131261500638378838631284483, 471734646474082036318131261500638381037654540036⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨556763640442969877903307630244600432745932143788, scale precision, 556763640442969877903307630244600433845443771565, scale precision,
    1, 128, 1, 128, ⟨-1410464390895499059692370231708317063208326205746, -1410464390895499059692370231708317063208324108593⟩, ⟨-1410464390895499059692370231708317060322113947018, -1410464390895499059692370231708317060322111849865⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨325752084660906962361547582823826438291185354523, 343200084397114651700616511900199179081958739591⟩
def wholeCExp : DyadicInterval precision := ⟨913757894713163016505213102396506444661361950543, 935838073098731428091206743465742976011027835909⟩
def wholeCLog : DyadicInterval precision := ⟨709766990723107812917057116339658852669625555846, 723290207512910948896569197677397723244966025564⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨913757894713163016505213102396506445211117764431, scale precision, 935838073098731428091206743465742975461272022021, scale precision,
    0, 128, 0, 128, ⟨-686400168794229303401233023800398359043220394017, -686400168794229303401233023800398359043218296864⟩, ⟨-651504169321813924723095165647652875723816153587, -651504169321813924723095165647652875723814056434⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨685181525156330141608904861608166484527615001142, 725489492374379835709792374714335031090376306719⟩
def wholeBExp : DyadicInterval precision := ⟨541541442301640071515188763044860576141432421831, 572251887168408786560163659583873234081268066202⟩
def wholeBLog : DyadicInterval precision := ⟨460669902469242203068314936618513431021734615805, 482907451584251491633720310604569716057813429007⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨541541442301640071515188763044860576691188235719, scale precision, 572251887168408786560163659583873233531512252314, scale precision,
    1, 128, 1, 128, ⟨-1450978984748759671419584749428670063664424087523, -1450978984748759671419584749428670063664421990370⟩, ⟨-1370363050312660283217809723216332967651183217824, -1370363050312660283217809723216332967651181120671⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0165StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0166StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0166StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨350612832656534878273289350463466381304708053312, 350612832656534878273289350463466381304708053313⟩
def centerCExp : DyadicInterval precision := ⟨904535574446282781591831345148351510141044763667, 904535574446282781591831345148351512340068019220⟩
def centerCLog : DyadicInterval precision := ⟨704081435105482625759316233007471152229012951878, 704081435105482625759316233007471154428036207431⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨904535574446282781591831345148351510690800577555, scale precision, 904535574446282781591831345148351511790312205332, scale precision,
    0, 128, 0, 128, ⟨-701225665313069756546578700926932763497684067890, -701225665313069756546578700926932763497681970737⟩, ⟨-701225665313069756546578700926932761721150242514, -701225665313069756546578700926932761721148145361⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨744345538749972729491016259880384513359700314460, 744345538749972729491016259880384513359700314461⟩
def centerBExp : DyadicInterval precision := ⟨527746436765935547897428936876787709526135016333, 527746436765935547897428936876787711725158271886⟩
def centerBLog : DyadicInterval precision := ⟨450569685504502068992217403955098930578078341074, 450569685504502068992217403955098932777101596627⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨527746436765935547897428936876787710075890830221, scale precision, 527746436765935547897428936876787711175402457998, scale precision,
    1, 128, 1, 128, ⟨-1488691077499945458982032519760769028241854442984, -1488691077499945458982032519760769028241852345831⟩, ⟨-1488691077499945458982032519760769025196948912010, -1488691077499945458982032519760769025196946814857⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨341854318407743454016368281757269571767095249299, 359397852428554738106003131332373091015701581058⟩
def wholeCExp : DyadicInterval precision := ⟨893726433608390897173481839235218910930089182868, 915442240848377048625704906156645270766577562093⟩
def wholeCLog : DyadicInterval precision := ⟨697389328778701834923201728847279072877923752111, 710803004767554370280158921986153511291947856895⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨893726433608390897173481839235218911479844996756, scale precision, 915442240848377048625704906156645270216821748205, scale precision,
    0, 128, 0, 128, ⟨-718795704857109476212006262664746182930414234247, -718795704857109476212006262664746182930412137094⟩, ⟨-683708636815486908032736563514539142656507531431, -683708636815486908032736563514539142656505434278⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨723893093223027775688689165539107035389142841532, 765014788252282813250131160493631294323377140995⟩
def wholeBExp : DyadicInterval precision := ⟨513028288099507064210632584166089565045428719698, 542725787603106952090962746584271118317506041208⟩
def wholeBLog : DyadicInterval precision := ⟨439716051805806544821236474510476353508652650316, 461533793562037058338836676920068879500828747977⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨513028288099507064210632584166089565595184533586, scale precision, 542725787603106952090962746584271117767750227320, scale precision,
    1, 128, 1, 128, ⟨-1530029576504565626500262320987262590212885387657, -1530029576504565626500262320987262590212883290504⟩, ⟨-1447786186446055551377378331078214069297853996579, -1447786186446055551377378331078214069297851899426⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0166StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0167StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0167StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨333792469247829993892333487767773019542502506639, 333792469247829993892333487767773019542502506640⟩
def centerCExp : DyadicInterval precision := ⟨925597573118910533378610288149866562447148305419, 925597573118910533378610288149866564646171560972⟩
def centerCLog : DyadicInterval precision := ⟨717033870838926804117779693846395340464032830331, 717033870838926804117779693846395342663056085884⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨925597573118910533378610288149866562996904119307, scale precision, 925597573118910533378610288149866564096415747084, scale precision,
    0, 128, 0, 128, ⟨-667584938495659987784666975535546039953060436094, -667584938495659987784666975535546039953058338941⟩, ⟨-667584938495659987784666975535546038216951687617, -667584938495659987784666975535546038216949590464⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨704442037130256083704478031096281018516005921246, 704442037130256083704478031096281018516005921247⟩
def centerBExp : DyadicInterval precision := ⟨557365992632033024680093724134223511128068267408, 557365992632033024680093724134223513327091522961⟩
def centerBLog : DyadicInterval precision := ⟨472170767224732138379776717773032601575822775049, 472170767224732138379776717773032603774846030602⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨557365992632033024680093724134223511677824081296, scale precision, 557365992632033024680093724134223512777335709073, scale precision,
    1, 128, 1, 128, ⟨-1408884074260512167408956062192562038473559438135, -1408884074260512167408956062192562038473557340982⟩, ⟨-1408884074260512167408956062192562035590466344005, -1408884074260512167408956062192562035590464246852⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨325083004739724723125590110073889241739908452155, 342527124855344147975691026216652607152220235331⟩
def wholeCExp : DyadicInterval precision := ⟨914599775845407951141658852493733684778068654548, 936695324557495237835579476887656905665291637098⟩
def wholeCLog : DyadicInterval precision := ⟨710284909980464209864602503695014410309771527727, 723812724390392070070417718976900628291755173688⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨914599775845407951141658852493733685327824468436, scale precision, 936695324557495237835579476887656905115535823210, scale precision,
    0, 128, 0, 128, ⟨-685054249710688295951382052433305215182933995783, -685054249710688295951382052433305215182931898630⟩, ⟨-650166009479449446251180220147778482622048087847, -650166009479449446251180220147778482622045990694⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨684399360005953308971632493353419901101605430196, 724691129966073447455472889180408340633634944758⟩
def wholeBExp : DyadicInterval precision := ⟨542133412340276077046867046612134314396216375727, 572864729605507992472824279702107331893346127089⟩
def wholeBLog : DyadicInterval precision := ⟨461101764055869272767539320246624532188395095138, 483347787786686117094276560541536452153470599421⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨542133412340276077046867046612134314945972189615, scale precision, 572864729605507992472824279702107331343590313201, scale precision,
    1, 128, 1, 128, ⟨-1449382259932146894910945778360816682749321303999, -1449382259932146894910945778360816682749319206846⟩, ⟨-1368798720011906617943264986706839800800666106082, -1368798720011906617943264986706839800800664008929⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0167StableWitnesses

end


