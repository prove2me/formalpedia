-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0089StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0089StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:47:00.131706+00:00
-- url     : https://prove2.me/theorems/8fd88d5b-848a-4588-b829-27586e569050
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0089StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0090StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0089StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0090StableWitnesses, GeneralCK.Certificates.E8TAxisProd0091StableWitnesses, GeneralCK.Certificates.E8TAxisProd0092StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0089StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0090StableWitnesses, GeneralCK.Certificates.E8TAxisProd0091StableWitnesses, GeneralCK.Certificates.E8TAxisProd0092StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0089StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0090StableWitnesses, GeneralCK.Certificates.E8TAxisProd0091StableWitnesses, GeneralCK.Certificates.E8TAxisProd0092StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0089StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0090StableWitnesses, GeneralCK/Certificates/E8TAxisProd0091StableWitnesses, GeneralCK/Certificates/E8TAxisProd0092StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0089StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0089StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2216017656540843594568486214625237657012954244, 2216017656540843594568486214625237657012954245⟩
def centerAExp : DyadicInterval precision := ⟨1457076315351450948047082186788007224970773813488, 1457076315351450948047082186788007227169797069041⟩
def centerALog : DyadicInterval precision := ⟨1010821401672838003372446069258059721789517968263, 1010821401672838003372446069258059723988541223816⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457076315351450948047082186788007225520529627376, scale precision, 1457076315351450948047082186788007226620041255153, scale precision,
    0, 128, 0, 128, ⟨-4432035313081687189136972429250475865452447731, -4432035313081687189136972429250475865450350578⟩, ⟨-4432035313081687189136972429250474762601466399, -4432035313081687189136972429250474762599369246⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨138984770367679047606875056826648434719489737964, 138984770367679047606875056826648434719489737965⟩
def centerDExp : DyadicInterval precision := ⟨1208367104819141335120726173598708722736266317802, 1208367104819141335120726173598708724935289573355⟩
def centerDLog : DyadicInterval precision := ⟨880649566147303539816976282535028842882764309855, 880649566147303539816976282535028845081787565408⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1208367104819141335120726173598708723286022131690, scale precision, 1208367104819141335120726173598708724385533759467, scale precision,
    0, 128, 0, 128, ⟨-277969540735358095213750113653296870103901821126, -277969540735358095213750113653296870103899723973⟩, ⟨-277969540735358095213750113653296868774059227885, -277969540735358095213750113653296868774057130732⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨141224420811029766118891746383511158396155384357, 141224420811029766118891746383511158396155384358⟩
def centerCExp : DyadicInterval precision := ⟨1204669295883328983247532709909671176030829159546, 1204669295883328983247532709909671178229852415099⟩
def centerCLog : DyadicInterval precision := ⟨878623961013858975130079514810963561894919978548, 878623961013858975130079514810963564093943234101⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1204669295883328983247532709909671176580584973434, scale precision, 1204669295883328983247532709909671177680096601211, scale precision,
    0, 128, 0, 128, ⟨-282448841622059532237783492767022317459274132075, -282448841622059532237783492767022317459272034922⟩, ⟨-282448841622059532237783492767022316125349502509, -282448841622059532237783492767022316125347405356⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨283210594487757176013526667602050323729662947435, 283210594487757176013526667602050323729662947436⟩
def centerBExp : DyadicInterval precision := ⟨991936011069411166803861559139642269775750493909, 991936011069411166803861559139642271974773749462⟩
def centerBLog : DyadicInterval precision := ⟨757095462834379114421784003611749971972807324275, 757095462834379114421784003611749974171830579828⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨991936011069411166803861559139642270325506307797, scale precision, 991936011069411166803861559139642271425017935574, scale precision,
    0, 128, 0, 128, ⟨-566421188975514352027053335204100648269327803547, -566421188975514352027053335204100648269325706394⟩, ⟨-566421188975514352027053335204100646649326083347, -566421188975514352027053335204100646649323986194⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1457707683773513925477741956702213446679176875042⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1011137530350683182654731711817158199758569694808⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨134987245269836870215393179468011326867547174258, 142984678294030808430193174439689638732873799525⟩
def wholeDExp : DyadicInterval precision := ⟨1201770939647839765988959733979548164468536451217, 1214995512532168524628632240632930004533537374880⟩
def wholeDLog : DyadicInterval precision := ⟨877034319321159546816789449956018115998925220947, 884273498322789745939213484257675327336644869096⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1201770939647839765988959733979548165018292265105, scale precision, 1214995512532168524628632240632930003983781560992, scale precision,
    0, 128, 0, 128, ⟨-285969356588061616860386348879379278134319500540, -285969356588061616860386348879379278134317403387⟩, ⟨-269974490539673740430786358936022653073801578439, -269974490539673740430786358936022653073799481286⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨136905764311649914033194382418989884301169624464, 145545901828368143194963992409340935150072244214⟩
def wholeCExp : DyadicInterval precision := ⟨1197566200971201614847448590493226404854019178586, 1211809837277935567452580249344919283340690026031⟩
def wholeCLog : DyadicInterval precision := ⟨874725096964288106315511122625193815440630015638, 882532923854732389511070129155831048916890633008⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1197566200971201614847448590493226405403774992474, scale precision, 1211809837277935567452580249344919282790934212143, scale precision,
    0, 128, 0, 128, ⟨-291091803656736286389927984818681870971063788938, -291091803656736286389927984818681870971061691785⟩, ⟨-273811528623299828066388764837979767939308031704, -273811528623299828066388764837979767939305934551⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨274634911788900228173282176755831575657819965956, 291807541876947883091319163960599378983261660200⟩
def wholeBExp : DyadicInterval precision := ⟨980334715740349356444873263819631438128983281171, 1003645390008539717121444684128138558547454476080⟩
def wholeBLog : DyadicInterval precision := ⟨750168233079204747346576826424831418700663925441, 764054094208851028748920460534275140123929063942⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨980334715740349356444873263819631438678739095059, scale precision, 1003645390008539717121444684128138557997698662192, scale precision,
    0, 128, 0, 128, ⟨-583615083753895766182638327921198758786110791072, -583615083753895766182638327921198758786108693919⟩, ⟨-549269823577800456346564353511663150515090277892, -549269823577800456346564353511663150515088180739⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0089StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0090StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0090StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2216017656540843594568486214625237657012954244, 2216017656540843594568486214625237657012954245⟩
def centerAExp : DyadicInterval precision := ⟨1457076315351450948047082186788007224970773813488, 1457076315351450948047082186788007227169797069041⟩
def centerALog : DyadicInterval precision := ⟨1010821401672838003372446069258059721789517968263, 1010821401672838003372446069258059723988541223816⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457076315351450948047082186788007225520529627376, scale precision, 1457076315351450948047082186788007226620041255153, scale precision,
    0, 128, 0, 128, ⟨-4432035313081687189136972429250475865452447731, -4432035313081687189136972429250475865450350578⟩, ⟨-4432035313081687189136972429250474762601466399, -4432035313081687189136972429250474762599369246⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨130992033893699994791369923976531926829092122734, 130992033893699994791369923976531926829092122735⟩
def centerDExp : DyadicInterval precision := ⟨1221656411836274069288773586476386668146918568609, 1221656411836274069288773586476386670345941824162⟩
def centerDLog : DyadicInterval precision := ⟨887906164936387943905585824070712899195502313636, 887906164936387943905585824070712901394525569189⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1221656411836274069288773586476386668696674382497, scale precision, 1221656411836274069288773586476386669796186010274, scale precision,
    0, 128, 0, 128, ⟨-261984067787399989582739847953063854315873506824, -261984067787399989582739847953063854315871409671⟩, ⟨-261984067787399989582739847953063853000497081267, -261984067787399989582739847953063853000494984114⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨133229071297323034321388512152475297047331653504, 133229071297323034321388512152475297047331653505⟩
def centerCExp : DyadicInterval precision := ⟨1217922290433565160643246168323628459994973121341, 1217922290433565160643246168323628462193996376894⟩
def centerCLog : DyadicInterval precision := ⟨885870792628949986422871820571776763026145242358, 885870792628949986422871820571776765225168497911⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1217922290433565160643246168323628460544728935229, scale precision, 1217922290433565160643246168323628461644240563006, scale precision,
    0, 128, 0, 128, ⟨-266458142594646068642777024304950594754369025121, -266458142594646068642777024304950594754366927968⟩, ⟨-266458142594646068642777024304950593434959686050, -266458142594646068642777024304950593434957588897⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨266737198912660470946768476706875305753730727530, 266737198912660470946768476706875305753730727531⟩
def centerBExp : DyadicInterval precision := ⟨1014551284541630147558099749032688176354221072515, 1014551284541630147558099749032688178553244328068⟩
def centerBLog : DyadicInterval precision := ⟨770505567034289825674541491306456144898808364501, 770505567034289825674541491306456147097831620054⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1014551284541630147558099749032688176903976886403, scale precision, 1014551284541630147558099749032688178003488514180, scale precision,
    0, 128, 0, 128, ⟨-533474397825320941893536953413750612299407705790, -533474397825320941893536953413750612299405608637⟩, ⟨-533474397825320941893536953413750610715517301485, -533474397825320941893536953413750610715515204332⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1457707683773513925477741956702213446679176875042⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1011137530350683182654731711817158199758569694808⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨126999067220414009923202423697912773180597398746, 134987245269836870215393179468011326867547174259⟩
def wholeDExp : DyadicInterval precision := ⟨1214995512532168524628632240632930002334514119327, 1228350054579566692017908102915209767793957734212⟩
def wholeDLog : DyadicInterval precision := ⟨884273498322789745939213484257675325137621613543, 891547615580027951955449639520829064234092557127⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1214995512532168524628632240632930002884269933215, scale precision, 1228350054579566692017908102915209767244201920324, scale precision,
    0, 128, 0, 128, ⟨-269974490539673740430786358936022654396389215748, -269974490539673740430786358936022654396387118595⟩, ⟨-253998134440828019846404847395825545707091570879, -253998134440828019846404847395825545707089473726⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨128915415445439189432118329664264522825212837107, 137545390441555441636628142146154648698480852906⟩
def wholeCExp : DyadicInterval precision := ⟨1210749604308243818427809082022567157993830116980, 1225133003644342460199839145696267111558012947046⟩
def wholeCLog : DyadicInterval precision := ⟨881953178625379635527778655317404030592541700466, 889798619868249611915181364736472279181627648570⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1210749604308243818427809082022567158543585930868, scale precision, 1225133003644342460199839145696267111008257133158, scale precision,
    0, 128, 0, 128, ⟨-275090780883110883273256284292309298060575626339, -275090780883110883273256284292309298060573529186⟩, ⟨-257830830890878378864236659328529044994604848970, -257830830890878378864236659328529044994602751817⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨258200553286989110154695673350758442940391985071, 275293839800143582953803650951007184676925300676⟩
def wholeBExp : DyadicInterval precision := ⟨1002740797131782167909766028290205809632710661710, 1026472790926053780153287048991705120466090968078⟩
def wholeBLog : DyadicInterval precision := ⟨763517693506255177197831839603501949907518917587, 777525405310052948838380109287370064523815343871⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1002740797131782167909766028290205810182466475598, scale precision, 1026472790926053780153287048991705119916335154190, scale precision,
    0, 128, 0, 128, ⟨-550587679600287165907607301902014370155124545604, -550587679600287165907607301902014370155122448451⟩, ⟨-516401106573978220309391346701516885098037507794, -516401106573978220309391346701516885098035410641⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0090StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0091StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0091StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1582869063071984205522252427078437298396921978, 1582869063071984205522252427078437298396921979⟩
def centerAExp : DyadicInterval precision := ⟨1458339325360928401721230227698749080144113015969, 1458339325360928401721230227698749082343136271522⟩
def centerALog : DyadicInterval precision := ⟨1011453727394019217297123487654775990758863259617, 1011453727394019217297123487654775992957886515170⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458339325360928401721230227698749080693868829857, scale precision, 1458339325360928401721230227698749081793380457634, scale precision,
    0, 128, 0, 128, ⟨-3165738126143968411044504854156875147742815392, -3165738126143968411044504854156875147740718239⟩, ⟨-3165738126143968411044504854156874045846969675, -3165738126143968411044504854156874045844872522⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨138984770367679047606875056826648434719489737964, 138984770367679047606875056826648434719489737965⟩
def centerDExp : DyadicInterval precision := ⟨1208367104819141335120726173598708722736266317802, 1208367104819141335120726173598708724935289573355⟩
def centerDLog : DyadicInterval precision := ⟨880649566147303539816976282535028842882764309855, 880649566147303539816976282535028845081787565408⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1208367104819141335120726173598708723286022131690, scale precision, 1208367104819141335120726173598708724385533759467, scale precision,
    0, 128, 0, 128, ⟨-277969540735358095213750113653296870103901821126, -277969540735358095213750113653296870103899723973⟩, ⟨-277969540735358095213750113653296868774059227885, -277969540735358095213750113653296868774057130732⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨140584443725808002240415513652096979788815350158, 140584443725808002240415513652096979788815350159⟩
def centerCExp : DyadicInterval precision := ⟨1205724783499052527270521447727456007704225240092, 1205724783499052527270521447727456009903248495645⟩
def centerCLog : DyadicInterval precision := ⟨879202427907022804935258220357852799845128357546, 879202427907022804935258220357852802044151613099⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1205724783499052527270521447727456008253981053980, scale precision, 1205724783499052527270521447727456009353492681757, scale precision,
    0, 128, 0, 128, ⟨-281168887451616004480831027304193960244010207002, -281168887451616004480831027304193960244008109849⟩, ⟨-281168887451616004480831027304193958911253290786, -281168887451616004480831027304193958911251193633⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨282550180075893896747053249684719621402133017725, 282550180075893896747053249684719621402133017726⟩
def centerBExp : DyadicInterval precision := ⟨992832876221449711308312758042132442961975981959, 992832876221449711308312758042132445160999237512⟩
def centerBLog : DyadicInterval precision := ⟨757629623695766385209665641195098643898631942955, 757629623695766385209665641195098646097655198508⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨992832876221449711308312758042132443511731795847, scale precision, 992832876221449711308312758042132444611243423624, scale precision,
    0, 128, 0, 128, ⟨-565100360151787793494106499369439243613536238357, -565100360151787793494106499369439243613534141204⟩, ⟨-565100360151787793494106499369439241994997929698, -565100360151787793494106499369439241994995832545⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 1899443256066344012630337314537754309230277492⟩
def wholeAExp : DyadicInterval precision := ⟨1457707683773513925477741956702213444480153619489, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1011137530350683182654731711817158197559546439255, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1457707683773513925477741956702213445029909433377, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-3798886512132688025260674629075509169648258520, -3798886512132688025260674629075509169646161367⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨134987245269836870215393179468011326867547174258, 142984678294030808430193174439689638732873799525⟩
def wholeDExp : DyadicInterval precision := ⟨1201770939647839765988959733979548164468536451217, 1214995512532168524628632240632930004533537374880⟩
def wholeDLog : DyadicInterval precision := ⟨877034319321159546816789449956018115998925220947, 884273498322789745939213484257675327336644869096⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1201770939647839765988959733979548165018292265105, scale precision, 1214995512532168524628632240632930003983781560992, scale precision,
    0, 128, 0, 128, ⟨-285969356588061616860386348879379278134319500540, -285969356588061616860386348879379278134317403387⟩, ⟨-269974490539673740430786358936022653073801578439, -269974490539673740430786358936022653073799481286⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨136266198261734498948575488111049025967412961208, 144905500794347715182706141919846628971144367137⟩
def wholeCExp : DyadicInterval precision := ⟨1198616160495418846851243315457668777087960285927, 1212870898957361524245949366676067230239779880047⟩
def wholeCLog : DyadicInterval precision := ⟨875302071594871397998691257579190995258055460709, 883112892079848277879085868200353356990886120878⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1198616160495418846851243315457668777637716099815, scale precision, 1212870898957361524245949366676067229690024066159, scale precision,
    0, 128, 0, 128, ⟨-289811001588695430365412283839693258612620326197, -289811001588695430365412283839693258612618229044⟩, ⟨-272532396523468997897150976222098051272374748897, -272532396523468997897150976222098051272372651744⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨273976105689032250524369501682889416191129069478, 291145468170785886189725348343662532983178579944⟩
def wholeBExp : DyadicInterval precision := ⟨981223319540892445972471542215359695416784709254, 1004550631347444800692433751777440836895772111289⟩
def wholeBLog : DyadicInterval precision := ⟨750699988478042889630716549908019610395685746829, 764590682423778549323092247085816657319200433585⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨981223319540892445972471542215359695966540523142, scale precision, 1004550631347444800692433751777440836346016297401, scale precision,
    0, 128, 0, 128, ⟨-582290936341571772379450696687325066785202406445, -582290936341571772379450696687325066785200309292⟩, ⟨-547952211378064501048739003365778831582429893661, -547952211378064501048739003365778831582427796508⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0091StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0092StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0092StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1582869063071984205522252427078437298396921978, 1582869063071984205522252427078437298396921979⟩
def centerAExp : DyadicInterval precision := ⟨1458339325360928401721230227698749080144113015969, 1458339325360928401721230227698749082343136271522⟩
def centerALog : DyadicInterval precision := ⟨1011453727394019217297123487654775990758863259617, 1011453727394019217297123487654775992957886515170⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458339325360928401721230227698749080693868829857, scale precision, 1458339325360928401721230227698749081793380457634, scale precision,
    0, 128, 0, 128, ⟨-3165738126143968411044504854156875147742815392, -3165738126143968411044504854156875147740718239⟩, ⟨-3165738126143968411044504854156874045846969675, -3165738126143968411044504854156874045844872522⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨130992033893699994791369923976531926829092122734, 130992033893699994791369923976531926829092122735⟩
def centerDExp : DyadicInterval precision := ⟨1221656411836274069288773586476386668146918568609, 1221656411836274069288773586476386670345941824162⟩
def centerDLog : DyadicInterval precision := ⟨887906164936387943905585824070712899195502313636, 887906164936387943905585824070712901394525569189⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1221656411836274069288773586476386668696674382497, scale precision, 1221656411836274069288773586476386669796186010274, scale precision,
    0, 128, 0, 128, ⟨-261984067787399989582739847953063854315873506824, -261984067787399989582739847953063854315871409671⟩, ⟨-261984067787399989582739847953063853000497081267, -261984067787399989582739847953063853000494984114⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨132589845216699039761540672329426062467968218293, 132589845216699039761540672329426062467968218294⟩
def centerCExp : DyadicInterval precision := ⟨1218988137068481088150684996096673855003909138256, 1218988137068481088150684996096673857202932393809⟩
def centerCLog : DyadicInterval precision := ⟨886452046995779479753574301936443145321577794348, 886452046995779479753574301936443147520601049901⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1218988137068481088150684996096673855553664952144, scale precision, 1218988137068481088150684996096673856653176579921, scale precision,
    0, 128, 0, 128, ⟨-265179690433398079523081344658852125595065328739, -265179690433398079523081344658852125595063231586⟩, ⟨-265179690433398079523081344658852124276809641588, -265179690433398079523081344658852124276807544435⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨266079832350596388828132186888714863173277742799, 266079832350596388828132186888714863173277742800⟩
def centerBExp : DyadicInterval precision := ⟨1015464362079470632172467455987637138476640090164, 1015464362079470632172467455987637140675663345717⟩
def centerBLog : DyadicInterval precision := ⟨771044415907225337487226169673911970368649173411, 771044415907225337487226169673911972567672428964⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1015464362079470632172467455987637139026395904052, scale precision, 1015464362079470632172467455987637140125907531829, scale precision,
    0, 128, 0, 128, ⟨-532159664701192777656264373777429727137789641051, -532159664701192777656264373777429727137787543898⟩, ⟨-532159664701192777656264373777429725555323427298, -532159664701192777656264373777429725555321330145⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 1899443256066344012630337314537754309230277492⟩
def wholeAExp : DyadicInterval precision := ⟨1457707683773513925477741956702213444480153619489, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1011137530350683182654731711817158197559546439255, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1457707683773513925477741956702213445029909433377, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-3798886512132688025260674629075509169648258520, -3798886512132688025260674629075509169646161367⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨126999067220414009923202423697912773180597398746, 134987245269836870215393179468011326867547174259⟩
def wholeDExp : DyadicInterval precision := ⟨1214995512532168524628632240632930002334514119327, 1228350054579566692017908102915209767793957734212⟩
def wholeDLog : DyadicInterval precision := ⟨884273498322789745939213484257675325137621613543, 891547615580027951955449639520829064234092557127⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1214995512532168524628632240632930002884269933215, scale precision, 1228350054579566692017908102915209767244201920324, scale precision,
    0, 128, 0, 128, ⟨-269974490539673740430786358936022654396389215748, -269974490539673740430786358936022654396387118595⟩, ⟨-253998134440828019846404847395825545707091570879, -253998134440828019846404847395825545707089473726⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨128276576533857721025787388172632631798945739446, 136905764311649914033194382418989884301169624465⟩
def wholeCExp : DyadicInterval precision := ⟨1211809837277935567452580249344919281141666770478, 1226204510955732588180712779922086014561330502580⟩
def wholeCLog : DyadicInterval precision := ⟨882532923854732389511070129155831046717867377455, 890381392629473614381711917360076509590264386473⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1211809837277935567452580249344919281691422584366, scale precision, 1226204510955732588180712779922086014011574688692, scale precision,
    0, 128, 0, 128, ⟨-273811528623299828066388764837979769265372563305, -273811528623299828066388764837979769265370466152⟩, ⟨-256553153067715442051574776345265262942643737442, -256553153067715442051574776345265262942641640289⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨257544697616875877678682630457661034482241905780, 274634911788900228173282176755831575657819965957⟩
def wholeBExp : DyadicInterval precision := ⟨1003645390008539717121444684128138556348431220527, 1027394473369725711169456262584538345768076300009⟩
def wholeBLog : DyadicInterval precision := ⟨764054094208851028748920460534275137924905808389, 778066725565575372226855198307689508685521720555⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1003645390008539717121444684128138556898187034415, scale precision, 1027394473369725711169456262584538345218320486121, scale precision,
    0, 128, 0, 128, ⟨-549269823577800456346564353511663152116191683087, -549269823577800456346564353511663152116189585934⟩, ⟨-515089395233751755357365260915322068182439557231, -515089395233751755357365260915322068182437460078⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0092StableWitnesses

end


