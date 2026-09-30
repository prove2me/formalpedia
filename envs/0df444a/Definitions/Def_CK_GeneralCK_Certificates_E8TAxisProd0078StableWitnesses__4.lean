-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0078StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0078StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:15:58.160716+00:00
-- url     : https://prove2.me/theorems/b0f495ba-2083-4431-b62f-99df26a38ba7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0078StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0081StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0078StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0081StableWitnesses, GeneralCK.Certificates.E8TAxisProd0082StableWitnesses, GeneralCK.Certificates.E8TAxisProd0083StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0078StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0081StableWitnesses, GeneralCK.Certificates.E8TAxisProd0082StableWitnesses, GeneralCK.Certificates.E8TAxisProd0083StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0078StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0081StableWitnesses, GeneralCK.Certificates.E8TAxisProd0082StableWitnesses, GeneralCK.Certificates.E8TAxisProd0083StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0078StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0081StableWitnesses, GeneralCK/Certificates/E8TAxisProd0082StableWitnesses, GeneralCK/Certificates/E8TAxisProd0083StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0078StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0078StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨135147101390608945924287450807414337612810530732, 135147101390608945924287450807414337612810530733⟩
def centerCExp : DyadicInterval precision := ⟨1214729754051857514558101602849122897434984790697, 1214729754051857514558101602849122899634008046250⟩
def centerCLog : DyadicInterval precision := ⟨884128373662932491534578806499669755149999657035, 884128373662932491534578806499669757349022912588⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1214729754051857514558101602849122897984740604585, scale precision, 1214729754051857514558101602849122899084252232362, scale precision,
    0, 128, 0, 128, ⟨-270294202781217891848574901614828675887060606505, -270294202781217891848574901614828675887058509352⟩, ⟨-270294202781217891848574901614828674564183613577, -270294202781217891848574901614828674564181516424⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨268710009678593781895538666619641291235894670402, 268710009678593781895538666619641291235894670403⟩
def centerBExp : DyadicInterval precision := ⟨1011815990481221450291314665696010399365269729665, 1011815990481221450291314665696010401564292985218⟩
def centerBLog : DyadicInterval precision := ⟨768890154684483194496653352947833578580675641014, 768890154684483194496653352947833580779698896567⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1011815990481221450291314665696010399915025543553, scale precision, 1011815990481221450291314665696010401014537171330, scale precision,
    0, 128, 0, 128, ⟨-537420019357187563791077333239282583265876497615, -537420019357187563791077333239282583265874400462⟩, ⟨-537420019357187563791077333239282581677704281147, -537420019357187563791077333239282581677702183994⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨130832272587569695809414699320324921011080789363, 139464632142328242790800863371446902113522637317⟩
def wholeCExp : DyadicInterval precision := ⟨1207573867472606940117047865330000286142825871831, 1221923527186106999084992706451107776121594480779⟩
def wholeCLog : DyadicInterval precision := ⟨880215278904111554895432601471468087067223483569, 888051653976961835389995825692819351397384016853⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1207573867472606940117047865330000286692581685719, scale precision, 1221923527186106999084992706451107775571838666891, scale precision,
    0, 128, 0, 128, ⟨-278929264284656485581601726742893804892404396759, -278929264284656485581601726742893804892402299606⟩, ⟨-261664545175139391618829398640649841364618186711, -261664545175139391618829398640649841364616089558⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨260168808084051724207340356924670106199222168443, 277271358307143331511699022410631785361523651159⟩
def wholeBExp : DyadicInterval precision := ⟨1000030902333961399782025547003040621404574319551, 1023711738189858330509771486033612624930537471063⟩
def wholeBLog : DyadicInterval precision := ⟨761909615141175183101165194030151438310789443093, 775902589655979148194684620099574952915501182542⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1000030902333961399782025547003040621954330133439, scale precision, 1023711738189858330509771486033612624380781657175, scale precision,
    0, 128, 0, 128, ⟨-554542716614286663023398044821263571526492544724, -554542716614286663023398044821263571526490447571⟩, ⟨-520337616168103448414680713849340211613586726374, -520337616168103448414680713849340211613584629221⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0078StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0081StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0081StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨142504561240778065286249570742540407429177017085, 142504561240778065286249570742540407429177017086⟩
def centerCExp : DyadicInterval precision := ⟨1202560785236638556030253761019287495635952095071, 1202560785236638556030253761019287497834975350624⟩
def centerCLog : DyadicInterval precision := ⟨877467691966140448861940968474382051368384397319, 877467691966140448861940968474382053567407652872⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1202560785236638556030253761019287496185707908959, scale precision, 1202560785236638556030253761019287497285219536736, scale precision,
    0, 128, 0, 128, ⟨-285009122481556130572499141485080815526486816290, -285009122481556130572499141485080815526484719137⟩, ⟨-285009122481556130572499141485080814190223349206, -285009122481556130572499141485080814190221252053⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨284531801088671116261690214367106515920047554003, 284531801088671116261690214367106515920047554004⟩
def centerBExp : DyadicInterval precision := ⟨990144198678373059505849704146940990247456323741, 990144198678373059505849704146940992446479579294⟩
def centerBLog : DyadicInterval precision := ⟨756027698394447142854739046132397363333733225694, 756027698394447142854739046132397365532756481247⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨990144198678373059505849704146940990797212137629, scale precision, 990144198678373059505849704146940991896723765406, scale precision,
    0, 128, 0, 128, ⟨-569063602177342232523380428734213032651562833057, -569063602177342232523380428734213032651560735904⟩, ⟨-569063602177342232523380428734213031028629480111, -569063602177342232523380428734213031028627382958⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨138185076934533291384460203659823029201118705568, 146826895900187411258321839193929239531070706026⟩
def wholeCExp : DyadicInterval precision := ⟨1195468726228719232833614102862965392793557276194, 1209690199028879381733560717407416115630677305567⟩
def wholeCLog : DyadicInterval precision := ⟨873571808438861005643647858596413659277366314966, 881373656190846597166423362808244091565646919916⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1195468726228719232833614102862965393343313090082, scale precision, 1209690199028879381733560717407416115080921491679, scale precision,
    0, 128, 0, 128, ⟨-293653791800374822516643678387858479734237852586, -293653791800374822516643678387858479734235755433⟩, ⟨-276370153869066582768920407319646057738044418317, -276370153869066582768920407319646057738042321164⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨275952890023213657918162872037315490194966272902, 293132078860916054207893698498414517389571821030⟩
def wholeBExp : DyadicInterval precision := ⟨978559399909553102312605645338368435756008675086, 1001836852022489929581002918286635592897964295331⟩
def wholeBLog : DyadicInterval precision := ⟨749105274602030926303810202237700048178051181348, 762981480182706404259605652287855780792825998204⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨978559399909553102312605645338368436305764488974, scale precision, 1001836852022489929581002918286635592348208481443, scale precision,
    0, 128, 0, 128, ⟨-586264157721832108415787396996829035600218017614, -586264157721832108415787396996829035600215920461⟩, ⟨-551905780046427315836325744074630979587937719994, -551905780046427315836325744074630979587935622841⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0081StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0082StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0082StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨134507699101499508151427061126861574946767081322, 134507699101499508151427061126861574946767081323⟩
def centerCExp : DyadicInterval precision := ⟨1215793099954274904344262609476815178677317095129, 1215793099954274904344262609476815180876340350682⟩
def centerCLog : DyadicInterval precision := ⟨884708956165200405579076037799999965886746359686, 884708956165200405579076037799999968085769615239⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1215793099954274904344262609476815179227072909017, scale precision, 1215793099954274904344262609476815180326584536794, scale precision,
    0, 128, 0, 128, ⟨-269015398202999016302854122253723150554395206365, -269015398202999016302854122253723150554393109212⟩, ⟨-269015398202999016302854122253723149232675216080, -269015398202999016302854122253723149232673118927⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨268052287277357283814821969372085474357094555644, 268052287277357283814821969372085474357094555645⟩
def centerBExp : DyadicInterval precision := ⟨1012727099452029448737505437602128351249512689804, 1012727099452029448737505437602128353448535945357⟩
def centerBLog : DyadicInterval precision := ⟨769428436559799899203756256629401221617708503587, 769428436559799899203756256629401223816731759140⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1012727099452029448737505437602128351799268503692, scale precision, 1012727099452029448737505437602128352898780131469, scale precision,
    0, 128, 0, 128, ⟨-536104574554714567629643938744170949507561861447, -536104574554714567629643938744170949507559764294⟩, ⟨-536104574554714567629643938744170947920818458283, -536104574554714567629643938744170947920816361130⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨130193263189897081724696786765399350405682799253, 138824824073724312515584487072396406921145910542⟩
def wholeCExp : DyadicInterval precision := ⟨1208631620422256427272457205985983279603569067747, 1222992512801046103160458641886624347196250203029⟩
def wholeCLog : DyadicInterval precision := ⟨880794356350518998071035925612790697885980629141, 888633750746898767010626281665463029187005572081⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1208631620422256427272457205985983280153324881635, scale precision, 1222992512801046103160458641886624346646494389141, scale precision,
    0, 128, 0, 128, ⟨-277649648147448625031168974144792814507068644639, -277649648147448625031168974144792814507066547486⟩, ⟨-260386526379794163449393573530798700154396948805, -260386526379794163449393573530798700154394851652⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨259512608222552546989136062823363700049786452422, 276612062758662568906369624396592009937292335739⟩
def wholeBExp : DyadicInterval precision := ⟨1000933553987258952345939520956286572862725412563, 1024631424062743262023069730778334654332110032394⟩
def wholeBLog : DyadicInterval precision := ⟨762445454105232810722635421847765873676358796030, 776443337496203877273105028517518165493353529212⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1000933553987258952345939520956286573412481226451, scale precision, 1024631424062743262023069730778334653782354218506, scale precision,
    0, 128, 0, 128, ⟨-553224125517325137812739248793184020677305360063, -553224125517325137812739248793184020677303262910⟩, ⟨-519025216445105093978272125646727399315419765622, -519025216445105093978272125646727399315417668469⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0082StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0083StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0083StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨141864459888192171309030458957339175671333069210, 141864459888192171309030458957339175671333069211⟩
def centerCExp : DyadicInterval precision := ⟨1203614630131583506862483159968614507950826836304, 1203614630131583506862483159968614510149850091857⟩
def centerCLog : DyadicInterval precision := ⟨878045715766473051802714412251363157232521062088, 878045715766473051802714412251363159431544317641⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1203614630131583506862483159968614508500582650192, scale precision, 1203614630131583506862483159968614509600094277969, scale precision,
    0, 128, 0, 128, ⟨-283728919776384342618060917914678352010213926639, -283728919776384342618060917914678352010211829486⟩, ⟨-283728919776384342618060917914678350675120447354, -283728919776384342618060917914678350675118350201⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨283871134724759237755935091389590224620654291174, 283871134724759237755935091389590224620654291175⟩
def centerBExp : DyadicInterval precision := ⟨991039785447791464819395115190855749355765331171, 991039785447791464819395115190855751554788586724⟩
def centerBLog : DyadicInterval precision := ⟨756561487777012649114008942824216057123817013927, 756561487777012649114008942824216059322840269480⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨991039785447791464819395115190855749905521145059, scale precision, 991039785447791464819395115190855751005032772836, scale precision,
    0, 128, 0, 128, ⟨-567742269449518475511870182779180450052042997970, -567742269449518475511870182779180450052040900817⟩, ⟨-567742269449518475511870182779180448430576263883, -567742269449518475511870182779180448430574166730⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨137545390441555441636628142146154648698480852905, 146186366769016461692580822654652725928794126922⟩
def wholeCExp : DyadicInterval precision := ⟨1196517056547333167756892797013132403020692530274, 1210749604308243818427809082022567160192853372533⟩
def wholeCLog : DyadicInterval precision := ⟨874148342644455436859287811626984683775662285053, 881953178625379635527778655317404032791564956019⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1196517056547333167756892797013132403570448344162, scale precision, 1210749604308243818427809082022567159643097558645, scale precision,
    0, 128, 0, 128, ⟨-292372733538032923385161645309305452529095836933, -292372733538032923385161645309305452529093739780⟩, ⟨-275090780883110883273256284292309296733349882434, -275090780883110883273256284292309296733347785281⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨275293839800143582953803650951007184676925300675, 292469745339287832750898622949857188568070755120⟩
def wholeBExp : DyadicInterval precision := ⟨979446742750594530073246032069957400534333385552, 1002740797131782167909766028290205811831733917263⟩
def wholeBLog : DyadicInterval precision := ⟨749636661828918999346616613489288628645341720858, 763517693506255177197831839603501952106542173140⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨979446742750594530073246032069957401084089199440, scale precision, 1002740797131782167909766028290205811281978103375, scale precision,
    0, 128, 0, 128, ⟨-584939490678575665501797245899714377956472023461, -584939490678575665501797245899714377956469926308⟩, ⟨-550587679600287165907607301902014368552578754252, -550587679600287165907607301902014368552576657099⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0083StableWitnesses

end


