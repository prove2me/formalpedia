-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0178StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0178StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:41:37.630267+00:00
-- url     : https://prove2.me/theorems/3a4e0db3-d0b3-4443-945f-ef5d90e3f41f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0178StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0179StableWitnesses, GeneralCK.Certificates.E8TAxisProd01…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0178StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0179StableWitnesses, GeneralCK.Certificates.E8TAxisProd0180StableWitnesses, GeneralCK.Certificates.E8TAxisProd0181StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0178StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0179StableWitnesses, GeneralCK.Certificates.E8TAxisProd0180StableWitnesses, GeneralCK.Certificates.E8TAxisProd0181StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0178StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0179StableWitnesses, GeneralCK.Certificates.E8TAxisProd0180StableWitnesses, GeneralCK.Certificates.E8TAxisProd0181StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0178StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0179StableWitnesses, GeneralCK/Certificates/E8TAxisProd0180StableWitnesses, GeneralCK/Certificates/E8TAxisProd0181StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0178StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0178StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨317065270755355282202997681696928277565512072744, 317065270755355282202997681696928277565512072745⟩
def centerCExp : DyadicInterval precision := ⟨947029251425728432434882935138905507314487525081, 947029251425728432434882935138905509513510780634⟩
def centerCLog : DyadicInterval precision := ⟨730096863944862566735825393324281300164269078371, 730096863944862566735825393324281302363292333924⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨947029251425728432434882935138905507864243338969, scale precision, 947029251425728432434882935138905508963754966746, scale precision,
    0, 128, 0, 128, ⟨-634130541510710564405995363393856555979435125354, -634130541510710564405995363393856555979433028201⟩, ⟨-634130541510710564405995363393856554282615262777, -634130541510710564405995363393856554282613165624⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨665332069838523774458374403334431477573278680816, 665332069838523774458374403334431477573278680817⟩
def centerBExp : DyadicInterval precision := ⟨588009058598433817213696549564095295848345414379, 588009058598433817213696549564095298047368669932⟩
def centerBLog : DyadicInterval precision := ⟨494187273274007061243092561185882271821086404499, 494187273274007061243092561185882274020109660052⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨588009058598433817213696549564095296398101228267, scale precision, 588009058598433817213696549564095297497612856044, scale precision,
    1, 128, 1, 128, ⟨-1330664139677047548916748806668862956512981274587, -1330664139677047548916748806668862956512979177434⟩, ⟨-1330664139677047548916748806668862953780135545831, -1330664139677047548916748806668862953780133448678⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨308402344933586987341878295350818749064874893139, 325752084660906962361547582823826438291185354524⟩
def wholeCExp : DyadicInterval precision := ⟨935838073098731428091206743465742973812004580356, 958322931087011801974061944595498988366705580372⟩
def wholeCLog : DyadicInterval precision := ⟨723290207512910948896569197677397721045942770011, 736933875662125097118239462317175086821229006121⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨935838073098731428091206743465742974361760394244, scale precision, 958322931087011801974061944595498987816949766484, scale precision,
    0, 128, 0, 128, ⟨-651504169321813924723095165647652877440927361662, -651504169321813924723095165647652877440925264509⟩, ⟨-616804689867173974683756590701637497291339276427, -616804689867173974683756590701637497291337179274⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨645678358225023297820972244365664480182160096607, 685181525156330141608904861608166484527615001143⟩
def wholeBExp : DyadicInterval precision := ⟨572251887168408786560163659583873231882244810649, 604038286356258000927807414446764987404552105521⟩
def wholeBLog : DyadicInterval precision := ⟨482907451584251491633720310604569713858790173454, 505573213941754560064922276940770860042027387539⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨572251887168408786560163659583873232432000624537, scale precision, 604038286356258000927807414446764986854796291633, scale precision,
    1, 128, 1, 128, ⟨-1370363050312660283217809723216332970459278883899, -1370363050312660283217809723216332970459276786746⟩, ⟨-1291356716450046595641944488731328959034158832753, -1291356716450046595641944488731328959034156735600⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0178StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0179StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0179StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨300426418305483197906266584742714344045151064362, 300426418305483197906266584742714344045151064363⟩
def centerCExp : DyadicInterval precision := ⟨968840030346013441168229531646548358874485901872, 968840030346013441168229531646548361073509157425⟩
def centerCLog : DyadicInterval precision := ⟨743272125169354209900142554196799700759673679881, 743272125169354209900142554196799702958696935434⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨968840030346013441168229531646548359424241715760, scale precision, 968840030346013441168229531646548360523753343537, scale precision,
    0, 128, 0, 128, ⟨-600852836610966395812533169485428688919613483403, -600852836610966395812533169485428688919611386250⟩, ⟨-600852836610966395812533169485428687260992871199, -600852836610966395812533169485428687260990774046⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨626974631422489401031446693986806754408781094068, 626974631422489401031446693986806754408781094069⟩
def centerBExp : DyadicInterval precision := ⟨619698334477132256161093139379644811593806165451, 619698334477132256161093139379644813792829421004⟩
def centerBLog : DyadicInterval precision := ⟨516611907156562443852977127317132592560733898758, 516611907156562443852977127317132594759757154311⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨619698334477132256161093139379644812143561979339, scale precision, 619698334477132256161093139379644813243073607116, scale precision,
    1, 128, 1, 128, ⟨-1253949262844978802062893387973613510114111859534, -1253949262844978802062893387973613510114109762381⟩, ⟨-1253949262844978802062893387973613507521014613894, -1253949262844978802062893387973613507521012516741⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨291807541876947883091319163960599378983261660199, 309067891082506609001259954034646670914709424587⟩
def wholeCExp : DyadicInterval precision := ⟨957450516359962807439347788495256245383035583615, 980334715740349356444873263819631440328006536724⟩
def wholeCLog : DyadicInterval precision := ⟨736406868263745359049599811702686315654895224316, 750168233079204747346576826424831420899687180994⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨957450516359962807439347788495256245932791397503, scale precision, 980334715740349356444873263819631439778250722836, scale precision,
    0, 128, 0, 128, ⟨-618135782165013218002519908069293342668595404370, -618135782165013218002519908069293342668593307217⟩, ⟨-583615083753895766182638327921198757146937946880, -583615083753895766182638327921198757146935849727⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨607688683814886317233059067511751340072132397305, 646445472228829654634772553930930557688303760501⟩
def wholeBExp : DyadicInterval precision := ⟨603404522986363053747953111358900315336825611364, 636271121405582600208554333597813226297514087923⟩
def wholeBLog : DyadicInterval precision := ⟨505124717004032677652167272468249726832712529887, 528203886224715361119572776350097478502620004373⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨603404522986363053747953111358900315886581425252, scale precision, 636271121405582600208554333597813225747758274035, scale precision,
    1, 128, 1, 128, ⟨-1292890944457659309269545107861861116708168064945, -1292890944457659309269545107861861116708165967792⟩, ⟨-1215377367629772634466118135023502678881488082105, -1215377367629772634466118135023502678881485984952⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0179StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0180StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0180StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨280899692551767667843547583927589246038699602854, 280899692551767667843547583927589246038699602855⟩
def centerDExp : DyadicInterval precision := ⟨995077841509260331069900400372341799476502701210, 995077841509260331069900400372341801675525956763⟩
def centerDLog : DyadicInterval precision := ⟨758965839592652166442507205173554655681704106112, 758965839592652166442507205173554657880727361665⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨995077841509260331069900400372341800026258515098, scale precision, 995077841509260331069900400372341801125770142875, scale precision,
    0, 128, 0, 128, ⟨-561799385103535335687095167855178492884843640736, -561799385103535335687095167855178492884841543583⟩, ⟨-561799385103535335687095167855178491269956867835, -561799385103535335687095167855178491269954770682⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨284531801088671116261690214367106515920047554003, 284531801088671116261690214367106515920047554004⟩
def centerCExp : DyadicInterval precision := ⟨990144198678373059505849704146940990247456323741, 990144198678373059505849704146940992446479579294⟩
def centerCLog : DyadicInterval precision := ⟨756027698394447142854739046132397363333733225694, 756027698394447142854739046132397365532756481247⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨990144198678373059505849704146940990797212137629, scale precision, 990144198678373059505849704146940991896723765406, scale precision,
    0, 128, 0, 128, ⟨-569063602177342232523380428734213032651562833057, -569063602177342232523380428734213032651560735904⟩, ⟨-569063602177342232523380428734213031028629480111, -569063602177342232523380428734213031028627382958⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨590074263965117041413339750919118229521081277626, 590074263965117041413339750919118229521081277627⟩
def centerBExp : DyadicInterval precision := ⟨651794490942690610385050598285126714408208934725, 651794490942690610385050598285126716607232190278⟩
def centerBLog : DyadicInterval precision := ⟨538979075788888405514578938212322336986621540679, 538979075788888405514578938212322339185644796232⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨651794490942690610385050598285126714957964748613, scale precision, 651794490942690610385050598285126716057476376390, scale precision,
    1, 128, 1, 128, ⟨-1180148527930234082826679501838236460274866600395, -1180148527930234082826679501838236460274864503242⟩, ⟨-1180148527930234082826679501838236457809460607263, -1180148527930234082826679501838236457809458510110⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨272658858022120150330970042848572591083767790686, 289160022559818845156424937767397025574157886774⟩
def wholeDExp : DyadicInterval precision := ⟨983892922446469118853387927975743979589855262870, 1006363062196829127890208034234317471389852404954⟩
def wholeDLog : DyadicInterval precision := ⟨752296360822110031467471195763059030745434384007, 765664421925330452562213141131585421551189535260⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨983892922446469118853387927975743980139611076758, scale precision, 1006363062196829127890208034234317470840096591066, scale precision,
    0, 128, 0, 128, ⟨-578320045119637690312849875534794051964939244950, -578320045119637690312849875534794051964937147797⟩, ⟨-545317716044240300661940085697145181369147805567, -545317716044240300661940085697145181369145708414⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨275952890023213657918162872037315490194966272902, 293132078860916054207893698498414517389571821030⟩
def wholeCExp : DyadicInterval precision := ⟨978559399909553102312605645338368435756008675086, 1001836852022489929581002918286635592897964295331⟩
def wholeCLog : DyadicInterval precision := ⟨749105274602030926303810202237700048178051181348, 762981480182706404259605652287855780792825998204⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨978559399909553102312605645338368436305764488974, scale precision, 1001836852022489929581002918286635592348208481443, scale precision,
    0, 128, 0, 128, ⟨-586264157721832108415787396996829035600218017614, -586264157721832108415787396996829035600215920461⟩, ⟨-551905780046427315836325744074630979587937719994, -551905780046427315836325744074630979587935622841⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨571127946572204846234959112820593845869730227307, 609194754030695706146459824247361692792154380133⟩
def wholeBExp : DyadicInterval precision := ⟨634961123322410324497384430462193625948714960728, 668914672492773994045833077282685238710950463674⟩
def wholeBLog : DyadicInterval precision := ⟨527290935868512365591092192366168076347195809522, 550771255147986942070435863946541789709263579838⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨634961123322410324497384430462193626498470774616, scale precision, 668914672492773994045833077282685238161194649786, scale precision,
    1, 128, 1, 128, ⟨-1218389508061391412292919648494723386849692826192, -1218389508061391412292919648494723386849690729039⟩, ⟨-1142255893144409692469918225641187690538308269198, -1142255893144409692469918225641187690538306172045⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0180StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0181StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0181StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨264436931605239354927088662990970038376004980339, 264436931605239354927088662990970038376004980340⟩
def centerDExp : DyadicInterval precision := ⟨1017749934528406450171674159073588388727957535413, 1017749934528406450171674159073588390926980790966⟩
def centerDLog : DyadicInterval precision := ⟨772392366462306324149504069119604065357703153956, 772392366462306324149504069119604067556726409509⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1017749934528406450171674159073588389277713349301, scale precision, 1017749934528406450171674159073588390377224977078, scale precision,
    0, 128, 0, 128, ⟨-528873863210478709854177325981940077541467235064, -528873863210478709854177325981940077541465137911⟩, ⟨-528873863210478709854177325981940075962554783446, -528873863210478709854177325981940075962552686293⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨268052287277357283814821969372085474357094555644, 268052287277357283814821969372085474357094555645⟩
def centerCExp : DyadicInterval precision := ⟨1012727099452029448737505437602128351249512689804, 1012727099452029448737505437602128353448535945357⟩
def centerCLog : DyadicInterval precision := ⟨769428436559799899203756256629401221617708503587, 769428436559799899203756256629401223816731759140⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1012727099452029448737505437602128351799268503692, scale precision, 1012727099452029448737505437602128352898780131469, scale precision,
    0, 128, 0, 128, ⟨-536104574554714567629643938744170949507561861447, -536104574554714567629643938744170949507559764294⟩, ⟨-536104574554714567629643938744170947920818458283, -536104574554714567629643938744170947920816361130⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨553083487252269539879068937036435361152253551230, 553083487252269539879068937036435361152253551231⟩
def centerBExp : DyadicInterval precision := ⟨685637832470146512443133284807622944325932003652, 685637832470146512443133284807622946524955259205⟩
def centerBLog : DyadicInterval precision := ⟨562198832703649323473565574343261283615949749530, 562198832703649323473565574343261285814973005083⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨685637832470146512443133284807622944875687817540, scale precision, 685637832470146512443133284807622945975199445317, scale precision,
    1, 128, 1, 128, ⟨-1106166974504539079758137874072870723476364463627, -1106166974504539079758137874072870723476362366474⟩, ⟨-1106166974504539079758137874072870721132651838448, -1106166974504539079758137874072870721132649741295⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨256233328382592948799518632260864583083635375283, 272658858022120150330970042848572591083767790687⟩
def wholeDExp : DyadicInterval precision := ⟨1006363062196829127890208034234317469190829149401, 1029239839924196772159254586274144060399381080023⟩
def wholeDLog : DyadicInterval precision := ⟨765664421925330452562213141131585419352166279707, 779149939480909138582665574125961105420771432974⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1006363062196829127890208034234317469740584963289, scale precision, 1029239839924196772159254586274144059849625266135, scale precision,
    0, 128, 0, 128, ⟨-545317716044240300661940085697145182965925454334, -545317716044240300661940085697145182965923357181⟩, ⟨-512466656765185897599037264521729165386628657514, -512466656765185897599037264521729165386626560361⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨259512608222552546989136062823363700049786452422, 276612062758662568906369624396592009937292335739⟩
def wholeCExp : DyadicInterval precision := ⟨1000933553987258952345939520956286572862725412563, 1024631424062743262023069730778334654332110032394⟩
def wholeCLog : DyadicInterval precision := ⟨762445454105232810722635421847765873676358796030, 776443337496203877273105028517518165493353529212⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1000933553987258952345939520956286573412481226451, scale precision, 1024631424062743262023069730778334653782354218506, scale precision,
    0, 128, 0, 128, ⟨-553224125517325137812739248793184020677305360063, -553224125517325137812739248793184020677303262910⟩, ⟨-519025216445105093978272125646727399315419765622, -519025216445105093978272125646727399315417668469⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨534462464943461988627643447017480232956872335843, 571867727011376782524101799745689538714186439502⟩
def wholeBExp : DyadicInterval precision := ⟨668237834944705656718489889486917622598934459722, 703333790844970445594430493989792989387989694238⟩
def wholeBLog : DyadicInterval precision := ⟨550306859363594067466694575029638275161843882401, 574194643415014070803989257396184405588225222324⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨668237834944705656718489889486917623148690273610, scale precision, 703333790844970445594430493989792988838233880350, scale precision,
    1, 128, 1, 128, ⟨-1143735454022753565048203599491379078630743772736, -1143735454022753565048203599491379078630741675583⟩, ⟨-1068924929886923977255286894034960464771373446120, -1068924929886923977255286894034960464771371348967⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0181StableWitnesses

end


