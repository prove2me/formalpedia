-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0204StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0204StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:49:04.856931+00:00
-- url     : https://prove2.me/theorems/c6852bb5-261e-4721-9228-0a6f24edbd11
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0204StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0205StableWitnesses, GeneralCK.Certificates.E8TAxisProd02…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0204StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0205StableWitnesses, GeneralCK.Certificates.E8TAxisProd0206StableWitnesses, GeneralCK.Certificates.E8TAxisProd0207StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0204StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0205StableWitnesses, GeneralCK.Certificates.E8TAxisProd0206StableWitnesses, GeneralCK.Certificates.E8TAxisProd0207StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0204StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0205StableWitnesses, GeneralCK.Certificates.E8TAxisProd0206StableWitnesses, GeneralCK.Certificates.E8TAxisProd0207StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0204StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0205StableWitnesses, GeneralCK/Certificates/E8TAxisProd0206StableWitnesses, GeneralCK/Certificates/E8TAxisProd0207StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0204StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0204StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨949721161203312387564849132921065893757597830, 949721161203312387564849132921065893757597831⟩
def centerAExp : DyadicInterval precision := ⟨1459603428780171974367103696970164794154811336420, 1459603428780171974367103696970164796353834591973⟩
def centerALog : DyadicInterval precision := ⟨1012086326714990166522051059359330288660433386585, 1012086326714990166522051059359330290859456642138⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1459603428780171974367103696970164794704567150308, scale precision, 1459603428780171974367103696970164795804078778085, scale precision,
    0, 128, 0, 128, ⟨-1899442322406624775129698265842132337987013411, -1899442322406624775129698265842132337984916258⟩, ⟨-1899442322406624775129698265842131237045475062, -1899442322406624775129698265842131237043377909⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨315064038341855424107327819982611679513196559210, 315064038341855424107327819982611679513196559211⟩
def centerCExp : DyadicInterval precision := ⟨949626337993123806397778588008838425028622195395, 949626337993123806397778588008838427227645450948⟩
def centerCLog : DyadicInterval precision := ⟨731671932531644544969007351596136164823520449655, 731671932531644544969007351596136167022543705208⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨949626337993123806397778588008838425578378009283, scale precision, 949626337993123806397778588008838426677889637060, scale precision,
    0, 128, 0, 128, ⟨-630128076683710848214655639965223359872483823513, -630128076683710848214655639965223359872481726360⟩, ⟨-630128076683710848214655639965223358180304510483, -630128076683710848214655639965223358180302413330⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨663009815081596323194924310459735315692685213044, 663009815081596323194924310459735315692685213045⟩
def centerBExp : DyadicInterval precision := ⟨589880666296200405133412701671308644049541822383, 589880666296200405133412701671308646248565077936⟩
def centerBLog : DyadicInterval precision := ⟨495521303644924158182122142436134223951472994727, 495521303644924158182122142436134226150496250280⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨589880666296200405133412701671308644599297636271, scale precision, 589880666296200405133412701671308645698809264048, scale precision,
    1, 128, 1, 128, ⟨-1326019630163192646389848620919470632747458873079, -1326019630163192646389848620919470632747456775926⟩, ⟨-1326019630163192646389848620919470630023284076251, -1326019630163192646389848620919470630023281979098⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669124066, 1266295042977660303900587558721132456011189596⟩
def wholeAExp : DyadicInterval precision := ⟨1458971240300741788424025014233787498548709353580, 1460235890986607494244084883518378978984154367596⟩
def wholeALog : DyadicInterval precision := ⟨1011769992837296815097311935000023817181636979342, 1012402729061596953461092784027353939761000525628⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458971240300741788424025014233787499098465167468, scale precision, 1460235890986607494244084883518378978434398553708, scale precision,
    0, 128, 0, 128, ⟨-2532590085955320607801175117442265462732722054, -2532590085955320607801175117442265462730624901⟩, ⟨-1266294766337831391377608966682622963106949258, -1266294766337831391377608966682622963104852105⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨306406529456171130952351701227325511683437947574, 323745279710826766446985521470106618369709766891⟩
def wholeCExp : DyadicInterval precision := ⟨938411625610146292314081985138210582434817627778, 960943865541731091515367813263173043883997422569⟩
def wholeCLog : DyadicInterval precision := ⟨724858293078083165410598662537004364670207960208, 738515985009427417807501760964090833030536662261⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨938411625610146292314081985138210582984573441666, scale precision, 960943865541731091515367813263173043334241608681, scale precision,
    0, 128, 0, 128, ⟨-647490559421653532893971042940213237595621635502, -647490559421653532893971042940213237595619538349⟩, ⟨-612813058912342261904703402454651022530752117977, -612813058912342261904703402454651022530750020824⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨643378770163079788231508868756731049805577603092, 682835956741538807505496934441851184518523283904⟩
def wholeBExp : DyadicInterval precision := ⟨574091655821216878552110089211839164047391593176, 605942118775985779112476417271788413472438145323⟩
def wholeBLog : DyadicInterval precision := ⟨484228953634616374141842731273179490768156175898, 506919676744907847991388293288181498278652820460⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨574091655821216878552110089211839164597147407064, scale precision, 605942118775985779112476417271788412922682331435, scale precision,
    1, 128, 1, 128, ⟨-1365671913483077615010993868883702370436595953278, -1365671913483077615010993868883702370436593856125⟩, ⟨-1286757540326159576463017737513462098285173133216, -1286757540326159576463017737513462098285171036063⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0204StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0205StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0205StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨949721161203312387564849132921065893757597830, 949721161203312387564849132921065893757597831⟩
def centerAExp : DyadicInterval precision := ⟨1459603428780171974367103696970164794154811336420, 1459603428780171974367103696970164796353834591973⟩
def centerALog : DyadicInterval precision := ⟨1012086326714990166522051059359330288660433386585, 1012086326714990166522051059359330290859456642138⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1459603428780171974367103696970164794704567150308, scale precision, 1459603428780171974367103696970164795804078778085, scale precision,
    0, 128, 0, 128, ⟨-1899442322406624775129698265842132337987013411, -1899442322406624775129698265842132337984916258⟩, ⟨-1899442322406624775129698265842131237045475062, -1899442322406624775129698265842131237043377909⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨298435465575850061418406400238001510943089159635, 298435465575850061418406400238001510943089159636⟩
def centerCExp : DyadicInterval precision := ⟨971483263490538796532098524079893513274919110751, 971483263490538796532098524079893515473942366304⟩
def centerCLog : DyadicInterval precision := ⟨744860786713891993512603520293301662555029559329, 744860786713891993512603520293301664754052814882⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨971483263490538796532098524079893513824674924639, scale precision, 971483263490538796532098524079893514924186552416, scale precision,
    0, 128, 0, 128, ⟨-596870931151700122836812800476003022713233268131, -596870931151700122836812800476003022713231170978⟩, ⟨-596870931151700122836812800476003021059125467563, -596870931151700122836812800476003021059123370410⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨624696207473745038952067298761232091946443453689, 624696207473745038952067298761232091946443453690⟩
def centerBExp : DyadicInterval precision := ⟨621633520770359393705655976551381905415773385494, 621633520770359393705655976551381907614796641047⟩
def centerBLog : DyadicInterval precision := ⟨517970240744734899790806500429930699084689917796, 517970240744734899790806500429930701283713173349⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨621633520770359393705655976551381905965529199382, scale precision, 621633520770359393705655976551381907065040827159, scale precision,
    1, 128, 1, 128, ⟨-1249392414947490077904134597522464185185400337102, -1249392414947490077904134597522464185185398239949⟩, ⟨-1249392414947490077904134597522464182600375574813, -1249392414947490077904134597522464182600373477660⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669124066, 1266295042977660303900587558721132456011189596⟩
def wholeAExp : DyadicInterval precision := ⟨1458971240300741788424025014233787498548709353580, 1460235890986607494244084883518378978984154367596⟩
def wholeALog : DyadicInterval precision := ⟨1011769992837296815097311935000023817181636979342, 1012402729061596953461092784027353939761000525628⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458971240300741788424025014233787499098465167468, scale precision, 1460235890986607494244084883518378978434398553708, scale precision,
    0, 128, 0, 128, ⟨-2532590085955320607801175117442265462732722054, -2532590085955320607801175117442265462730624901⟩, ⟨-1266294766337831391377608966682622963106949258, -1266294766337831391377608966682622963104852105⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨289821708815072720468221936650414567978851753460, 307071664425993428826262081180784357445038659394⟩
def wholeCExp : DyadicInterval precision := ⟨960069605044216067758791316721619524932751404449, 983002422228797412925137426354919001783949206612⟩
def wholeCLog : DyadicInterval precision := ⟨737988433917165373290026871067955246872246107010, 751764052223558962742893770839715829786720136548⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨960069605044216067758791316721619525482507218337, scale precision, 983002422228797412925137426354919001234193392724, scale precision,
    0, 128, 0, 128, ⟨-614143328851986857652524162361568715726964586767, -614143328851986857652524162361568715726962489614⟩, ⟨-579643417630145440936443873300829135140342355811, -579643417630145440936443873300829135140340258658⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨605431645944060642830475516575250844744428501844, 644145007526174221275011166293271114455550577546⟩
def wholeBExp : DyadicInterval precision := ⟨605307084037418669909985707985390307333594685328, 638239382071719336254913965627636769293322442569⟩
def wholeBLog : DyadicInterval precision := ⟨506470693852579101420786088049142738983229813925, 529574514910709885545224575151705635688110313530⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨605307084037418669909985707985390307883350499216, scale precision, 638239382071719336254913965627636768743566628681, scale precision,
    1, 128, 1, 128, ⟨-1288290015052348442550022332586542230238476429608, -1288290015052348442550022332586542230238474332455⟩, ⟨-1210863291888121285660951033150501688229974560116, -1210863291888121285660951033150501688229972462963⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0205StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0206StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0206StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨949721161203312387564849132921065893757597830, 949721161203312387564849132921065893757597831⟩
def centerAExp : DyadicInterval precision := ⟨1459603428780171974367103696970164794154811336420, 1459603428780171974367103696970164796353834591973⟩
def centerALog : DyadicInterval precision := ⟨1012086326714990166522051059359330288660433386585, 1012086326714990166522051059359330290859456642138⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1459603428780171974367103696970164794704567150308, scale precision, 1459603428780171974367103696970164795804078778085, scale precision,
    0, 128, 0, 128, ⟨-1899442322406624775129698265842132337987013411, -1899442322406624775129698265842132337984916258⟩, ⟨-1899442322406624775129698265842131237045475062, -1899442322406624775129698265842131237043377909⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨281889891187500602225492145883405813174137005050, 281889891187500602225492145883405813174137005051⟩
def centerCExp : DyadicInterval precision := ⟨993730381583379599097308682273953379443783315800, 993730381583379599097308682273953381642806571353⟩
def centerCLog : DyadicInterval precision := ⟨758163970490706976153581311423354385165468494720, 758163970490706976153581311423354387364491750273⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨993730381583379599097308682273953379993539129688, scale precision, 993730381583379599097308682273953381093050757465, scale precision,
    0, 128, 0, 128, ⟨-563779782375001204450984291766811627156813307100, -563779782375001204450984291766811627156811209947⟩, ⟨-563779782375001204450984291766811625539736810254, -563779782375001204450984291766811625539734713101⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨587090917371123412550892872193191959850461390943, 587090917371123412550892872193191959850461390944⟩
def centerBExp : DyadicInterval precision := ⟨654460931508445860905247778988483449137674029885, 654460931508445860905247778988483451336697285438⟩
def centerBLog : DyadicInterval precision := ⟨540821955616366686180134223351156817807248893493, 540821955616366686180134223351156820006272149046⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨654460931508445860905247778988483449687429843773, scale precision, 654460931508445860905247778988483450786941471550, scale precision,
    1, 128, 1, 128, ⟨-1174181834742246825101785744386383920928604480978, -1174181834742246825101785744386383920928602383825⟩, ⟨-1174181834742246825101785744386383918473243179950, -1174181834742246825101785744386383918473241082797⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669124066, 1266295042977660303900587558721132456011189596⟩
def wholeAExp : DyadicInterval precision := ⟨1458971240300741788424025014233787498548709353580, 1460235890986607494244084883518378978984154367596⟩
def wholeALog : DyadicInterval precision := ⟨1011769992837296815097311935000023817181636979342, 1012402729061596953461092784027353939761000525628⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458971240300741788424025014233787499098465167468, scale precision, 1460235890986607494244084883518378978434398553708, scale precision,
    0, 128, 0, 128, ⟨-2532590085955320607801175117442265462732722054, -2532590085955320607801175117442265462730624901⟩, ⟨-1266294766337831391377608966682622963106949258, -1266294766337831391377608966682622963104852105⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨273317421200188951886965822796529956432845743030, 290483523917795193092868089669284608761847021739⟩
def wholeCExp : DyadicInterval precision := ⟨982112554815529200933538642394290479384834490112, 1005456521844459780778513696130758001103534370433⟩
def wholeCLog : DyadicInterval precision := ⟨751231928150900893187639013654524025954953593514, 765127458284635026651998529297265612673788156792⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨982112554815529200933538642394290479934590304000, scale precision, 1005456521844459780778513696130758000553778556545, scale precision,
    0, 128, 0, 128, ⟨-580967047835590386185736179338569218341797883012, -580967047835590386185736179338569218341795785859⟩, ⟨-546634842400377903773931645593059912066583866411, -546634842400377903773931645593059912066581769258⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨568171414034215943204650226253966784153927364517, 606183716689493157306697982937559629362813307669⟩
def wholeBExp : DyadicInterval precision := ⟨637582859714700807264550851465307623360327839830, 671626505379762610309279954216804845705411868178⟩
def wholeBLog : DyadicInterval precision := ⟨529117478292356701539439618664200609440277304226, 552630435359708772284793273908962786831313300314⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨637582859714700807264550851465307623910083653718, scale precision, 671626505379762610309279954216804845155656054290, scale precision,
    1, 128, 1, 128, ⟨-1212367433378986314613395965875119259985807434885, -1212367433378986314613395965875119259985805337732⟩, ⟨-1136342828068431886409300452507933567111552451738, -1136342828068431886409300452507933567111550354585⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0206StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0207StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0207StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨949721161203312387564849132921065893757597830, 949721161203312387564849132921065893757597831⟩
def centerAExp : DyadicInterval precision := ⟨1459603428780171974367103696970164794154811336420, 1459603428780171974367103696970164796353834591973⟩
def centerALog : DyadicInterval precision := ⟨1012086326714990166522051059359330288660433386585, 1012086326714990166522051059359330290859456642138⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1459603428780171974367103696970164794704567150308, scale precision, 1459603428780171974367103696970164795804078778085, scale precision,
    0, 128, 0, 128, ⟨-1899442322406624775129698265842132337987013411, -1899442322406624775129698265842132337984916258⟩, ⟨-1899442322406624775129698265842131237045475062, -1899442322406624775129698265842131237043377909⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨265422583803151174472145889972799573614074303170, 265422583803151174472145889972799573614074303171⟩
def centerCExp : DyadicInterval precision := ⟨1016378097227541860396043359255007668086400657818, 1016378097227541860396043359255007670285423913371⟩
def centerCLog : DyadicInterval precision := ⟨771583454053650768603597651634296496291784930023, 771583454053650768603597651634296498490808185576⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1016378097227541860396043359255007668636156471706, scale precision, 1016378097227541860396043359255007669735668099483, scale precision,
    0, 128, 0, 128, ⟨-530845167606302348944291779945599148018671434481, -530845167606302348944291779945599148018669337328⟩, ⟨-530845167606302348944291779945599146437627875353, -530845167606302348944291779945599146437625778200⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨550151891568149445393829345918788548102233537559, 550151891568149445393829345918788548102233537560⟩
def centerBExp : DyadicInterval precision := ⟨688393970539538044919175513872413720489371346528, 688393970539538044919175513872413722688394602081⟩
def centerBLog : DyadicInterval precision := ⟨564073660709798767575688932923612729824362167735, 564073660709798767575688932923612732023385423288⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨688393970539538044919175513872413721039127160416, scale precision, 688393970539538044919175513872413722138638788193, scale precision,
    1, 128, 1, 128, ⟨-1100303783136298890787658691837577097371632649410, -1100303783136298890787658691837577097371630552257⟩, ⟨-1100303783136298890787658691837577095037303597978, -1100303783136298890787658691837577095037301500825⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669124066, 1266295042977660303900587558721132456011189596⟩
def wholeAExp : DyadicInterval precision := ⟨1458971240300741788424025014233787498548709353580, 1460235890986607494244084883518378978984154367596⟩
def wholeALog : DyadicInterval precision := ⟨1011769992837296815097311935000023817181636979342, 1012402729061596953461092784027353939761000525628⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458971240300741788424025014233787499098465167468, scale precision, 1460235890986607494244084883518378978434398553708, scale precision,
    0, 128, 0, 128, ⟨-2532590085955320607801175117442265462732722054, -2532590085955320607801175117442265462730624901⟩, ⟨-1266294766337831391377608966682622963106949258, -1266294766337831391377608966682622963104852105⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨256888956081337702934193299911104684499841158149, 273976105689032250524369501682889416191129069479⟩
def wholeCExp : DyadicInterval precision := ⟨1004550631347444800692433751777440834696748855736, 1028316822792456288805504901327625679521528299792⟩
def wholeCLog : DyadicInterval precision := ⟨764590682423778549323092247085816655120177178032, 778608236908616865199884766058755225780285862419⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1004550631347444800692433751777440835246504669624, scale precision, 1028316822792456288805504901327625678971772485904, scale precision,
    0, 128, 0, 128, ⟨-547952211378064501048739003365778833182088481407, -547952211378064501048739003365778833182086384254⟩, ⟨-513777912162675405868386599822209368218339517999, -513777912162675405868386599822209368218337420846⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨531555965882942544279009677206999034689002146543, 568910159460005203037701263054547190977742742780⟩
def wholeBExp : DyadicInterval precision := ⟨670947874188470107088316443584737422088322640469, 706136811708486537592693838597541054729562969102⟩
def wholeBLog : DyadicInterval precision := ⟨552165400756668643090788745572559347418782301029, 576085766255771006117633656584879295762899640313⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨670947874188470107088316443584737422638078454357, scale precision, 706136811708486537592693838597541054179807155214, scale precision,
    1, 128, 1, 128, ⟨-1137820318920010406075402526109094383152999862728, -1137820318920010406075402526109094383152997765575⟩, ⟨-1063111931765885088558019354413998068240167731716, -1063111931765885088558019354413998068240165634563⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0207StableWitnesses

end


