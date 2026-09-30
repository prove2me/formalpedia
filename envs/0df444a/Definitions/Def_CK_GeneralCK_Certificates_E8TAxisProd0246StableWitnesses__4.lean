-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0246StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0246StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T23:20:52.43744+00:00
-- url     : https://prove2.me/theorems/9aa38f2b-1f58-40d6-b7c6-97e5cbd72611
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0246StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0247StableWitnesses, GeneralCK.Certificates.E8TAxisProd02…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0246StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0247StableWitnesses, GeneralCK.Certificates.E8TAxisProd0248StableWitnesses, GeneralCK.Certificates.E8TAxisProd0249StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0246StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0247StableWitnesses, GeneralCK.Certificates.E8TAxisProd0248StableWitnesses, GeneralCK.Certificates.E8TAxisProd0249StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0246StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0247StableWitnesses, GeneralCK.Certificates.E8TAxisProd0248StableWitnesses, GeneralCK.Certificates.E8TAxisProd0249StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0246StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0247StableWitnesses, GeneralCK/Certificates/E8TAxisProd0248StableWitnesses, GeneralCK/Certificates/E8TAxisProd0249StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0246StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0246StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨864539270161105163740168296694370154034029348165, 864539270161105163740168296694370154034029348166⟩
def centerDExp : DyadicInterval precision := ⟨447705727508954974656542730347776284626226541037, 447705727508954974656542730347776286825249796590⟩
def centerDLog : DyadicInterval precision := ⟨390547930354595539952804600044570644160315185441, 390547930354595539952804600044570646359338440994⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨447705727508954974656542730347776285175982354925, scale precision, 447705727508954974656542730347776286275493982702, scale precision,
    1, 128, 1, 128, ⟨-1729078540322210327480336593388740309862696205336, -1729078540322210327480336593388740309862694108183⟩, ⟨-1729078540322210327480336593388740306273423284479, -1729078540322210327480336593388740306273421187326⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨869046853971605974657962034243862010407611894962, 869046853971605974657962034243862010407611894963⟩
def centerCExp : DyadicInterval precision := ⟨444952586968089858533015012274794682354891837480, 444952586968089858533015012274794684553915093033⟩
def centerCLog : DyadicInterval precision := ⟨388438875338815191845889800674510782470049110589, 388438875338815191845889800674510784669072366142⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨444952586968089858533015012274794682904647651368, scale precision, 444952586968089858533015012274794684004159279145, scale precision,
    1, 128, 1, 128, ⟨-1738093707943211949315924068487724022620965597545, -1738093707943211949315924068487724022620963500392⟩, ⟨-1738093707943211949315924068487724019009484079457, -1738093707943211949315924068487724019009481982304⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2204394809293916160202655485632233934359565392374, 2204394809293916160202655485632233934359565392375⟩
def centerBExp : DyadicInterval precision := ⟨71564807253294823696636485309179008352675057788, 71564807253294823696636485309179010551698313341⟩
def centerBLog : DyadicInterval precision := ⟨69867839790793296750330173306380511968036935890, 69867839790793296750330173306380514167060191443⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨71564807253294823696636485309179008902430871676, scale precision, 71564807253294823696636485309179010001942499453, scale precision,
    4, 128, 4, 128, ⟨-4408789618587832320405310971264467879946284577365, -4408789618587832320405310971264467879946282480212⟩, ⟨-4408789618587832320405310971264467857491979089293, -4408789618587832320405310971264467857491976992140⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨858384943750592238779991986336301839154815993316, 870712988176454679833831807012927217752922944019⟩
def wholeDExp : DyadicInterval precision := ⟨443939237141351316813290285207320724478560656031, 451492192509468156215846209344698069605083336703⟩
def wholeDLog : DyadicInterval precision := ⟨387661827478115861734404726101104695617766958964, 393443605556601543377574216062392477640846281111⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨443939237141351316813290285207320725028316469919, scale precision, 451492192509468156215846209344698069055327522815, scale precision,
    1, 128, 1, 128, ⟨-1741425976352909359667663614025854437315709536964, -1741425976352909359667663614025854437315707439811⟩, ⟨-1716769887501184477559983972672603676530047395724, -1716769887501184477559983972672603676530045298571⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨862664165944678037906770610371578220863353369136, 875450381097759436291800264524955588507782850625⟩
def wholeCExp : DyadicInterval precision := ⟨441070527177795794773485290264547030093107179644, 448856014129685698715715233182597972040134094004⟩
def wholeCLog : DyadicInterval precision := ⟨385459826035909576946753455995963963139356987460, 391428211655344317075084778943367369386924390451⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨441070527177795794773485290264547030642862993532, scale precision, 448856014129685698715715233182597971490378280116, scale precision,
    1, 128, 1, 128, ⟨-1750900762195518872583600529049911178837200644233, -1750900762195518872583600529049911178837198547080⟩, ⟨-1725328331889356075813541220743156439936670454527, -1725328331889356075813541220743156439936668357374⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2185930721759970506683951043565355111437476297357, 2222888007552602058058829035351166079076765041853⟩
def wholeBExp : DyadicInterval precision := ⟨69776432875530125008875027517095703772838780845, 73396093860432837040928756228195812370572654915⟩
def wholeBLog : DyadicInterval precision := ⟨68161953024217499512649629577828429703269208720, 71612598555419744477175956947252756990541041040⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨69776432875530125008875027517095704322594594733, scale precision, 73396093860432837040928756228195811820816841027, scale precision,
    4, 128, 4, 128, ⟨-4445776015105204116117658070702332169668436509622, -4445776015105204116117658070702332169668434412469⟩, ⟨-4371861443519941013367902087130710211927926630402, -4371861443519941013367902087130710211927924533249⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0246StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0247StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0247StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨852249911794452062012049136358764955095133789484, 852249911794452062012049136358764955095133789485⟩
def centerDExp : DyadicInterval precision := ⟨455298659801689467951201474539649436055069582612, 455298659801689467951201474539649438254092838165⟩
def centerDLog : DyadicInterval precision := ⟨396348806111750593903736846609666706637987139797, 396348806111750593903736846609666708837010395350⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨455298659801689467951201474539649436604825396500, scale precision, 455298659801689467951201474539649437704337024277, scale precision,
    1, 128, 1, 128, ⟨-1704499823588904124024098272717529911954976264684, -1704499823588904124024098272717529911954974167531⟩, ⟨-1704499823588904124024098272717529908425560990410, -1704499823588904124024098272717529908425558893257⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨856729257069715447970379027540490673392582822429, 856729257069715447970379027540490673392582822430⟩
def centerCExp : DyadicInterval precision := ⟨452516313293133630791930274918717209270859597600, 452516313293133630791930274918717211469882853153⟩
def centerCLog : DyadicInterval precision := ⟨394225810746311379832478263158514618977801421658, 394225810746311379832478263158514621176824677211⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨452516313293133630791930274918717209820615411488, scale precision, 452516313293133630791930274918717210920127039265, scale precision,
    1, 128, 1, 128, ⟨-1713458514139430895940758055080981348560724830297, -1713458514139430895940758055080981348560722733144⟩, ⟨-1713458514139430895940758055080981345009608556573, -1713458514139430895940758055080981345009606459420⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2168126489320482858692114673964589720131575652598, 2168126489320482858692114673964589720131575652599⟩
def centerBExp : DyadicInterval precision := ⟨75206301005411998564098369101513490005966915401, 75206301005411998564098369101513492204990170954⟩
def centerBLog : DyadicInterval precision := ⟨73335229190485241352656979447272269321864889300, 73335229190485241352656979447272271520888144853⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨75206301005411998564098369101513490555722729289, scale precision, 75206301005411998564098369101513491655234357066, scale precision,
    4, 128, 4, 128, ⟨-4336252978640965717384229347929179450946685666658, -4336252978640965717384229347929179450946683569505⟩, ⟨-4336252978640965717384229347929179429579619040887, -4336252978640965717384229347929179429579616943734⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨846134075813431409586727826645377644661771969770, 858384943750592238779991986336301839154815993317⟩
def wholeDExp : DyadicInterval precision := ⟨451492192509468156215846209344698067406060081150, 459125158042315647897421247370792079661750447941⟩
def wholeDLog : DyadicInterval precision := ⟨393443605556601543377574216062392475441823025558, 399263485746125009998379766489542017105011910291⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨451492192509468156215846209344698067955815895038, scale precision, 459125158042315647897421247370792079111994634053, scale precision,
    1, 128, 1, 128, ⟨-1716769887501184477559983972672603680089218674697, -1716769887501184477559983972672603680089216577544⟩, ⟨-1692268151626862819173455653290755287573544997795, -1692268151626862819173455653290755287573542900642⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨850386542888000117380538996831220905561473744101, 863092602976343363120049422656952885391503630223⟩
def wholeCExp : DyadicInterval precision := ⟨448592928314291104169226410237714887778579011163, 456461124398420646140519875978592761425115262146⟩
def wholeCLog : DyadicInterval precision := ⟨391226926399717280649279904416100868889618614657, 397234881176845431287963500914531380870877706681⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨448592928314291104169226410237714888328334825051, scale precision, 456461124398420646140519875978592760875359448258, scale precision,
    1, 128, 1, 128, ⟨-1726185205952686726240098845313905772574095442627, -1726185205952686726240098845313905772574093345474⟩, ⟨-1700773085776000234761077993662441809362735061449, -1700773085776000234761077993662441809362732964296⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2149722659407825392669716209602936538923481892126, 2186561480892606085181618831099001597706850345603⟩
def wholeBExp : DyadicInterval precision := ⟨73332768194793960874704589150555949099464379505, 77124410615442447286280068637069908139360973008⟩
def wholeBLog : DyadicInterval precision := ⟨71552299767181892017010150272129687465266537135, 75158329193055089667243258667663973125913219720⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨73332768194793960874704589150555949649220193393, scale precision, 77124410615442447286280068637069907589605159120, scale precision,
    4, 128, 4, 128, ⟨-4373122961785212170363237662198003206370181931495, -4373122961785212170363237662198003206370179834342⟩, ⟨-4299445318815650785339432419205873067429134528284, -4299445318815650785339432419205873067429132431131⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0247StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0248StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0248StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨889351442612263296687940979624415955523303356852, 889351442612263296687940979624415955523303356853⟩
def centerDExp : DyadicInterval precision := ⟨432759351678313928226043309926168445711221586154, 432759351678313928226043309926168447910244841707⟩
def centerDLog : DyadicInterval precision := ⟨379061432685197727184727484874290046165241739981, 379061432685197727184727484874290048364264995534⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨432759351678313928226043309926168446260977400042, scale precision, 432759351678313928226043309926168447360489027819, scale precision,
    1, 128, 1, 128, ⟨-1778702885224526593375881959248831912903226270963, -1778702885224526593375881959248831912903224173810⟩, ⟨-1778702885224526593375881959248831909189989253603, -1778702885224526593375881959248831909189987156450⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨893481129202933955529473607293960477765771384381, 893481129202933955529473607293960477765771384382⟩
def centerCExp : DyadicInterval precision := ⟨430320599559051156640363062367031650220853726695, 430320599559051156640363062367031652419876982248⟩
def centerCLog : DyadicInterval precision := ⟨377178621085118363121601848226553238553508754136, 377178621085118363121601848226553240752532009689⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨430320599559051156640363062367031650770609540583, scale precision, 430320599559051156640363062367031651870121168360, scale precision,
    1, 128, 1, 128, ⟨-1786962258405867911058947214587920957398684323634, -1786962258405867911058947214587920957398682226481⟩, ⟨-1786962258405867911058947214587920953664403311042, -1786962258405867911058947214587920953664401213889⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2276626001067324982458907817345240152779357698722, 2276626001067324982458907817345240152779357698723⟩
def centerBExp : DyadicInterval precision := ⟨64829338815296330724479711781752923409416857902, 64829338815296330724479711781752925608440113455⟩
def centerBLog : DyadicInterval precision := ⟨63432641808477751350448342652991154244958772252, 63432641808477751350448342652991156443982027805⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨64829338815296330724479711781752923959172671790, scale precision, 64829338815296330724479711781752925058684299567, scale precision,
    4, 128, 4, 128, ⟨-4553252002134649964917815634690480317952318429525, -4553252002134649964917815634690480317952316332372⟩, ⟨-4553252002134649964917815634690480293165114462525, -4553252002134649964917815634690480293165112365372⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨883118980747789020882084464779538700246874405266, 895603670620266646532188138393358736598408063638⟩
def wholeDExp : DyadicInterval precision := ⟨429072502312048699316189665111836193246265566837, 436466074505762269046786189274013978256547303798⟩
def wholeDLog : DyadicInterval precision := ⟨376214102269711135965559641860188009991436493933, 381918529993447746751868483809797876669420495502⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨429072502312048699316189665111836193796021380725, scale precision, 436466074505762269046786189274013977706791489910, scale precision,
    1, 128, 1, 128, ⟨-1791207341240533293064376276786717475069388868982, -1791207341240533293064376276786717475069386771829⟩, ⟨-1766237961495578041764168929559077398652898830676, -1766237961495578041764168929559077398652896733523⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨887018735049816900191077495365469056175113535616, 899964752258515571135825607469572528313135710726⟩
def wholeCExp : DyadicInterval precision := ⟨426519446490657618285420856149314858139836058465, 434143016219362010869024635375220975041976193006⟩
def wholeCLog : DyadicInterval precision := ⟨374239137707329141134551415843151014207765969638, 380128598083406369020701180328906596411189651194⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨426519446490657618285420856149314858689591872353, scale precision, 434143016219362010869024635375220974492220379118, scale precision,
    1, 128, 1, 128, ⟨-1799929504517031142271651214939145058510052984001, -1799929504517031142271651214939145058510050886848⟩, ⟨-1774037470099633800382154990730938110499526871343, -1774037470099633800382154990730938110499524774190⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2258054091262509235013941793937008873212629311583, 2295223201132113101982491751247661809681992464764⟩
def wholeBExp : DyadicInterval precision := ⟨63200285534184802563593463211844643735610989187, 66498081198861217224540281200084957785488879054⟩
def wholeBLog : DyadicInterval precision := ⟨61871947877798627547733339720382298238688343990, 65029633236277992481662786342700941722435376657⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨63200285534184802563593463211844644285366803075, scale precision, 66498081198861217224540281200084957235733065166, scale precision,
    4, 128, 4, 128, ⟨-4590446402264226203964983502495323632077045979948, -4590446402264226203964983502495323632077043882795⟩, ⟨-4516108182525018470027883587874017734342670104565, -4516108182525018470027883587874017734342668007412⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0248StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0249StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0249StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨876906193579724784222253173988686333103956064712, 876906193579724784222253173988686333103956064713⟩
def centerDExp : DyadicInterval precision := ⟨440192694720248252032582341812381160071591754974, 440192694720248252032582341812381162270615010527⟩
def centerDLog : DyadicInterval precision := ⟨384785344583078380142629370287541215891742295997, 384785344583078380142629370287541218090765551550⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨440192694720248252032582341812381160621347568862, scale precision, 440192694720248252032582341812381161720859196639, scale precision,
    1, 128, 1, 128, ⟨-1753812387159449568444506347977372668033179775489, -1753812387159449568444506347977372668033177678336⟩, ⟨-1753812387159449568444506347977372664382646580517, -1753812387159449568444506347977372664382644483364⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨881009835396222819242282487352402857224849181973, 881009835396222819242282487352402857224849181974⟩
def centerCExp : DyadicInterval precision := ⟨437727653905716594913428547200825003642779767233, 437727653905716594913428547200825005841803022786⟩
def centerCLog : DyadicInterval precision := ⟨382889667611540996559563260486245162071671742740, 382889667611540996559563260486245164270694998293⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨437727653905716594913428547200825004192535581121, scale precision, 437727653905716594913428547200825005292047208898, scale precision,
    1, 128, 1, 128, ⟨-1762019670792445638484564974704805716285244905162, -1762019670792445638484564974704805716285242808009⟩, ⟨-1762019670792445638484564974704805712614153919884, -1762019670792445638484564974704805712614151822731⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2240142016831320939368481597391131719368743573604, 2240142016831320939368481597391131719368743573605⟩
def centerBExp : DyadicInterval precision := ⟨68148215330776284178585011382143623568393434649, 68148215330776284178585011382143625767416690202⟩
def centerBLog : DyadicInterval precision := ⟨66607102408980847353409329106188894184480948390, 66607102408980847353409329106188896383504203943⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨68148215330776284178585011382143624118149248537, scale precision, 68148215330776284178585011382143625217660876314, scale precision,
    4, 128, 4, 128, ⟨-4480284033662641878736963194782263450527511136678, -4480284033662641878736963194782263450527509039525⟩, ⟨-4480284033662641878736963194782263426947465254908, -4480284033662641878736963194782263426947463157755⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨870712988176454679833831807012927217752922944018, 883118980747789020882084464779538700246874405267⟩
def wholeDExp : DyadicInterval precision := ⟨436466074505762269046786189274013976057524048245, 443939237141351316813290285207320726677583911584⟩
def wholeDLog : DyadicInterval precision := ⟨381918529993447746751868483809797874470397239949, 387661827478115861734404726101104697816790214517⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨436466074505762269046786189274013976607279862133, scale precision, 443939237141351316813290285207320726127828097696, scale precision,
    1, 128, 1, 128, ⟨-1766237961495578041764168929559077402334600887543, -1766237961495578041764168929559077402334598790390⟩, ⟨-1741425976352909359667663614025854433695984336263, -1741425976352909359667663614025854433695982239110⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨874588186260648773346854413637122018667374633122, 887452518126024329387449100396608241854937682768⟩
def wholeCExp : DyadicInterval precision := ⟨433885379821840795062740651528376066507558089152, 441591242524962125809089712112610745208220928226⟩
def wholeCLog : DyadicInterval precision := ⟨379929952411146320145342193240938591846480823686, 385859769976505728721241860644683745250221608884⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨433885379821840795062740651528376067057313903040, scale precision, 441591242524962125809089712112610744658465114338, scale precision,
    1, 128, 1, 128, ⟨-1774905036252048658774898200793216485561676588756, -1774905036252048658774898200793216485561674491603⟩, ⟨-1749176372521297546693708827274244035515264453790, -1749176372521297546693708827274244035515262356637⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2221622609040950356192009939625428230446663911098, 2258688600615288423749694210981906718736471655737⟩
def wholeBExp : DyadicInterval precision := ⟨66440366119580210727244391745449862406203672369, 69897365324512522267441137724532177321971545254⟩
def wholeBLog : DyadicInterval precision := ⟨64974428857037904313803202997314515746298707841, 68277370332723297249157721280231310385264934037⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨66440366119580210727244391745449862955959486257, scale precision, 69897365324512522267441137724532176772215731366, scale precision,
    4, 128, 4, 128, ⟨-4517377201230576847499388421963813449566029769676, -4517377201230576847499388421963813449566027672523⟩, ⟨-4443245218081900712384019879250856449398345928276, -4443245218081900712384019879250856449398343831123⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0249StableWitnesses

end


