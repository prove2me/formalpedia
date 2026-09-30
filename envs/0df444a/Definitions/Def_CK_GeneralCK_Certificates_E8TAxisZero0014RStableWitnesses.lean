-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0014RStableWitnesses
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0014RStableWitnesses
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:25:39.267915+00:00
-- url     : https://prove2.me/theorems/70197b56-224c-467b-8e4f-917b1ab17f0b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0014RStableWitnesses` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0014RStableWitnesses` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0014RStableWitnesses` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0014RStableWitnesses (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0014RStableWitnesses.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0014RStableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0014RStableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨33642866171408924506845362522458271850125470383, 33642866171408924506845362522458271850125470384⟩
def centerDExp : DyadicInterval precision := ⟨1395741282673356127811668669406441745729084947230, 1395741282673356127811668669406441747928108202783⟩
def centerDLog : DyadicInterval precision := ⟨979780057949121675793051764724504043556953588686, 979780057949121675793051764724504045755976844239⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1395741282673356127811668669406441746278840761118, scale precision, 1395741282673356127811668669406441747378352388895, scale precision,
    0, 128, 0, 128, ⟨-67285732342817849013690725044916544275909550028, -67285732342817849013690725044916544275907452875⟩, ⟨-67285732342817849013690725044916543124594428660, -67285732342817849013690725044916543124592331507⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨34276411375151605005412071410238652429608274587, 34276411375151605005412071410238652429608274588⟩
def centerCExp : DyadicInterval precision := ⟨1394531729479504118538607465914235926766631590589, 1394531729479504118538607465914235928965654846142⟩
def centerCLog : DyadicInterval precision := ⟨979161231233619009805838993731661428794768707032, 979161231233619009805838993731661430993791962585⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1394531729479504118538607465914235927316387404477, scale precision, 1394531729479504118538607465914235928415899032254, scale precision,
    0, 128, 0, 128, ⟨-68552822750303210010824142820477305435374457538, -68552822750303210010824142820477305435372360385⟩, ⟨-68552822750303210010824142820477304283060737964, -68552822750303210010824142820477304283058640811⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨67961964551488262188828254855795778736014617692, 67961964551488262188828254855795778736014617693⟩
def centerBExp : DyadicInterval precision := ⟨1331706895592994339422554366030765224790648439236, 1331706895592994339422554366030765226989671694789⟩
def centerBLog : DyadicInterval precision := ⟨946653370983950457516442070999313412297977171613, 946653370983950457516442070999313414497000427166⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1331706895592994339422554366030765225340404253124, scale precision, 1331706895592994339422554366030765226439915880901, scale precision,
    0, 128, 0, 128, ⟨-135923929102976524377656509711591558075368019005, -135923929102976524377656509711591558075365921852⟩, ⟨-135923929102976524377656509711591556868692548916, -135923929102976524377656509711591556868690451763⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨32455008327171042732967145611016798201694283382, 34830775707694518323356855819802492385993843110⟩
def wholeDExp : DyadicInterval precision := ⟨1393474206903787201785230037422771619329955308483, 1398011947908555347946217879565997678938216728909⟩
def wholeDLog : DyadicInterval precision := ⟨978619971033722696354607064598753113312271289775, 980941059342323278062008541570423723639018833157⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1393474206903787201785230037422771619879711122371, scale precision, 1398011947908555347946217879565997678388460915021, scale precision,
    0, 128, 0, 128, ⟨-69661551415389036646713711639604985348582846224, -69661551415389036646713711639604985348580749071⟩, ⟨-64910016654342085465934291222033595828667043526, -64910016654342085465934291222033595828664946373⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨32455008327171042732967145611016798201694283382, 36097938246870058546958457136650379086153782136⟩
def wholeCExp : DyadicInterval precision := ⟨1391059939013504036843525882064723711480639709966, 1398011947908555347946217879565997678938216728909⟩
def wholeCLog : DyadicInterval precision := ⟨977383551042037225952002295716720299619872254510, 980941059342323278062008541570423723639018833157⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1391059939013504036843525882064723712030395523854, scale precision, 1398011947908555347946217879565997678388460915021, scale precision,
    0, 128, 0, 128, ⟨-72195876493740117093916914273300758749903437913, -72195876493740117093916914273300758749901340760⟩, ⟨-64910016654342085465934291222033595828667043526, -64910016654342085465934291222033595828664946373⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨64947280332316000322410712642463922028995212820, 70977319494027914470138645364705689093823642823⟩
def wholeBExp : DyadicInterval precision := ⟨1326223089935828755009860249456747404184866625909, 1337212148894607956893006348174756918946660708639⟩
def wholeBLog : DyadicInterval precision := ⟨943781237183937452238576505826193084304704565402, 949531071658069409953583687276334193257047206654⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1326223089935828755009860249456747404734622439797, scale precision, 1337212148894607956893006348174756918396904894751, scale precision,
    0, 128, 0, 128, ⟨-141954638988055828940277290729411378793480813105, -141954638988055828940277290729411378793478715952⟩, ⟨-129894560664632000644821425284927843457137658468, -129894560664632000644821425284927843457135561315⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0014RStableWitnesses

end


