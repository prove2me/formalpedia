-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0075StableWitnesses__2
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0075StableWitnesses__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:42:08.047075+00:00
-- url     : https://prove2.me/theorems/3e2b6d5f-cc87-4185-a295-ca404b69a19c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0075StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisZero0076StableWitnesses)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0075StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisZero0076StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0075StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisZero0076StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0075StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisZero0076StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0075StableWitnesses (+1 modules: GeneralCK/Certificates/E8TAxisZero0076StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0075StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0075StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨610560585232978838677636124558316081121189005779, 610560585232978838677636124558316081121189005780⟩
def centerDExp : DyadicInterval precision := ⟨633775439067498409587600235923873634184078301602, 633775439067498409587600235923873636383101557155⟩
def centerDLog : DyadicInterval precision := ⟨526464129056309766045029930608943037858964020595, 526464129056309766045029930608943040057987276148⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨633775439067498409587600235923873634733834115490, scale precision, 633775439067498409587600235923873635833345743267, scale precision,
    0, 256, 0, 256, ⟨-1221121170465957677355272249116632163510129390304, -1221121170465957677355272249116632163510127293151⟩, ⟨-1221121170465957677355272249116632160974628729968, -1221121170465957677355272249116632160974626632815⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨610749047126901767587564500529189331296618098081, 610749047126901767587564500529189331296618098082⟩
def centerCExp : DyadicInterval precision := ⟨633612008366326002956931659390302824530057507953, 633612008366326002956931659390302826729080763506⟩
def centerCLog : DyadicInterval precision := ⟨526350128117821975057761591026494238206246082139, 526350128117821975057761591026494240405269337692⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨633612008366326002956931659390302825079813321841, scale precision, 633612008366326002956931659390302826179324949618, scale precision,
    0, 256, 0, 256, ⟨-1221498094253803535175129001058378663861314572065, -1221498094253803535175129001058378663861312474912⟩, ⟨-1221498094253803535175129001058378661325159917415, -1221498094253803535175129001058378661325157820262⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1443004964744911456381893345181437087061296185227, 1443004964744911456381893345181437087061296185228⟩
def centerBExp : DyadicInterval precision := ⟨202863142899278333144133474395543879112030305842, 202863142899278333144133474395543881311053561395⟩
def centerBLog : DyadicInterval precision := ⟨189964684108491441202320786674619182757561547303, 189964684108491441202320786674619184956584802856⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨202863142899278333144133474395543879661786119730, scale precision, 202863142899278333144133474395543880761297747507, scale precision,
    0, 256, 0, 256, ⟨-2886009929489822912763786690362874178083239057500, -2886009929489822912763786690362874178083236960347⟩, ⟨-2886009929489822912763786690362874170161947780561, -2886009929489822912763786690362874170161945683408⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨605149690269836019889894242842311313124295302837, 615985792935344704096715461380744242879788980550⟩
def wholeDExp : DyadicInterval precision := ⟨629087614762237432177832619094338710911004411584, 638485690296710810307667032247350013857008098659⟩
def wholeDLog : DyadicInterval precision := ⟨523190605620864448684409715253755539004186757001, 529745944986552956313550471423206443941852059644⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨629087614762237432177832619094338711460760225472, scale precision, 638485690296710810307667032247350013307252284771, scale precision,
    0, 256, 0, 256, ⟨-1231971585870689408193430922761488487036776340025, -1231971585870689408193430922761488487036774242872⟩, ⟨-1210299380539672039779788485684622624990193800798, -1210299380539672039779788485684622624990191703645⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨605149690269836019889894242842311313124295302837, 616363734361026223237742947818267087747671058165⟩
def wholeCExp : DyadicInterval precision := ⟨628762337265843974427670312309187543226601716812, 638485690296710810307667032247350013857008098659⟩
def wholeCLog : DyadicInterval precision := ⟨522963190991003585654296136532930259229423481083, 529745944986552956313550471423206443941852059644⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨628762337265843974427670312309187543776357530700, scale precision, 638485690296710810307667032247350013307252284771, scale precision,
    0, 256, 0, 256, ⟨-1232727468722052446475485895636534176773201227500, -1232727468722052446475485895636534176773199130347⟩, ⟨-1210299380539672039779788485684622624990193800798, -1210299380539672039779788485684622624990191703645⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1426986055799192838512876476998623343810958899863, 1459105292769415311780651483550583481703716855454⟩
def wholeBExp : DyadicInterval precision := ⟨198442422649099753169740729801347107467503131598, 207359239024952214856023796255612672876113350451⟩
def wholeBLog : DyadicInterval precision := ⟨186077624269660424130344023251612345836403337540, 193907444972304278420007757169750671401985563327⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨198442422649099753169740729801347108017258945486, scale precision, 207359239024952214856023796255612672326357536563, scale precision,
    0, 256, 0, 256, ⟨-2918210585538830623561302967101166967456312068098, -2918210585538830623561302967101166967456309970945⟩, ⟨-2853972111598385677025752953997246683747150470931, -2853972111598385677025752953997246683747148373778⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0075StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0076StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0076StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨599752983055354003753543703993878049904129928193, 599752983055354003753543703993878049904129928194⟩
def centerDExp : DyadicInterval precision := ⟨643218459949503680164771431112985722806282727100, 643218459949503680164771431112985725005305982653⟩
def centerDLog : DyadicInterval precision := ⟨533036044781290419045280039370268756967708914819, 533036044781290419045280039370268759166732170372⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨643218459949503680164771431112985723356038540988, scale precision, 643218459949503680164771431112985724455550168765, scale precision,
    0, 256, 0, 256, ⟨-1199505966110708007507087407987756101057399529178, -1199505966110708007507087407987756101057397432025⟩, ⟨-1199505966110708007507087407987756098559122280751, -1199505966110708007507087407987756098559120183598⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨599940457824606446097303393245383275788639510006, 599940457824606446097303393245383275788639510007⟩
def centerCExp : DyadicInterval precision := ⟨643053462850327966748013950952207298885854142488, 643053462850327966748013950952207301084877398041⟩
def centerCLog : DyadicInterval precision := ⟨532921467558651670686858572617303301739995189822, 532921467558651670686858572617303303939018445375⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨643053462850327966748013950952207299435609956376, scale precision, 643053462850327966748013950952207300535121584153, scale precision,
    0, 256, 0, 256, ⟨-1199880915649212892194606786490766552826739201536, -1199880915649212892194606786490766552826737104383⟩, ⟨-1199880915649212892194606786490766550327820935646, -1199880915649212892194606786490766550327818838493⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1411592916174558478281194275238796835225115895810, 1411592916174558478281194275238796835225115895811⟩
def centerBExp : DyadicInterval precision := ⟨211773555716668477759359153201217397220730394520, 211773555716668477759359153201217399419753650073⟩
def centerBLog : DyadicInterval precision := ⟨197768170382821875603273840472275868209755357793, 197768170382821875603273840472275870408778613346⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨211773555716668477759359153201217397770486208408, scale precision, 211773555716668477759359153201217398869997836185, scale precision,
    0, 256, 0, 256, ⟨-2823185832349116956562388550477593674244233556721, -2823185832349116956562388550477593674244231459568⟩, ⟨-2823185832349116956562388550477593666656232123670, -2823185832349116956562388550477593666656230026517⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨594370338528145575810628189240163754488538282193, 605149690269836019889894242842311313124295302838⟩
def wholeDExp : DyadicInterval precision := ⟨638485690296710810307667032247350011657984843106, 647973841382699837641744325099416508397027426555⟩
def wholeDLog : DyadicInterval precision := ⟨529745944986552956313550471423206441742828804091, 536334420746670162773197764634792507319087016290⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨638485690296710810307667032247350012207740656994, scale precision, 647973841382699837641744325099416507847271612667, scale precision,
    0, 256, 0, 256, ⟨-1210299380539672039779788485684622627506989507705, -1210299380539672039779788485684622627506987410552⟩, ⟨-1188740677056291151621256378480327507737106227057, -1188740677056291151621256378480327507737104129904⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨594370338528145575810628189240163754488538282193, 605525639754255905015627397518030978757082458824⟩
def wholeCExp : DyadicInterval precision := ⟨638157292949424889611811082552144833822350395501, 647973841382699837641744325099416508397027426555⟩
def wholeCLog : DyadicInterval precision := ⟨529517376563282544334914908910001489494683722941, 536334420746670162773197764634792507319087016290⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨638157292949424889611811082552144834372106209389, scale precision, 647973841382699837641744325099416507847271612667, scale precision,
    0, 256, 0, 256, ⟨-1211051279508511810031254795036061958773211394376, -1211051279508511810031254795036061958773209297223⟩, ⟨-1188740677056291151621256378480327507737106227057, -1188740677056291151621256378480327507737104129904⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1395736578421875585713064654815202821689844121484, 1427532357011884353116380646773615700350616453587⟩
def wholeBExp : DyadicInterval precision := ⟨207204277487123306070497951639103121346824725159, 216418982690659711841585523831481963557579766423⟩
def wholeBLog : DyadicInterval precision := ⟨193771731408745391637673883239025316871984323092, 201820039539960432879508642673404400180704130685⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨207204277487123306070497951639103121896580539047, scale precision, 216418982690659711841585523831481963007823952535, scale precision,
    0, 256, 0, 256, ⟨-2855064714023768706232761293547231404578900150069, -2855064714023768706232761293547231404578898052916⟩, ⟨-2791473156843751171426129309630405639667126686632, -2791473156843751171426129309630405639667124589479⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0076StableWitnesses

end


