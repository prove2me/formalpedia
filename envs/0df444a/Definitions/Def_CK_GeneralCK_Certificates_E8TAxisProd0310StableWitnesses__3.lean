-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0310StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0310StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T22:37:17.854206+00:00
-- url     : https://prove2.me/theorems/30b7190c-de79-45f5-a9a5-96cd094ff6ad
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0310StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0311StableWitnesses, GeneralCK.Certificates.E8TAxisProd03…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0310StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0311StableWitnesses, GeneralCK.Certificates.E8TAxisProd0312StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0310StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0311StableWitnesses, GeneralCK.Certificates.E8TAxisProd0312StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0310StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0311StableWitnesses, GeneralCK.Certificates.E8TAxisProd0312StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0310StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0311StableWitnesses, GeneralCK/Certificates/E8TAxisProd0312StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0310StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0310StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨772618178325993916298133301034463828142750633618, 772618178325993916298133301034463828142750633619⟩
def centerCExp : DyadicInterval precision := ⟨507717954105578807436570431699702839731229410835, 507717954105578807436570431699702841930252666388⟩
def centerCLog : DyadicInterval precision := ⟨435780169729992891186665376689988318171378583284, 435780169729992891186665376689988320370401838837⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨507717954105578807436570431699702840280985224723, scale precision, 507717954105578807436570431699702841380496852500, scale precision,
    1, 128, 1, 128, ⟨-1545236356651987832596266602068927657868012872379, -1545236356651987832596266602068927657868010775226⟩, ⟨-1545236356651987832596266602068927654702991759247, -1545236356651987832596266602068927654702989662094⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1918101887499640943383065804964471544137167788471, 1918101887499640943383065804964471544137167788472⟩
def centerBExp : DyadicInterval precision := ⟨105888067245425458300944395656718208313557882695, 105888067245425458300944395656718210512581138248⟩
def centerBLog : DyadicInterval precision := ⟨102227949176355954500557247767957492428280593225, 102227949176355954500557247767957494627303848778⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨105888067245425458300944395656718208863313696583, scale precision, 105888067245425458300944395656718209962825324360, scale precision,
    3, 128, 3, 128, ⟨-3836203774999281886766131609928943095862245660331, -3836203774999281886766131609928943095862243563178⟩, ⟨-3836203774999281886766131609928943080686427590709, -3836203774999281886766131609928943080686425493556⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨766543284056398443880337599899263821150731954391, 778712112448521877793443428117797062747093418423⟩
def wholeCExp : DyadicInterval precision := ⟨503501558295645583797981801823466968265926156683, 511956319337700100780229335505113423907156362141⟩
def wholeCLog : DyadicInterval precision := ⟨432647519611944829173698619020478875784049588451, 438922389724849711869975308050039350190114413275⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨503501558295645583797981801823466968815681970571, scale precision, 511956319337700100780229335505113423357400548253, scale precision,
    1, 128, 1, 128, ⟨-1557424224897043755586886856235594127089950617218, -1557424224897043755586886856235594127089948520065⟩, ⟨-1533086568112796887760675199798527640732055631250, -1533086568112796887760675199798527640732053534097⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1900244131801229544260039015145987342780720627063, 1936007185943845989390045675498262083038031684069⟩
def wholeBExp : DyadicInterval precision := ⟨103325062170948613155723074595141223076001821906, 108507588580371119240580468199774102005274448076⟩
def wholeBLog : DyadicInterval precision := ⟨99836136820102029132063017789269585824840063354, 104668464835658082301776798276656093344815040984⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨103325062170948613155723074595141223625757635794, scale precision, 108507588580371119240580468199774101455518634188, scale precision,
    3, 128, 3, 128, ⟨-3872014371887691978780091350996524173852193511129, -3872014371887691978780091350996524173852191413976⟩, ⟨-3800488263602459088520078030291974678156715751854, -3800488263602459088520078030291974678156713654701⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0310StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0311StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0311StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨760893838179565244591048187893082920951451269576, 760893838179565244591048187893082920951451269577⟩
def centerCExp : DyadicInterval precision := ⟨515929600516915308014711013458534472462640534771, 515929600516915308014711013458534474661663790324⟩
def centerCLog : DyadicInterval precision := ⟨441861960348452815002579441510955267969557915802, 441861960348452815002579441510955270168581171355⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨515929600516915308014711013458534473012396348659, scale precision, 515929600516915308014711013458534474111907976436, scale precision,
    1, 128, 1, 128, ⟨-1521787676359130489182096375786165843460226566146, -1521787676359130489182096375786165843460224468993⟩, ⟨-1521787676359130489182096375786165840345580609313, -1521787676359130489182096375786165840345578512160⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1883043247241748486808674043083625964163645243066, 1883043247241748486808674043083625964163645243067⟩
def centerBExp : DyadicInterval precision := ⟨111092007791852203090591176949185243069376035763, 111092007791852203090591176949185245268399291316⟩
def centerBLog : DyadicInterval precision := ⟨107072289891283389686846551484967344530461745042, 107072289891283389686846551484967346729485000595⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨111092007791852203090591176949185243619131849651, scale precision, 111092007791852203090591176949185244718643477428, scale precision,
    3, 128, 3, 128, ⟨-3766086494483496973617348086167251935559756210617, -3766086494483496973617348086167251935559754113464⟩, ⟨-3766086494483496973617348086167251921094826858802, -3766086494483496973617348086167251921094824761649⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨754855386585398468500627975800350234813760938710, 766951085873784580849996981851196430098060948880⟩
def wholeCExp : DyadicInterval precision := ⟨511670697388158399334391840273658287173953953392, 520210571891979109741571502838567210244697096446⟩
def wholeCLog : DyadicInterval precision := ⟨438710848781401039820434191310281856273377658118, 445022567785922596974052891693358794550706380104⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨511670697388158399334391840273658287723709767280, scale precision, 520210571891979109741571502838567209694941282558, scale precision,
    1, 128, 1, 128, ⟨-1533902171747569161699993963702392861766408339325, -1533902171747569161699993963702392861766406242172⟩, ⟨-1509710773170796937001255951600700468083015633098, -1509710773170796937001255951600700468083013535945⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1865282740747114709560789611291861752887150191838, 1900853854446340605990425969242132023366817734085⟩
def wholeBExp : DyadicInterval precision := ⟨108417089960500950192122432288490334204411804575, 113825118278592471637931064216425560283924492297⟩
def wholeBLog : DyadicInterval precision := ⟨104584218392348352322224546440265338696858519877, 109610121822576387562790882916441635761102963324⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨108417089960500950192122432288490334754167618463, scale precision, 113825118278592471637931064216425559734168678409, scale precision,
    3, 128, 3, 128, ⟨-3801707708892681211980851938484264054144543989206, -3801707708892681211980851938484264054144541892053⟩, ⟨-3730565481494229419121579222583723498715498996710, -3730565481494229419121579222583723498715496899557⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0311StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0312StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0312StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨795867129274905694949066477430310377327234598141, 795867129274905694949066477430310377327234598142⟩
def centerCExp : DyadicInterval precision := ⟨491819082027405788418640716275745892991892429394, 491819082027405788418640716275745895190915684947⟩
def centerCLog : DyadicInterval precision := ⟨423932564362270161653305549919455906409965442040, 423932564362270161653305549919455908608988697593⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨491819082027405788418640716275745893541648243282, scale precision, 491819082027405788418640716275745894641159871059, scale precision,
    1, 128, 1, 128, ⟨-1591734258549811389898132954860620756288138094464, -1591734258549811389898132954860620756288135997311⟩, ⟨-1591734258549811389898132954860620753020802395255, -1591734258549811389898132954860620753020800298102⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1988143268489162038306454172245533300458124313689, 1988143268489162038306454172245533300458124313690⟩
def centerBExp : DyadicInterval precision := ⟨96210072078050374425629211497013670104772460248, 96210072078050374425629211497013672303795715801⟩
def centerBLog : DyadicInterval precision := ⟨93175794300609236658819630553810819201013997988, 93175794300609236658819630553810821400037253541⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨96210072078050374425629211497013670654528274136, scale precision, 96210072078050374425629211497013671754039901913, scale precision,
    3, 128, 3, 128, ⟨-3976286536978324076612908344491066609267444148379, -3976286536978324076612908344491066609267442051226⟩, ⟨-3976286536978324076612908344491066592565055203521, -3976286536978324076612908344491066592565053106368⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨789719255653951548822230430713390385501532680032, 802034511325989184277795602978615452582503309186⟩
def wholeCExp : DyadicInterval precision := ⟨487685700168395757571706970810843592807408122732, 495974255465491844759123076081273879529381429263⟩
def wholeCLog : DyadicInterval precision := ⟨420836633988471038083924660832487715266889228560, 427038220662286302690951182009306300718271408754⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨487685700168395757571706970810843593357163936620, scale precision, 495974255465491844759123076081273878979625615375, scale precision,
    1, 128, 1, 128, ⟨-1604069022651978368555591205957230906812521674131, -1604069022651978368555591205957230906812519576978⟩, ⟨-1579438511307903097644460861426780769383085102604, -1579438511307903097644460861426780769383083005451⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1970107443032899946045237766792141542604738794844, 2006221688941413715305331658289350086425460307603⟩
def wholeBExp : DyadicInterval precision := ⟨93859082683571968622916965027346296091300004484, 98614200906528023923283228289019031220726679912⟩
def wholeBLog : DyadicInterval precision := ⟨90968344534833916812255184577450509197456943150, 95429696328133777529932636628055569512364106980⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨93859082683571968622916965027346296641055818372, scale precision, 98614200906528023923283228289019030670970866024, scale precision,
    3, 128, 3, 128, ⟨-4012443377882827430610663316578700181411297486328, -4012443377882827430610663316578700181411295389175⟩, ⟨-3940214886065799892090475533584283077061879055815, -3940214886065799892090475533584283077061876958662⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0312StableWitnesses

end


