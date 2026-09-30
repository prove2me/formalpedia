-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0005StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0005StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:42:19.384815+00:00
-- url     : https://prove2.me/theorems/af1b4ccb-f401-4277-9980-4254ffbd0270
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0005StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0006StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0005StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0006StableWitnesses, GeneralCK.Certificates.E8TAxisProd0007StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0005StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0006StableWitnesses, GeneralCK.Certificates.E8TAxisProd0007StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0005StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0006StableWitnesses, GeneralCK.Certificates.E8TAxisProd0007StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0005StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0006StableWitnesses, GeneralCK/Certificates/E8TAxisProd0007StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0005StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0005StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3165742448647063503620071141085134670978073809⟩
def centerAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1455183847209450510423929547351191477780877052172⟩
def centerALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1009873425488092576137085252579843092274389747387⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨60981562246941182391851692343549914653715634261, 60981562246941182391851692343549914653715634262⟩
def centerDExp : DyadicInterval precision := ⟨1344488804354560387653913977701155507615899604953, 1344488804354560387653913977701155509814922860506⟩
def centerDLog : DyadicInterval precision := ⟨953326044385255946846825783453523246727646501740, 953326044385255946846825783453523248926669757293⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1344488804354560387653913977701155508165655418841, scale precision, 1344488804354560387653913977701155509265167046618, scale precision,
    0, 128, 0, 128, ⟨-121963124493882364783703384687099829905034185949, -121963124493882364783703384687099829905032088796⟩, ⟨-121963124493882364783703384687099828709830448249, -121963124493882364783703384687099828709828351096⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨64154050119072738717927061941999861748319015637, 64154050119072738717927061941999861748319015638⟩
def centerCExp : DyadicInterval precision := ⟨1338664481158377319868442614923318553637791963077, 1338664481158377319868442614923318555836815218630⟩
def centerCLog : DyadicInterval precision := ⟨950289289753537869413981234731004287925457477757, 950289289753537869413981234731004290124480733310⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1338664481158377319868442614923318554187547776965, scale precision, 1338664481158377319868442614923318555287059404742, scale precision,
    0, 128, 0, 128, ⟨-128308100238145477435854123883999724096841022489, -128308100238145477435854123883999724096838925336⟩, ⟨-128308100238145477435854123883999722896437137215, -128308100238145477435854123883999722896435040062⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨125402493624018912427648049832801727070032528594, 125402493624018912427648049832801727070032528595⟩
def centerBExp : DyadicInterval precision := ⟨1231036736791996140905685039204399592145524780851, 1231036736791996140905685039204399594344548036404⟩
def centerBLog : DyadicInterval precision := ⟨893006666570535834290831861391604750410654924000, 893006666570535834290831861391604752609678179553⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1231036736791996140905685039204399592695280594739, scale precision, 1231036736791996140905685039204399593794792222516, scale precision,
    0, 128, 0, 128, ⟨-250804987248037824855296099665603454792742827846, -250804987248037824855296099665603454792740730693⟩, ⟨-250804987248037824855296099665603453487389383685, -250804987248037824855296099665603453487387286532⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨58602635770181898821662589353151101542136562992, 63360863746962342702697993485127651995684952634⟩
def wholeDExp : DyadicInterval precision := ⟨1340118310385255731396483422015350658626993302998, 1348872859460053731599279250908956040444361819487⟩
def wholeDLog : DyadicInterval precision := ⟨951047895604627342379828868169897140353010055619, 955607699899585814401544643147774225289199821907⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1340118310385255731396483422015350659176749116886, scale precision, 1348872859460053731599279250908956039894606005599, scale precision,
    0, 128, 0, 128, ⟨-126721727493924685405395986970255304590921766561, -126721727493924685405395986970255304590919669408⟩, ⟨-117205271540363797643325178706302202488614608506, -117205271540363797643325178706302202488612511353⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨61140170517420599824312204870708940218430869241, 67168562787799141081803508490387093149476999624⟩
def wholeCExp : DyadicInterval precision := ⟨1333153561628146457527002171218901943436991275957, 1344197016924831398370770481048404983662735251825⟩
def wholeCLog : DyadicInterval precision := ⟨947410119869654349424280900742328518352281853064, 953174058842438098605194693086279847015512870781⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1333153561628146457527002171218901943986747089845, scale precision, 1344197016924831398370770481048404983112979437937, scale precision,
    0, 128, 0, 128, ⟨-134337125575598282163607016980774186901638073439, -134337125575598282163607016980774186901635976286⟩, ⟨-122280341034841199648624409741417879839131195623, -122280341034841199648624409741417879839129098470⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨119976688018282527118403186318767332493118324027, 130832272587569695809414699320324921011080789364⟩
def wholeBExp : DyadicInterval precision := ⟨1221923527186106999084992706451107773922571225226, 1240211169993063747833404125148284451184524728949⟩
def wholeBLog : DyadicInterval precision := ⟨888051653976961835389995825692819349198360761300, 897978056156449534723239001596928882874517807089⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1221923527186106999084992706451107774472327039114, scale precision, 1240211169993063747833404125148284450634768915061, scale precision,
    0, 128, 0, 128, ⟨-261664545175139391618829398640649842679707067895, -261664545175139391618829398640649842679704970742⟩, ⟨-239953376036565054236806372637534664338389135378, -239953376036565054236806372637534664338387038225⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0005StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0006StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0006StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3165742448647063503620071141085134670978073809⟩
def centerAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1455183847209450510423929547351191477780877052172⟩
def centerALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1009873425488092576137085252579843092274389747387⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨56224069662401947129176131245290424868351320698, 56224069662401947129176131245290424868351320699⟩
def centerDExp : DyadicInterval precision := ⟨1353270542552318619031293173544076935377002222510, 1353270542552318619031293173544076937576025478063⟩
def centerDLog : DyadicInterval precision := ⟨957892874924759606731049484620710570189124178339, 957892874924759606731049484620710572388147433892⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1353270542552318619031293173544076935926758036398, scale precision, 1353270542552318619031293173544076937026269664175, scale precision,
    0, 128, 0, 128, ⟨-112448139324803894258352262490580850330427558828, -112448139324803894258352262490580850330425461675⟩, ⟨-112448139324803894258352262490580849142979821120, -112448139324803894258352262490580849142977723967⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨59395570497876155871827030919663866166637369624, 59395570497876155871827030919663866166637369625⟩
def centerCExp : DyadicInterval precision := ⟨1347409996848020761489776342990284079242469447724, 1347409996848020761489776342990284081441492703277⟩
def centerCLog : DyadicInterval precision := ⟨954846757637119094317035204684427443722289228504, 954846757637119094317035204684427445921312484057⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1347409996848020761489776342990284079792225261612, scale precision, 1347409996848020761489776342990284080891736889389, scale precision,
    0, 128, 0, 128, ⟨-118791140995752311743654061839327732929582052443, -118791140995752311743654061839327732929579955290⟩, ⟨-118791140995752311743654061839327731736969523206, -118791140995752311743654061839327731736967426053⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨115830115911088690603873350786801642312307965168, 115830115911088690603873350786801642312307965169⟩
def centerBExp : DyadicInterval precision := ⟨1247268628163904109363396151575364607208413105204, 1247268628163904109363396151575364609407436360757⟩
def centerBLog : DyadicInterval precision := ⟨901790836783685839964817005160478221464050169807, 901790836783685839964817005160478223663073425360⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1247268628163904109363396151575364607758168919092, scale precision, 1247268628163904109363396151575364608857680546869, scale precision,
    0, 128, 0, 128, ⟨-231660231822177381207746701573603285268799798867, -231660231822177381207746701573603285268797701714⟩, ⟨-231660231822177381207746701573603283980434158959, -231660231822177381207746701573603283980432061806⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨53845849274430363340356920789158241656378561384, 58602635770181898821662589353151101542136562993⟩
def wholeDExp : DyadicInterval precision := ⟨1348872859460053731599279250908956038245338563934, 1357681920934804568838490939788917163911062976792⟩
def wholeDLog : DyadicInterval precision := ⟨955607699899585814401544643147774223090176566354, 960181582307675404146178190201383839808765855727⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1348872859460053731599279250908956038795094377822, scale precision, 1357681920934804568838490939788917163361307162904, scale precision,
    0, 128, 0, 128, ⟨-117205271540363797643325178706302203679933740618, -117205271540363797643325178706302203679931643465⟩, ⟨-107691698548860726680713841578316482720963429336, -107691698548860726680713841578316482720961332183⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨56382629818508109569023805582825185317660096337, 62409097206069606708408168815139972464900235696⟩
def wholeCExp : DyadicInterval precision := ⟨1341864884896329694947165175434287948105478460060, 1352976938350729088534078276200742858212998179616⟩
def wholeCLog : DyadicInterval precision := ⟨951958735123675020100840869810752676708805883875, 957740420169989537447061925271607359318767175926⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1341864884896329694947165175434287948655234273948, scale precision, 1352976938350729088534078276200742857663242365728, scale precision,
    0, 128, 0, 128, ⟨-124818194412139213416816337630279945528571955927, -124818194412139213416816337630279945528569858774⟩, ⟨-112765259637016219138047611165650370041468530716, -112765259637016219138047611165650370041466433563⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨110410900082256569655872652612393379359363185641, 121252999859680607281913286376018482511954730470⟩
def wholeBExp : DyadicInterval precision := ⟨1238046937477863287537128374947874708364674802875, 1256552699861900996669668890440374795766024544392⟩
def wholeBLog : DyadicInterval precision := ⟨896806837320689770602186504796947360532285656195, 906791440347840233037779814200164607749318561565⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1238046937477863287537128374947874708914430616763, scale precision, 1256552699861900996669668890440374795216268730504, scale precision,
    0, 128, 0, 128, ⟨-242505999719361214563826572752036965672891576233, -242505999719361214563826572752036965672889479080⟩, ⟨-220821800164513139311745305224786758079304161115, -220821800164513139311745305224786758079302063962⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0006StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0007StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0007StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 4432047174048269527644776165804031130864675905⟩
def centerAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1452664369350591901250217311774540050861815457867⟩
def centerALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1008610412272733567070593870872814922068705325217⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨51467959962003113552544491254031858203557026049, 51467959962003113552544491254031858203557026050⟩
def centerDExp : DyadicInterval precision := ⟨1362107062367078087011245274026450153640437332371, 1362107062367078087011245274026450155839460587924⟩
def centerDLog : DyadicInterval precision := ⟨962473834965157682455461912650904923379559762004, 962473834965157682455461912650904925578583017557⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1362107062367078087011245274026450154190193146259, scale precision, 1362107062367078087011245274026450155289704774036, scale precision,
    0, 128, 0, 128, ⟨-102935919924006227105088982508063716996987251205, -102935919924006227105088982508063716996985154052⟩, ⟨-102935919924006227105088982508063715817242950146, -102935919924006227105088982508063715817240852993⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨55906953955441934614833995922022843761568683825, 55906953955441934614833995922022843761568683826⟩
def centerCExp : DyadicInterval precision := ⟨1353857933578876353992516595434652697394001293428, 1353857933578876353992516595434652699593024548981⟩
def centerCLog : DyadicInterval precision := ⟨958197831536143147344228658020216315302294402435, 958197831536143147344228658020216317501317657988⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1353857933578876353992516595434652697943757107316, scale precision, 1353857933578876353992516595434652699043268735093, scale precision,
    0, 128, 0, 128, ⟨-111813907910883869229667991844045688116604689315, -111813907910883869229667991844045688116602592162⟩, ⟨-111813907910883869229667991844045686929672143141, -111813907910883869229667991844045686929670045988⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨107543329557845300854416487999214804132516471541, 107543329557845300854416487999214804132516471542⟩
def centerBExp : DyadicInterval precision := ⟨1261493279454225181138807740921280170198791709967, 1261493279454225181138807740921280172397814965520⟩
def centerBLog : DyadicInterval precision := ⟨909445585462496600894484341538178490322391020316, 909445585462496600894484341538178492521414275869⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1261493279454225181138807740921280170748547523855, scale precision, 1261493279454225181138807740921280171848059151632, scale precision,
    0, 128, 0, 128, ⟨-215086659115690601708832975998429608901952979034, -215086659115690601708832975998429608901950881881⟩, ⟨-215086659115690601708832975998429607628115004284, -215086659115690601708832975998429607628112907131⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨49090387085558120317010643908319081445949446151, 53845849274430363340356920789158241656378561385⟩
def wholeDExp : DyadicInterval precision := ⟨1357681920934804568838490939788917161712039721239, 1366546035068101924073630463753607685068326572837⟩
def wholeDLog : DyadicInterval precision := ⟨960181582307675404146178190201383837609742600174, 964769645884129960942701944278613212870985597104⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1357681920934804568838490939788917162261795535127, scale precision, 1366546035068101924073630463753607684518570758949, scale precision,
    0, 128, 0, 128, ⟨-107691698548860726680713841578316483904552913354, -107691698548860726680713841578316483904550816201⟩, ⟨-98180774171116240634021287816638162303943881213, -98180774171116240634021287816638162303941784060⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨52894654640312737718564223508938723181660032364, 58919804825955909032364572049386937727349041578⟩
def wholeCExp : DyadicInterval precision := ⟨1348287532848287284980723174921240026142489248363, 1359450322131803465594110234910581444816556103210⟩
def wholeCLog : DyadicInterval precision := ⟨955303276094424938826883423928977436038798109560, 961098057212024705716880693696126330178995185874⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1348287532848287284980723174921240026692245062251, scale precision, 1359450322131803465594110234910581444266800289322, scale precision,
    0, 128, 0, 128, ⟨-117839609651911818064729144098773876050617289065, -117839609651911818064729144098773876050615191912⟩, ⟨-105789309280625475437128447017877445772296190180, -105789309280625475437128447017877445772294093027⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨102129390020906529768254950722841265361436076310, 112960673334547772762854008241628397815545237559⟩
def wholeBExp : DyadicInterval precision := ⟨1252175912003097356370097669709037543462646429681, 1270874056444511995859724187879660955784670188710⟩
def wholeBLog : DyadicInterval precision := ⟨904436138525164158684702223684340509341783287338, 914471837727390744515614782897821296632039616383⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1252175912003097356370097669709037544012402243569, scale precision, 1270874056444511995859724187879660955234914374822, scale precision,
    0, 128, 0, 128, ⟨-225921346669095545525708016483256796272749787862, -225921346669095545525708016483256796272747690709⟩, ⟨-204258780041813059536509901445682530090655541190, -204258780041813059536509901445682530090653444037⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0007StableWitnesses

end


