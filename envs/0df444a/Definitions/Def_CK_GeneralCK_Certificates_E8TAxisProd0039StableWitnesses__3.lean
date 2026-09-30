-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0039StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0039StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:42:09.792639+00:00
-- url     : https://prove2.me/theorems/699c4830-7f77-4e9d-a41b-60771575bb6f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0039StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0040StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0039StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0040StableWitnesses, GeneralCK.Certificates.E8TAxisProd0041StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0039StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0040StableWitnesses, GeneralCK.Certificates.E8TAxisProd0041StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0039StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0040StableWitnesses, GeneralCK.Certificates.E8TAxisProd0041StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0039StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0040StableWitnesses, GeneralCK/Certificates/E8TAxisProd0041StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0039StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0039StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨107065494589907116025240672481192988302250052280, 107065494589907116025240672481192988302250052281⟩
def centerDExp : DyadicInterval precision := ⟨1262318434497260164208401614240797141306259170539, 1262318434497260164208401614240797143505282426092⟩
def centerDLog : DyadicInterval precision := ⟨909888400376604858648946115122446892680058539307, 909888400376604858648946115122446894879081794860⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1262318434497260164208401614240797141856014984427, scale precision, 1262318434497260164208401614240797142955526612204, scale precision,
    0, 128, 0, 128, ⟨-214130989179814232050481344962385977241003797932, -214130989179814232050481344962385977241001700779⟩, ⟨-214130989179814232050481344962385975967998508344, -214130989179814232050481344962385975967996411191⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨110251565142694123281775922430296768663694160594, 110251565142694123281775922430296768663694160595⟩
def centerCExp : DyadicInterval precision := ⟨1256826711977157757187599113423829322186906438599, 1256826711977157757187599113423829324385929694152⟩
def centerCLog : DyadicInterval precision := ⟨906938769621193192292347091397006762064180799801, 906938769621193192292347091397006764263204055354⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1256826711977157757187599113423829322736662252487, scale precision, 1256826711977157757187599113423829323836173880264, scale precision,
    0, 128, 0, 128, ⟨-220503130285388246563551844860593537966673222084, -220503130285388246563551844860593537966671124931⟩, ⟨-220503130285388246563551844860593536688105517446, -220503130285388246563551844860593536688103420293⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨218716309774253515715349559598011326794849994989, 218716309774253515715349559598011326794849994990⟩
def centerBExp : DyadicInterval precision := ⟨1083461363001147522481644668816972141344008008553, 1083461363001147522481644668816972143543031264106⟩
def centerBLog : DyadicInterval precision := ⟨810624347003225179965347206965641653964661957660, 810624347003225179965347206965641656163685213213⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1083461363001147522481644668816972141893763822441, scale precision, 1083461363001147522481644668816972142993275450218, scale precision,
    0, 128, 0, 128, ⟨-437432619548507031430699119196022654331277110918, -437432619548507031430699119196022654331275013765⟩, ⟨-437432619548507031430699119196022652848124966194, -437432619548507031430699119196022652848122869041⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨103084551358829778834915002511195342403115231675, 111048270122241576078328386047482676587330985905⟩
def wholeDExp : DyadicInterval precision := ⟨1255457196643991312782767932801799986914544905423, 1269213987453105464161597200857722394416664115457⟩
def wholeDLog : DyadicInterval precision := ⟨906202267987834631995011695345793199517903616160, 913583624998653703523149262826058897164757379534⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1255457196643991312782767932801799987464300719311, scale precision, 1269213987453105464161597200857722393866908301569, scale precision,
    0, 128, 0, 128, ⟨-222096540244483152156656772094965353814644235419, -222096540244483152156656772094965353814642138266⟩, ⟨-206169102717659557669830005022390684173186942555, -206169102717659557669830005022390684173184845402⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨105632147522948726430034597027139165605022884109, 114873522086229401550599629602980010984739621715⟩
def wholeCExp : DyadicInterval precision := ⟨1248902441927408411362553828834974221319531295825, 1264796866303566207571429692709404440762760122709⟩
def wholeCLog : DyadicInterval precision := ⟨902672085996534669099115243778699389322062192753, 911217631050199692609930985507329346993291691625⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1248902441927408411362553828834974221869287109713, scale precision, 1264796866303566207571429692709404440213004308821, scale precision,
    0, 128, 0, 128, ⟨-229747044172458803101199259205960022612820392205, -229747044172458803101199259205960022612818295052⟩, ⟨-211264295045897452860069194054278330574791430310, -211264295045897452860069194054278330574789333157⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨209956316671997090000842133265351880706535748528, 227493904775828364443481753968725214648101220907⟩
def wholeBExp : DyadicInterval precision := ⟨1070524947694947175059872365104781307820615696770, 1096527691430814070408977739606207489392109661352⟩
def wholeBLog : DyadicInterval precision := ⟨803176377000203245651677875656754746083613733583, 818108780016791024693045805775745556061045574755⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1070524947694947175059872365104781308370371510658, scale precision, 1096527691430814070408977739606207488842353847464, scale precision,
    0, 128, 0, 128, ⟨-454987809551656728886963507937450430046740900901, -454987809551656728886963507937450430046738803748⟩, ⟨-419912633343994180001684266530703760680333164395, -419912633343994180001684266530703760680331067242⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0039StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0040StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0040StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨99105371957748756558358702025034649328540468989, 99105371957748756558358702025034649328540468990⟩
def centerDExp : DyadicInterval precision := ⟨1276144127861541994145963581661485621034162019732, 1276144127861541994145963581661485623233185275285⟩
def centerDLog : DyadicInterval precision := ⟨917287995011510229356867982908921321385400443938, 917287995011510229356867982908921323584423699491⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1276144127861541994145963581661485621583917833620, scale precision, 1276144127861541994145963581661485622683429461397, scale precision,
    0, 128, 0, 128, ⟨-198210743915497513116717404050069299286688787692, -198210743915497513116717404050069299286686690539⟩, ⟨-198210743915497513116717404050069298027475185421, -198210743915497513116717404050069298027473088268⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨102288576562075948255867412728424315936308840623, 102288576562075948255867412728424315936308840624⟩
def centerCExp : DyadicInterval precision := ⟨1270597239769667432850029641087028140482480003571, 1270597239769667432850029641087028142681503259124⟩
def centerCLog : DyadicInterval precision := ⟨914323765659848105821442175011509898967812753901, 914323765659848105821442175011509901166836009454⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1270597239769667432850029641087028141032235817459, scale precision, 1270597239769667432850029641087028142131747445236, scale precision,
    0, 128, 0, 128, ⟨-204577153124151896511734825456848632504974126941, -204577153124151896511734825456848632504972029788⟩, ⟨-204577153124151896511734825456848631240263332707, -204577153124151896511734825456848631240261235554⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨202507445516537500012131595254672422594967063253, 202507445516537500012131595254672422594967063254⟩
def centerBExp : DyadicInterval precision := ⟨1107762252645637980489192806237745350742128503631, 1107762252645637980489192806237745352941151759184⟩
def centerBLog : DyadicInterval precision := ⟨824513467709269488069291355952413269384983419907, 824513467709269488069291355952413271584006675460⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1107762252645637980489192806237745351291884317519, scale precision, 1107762252645637980489192806237745352391395945296, scale precision,
    0, 128, 0, 128, ⟨-405014891033075000024263190509344845915243353992, -405014891033075000024263190509344845915241256839⟩, ⟨-405014891033075000024263190509344844464626996174, -405014891033075000024263190509344844464624899021⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨95127887983717436574352739463518235552733806994, 103084551358829778834915002511195342403115231676⟩
def wholeDExp : DyadicInterval precision := ⟨1269213987453105464161597200857722392217640859904, 1283109131137421329953040259475754031879254989498⟩
def wholeDLog : DyadicInterval precision := ⟨913583624998653703523149262826058894965734123981, 921001564088758741914731412563984562181431746082⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1269213987453105464161597200857722392767396673792, scale precision, 1283109131137421329953040259475754031329499175610, scale precision,
    0, 128, 0, 128, ⟨-206169102717659557669830005022390685439276081302, -206169102717659557669830005022390685439273984149⟩, ⟨-190255775967434873148705478927036470479279507931, -190255775967434873148705478927036470479277410778⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨97673285984124066128015298065358904033793501767, 106906222136452251800882146200705633326592822457⟩
def wholeCExp : DyadicInterval precision := ⟨1262593595962690659632005253813941875690834165027, 1278647498360097009011004557740837225305962198767⟩
def wholeCLog : DyadicInterval precision := ⟨910036034438471029983882665499693163200533247330, 918623817328114892230994065911876788425610704738⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1262593595962690659632005253813941876240589978915, scale precision, 1278647498360097009011004557740837224756206384879, scale precision,
    0, 128, 0, 128, ⟨-213812444272904503601764292401411267289550623024, -213812444272904503601764292401411267289548525871⟩, ⟨-195346571968248132256030596130717807439213912124, -195346571968248132256030596130717807439211814971⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨193778155013554683299889988710244792947684043083, 211253010738814688741513314259447908539070264892⟩
def wholeBExp : DyadicInterval precision := ⟨1094583663264658192859639577095084240099742816761, 1121074541873184918683835318833754696716371101054⟩
def wholeBLog : DyadicInterval precision := ⟨816997658858733881976258143282406435194459036245, 832066487812359628690065743459079147773281772204⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1094583663264658192859639577095084240649498630649, scale precision, 1121074541873184918683835318833754696166615287166, scale precision,
    0, 128, 0, 128, ⟨-422506021477629377483026628518895817812182336590, -422506021477629377483026628518895817812180239437⟩, ⟨-387556310027109366599779977420489585178673685762, -387556310027109366599779977420489585178671588609⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0040StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0041StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0041StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 1899443256066344012630337314537754309230277492⟩
def centerAExp : DyadicInterval precision := ⟨1457707683773513925477741956702213444480153619489, 1457707683773513925477741956702213446679176875042⟩
def centerALog : DyadicInterval precision := ⟨1011137530350683182654731711817158197559546439255, 1011137530350683182654731711817158199758569694808⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457707683773513925477741956702213445029909433377, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-3798886512132688025260674629075509169648258520, -3798886512132688025260674629075509169646161367⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨123008276316677968590567857617524352972070183257, 123008276316677968590567857617524352972070183258⟩
def centerDExp : DyadicInterval precision := ⟨1235076695440473766556638255203847372603080990588, 1235076695440473766556638255203847374802104246141⟩
def centerDLog : DyadicInterval precision := ⟨895197900350273137203831070133649824645107273249, 895197900350273137203831070133649826844130528802⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1235076695440473766556638255203847373152836804476, scale precision, 1235076695440473766556638255203847374252348432253, scale precision,
    0, 128, 0, 128, ⟨-246016552633355937181135715235048706594683219577, -246016552633355937181135715235048706594681122424⟩, ⟨-246016552633355937181135715235048705293599610606, -246016552633355937181135715235048705293597513453⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨124923588769881387089525846289839825785387700913, 124923588769881387089525846289839825785387700914⟩
def centerCExp : DyadicInterval precision := ⟨1231843773444689659229450766872696729778035932562, 1231843773444689659229450766872696731977059188115⟩
def centerCLog : DyadicInterval precision := ⟨893444657973704398289046431945818818258675888155, 893444657973704398289046431945818820457699143708⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1231843773444689659229450766872696730327791746450, scale precision, 1231843773444689659229450766872696731427303374227, scale precision,
    0, 128, 0, 128, ⟨-249847177539762774179051692579679652223025574402, -249847177539762774179051692579679652223023477249⟩, ⟨-249847177539762774179051692579679650918527326408, -249847177539762774179051692579679650918525229255⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨250010485980183976055392476858641416483499955009, 250010485980183976055392476858641416483499955010⟩
def centerBExp : DyadicInterval precision := ⟨1038041945019907988417555870178637115729740566111, 1038041945019907988417555870178637117928763821664⟩
def centerBLog : DyadicInterval precision := ⟨784305678760996942073221918091369059578222346533, 784305678760996942073221918091369061777245602086⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1038041945019907988417555870178637116279496379999, scale precision, 1038041945019907988417555870178637117379008007776, scale precision,
    0, 128, 0, 128, ⟨-500020971960367952110784953717282833741024615332, -500020971960367952110784953717282833741022518179⟩, ⟨-500020971960367952110784953717282832192977301859, -500020971960367952110784953717282832192975204706⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨119019592332330079773337734920394720791278241017, 126999067220414009923202423697912773180597398747⟩
def wholeDExp : DyadicInterval precision := ⟨1228350054579566692017908102915209765594934478659, 1241836591959774864289057338296444370704392702246⟩
def wholeDLog : DyadicInterval precision := ⟨891547615580027951955449639520829062035069301574, 898857069849833759981739512399832702035676431148⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1228350054579566692017908102915209766144690292547, scale precision, 1241836591959774864289057338296444370154636888358, scale precision,
    0, 128, 0, 128, ⟨-253998134440828019846404847395825547015300121259, -253998134440828019846404847395825547015298024106⟩, ⟨-238039184664660159546675469840789440935556928976, -238039184664660159546675469840789440935554831823⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨120295746166073688299697151201661012754942157297, 129554310903328861618553401759095070205044128552⟩
def wholeCExp : DyadicInterval precision := ⟨1224062337940262835884041942228948967468729640351, 1239669791048700762763922815625918521217213058002⟩
def wholeCLog : DyadicInterval precision := ⟨889216072642414855396552704879363494821126166276, 897685165847594704246171044993454083773936727286⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1224062337940262835884041942228948968018485454239, scale precision, 1239669791048700762763922815625918520667457244114, scale precision,
    0, 128, 0, 128, ⟨-259108621806657723237106803518190141066484815308, -259108621806657723237106803518190141066482718155⟩, ⟨-240591492332147376599394302403322024861753878536, -240591492332147376599394302403322024861751781383⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨241184626806749055639611155786176124284241534580, 258856523389556057576596003104549794743303155872⟩
def wholeBExp : DyadicInterval precision := ⟨1025551774732822142853509456880829104766074972342, 1050655220626468140158581794906027349332101733979⟩
def wholeBLog : DyadicInterval precision := ⟨776984276000630970805974684708486429238247565004, 791662208582552229743762264383106992014978222243⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1025551774732822142853509456880829105315830786230, scale precision, 1050655220626468140158581794906027348782345920091, scale precision,
    0, 128, 0, 128, ⟨-517713046779112115153192006209099590270057832471, -517713046779112115153192006209099590270055735318⟩, ⟨-482369253613498111279222311572352247803752732639, -482369253613498111279222311572352247803750635486⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0041StableWitnesses

end


