-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0059StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0059StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:43:05.650972+00:00
-- url     : https://prove2.me/theorems/19236da5-c0d2-43cc-a773-b4c96a9fb563
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0059StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0060StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0059StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0060StableWitnesses, GeneralCK.Certificates.E8TAxisProd0061StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0059StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0060StableWitnesses, GeneralCK.Certificates.E8TAxisProd0061StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0059StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0060StableWitnesses, GeneralCK.Certificates.E8TAxisProd0061StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0059StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0060StableWitnesses, GeneralCK/Certificates/E8TAxisProd0061StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0059StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0059StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨248047465841179905852080519169529384371630755610, 248047465841179905852080519169529384371630755611⟩
def centerDExp : DyadicInterval precision := ⟨1040834191819245838922303450900148559184359318387, 1040834191819245838922303450900148561383382573940⟩
def centerDLog : DyadicInterval precision := ⟨785937414897454142996966385139071281278247176763, 785937414897454142996966385139071283477270432316⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1040834191819245838922303450900148559734115132275, scale precision, 1040834191819245838922303450900148560833626760052, scale precision,
    0, 128, 0, 128, ⟨-496094931682359811704161038339058769515209742591, -496094931682359811704161038339058769515207645438⟩, ⟨-496094931682359811704161038339058767971315377004, -496094931682359811704161038339058767971313279851⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨251319719158077856123941449565787593282445443877, 251319719158077856123941449565787593282445443878⟩
def centerCExp : DyadicInterval precision := ⟨1036183825670844774535695031954842783979263822311, 1036183825670844774535695031954842786178287077864⟩
def centerCLog : DyadicInterval precision := ⟨783218818594485091996894003512475467208046130526, 783218818594485091996894003512475469407069386079⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1036183825670844774535695031954842784529019636199, scale precision, 1036183825670844774535695031954842785628531263976, scale precision,
    0, 128, 0, 128, ⟨-502639438316155712247882899131575187340303598071, -502639438316155712247882899131575187340301500918⟩, ⟨-502639438316155712247882899131575185789480274593, -502639438316155712247882899131575185789478177440⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨516359633483965550769306828629969539074360786554, 516359633483965550769306828629969539074360786555⟩
def centerBExp : DyadicInterval precision := ⟨720975032818824115508540015583366917188737582963, 720975032818824115508540015583366919387760838516⟩
def centerBLog : DyadicInterval precision := ⟨586056154606097964526562885964265142333704434633, 586056154606097964526562885964265144532727690186⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨720975032818824115508540015583366917738493396851, scale precision, 720975032818824115508540015583366918838005024628, scale precision,
    1, 128, 1, 128, ⟨-1032719266967931101538613657259939079263142657826, -1032719266967931101538613657259939079263140560673⟩, ⟨-1032719266967931101538613657259939077034302585545, -1032719266967931101538613657259939077034300488392⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨239878763828786629732963390089367294542248751090, 256233328382592948799518632260864583083635375284⟩
def wholeDExp : DyadicInterval precision := ⟨1029239839924196772159254586274144058200357824470, 1052534436295863801714746685306812133363569214732⟩
def wholeDLog : DyadicInterval precision := ⟨779149939480909138582665574125961103221748177421, 792755074273575496363197836249071888393767558659⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1029239839924196772159254586274144058750113638358, scale precision, 1052534436295863801714746685306812132813813400844, scale precision,
    0, 128, 0, 128, ⟨-512466656765185897599037264521729166947914940776, -512466656765185897599037264521729166947912843623⟩, ⟨-479757527657573259465926780178734588321132532104, -479757527657573259465926780178734588321130434951⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨242490916659753179449762138168969105284430212067, 260168808084051724207340356924670106199222168444⟩
def wholeCExp : DyadicInterval precision := ⟨1023711738189858330509771486033612622731514215510, 1048778747491402917119097353667193952174950851636⟩
def wholeCLog : DyadicInterval precision := ⟨775902589655979148194684620099574950716477926989, 790570121791082467784100830538504735231304343792⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1023711738189858330509771486033612623281270029398, scale precision, 1048778747491402917119097353667193951625195037748, scale precision,
    0, 128, 0, 128, ⟨-520337616168103448414680713849340213183304044553, -520337616168103448414680713849340213183301947400⟩, ⟨-484981833319506358899524276337938209802761831533, -484981833319506358899524276337938209802759734380⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨497687795998397117649244397984432485175960451123, 535189694952680963304873857541902184088170916890⟩
def wholeBExp : DyadicInterval precision := ⟨702634193937220187064536449449028084192960932753, 739634457227329619408055627098249372995739319291⟩
def wholeBLog : DyadicInterval precision := ⟨573722262346269697173879383144077547871295278180, 598498377720168544671336610201384666902698356016⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨702634193937220187064536449449028084742716746641, scale precision, 739634457227329619408055627098249372445983505403, scale precision,
    1, 128, 0, 128, ⟨-1070379389905361926609747715083804369319852590627, -1070379389905361926609747715083804369319850493474⟩, ⟨-995375591996794235298488795968864969265616392342, -995375591996794235298488795968864969265614295189⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0059StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0060StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0060StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨231726644506236789334274380203310872944649121715, 231726644506236789334274380203310872944649121716⟩
def centerDExp : DyadicInterval precision := ⟨1064342052735172538949525898691347990568366073785, 1064342052735172538949525898691347992767389329338⟩
def centerDLog : DyadicInterval precision := ⟨799603206825097674192041553707670067993043651350, 799603206825097674192041553707670070192066906903⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1064342052735172538949525898691347991118121887673, scale precision, 1064342052735172538949525898691347992217633515450, scale precision,
    0, 128, 0, 128, ⟨-463453289012473578668548760406621746644196667401, -463453289012473578668548760406621746644194570248⟩, ⟨-463453289012473578668548760406621745134401916614, -463453289012473578668548760406621745134399819461⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨234985539199456772845014830690100987041247113914, 234985539199456772845014830690100987041247113915⟩
def centerCExp : DyadicInterval precision := ⟨1059606025438338833497597228890590279939812954341, 1059606025438338833497597228890590282138836209894⟩
def centerCLog : DyadicInterval precision := ⟨796860278194889237597851068653529001927470433564, 796860278194889237597851068653529004126493689117⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1059606025438338833497597228890590280489568768229, scale precision, 1059606025438338833497597228890590281589080396006, scale precision,
    0, 128, 0, 128, ⟨-469971078398913545690029661380201974840766749803, -469971078398913545690029661380201974840764652650⟩, ⟨-469971078398913545690029661380201973324223803007, -469971078398913545690029661380201973324221705854⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨480587617583154446417785413694201341604360523168, 480587617583154446417785413694201341604360523169⟩
def centerBExp : DyadicInterval precision := ⟨757146620674580303634324056305096653975843228393, 757146620674580303634324056305096656174866483946⟩
def centerBLog : DyadicInterval precision := ⟨610080023993545524805315611001473672646929834568, 610080023993545524805315611001473674845953090121⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨757146620674580303634324056305096654525599042281, scale precision, 757146620674580303634324056305096655625110670058, scale precision,
    0, 128, 0, 128, ⟨-961175235166308892835570827388402684269902321030, -961175235166308892835570827388402684269900223877⟩, ⟨-961175235166308892835570827388402682147541868798, -961175235166308892835570827388402682147539771645⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨223590532296792858273138350117122513977217811276, 239878763828786629732963390089367294542248751091⟩
def wholeDExp : DyadicInterval precision := ⟨1052534436295863801714746685306812131164545959179, 1076258554488359441934578352032876250046492487573⟩
def wholeDLog : DyadicInterval precision := ⟨792755074273575496363197836249071886194744303106, 806482109433465224369192354012429701629745321451⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1052534436295863801714746685306812131714301773067, scale precision, 1076258554488359441934578352032876249496736673685, scale precision,
    0, 128, 0, 128, ⟨-479757527657573259465926780178734589847864569410, -479757527657573259465926780178734589847862472257⟩, ⟨-447181064593585716546276700234245027207897636639, -447181064593585716546276700234245027207895539486⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨226192381607875787764973691711067383103547195306, 243797635752172854441566085746482099908275673540⟩
def wholeCExp : DyadicInterval precision := ⟨1046905010795551553201549808992034659047908757745, 1072433333592369868803923397647789076681842146302⟩
def wholeCLog : DyadicInterval precision := ⟨789478812706385577759978772296657459964350391989, 804277494414882387092884188447412248693008087316⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1046905010795551553201549808992034659597664571633, scale precision, 1072433333592369868803923397647789076132086332414, scale precision,
    0, 128, 0, 128, ⟨-487595271504345708883132171492964200584023191808, -487595271504345708883132171492964200584021094655⟩, ⟨-452384763215751575529947383422134765457893603549, -452384763215751575529947383422134765457891506396⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨462203602748688269141792523640124819118951699959, 499118607398289371570928132321858375692748600604⟩
def wholeBExp : DyadicInterval precision := ⟨738187668517019050850553078864002934613595944449, 776436318258027888796895818405699250029800786455⟩
def wholeBLog : DyadicInterval precision := ⟨597537428828638861458087364241545117081426549103, 622731905639341251634754391147859036246665954587⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨738187668517019050850553078864002935163351758337, scale precision, 776436318258027888796895818405699249480044972567, scale precision,
    0, 128, 0, 128, ⟨-998237214796578743141856264643716752473932880160, -998237214796578743141856264643716752473930783007⟩, ⟨-924407205497376538283585047280249637203088065959, -924407205497376538283585047280249637203085968806⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0060StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0061StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0061StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨215469853832861228733019240262249168447508352861, 215469853832861228733019240262249168447508352862⟩
def centerDExp : DyadicInterval precision := ⟨1088285489568234168416510694967649720478852956927, 1088285489568234168416510694967649722677876212480⟩
def centerDLog : DyadicInterval precision := ⟨813392086659747652895796213383370383407954793069, 813392086659747652895796213383370385606978048622⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1088285489568234168416510694967649721028608770815, scale precision, 1088285489568234168416510694967649722128120398592, scale precision,
    0, 128, 0, 128, ⟨-430939707665722457466038480524498337633306585522, -430939707665722457466038480524498337633304488369⟩, ⟨-430939707665722457466038480524498336156728923076, -430939707665722457466038480524498336156726825923⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨220015566163561586175537252383320360307282815723, 220015566163561586175537252383320360307282815724⟩
def centerCExp : DyadicInterval precision := ⟨1081536707726478807316248973790450002371416071496, 1081536707726478807316248973790450004570439327049⟩
def centerCLog : DyadicInterval precision := ⟨809518652732157095875767932892631841705419802721, 809518652732157095875767932892631843904443058274⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1081536707726478807316248973790450002921171885384, scale precision, 1081536707726478807316248973790450004020683513161, scale precision,
    0, 128, 0, 128, ⟨-440031132327123172351074504766640721357462428629, -440031132327123172351074504766640721357460331476⟩, ⟨-440031132327123172351074504766640719871670931419, -440031132327123172351074504766640719871668834266⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨446758396143924564664295531329901350112173885284, 446758396143924564664295531329901350112173885285⟩
def centerBExp : DyadicInterval precision := ⟨793021795703973532967486569668771474398587913622, 793021795703973532967486569668771476597611169175⟩
def centerBLog : DyadicInterval precision := ⟨633523233810714225471076050968041106150341188438, 633523233810714225471076050968041108349364443991⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨793021795703973532967486569668771474948343727510, scale precision, 793021795703973532967486569668771476047855355287, scale precision,
    0, 128, 0, 128, ⟨-893516792287849129328591062659802701237522765288, -893516792287849129328591062659802701237520668135⟩, ⟨-893516792287849129328591062659802699211174873003, -893516792287849129328591062659802699211172775850⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨207364037900146833805279022757379167895402526013, 223590532296792858273138350117122513977217811277⟩
def wholeDExp : DyadicInterval precision := ⟨1076258554488359441934578352032876247847469232020, 1100424441361699833197968540687666015087121635409⟩
def wholeDLog : DyadicInterval precision := ⟨806482109433465224369192354012429699430722065898, 820333450761233184846212780159319759056095221943⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1076258554488359441934578352032876248397225045908, scale precision, 1100424441361699833197968540687666014537365821521, scale precision,
    0, 128, 0, 128, ⟨-447181064593585716546276700234245028700975705620, -447181064593585716546276700234245028700973608467⟩, ⟨-414728075800293667610558045514758335060661447385, -414728075800293667610558045514758335060659350232⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨211253010738814688741513314259447908539070264891, 228795830081704859847687774194111259693403688136⟩
def wholeCExp : DyadicInterval precision := ⟨1068619369684015382867667652417372494517590509916, 1094583663264658192859639577095084242298766072314⟩
def wholeCLog : DyadicInterval precision := ⟨802076051312755177186185483652806810775416639633, 816997658858733881976258143282406437393482291798⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1068619369684015382867667652417372495067346323804, scale precision, 1094583663264658192859639577095084241749010258426, scale precision,
    0, 128, 0, 128, ⟨-457591660163409719695375548388222520138684204871, -457591660163409719695375548388222520138682107718⟩, ⟨-422506021477629377483026628518895816344100820128, -422506021477629377483026628518895816344098722975⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨428630511643972528454174557156597790389313925336, 465022579048418109843785227554347945752391019349⟩
def wholeBExp : DyadicInterval precision := ⟨773446873391979796336261237240710449401174426331, 812940491109497126172575141947222965256521559932⟩
def wholeBLog : DyadicInterval precision := ⟨620778321863009711612674686753872664233332323840, 646378881863236975591500270143725018767912030097⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨773446873391979796336261237240710449950930240219, scale precision, 812940491109497126172575141947222964706765746044, scale precision,
    0, 128, 0, 128, ⟨-930045158096836219687570455108695892543599132396, -930045158096836219687570455108695892543597035243⟩, ⟨-857261023287945056908349114313195579790279775400, -857261023287945056908349114313195579790277678247⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0061StableWitnesses

end


