-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0008StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0008StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:26:54.416378+00:00
-- url     : https://prove2.me/theorems/9b55f5ab-c68f-49ee-92e0-991ed5d50024
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0008StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0009StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0008StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0009StableWitnesses, GeneralCK.Certificates.E8TAxisProd0010StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0008StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0009StableWitnesses, GeneralCK.Certificates.E8TAxisProd0010StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0008StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0009StableWitnesses, GeneralCK.Certificates.E8TAxisProd0010StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0008StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0009StableWitnesses, GeneralCK/Certificates/E8TAxisProd0010StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0008StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0008StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨46713116010029980514615076818759635730538499645, 46713116010029980514615076818759635730538499646⟩
def centerDExp : DyadicInterval precision := ⟨1370998907719543522785095389796795666922964041466, 1370998907719543522785095389796795669121987297019⟩
def centerDLog : DyadicInterval precision := ⟨967069028121789112925837016599212484240830577134, 967069028121789112925837016599212486439853832687⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1370998907719543522785095389796795667472719855354, scale precision, 1370998907719543522785095389796795668572231483131, scale precision,
    0, 128, 0, 128, ⟨-93426232020059961029230153637519272047124482774, -93426232020059961029230153637519272047122385621⟩, ⟨-93426232020059961029230153637519270875031612960, -93426232020059961029230153637519270875029515807⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨51150932281662749119088084783521713939892005221, 51150932281662749119088084783521713939892005222⟩
def centerCExp : DyadicInterval precision := ⟨1362698124759510805395731213262134349470631228868, 1362698124759510805395731213262134351669654484421⟩
def centerCLog : DyadicInterval precision := ⟨962779737214960709662293153331854104001802646158, 962779737214960709662293153331854106200825901711⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1362698124759510805395731213262134350020387042756, scale precision, 1362698124759510805395731213262134351119898670533, scale precision,
    0, 128, 0, 128, ⟨-102301864563325498238176169567043428469401355933, -102301864563325498238176169567043428469399258780⟩, ⟨-102301864563325498238176169567043427290168762108, -102301864563325498238176169567043427290166664955⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨97991508486213100906881016662061699711450274347, 97991508486213100906881016662061699711450274348⟩
def centerBExp : DyadicInterval precision := ⟨1278090802681005969735304411430051443822198035137, 1278090802681005969735304411430051446021221290690⟩
def centerBLog : DyadicInterval precision := ⟨918326864766376145407801088101513658280181778148, 918326864766376145407801088101513660479205033701⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1278090802681005969735304411430051444371953849025, scale precision, 1278090802681005969735304411430051445471465476802, scale precision,
    0, 128, 0, 128, ⟨-195983016972426201813762033324123400051549437037, -195983016972426201813762033324123400051547339884⟩, ⟨-195983016972426201813762033324123398794253757505, -195983016972426201813762033324123398794251660352⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨44336132104644388932745897738796280177181849964, 49090387085558120317010643908319081445949446152⟩
def wholeDExp : DyadicInterval precision := ⟨1366546035068101924073630463753607682869303317284, 1375465749469112915336031076552653134255992540413⟩
def wholeDLog : DyadicInterval precision := ⟨964769645884129960942701944278613210671962341551, 969371994805781330198871946178310256493558400824⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1366546035068101924073630463753607683419059131172, scale precision, 1375465749469112915336031076552653133706236726525, scale precision,
    0, 128, 0, 128, ⟨-98180774171116240634021287816638163479856000544, -98180774171116240634021287816638163479853903391⟩, ⟨-88672264209288777865491795477592559770221506523, -88672264209288777865491795477592559770219409370⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨48139443258654111572486032703577432783283710516, 54162925877756763919340827554361401275146674865⟩
def wholeCExp : DyadicInterval precision := ⟨1357092943435704973170072444971207084218168621413, 1368325512272832093860385387564911615354723601256⟩
def wholeCLog : DyadicInterval precision := ⟨959876216767851444361231668919552839199260992169, 965688969487382976922535666450008845585304741129⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1357092943435704973170072444971207084767924435301, scale precision, 1368325512272832093860385387564911614804967787368, scale precision,
    0, 128, 0, 128, ⟨-108325851755513527838681655108722803142345978868, -108325851755513527838681655108722803142343881715⟩, ⟨-96278886517308223144972065407154864979377033855, -96278886517308223144972065407154864979374936702⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨92583156438057309662723508651133081399695069698, 103402961001705903159541306379016428074403636523⟩
def wholeBExp : DyadicInterval precision := ⟨1268661074025871623046630242737151198263298966636, 1287585157761878472691080512611594150905643582338⟩
def wholeBLog : DyadicInterval precision := ⟨913287671186015957064045568243077573118744489431, 923383100972513773832431775171399220618462243061⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1268661074025871623046630242737151198813054780524, scale precision, 1287585157761878472691080512611594150355887768450, scale precision,
    0, 128, 0, 128, ⟨-206805922003411806319082612758032856782128787252, -206805922003411806319082612758032856782126690099⟩, ⟨-185166312876114619325447017302266162175378851945, -185166312876114619325447017302266162175376754792⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0008StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0009StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0009StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨54638551894507817015462628165339991774672950346, 54638551894507817015462628165339991774672950347⟩
def centerCExp : DyadicInterval precision := ⟨1356209935601794162540585984315866242507156352424, 1356209935601794162540585984315866244706179607977⟩
def centerCLog : DyadicInterval precision := ⟨959418286566615773605534512956967188799387591442, 959418286566615773605534512956967190998410846995⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1356209935601794162540585984315866243056912166312, scale precision, 1356209935601794162540585984315866244156423794089, scale precision,
    0, 128, 0, 128, ⟨-109277103789015634030925256330679984141784005687, -109277103789015634030925256330679984141781908534⟩, ⟨-109277103789015634030925256330679982956909892854, -109277103789015634030925256330679982956907795701⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨106269161551675414289443474824466055497369109813, 106269161551675414289443474824466055497369109814⟩
def centerBExp : DyadicInterval precision := ⟨1263694791208872452167360945316496888187587059415, 1263694791208872452167360945316496890386610314968⟩
def centerBLog : DyadicInterval precision := ⟨910626716228728383469297278499603122347795776565, 910626716228728383469297278499603124546819032118⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1263694791208872452167360945316496888737342873303, scale precision, 1263694791208872452167360945316496889836854501080, scale precision,
    0, 128, 0, 128, ⟨-212538323103350828578886949648932111630548664364, -212538323103350828578886949648932111630546567211⟩, ⟨-212538323103350828578886949648932110358929872042, -212538323103350828578886949648932110358927774889⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨51626475909575562598122397028042009565357232054, 57651166903258272846568912508060285708089093758⟩
def wholeCExp : DyadicInterval precision := ⟨1350630293579732954838529998654005142815150413311, 1361811623389207099593779473574397854440907878544⟩
def wholeCLog : DyadicInterval precision := ⟨956521346850492119777299553570157691252604864889, 962320907563890103076833485319333026979979193586⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1350630293579732954838529998654005143364906227199, scale precision, 1361811623389207099593779473574397853891152064656, scale precision,
    0, 128, 0, 128, ⟨-115302333806516545693137825016120572011063732575, -115302333806516545693137825016120572011061635422⟩, ⟨-103252951819151125196244794056084018540715392015, -103252951819151125196244794056084018540713294862⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨100855997974081054332202374750186544677787710248, 111685688823663682104164597513308723070171042185⟩
def wholeBExp : DyadicInterval precision := ⟨1254362564991884505726197553118043777945372906018, 1273090587334595101171992503582187426125266470464⟩
def wholeBLog : DyadicInterval precision := ⟨905613327040268922296823991053019242482330402065, 915656942067084075958202759333488411830290691733⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1254362564991884505726197553118043778495128719906, scale precision, 1273090587334595101171992503582187425575510656576, scale precision,
    0, 128, 0, 128, ⟨-223371377647327364208329195026617446780882833790, -223371377647327364208329195026617446780880736637⟩, ⟨-201711995948162108664404749500373088724459539828, -201711995948162108664404749500373088724457442675⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0009StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0010StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0010StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨46713116010029980514615076818759635730538499645, 46713116010029980514615076818759635730538499646⟩
def centerDExp : DyadicInterval precision := ⟨1370998907719543522785095389796795666922964041466, 1370998907719543522785095389796795669121987297019⟩
def centerDLog : DyadicInterval precision := ⟨967069028121789112925837016599212484240830577134, 967069028121789112925837016599212486439853832687⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1370998907719543522785095389796795667472719855354, scale precision, 1370998907719543522785095389796795668572231483131, scale precision,
    0, 128, 0, 128, ⟨-93426232020059961029230153637519272047124482774, -93426232020059961029230153637519272047122385621⟩, ⟨-93426232020059961029230153637519270875031612960, -93426232020059961029230153637519270875029515807⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨49882877121642235696902406834484653250547420191, 49882877121642235696902406834484653250547420192⟩
def centerCExp : DyadicInterval precision := ⟨1365064836463403128950644412386945863580599859199, 1365064836463403128950644412386945865779623114752⟩
def centerCLog : DyadicInterval precision := ⟨964003979410866161092024153970374903728856392000, 964003979410866161092024153970374905927879647553⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1365064836463403128950644412386945864130355673087, scale precision, 1365064836463403128950644412386945865229867300864, scale precision,
    0, 128, 0, 128, ⟨-99765754243284471393804813668969307089689925424, -99765754243284471393804813668969307089687828271⟩, ⟨-99765754243284471393804813668969305912501852494, -99765754243284471393804813668969305912499755341⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨96718682497106144074805298734848581172671486269, 96718682497106144074805298734848581172671486270⟩
def centerBExp : DyadicInterval precision := ⟨1280318928527868251721071046493254387181035325497, 1280318928527868251721071046493254389380058581050⟩
def centerBLog : DyadicInterval precision := ⟨919515029113501723532667659916250725268267792895, 919515029113501723532667659916250727467291048448⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1280318928527868251721071046493254387730791139385, scale precision, 1280318928527868251721071046493254388830302767162, scale precision,
    0, 128, 0, 128, ⟨-193437364994212288149610597469697162972897831518, -193437364994212288149610597469697162972895734365⟩, ⟨-193437364994212288149610597469697161717790210710, -193437364994212288149610597469697161717788113557⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨44336132104644388932745897738796280177181849964, 49090387085558120317010643908319081445949446152⟩
def wholeDExp : DyadicInterval precision := ⟨1366546035068101924073630463753607682869303317284, 1375465749469112915336031076552653134255992540413⟩
def wholeDLog : DyadicInterval precision := ⟨964769645884129960942701944278613210671962341551, 969371994805781330198871946178310256493558400824⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1366546035068101924073630463753607683419059131172, scale precision, 1375465749469112915336031076552653133706236726525, scale precision,
    0, 128, 0, 128, ⟨-98180774171116240634021287816638163479856000544, -98180774171116240634021287816638163479853903391⟩, ⟨-88672264209288777865491795477592559770221506523, -88672264209288777865491795477592559770219409370⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨46871591652396955948239255283142047275791395945, 52894654640312737718564223508938723181660032365⟩
def wholeCExp : DyadicInterval precision := ⟨1359450322131803465594110234910581442617532847657, 1370701615716012189539119176421333098610924879644⟩
def wholeCLog : DyadicInterval precision := ⟨961098057212024705716880693696126327979971930321, 966915624602095365704810787008635854487439275214⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1359450322131803465594110234910581443167288661545, scale precision, 1370701615716012189539119176421333098061169065756, scale precision,
    0, 128, 0, 128, ⟨-105789309280625475437128447017877446954346036430, -105789309280625475437128447017877446954343939277⟩, ⟨-93743183304793911896478510566284093965410297723, -93743183304793911896478510566284093965408200570⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨91311034991450526690257298210518105305139512278, 102129390020906529768254950722841265361436076311⟩
def wholeBExp : DyadicInterval precision := ⟨1270874056444511995859724187879660953585646933157, 1289828591772333900582106418481172348582963384926⟩
def wholeBLog : DyadicInterval precision := ⟨914471837727390744515614782897821294433016360830, 924575295181394674888129935513667209445563708692⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1270874056444511995859724187879660954135402747045, scale precision, 1289828591772333900582106418481172348033207571038, scale precision,
    0, 128, 0, 128, ⟨-204258780041813059536509901445682531355090861206, -204258780041813059536509901445682531355088764053⟩, ⟨-182622069982901053380514596421036209987353098762, -182622069982901053380514596421036209987351001609⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0010StableWitnesses

end


