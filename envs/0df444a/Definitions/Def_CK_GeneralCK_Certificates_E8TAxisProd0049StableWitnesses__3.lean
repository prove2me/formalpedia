-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0049StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0049StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:46:15.756973+00:00
-- url     : https://prove2.me/theorems/aa76ffbf-7f01-4da3-8448-00d953d186d9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0049StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0050StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0049StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0050StableWitnesses, GeneralCK.Certificates.E8TAxisProd0051StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0049StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0050StableWitnesses, GeneralCK.Certificates.E8TAxisProd0051StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0049StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0050StableWitnesses, GeneralCK.Certificates.E8TAxisProd0051StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0049StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0050StableWitnesses, GeneralCK/Certificates/E8TAxisProd0051StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0049StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0049StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨75263509879409481448600087548378166009129228127, 75263509879409481448600087548378166009129228128⟩
def centerDExp : DyadicInterval precision := ⟨1318466949108280820343673762456176585110097807004, 1318466949108280820343673762456176587309121062557⟩
def centerDLog : DyadicInterval precision := ⟨939709310368699983502098003954865527411730866232, 939709310368699983502098003954865529610754121785⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1318466949108280820343673762456176585659853620892, scale precision, 1318466949108280820343673762456176586759365248669, scale precision,
    0, 128, 0, 128, ⟨-150527019758818962897200175096756332627655912283, -150527019758818962897200175096756332627653815130⟩, ⟨-150527019758818962897200175096756331408863097380, -150527019758818962897200175096756331408861000227⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨79710033899234387173522675869461582209181857027, 79710033899234387173522675869461582209181857028⟩
def centerCExp : DyadicInterval precision := ⟨1310468607721880506151043417000451408641022659350, 1310468607721880506151043417000451410840045914903⟩
def centerCLog : DyadicInterval precision := ⟨935498314003653825063066366640589261682977813757, 935498314003653825063066366640589263882001069310⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1310468607721880506151043417000451409190778473238, scale precision, 1310468607721880506151043417000451410290290101015, scale precision,
    0, 128, 0, 128, ⟨-159420067798468774347045351738923165031480572805, -159420067798468774347045351738923165031478475652⟩, ⟨-159420067798468774347045351738923163805248952458, -159420067798468774347045351738923163805246855305⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨155480465510961978161806974473057541859913965829, 155480465510961978161806974473057541859913965830⟩
def centerBExp : DyadicInterval precision := ⟨1181395447964627495733780322911049524889188799936, 1181395447964627495733780322911049527088212055489⟩
def centerBLog : DyadicInterval precision := ⟨865810041652312317067648650979185486527488236654, 865810041652312317067648650979185488726511492207⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1181395447964627495733780322911049525438944613824, scale precision, 1181395447964627495733780322911049526538456241601, scale precision,
    0, 128, 0, 128, ⟨-310960931021923956323613948946115084399930654501, -310960931021923956323613948946115084399928557348⟩, ⟨-310960931021923956323613948946115083039727305970, -310960931021923956323613948946115083039725208817⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨71294765512122033387053971255115540159908214514, 79233540548598202161862116954926444096871869276⟩
def wholeDExp : DyadicInterval precision := ⟨1311323390486212533981803318339124542185441636828, 1325647089475606555897615027767584925570467038145⟩
def wholeDLog : DyadicInterval precision := ⟨935948922676490622602857379124864309894134156234, 943479230106772831249544853595316780957610367733⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1311323390486212533981803318339124542735197450716, scale precision, 1325647089475606555897615027767584925020711224257, scale precision,
    0, 128, 0, 128, ⟨-158467081097196404323724233909852888806460939344, -158467081097196404323724233909852888806458842191⟩, ⟨-142589531024244066774107942510231079713721761400, -142589531024244066774107942510231079713719664247⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨75104735860464000039654512611793576370486962764, 84317165343519145459876495372617231162663726897⟩
def wholeCExp : DyadicInterval precision := ⟨1302232545947558403334995047843704355078721026318, 1318753450381580412863595815200602614923010275119⟩
def wholeCLog : DyadicInterval precision := ⟨931149445018404426052713782177447150401369534218, 939859923763028657024581547280875581739684237951⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1302232545947558403334995047843704355628476840206, scale precision, 1318753450381580412863595815200602614373254461231, scale precision,
    0, 128, 0, 128, ⟨-168634330687038290919752990745234462942322006816, -168634330687038290919752990745234462942319909663⟩, ⟨-150209471720928000079309025223587152131710958988, -150209471720928000079309025223587152131708861835⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨146826895900187411258321839193929239531070706025, 164146485543706911380212608705974937802842585670⟩
def wholeBExp : DyadicInterval precision := ⟨1167467951615164010714111386766126676457788552734, 1195468726228719232833614102862965394992580531747⟩
def wholeBLog : DyadicInterval precision := ⟨858087878960455589474575508211226886006542865453, 873571808438861005643647858596413661476389570519⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1167467951615164010714111386766126677007544366622, scale precision, 1195468726228719232833614102862965394442824717859, scale precision,
    0, 128, 0, 128, ⟨-328292971087413822760425217411949876293901276284, -328292971087413822760425217411949876293899179131⟩, ⟨-293653791800374822516643678387858478390047068667, -293653791800374822516643678387858478390044971514⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0049StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0050StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0050StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨67327239450709848584332901078869677125813867607, 67327239450709848584332901078869677125813867608⟩
def centerDExp : DyadicInterval precision := ⟨1332864109481912054585740658098352653964589647865, 1332864109481912054585740658098352656163612903418⟩
def centerDLog : DyadicInterval precision := ⟨947258739228882635667763210876156281479935267063, 947258739228882635667763210876156283678958522616⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1332864109481912054585740658098352654514345461753, scale precision, 1332864109481912054585740658098352655613857089530, scale precision,
    0, 128, 0, 128, ⟨-134654478901419697168665802157739354854442691388, -134654478901419697168665802157739354854440594235⟩, ⟨-134654478901419697168665802157739353648814876197, -134654478901419697168665802157739353648812779044⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨71770949169761869064228587061123060814140881512, 71770949169761869064228587061123060814140881513⟩
def centerCExp : DyadicInterval precision := ⟨1324783531289683874622506616576310291771961496406, 1324783531289683874622506616576310293970984751959⟩
def centerCLog : DyadicInterval precision := ⟨943026334553892336369969927401574342167326812112, 943026334553892336369969927401574344366350067665⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1324783531289683874622506616576310292321717310294, scale precision, 1324783531289683874622506616576310293421228938071, scale precision,
    0, 128, 0, 128, ⟨-143541898339523738128457174122246122234773610402, -143541898339523738128457174122246122234771513249⟩, ⟨-143541898339523738128457174122246121021792012800, -143541898339523738128457174122246121021789915647⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨139464632142328242790800863371446902113522637316, 139464632142328242790800863371446902113522637317⟩
def centerBExp : DyadicInterval precision := ⟨1207573867472606940117047865330000286142825871831, 1207573867472606940117047865330000288341849127384⟩
def centerBLog : DyadicInterval precision := ⟨880215278904111554895432601471468087067223483569, 880215278904111554895432601471468089266246739122⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1207573867472606940117047865330000286692581685719, scale precision, 1207573867472606940117047865330000287792093313496, scale precision,
    0, 128, 0, 128, ⟨-278929264284656485581601726742893804892404396759, -278929264284656485581601726742893804892402299606⟩, ⟨-278929264284656485581601726742893803561688249661, -278929264284656485581601726742893803561686152508⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨63360863746962342702697993485127651995684952633, 71294765512122033387053971255115540159908214515⟩
def wholeDExp : DyadicInterval precision := ⟨1325647089475606555897615027767584923371443782592, 1340118310385255731396483422015350660826016558551⟩
def wholeDLog : DyadicInterval precision := ⟨943479230106772831249544853595316778758587112180, 951047895604627342379828868169897142552033311172⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1325647089475606555897615027767584923921199596480, scale precision, 1340118310385255731396483422015350660276260744663, scale precision,
    0, 128, 0, 128, ⟨-142589531024244066774107942510231080925913193810, -142589531024244066774107942510231080925911096657⟩, ⟨-126721727493924685405395986970255303391820141124, -126721727493924685405395986970255303391818043971⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨67168562787799141081803508490387093149476999623, 76374985881963571005968758312776897107481839194⟩
def wholeCExp : DyadicInterval precision := ⟨1316463077984154067335507827451789360010015547518, 1333153561628146457527002171218901945636014531510⟩
def wholeCLog : DyadicInterval precision := ⟨938655443437664033907002461647759913077301408905, 947410119869654349424280900742328520551305108617⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1316463077984154067335507827451789360559771361406, scale precision, 1333153561628146457527002171218901945086258717622, scale precision,
    0, 128, 0, 128, ⟨-152749971763927142011937516625553794825288734955, -152749971763927142011937516625553794825286637802⟩, ⟨-134337125575598282163607016980774185696272022210, -134337125575598282163607016980774185696269925057⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨130832272587569695809414699320324921011080789363, 148108147869986271169876541451996606643262190666⟩
def wholeBExp : DyadicInterval precision := ⟨1193374503935763818484320017448353804443791307183, 1221923527186106999084992706451107776121594480779⟩
def wholeBLog : DyadicInterval precision := ⟨872419399585973093481858653506423335782807107340, 888051653976961835389995825692819351397384016853⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1193374503935763818484320017448353804993547121071, scale precision, 1221923527186106999084992706451107775571838666891, scale precision,
    0, 128, 0, 128, ⟨-296216295739972542339753082903993213959800264825, -296216295739972542339753082903993213959798167672⟩, ⟨-261664545175139391618829398640649841364618186711, -261664545175139391618829398640649841364616089558⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0050StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0051StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0051StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨75263509879409481448600087548378166009129228127, 75263509879409481448600087548378166009129228128⟩
def centerDExp : DyadicInterval precision := ⟨1318466949108280820343673762456176585110097807004, 1318466949108280820343673762456176587309121062557⟩
def centerDLog : DyadicInterval precision := ⟨939709310368699983502098003954865527411730866232, 939709310368699983502098003954865529610754121785⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1318466949108280820343673762456176585659853620892, scale precision, 1318466949108280820343673762456176586759365248669, scale precision,
    0, 128, 0, 128, ⟨-150527019758818962897200175096756332627655912283, -150527019758818962897200175096756332627653815130⟩, ⟨-150527019758818962897200175096756331408863097380, -150527019758818962897200175096756331408861000227⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨78439428245126086554082925388261307301756194395, 78439428245126086554082925388261307301756194396⟩
def centerCExp : DyadicInterval precision := ⟨1312749189857871713252076028239330845665608549794, 1312749189857871713252076028239330847864631805347⟩
def centerCLog : DyadicInterval precision := ⟨936700240385692490460411388451972783003774244107, 936700240385692490460411388451972785202797499660⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1312749189857871713252076028239330846215364363682, scale precision, 1312749189857871713252076028239330847314875991459, scale precision,
    0, 128, 0, 128, ⟨-156878856490252173108165850776522615215564108079, -156878856490252173108165850776522615215562010926⟩, ⟨-156878856490252173108165850776522613991462766653, -156878856490252173108165850776522613991460669500⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨154197686497932961536819931575887586175858849817, 154197686497932961536819931575887586175858849818⟩
def centerBExp : DyadicInterval precision := ⟨1183471121605739864066405757523309461858073347133, 1183471121605739864066405757523309464057096602686⟩
def centerBLog : DyadicInterval precision := ⟨866957422609189959781681149222032679416400610503, 866957422609189959781681149222032681615423866056⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1183471121605739864066405757523309462407829161021, scale precision, 1183471121605739864066405757523309463507340788798, scale precision,
    0, 128, 0, 128, ⟨-308395372995865923073639863151775173030627601552, -308395372995865923073639863151775173030625504399⟩, ⟨-308395372995865923073639863151775171672809894872, -308395372995865923073639863151775171672807797719⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨71294765512122033387053971255115540159908214514, 79233540548598202161862116954926444096871869276⟩
def wholeDExp : DyadicInterval precision := ⟨1311323390486212533981803318339124542185441636828, 1325647089475606555897615027767584925570467038145⟩
def wholeDLog : DyadicInterval precision := ⟨935948922676490622602857379124864309894134156234, 943479230106772831249544853595316780957610367733⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1311323390486212533981803318339124542735197450716, scale precision, 1325647089475606555897615027767584925020711224257, scale precision,
    0, 128, 0, 128, ⟨-158467081097196404323724233909852888806460939344, -158467081097196404323724233909852888806458842191⟩, ⟨-142589531024244066774107942510231079713721761400, -142589531024244066774107942510231079713719664247⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨73834617277284679112775982643791805006453058899, 83046043307877945193488452689099171381514026012⟩
def wholeCExp : DyadicInterval precision := ⟨1304499716849142180193281360330416127169676577653, 1321047569937851251477172603640981665970539907879⟩
def wholeCLog : DyadicInterval precision := ⟨932347865502707798009618186313188909323406870259, 941065380399649366716716759699609517482474486944⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1304499716849142180193281360330416127719432391541, scale precision, 1321047569937851251477172603640981665420784093991, scale precision,
    0, 128, 0, 128, ⟨-166092086615755890386976905378198343378950293799, -166092086615755890386976905378198343378948196646⟩, ⟨-147669234554569358225551965287583609404701193771, -147669234554569358225551965287583609404699096618⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨145545901828368143194963992409340935150072244213, 162861817784200237565871966520572794999609887196⟩
def wholeBExp : DyadicInterval precision := ⟨1169522177914865128352659833859980547197351443196, 1197566200971201614847448590493226407053042434139⟩
def wholeBLog : DyadicInterval precision := ⟨859229422313229852746433528080764615766696322391, 874725096964288106315511122625193817639653271191⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1169522177914865128352659833859980547747107257084, scale precision, 1197566200971201614847448590493226406503286620251, scale precision,
    0, 128, 0, 128, ⟨-325723635568400475131743933041145590686227052780, -325723635568400475131743933041145590686224955627⟩, ⟨-291091803656736286389927984818681869629227285071, -291091803656736286389927984818681869629225187918⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0051StableWitnesses

end


