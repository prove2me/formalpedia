-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0045StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0045StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:14:29.520897+00:00
-- url     : https://prove2.me/theorems/73393e34-3f58-4f37-8704-7bff073dead6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0045StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0046StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0045StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0046StableWitnesses, GeneralCK.Certificates.E8TAxisProd0047StableWitnesses, GeneralCK.Certificates.E8TAxisProd0048StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0045StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0046StableWitnesses, GeneralCK.Certificates.E8TAxisProd0047StableWitnesses, GeneralCK.Certificates.E8TAxisProd0048StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0045StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0046StableWitnesses, GeneralCK.Certificates.E8TAxisProd0047StableWitnesses, GeneralCK.Certificates.E8TAxisProd0048StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0045StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0046StableWitnesses, GeneralCK/Certificates/E8TAxisProd0047StableWitnesses, GeneralCK/Certificates/E8TAxisProd0048StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0045StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0045StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨91152031099581959275053171704673662682537650095, 91152031099581959275053171704673662682537650096⟩
def centerDExp : DyadicInterval precision := ⟨1290109275795961219083538977138292162718810472007, 1290109275795961219083538977138292164917833727560⟩
def centerDLog : DyadicInterval precision := ⟨924724386421826679470683559697340152094656101669, 924724386421826679470683559697340154293679357222⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1290109275795961219083538977138292163268566285895, scale precision, 1290109275795961219083538977138292164368077913672, scale precision,
    0, 128, 0, 128, ⟨-182304062199163918550106343409347325987867795357, -182304062199163918550106343409347325987865698204⟩, ⟨-182304062199163918550106343409347324742284902180, -182304062199163918550106343409347324742282805027⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨95605098803788763341350581278455531298037607367, 95605098803788763341350581278455531298037607368⟩
def centerCExp : DyadicInterval precision := ⟨1282271480798318499511278933935593100725746229493, 1282271480798318499511278933935593102924769485046⟩
def centerCLog : DyadicInterval precision := ⟨920555448300610376672772997936908751406845418770, 920555448300610376672772997936908753605868674323⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1282271480798318499511278933935593101275502043381, scale precision, 1282271480798318499511278933935593102375013671158, scale precision,
    0, 128, 0, 128, ⟨-191210197607577526682701162556911063222674479182, -191210197607577526682701162556911063222672382029⟩, ⟨-191210197607577526682701162556911061969478047440, -191210197607577526682701162556911061969475950287⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨187644691682397333940043399819643548548804667376, 187644691682397333940043399819643548548804667377⟩
def centerBExp : DyadicInterval precision := ⟨1130523737175883657858269274576851861196910964489, 1130523737175883657858269274576851863395934220042⟩
def centerBLog : DyadicInterval precision := ⟨837404108347216864497003198437610963611949278355, 837404108347216864497003198437610965810972533908⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1130523737175883657858269274576851861746666778377, scale precision, 1130523737175883657858269274576851862846178406154, scale precision,
    0, 128, 0, 128, ⟨-375289383364794667880086799639287097808315515570, -375289383364794667880086799639287097808313418417⟩, ⟨-375289383364794667880086799639287096386905251090, -375289383364794667880086799639287096386903153937⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨87177733031446937316788780256552774640368349422, 95127887983717436574352739463518235552733806995⟩
def wholeDExp : DyadicInterval precision := ⟨1283109131137421329953040259475754029680231733945, 1297144843488804201115883427901752815058870064878⟩
def wholeDLog : DyadicInterval precision := ⟨921001564088758741914731412563984559982408490529, 928456516721811008488201258314450140012001202708⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1283109131137421329953040259475754030229987547833, scale precision, 1297144843488804201115883427901752814509114250990, scale precision,
    0, 128, 0, 128, ⟨-190255775967434873148705478927036471731657817199, -190255775967434873148705478927036471731655720046⟩, ⟨-174355466062893874633577560513105548661324251571, -174355466062893874633577560513105548661322154418⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨90993029701810910407875348998086064286689244830, 100219368350368952704840798909014325337853247827⟩
def wholeCExp : DyadicInterval precision := ⟨1274200186272218274311544412594467246427509635515, 1290390016496021039718744254842648934381969425033⟩
def wholeCLog : DyadicInterval precision := ⟨916249846460174679731666506774178024610076895028, 924873492554936324319240729026000008420487948520⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1274200186272218274311544412594467246977265449403, scale precision, 1290390016496021039718744254842648933832213611145, scale precision,
    0, 128, 0, 128, ⟨-200438736700737905409681597818028651306274884265, -200438736700737905409681597818028651306272787112⟩, ⟨-181986059403621820815750697996172127950723587821, -181986059403621820815750697996172127950721490668⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨178941488288963307887393676781801825848635031175, 196362957030864100704840821354813837189552226138⟩
def wholeBExp : DyadicInterval precision := ⟨1117116097011558262308417944608218308768982331719, 1144068714643020262775623526541037564997604254333⟩
def wholeBLog : DyadicInterval precision := ⟨829824651958942518772624474895005256789833599495, 845021496309331141540576730411200641999362073450⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1117116097011558262308417944608218309318738145607, scale precision, 1144068714643020262775623526541037564447848440445, scale precision,
    0, 128, 0, 128, ⟨-392725914061728201409681642709627675098340524212, -392725914061728201409681642709627675098338427059⟩, ⟨-357882976577926615774787353563603650994980232899, -357882976577926615774787353563603650994978135746⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0045StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0046StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0046StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨83204925566128923103386656610767262849242461462, 83204925566128923103386656610767262849242461463⟩
def centerDExp : DyadicInterval precision := ⟨1304216119040613274645831231453751221172217307273, 1304216119040613274645831231453751223371240562826⟩
def centerDLog : DyadicInterval precision := ⟨932198010221342921271619522959115051456047294407, 932198010221342921271619522959115053655070549960⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1304216119040613274645831231453751221721973121161, scale precision, 1304216119040613274645831231453751222821484748938, scale precision,
    0, 128, 0, 128, ⟨-166409851132257846206773313221534526314541094883, -166409851132257846206773313221534526314538997730⟩, ⟨-166409851132257846206773313221534525082430848122, -166409851132257846206773313221534525082428750969⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨87654568751724973805813341132355117337779426775, 87654568751724973805813341132355117337779426776⟩
def centerCExp : DyadicInterval precision := ⟨1296298695634767445520797352068850309414102192404, 1296298695634767445520797352068850311613125447957⟩
def centerCLog : DyadicInterval precision := ⟨928008167802464311998713280127141989085575937581, 928008167802464311998713280127141991284599193134⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1296298695634767445520797352068850309963858006292, scale precision, 1296298695634767445520797352068850311063369634069, scale precision,
    0, 128, 0, 128, ⟨-175309137503449947611626682264710235295377714824, -175309137503449947611626682264710235295375617671⟩, ⟨-175309137503449947611626682264710234055742089430, -175309137503449947611626682264710234055739992277⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨171538997309695458050826399408847654410041355932, 171538997309695458050826399408847654410041355933⟩
def centerBExp : DyadicInterval precision := ⟨1155717006400697186159529709117728916448560790677, 1155717006400697186159529709117728918647584046230⟩
def centerBLog : DyadicInterval precision := ⟨851540628411629728550962471590575925564239217522, 851540628411629728550962471590575927763262473075⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1155717006400697186159529709117728916998316604565, scale precision, 1155717006400697186159529709117728918097828232342, scale precision,
    0, 128, 0, 128, ⟨-343077994619390916101652798817695309515296358059, -343077994619390916101652798817695309515294260906⟩, ⟨-343077994619390916101652798817695308124871162824, -343077994619390916101652798817695308124869065671⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨79233540548598202161862116954926444096871869275, 87177733031446937316788780256552774640368349423⟩
def wholeDExp : DyadicInterval precision := ⟨1297144843488804201115883427901752812859846809325, 1311323390486212533981803318339124544384464892381⟩
def wholeDLog : DyadicInterval precision := ⟨928456516721811008488201258314450137812977947155, 935948922676490622602857379124864312093157411787⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1297144843488804201115883427901752813409602623213, scale precision, 1311323390486212533981803318339124543834709078493, scale precision,
    0, 128, 0, 128, ⟨-174355466062893874633577560513105549900151243272, -174355466062893874633577560513105549900149146119⟩, ⟨-158467081097196404323724233909852887581028634911, -158467081097196404323724233909852887581026537758⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨83046043307877945193488452689099171381514026011, 92265110963307647404461616612304866415569488541⟩
def wholeCExp : DyadicInterval precision := ⟨1288145676821355523500604517963587326484695435302, 1304499716849142180193281360330416129368699833206⟩
def wholeCLog : DyadicInterval precision := ⟨923681060288146433929791633710211402355123346172, 932347865502707798009618186313188911522430125812⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1288145676821355523500604517963587327034451249190, scale precision, 1304499716849142180193281360330416128818944019318, scale precision,
    0, 128, 0, 128, ⟨-184530221926615294808923233224609733454880831210, -184530221926615294808923233224609733454878734057⟩, ⟨-166092086615755890386976905378198342147107907400, -166092086615755890386976905378198342147105810247⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨162861817784200237565871966520572794999609887195, 180229928962105787157545353371120701075525520159⟩
def wholeBExp : DyadicInterval precision := ⟨1142053299983816464308427514740350847627507001189, 1169522177914865128352659833859980549396374698749⟩
def wholeBLog : DyadicInterval precision := ⟨843890583993838071132742594415801782037440985357, 859229422313229852746433528080764617965719577944⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1142053299983816464308427514740350848177262815077, scale precision, 1169522177914865128352659833859980548846618884861, scale precision,
    0, 128, 0, 128, ⟨-360459857924211574315090706742241402854582320051, -360459857924211574315090706742241402854580222898⟩, ⟨-325723635568400475131743933041145589312214593157, -325723635568400475131743933041145589312212496004⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0046StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0047StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0047StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨91152031099581959275053171704673662682537650095, 91152031099581959275053171704673662682537650096⟩
def centerDExp : DyadicInterval precision := ⟨1290109275795961219083538977138292162718810472007, 1290109275795961219083538977138292164917833727560⟩
def centerDLog : DyadicInterval precision := ⟨924724386421826679470683559697340152094656101669, 924724386421826679470683559697340154293679357222⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1290109275795961219083538977138292163268566285895, scale precision, 1290109275795961219083538977138292164368077913672, scale precision,
    0, 128, 0, 128, ⟨-182304062199163918550106343409347325987867795357, -182304062199163918550106343409347325987865698204⟩, ⟨-182304062199163918550106343409347324742284902180, -182304062199163918550106343409347324742282805027⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨94332588625358148704839561374588024261247268443, 94332588625358148704839561374588024261247268444⟩
def centerCExp : DyadicInterval precision := ⟨1284506339791058690826854556169547883558108223354, 1284506339791058690826854556169547885757131478907⟩
def centerCLog : DyadicInterval precision := ⟨921745386551646615460454213758147287264051259801, 921745386551646615460454213758147289463074515354⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1284506339791058690826854556169547884107864037242, scale precision, 1284506339791058690826854556169547885207375665019, scale precision,
    0, 128, 0, 128, ⟨-188665177250716297409679122749176049148003609240, -188665177250716297409679122749176049148001512087⟩, ⟨-188665177250716297409679122749176047896987561688, -188665177250716297409679122749176047896985464535⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨186354394939751837427234698441450889506082638516, 186354394939751837427234698441450889506082638517⟩
def centerBExp : DyadicInterval precision := ⟨1132521681823606051222395651713336554434258106725, 1132521681823606051222395651713336556633281362278⟩
def centerBLog : DyadicInterval precision := ⟨838530206342391626211135227062589235496945292736, 838530206342391626211135227062589237695968548289⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1132521681823606051222395651713336554984013920613, scale precision, 1132521681823606051222395651713336556083525548390, scale precision,
    0, 128, 0, 128, ⟨-372708789879503674854469396882901779721617663297, -372708789879503674854469396882901779721615566144⟩, ⟨-372708789879503674854469396882901778302714987921, -372708789879503674854469396882901778302712890768⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨87177733031446937316788780256552774640368349422, 95127887983717436574352739463518235552733806995⟩
def wholeDExp : DyadicInterval precision := ⟨1283109131137421329953040259475754029680231733945, 1297144843488804201115883427901752815058870064878⟩
def wholeDLog : DyadicInterval precision := ⟨921001564088758741914731412563984559982408490529, 928456516721811008488201258314450140012001202708⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1283109131137421329953040259475754030229987547833, scale precision, 1297144843488804201115883427901752814509114250990, scale precision,
    0, 128, 0, 128, ⟨-190255775967434873148705478927036471731657817199, -190255775967434873148705478927036471731655720046⟩, ⟨-174355466062893874633577560513105548661324251571, -174355466062893874633577560513105548661322154418⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨89721107783089542081821969135731415731772400073, 98946240501651460655236999370633104625806438932⟩
def wholeCExp : DyadicInterval precision := ⟨1276422056781884267024825639853428502586462838091, 1292637984625462899532542257724932185206364071202⟩
def wholeCLog : DyadicInterval precision := ⟨917436360793557022095544909352086773358411617360, 926066878178749407023252589922216529214153353053⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1276422056781884267024825639853428503136218651979, scale precision, 1292637984625462899532542257724932184656608257314, scale precision,
    0, 128, 0, 128, ⟨-197892481003302921310473998741266209881083636605, -197892481003302921310473998741266209881081539452⟩, ⟨-179442215566179084163643938271462830841972731046, -179442215566179084163643938271462830841970633893⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨177653362642421903985383099533020772929530993741, 195070384091725537299207625964822441604096874998⟩
def wholeBExp : DyadicInterval precision := ⟨1119093832522548353760792784395684184277949257102, 1146087191884889049255178951498653941075489630982⟩
def wholeBLog : DyadicInterval precision := ⟨830945157630913290200624245407414187859975664587, 846153250717279300440655301955098260381673404805⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1119093832522548353760792784395684184827705070990, scale precision, 1146087191884889049255178951498653940525733817094, scale precision,
    0, 128, 0, 128, ⟨-390140768183451074598415251929644883926158742953, -390140768183451074598415251929644883926156645800⟩, ⟨-355306725284843807970766199066041545158009025667, -355306725284843807970766199066041545158006928514⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0047StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0048StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0048StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨83204925566128923103386656610767262849242461462, 83204925566128923103386656610767262849242461463⟩
def centerDExp : DyadicInterval precision := ⟨1304216119040613274645831231453751221172217307273, 1304216119040613274645831231453751223371240562826⟩
def centerDLog : DyadicInterval precision := ⟨932198010221342921271619522959115051456047294407, 932198010221342921271619522959115053655070549960⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1304216119040613274645831231453751221721973121161, scale precision, 1304216119040613274645831231453751222821484748938, scale precision,
    0, 128, 0, 128, ⟨-166409851132257846206773313221534526314541094883, -166409851132257846206773313221534526314538997730⟩, ⟨-166409851132257846206773313221534525082430848122, -166409851132257846206773313221534525082428750969⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨86383054471940091388009192239777962201422527440, 86383054471940091388009192239777962201422527441⟩
def centerCExp : DyadicInterval precision := ⟨1298556232799797858122153693852693087705713630123, 1298556232799797858122153693852693089904736885676⟩
def centerCLog : DyadicInterval precision := ⟨929204064589109079093218318114702277542861425686, 929204064589109079093218318114702279741884681239⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1298556232799797858122153693852693088255469444011, scale precision, 1298556232799797858122153693852693089354981071788, scale precision,
    0, 128, 0, 128, ⟨-172766108943880182776018384479555925021586364246, -172766108943880182776018384479555925021584267093⟩, ⟨-172766108943880182776018384479555923784105842670, -172766108943880182776018384479555923784103745517⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨170252638495234241027575132082892085370180792619, 170252638495234241027575132082892085370180792620⟩
def centerBExp : DyadicInterval precision := ⟨1157753235436019582024414064717411361587718781511, 1157753235436019582024414064717411363786742037064⟩
def centerBLog : DyadicInterval precision := ⟨852677252977656561354010438411630507207655061058, 852677252977656561354010438411630509406678316611⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1157753235436019582024414064717411362137474595399, scale precision, 1157753235436019582024414064717411363236986223176, scale precision,
    0, 128, 0, 128, ⟨-340505276990468482055150264165784171434352507943, -340505276990468482055150264165784171434350410790⟩, ⟨-340505276990468482055150264165784170046372759689, -340505276990468482055150264165784170046370662536⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨79233540548598202161862116954926444096871869275, 87177733031446937316788780256552774640368349423⟩
def wholeDExp : DyadicInterval precision := ⟨1297144843488804201115883427901752812859846809325, 1311323390486212533981803318339124544384464892381⟩
def wholeDLog : DyadicInterval precision := ⟨928456516721811008488201258314450137812977947155, 935948922676490622602857379124864312093157411787⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1297144843488804201115883427901752813409602623213, scale precision, 1311323390486212533981803318339124543834709078493, scale precision,
    0, 128, 0, 128, ⟨-174355466062893874633577560513105549900151243272, -174355466062893874633577560513105549900149146119⟩, ⟨-158467081097196404323724233909852887581028634911, -158467081097196404323724233909852887581026537758⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨81775066651422335775660018154838453034717622374, 90993029701810910407875348998086064286689244831⟩
def wholeCExp : DyadicInterval precision := ⟨1290390016496021039718744254842648932182946169480, 1306770574892044410141964846722889503619682838667⟩
def wholeCLog : DyadicInterval precision := ⟨924873492554936324319240729026000006221464692967, 933547250713536054780546866575375687641838410735⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1290390016496021039718744254842648932732701983368, scale precision, 1306770574892044410141964846722889503069927024779, scale precision,
    0, 128, 0, 128, ⟨-181986059403621820815750697996172129196035488655, -181986059403621820815750697996172129196033391502⟩, ⟨-163550133302844671551320036309676905454585425416, -163550133302844671551320036309676905454583328263⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨161577436401748847597890018140472027124415234621, 178941488288963307887393676781801825848635031176⟩
def wholeBExp : DyadicInterval precision := ⟨1144068714643020262775623526541037562798580998780, 1171579559607242623643396951962840840340700091833⟩
def wholeBLog : DyadicInterval precision := ⟨845021496309331141540576730411200639800338817897, 860371826143762983574909401721668987473088645056⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1144068714643020262775623526541037563348336812668, scale precision, 1171579559607242623643396951962840839790944277945, scale precision,
    0, 128, 0, 128, ⟨-357882976577926615774787353563603652399561988954, -357882976577926615774787353563603652399559891801⟩, ⟨-323154872803497695195780036280944053563031722542, -323154872803497695195780036280944053563029625389⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0048StableWitnesses

end


