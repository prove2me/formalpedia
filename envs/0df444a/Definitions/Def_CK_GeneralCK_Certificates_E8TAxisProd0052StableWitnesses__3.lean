-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0052StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0052StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:25:43.609344+00:00
-- url     : https://prove2.me/theorems/6eaf313a-f9a6-427b-a390-91e7bb8ffea8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0052StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0053StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0052StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0053StableWitnesses, GeneralCK.Certificates.E8TAxisProd0054StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0052StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0053StableWitnesses, GeneralCK.Certificates.E8TAxisProd0054StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0052StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0053StableWitnesses, GeneralCK.Certificates.E8TAxisProd0054StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0052StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0053StableWitnesses, GeneralCK/Certificates/E8TAxisProd0054StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0052StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0052StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨70501165010384356241207145761763522412751346678, 70501165010384356241207145761763522412751346679⟩
def centerCExp : DyadicInterval precision := ⟨1327087533514189467637507755375978127658721178284, 1327087533514189467637507755375978129857744433837⟩
def centerCLog : DyadicInterval precision := ⟨944234362936310345551894453489616133257166305955, 944234362936310345551894453489616135456189561508⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1327087533514189467637507755375978128208476992172, scale precision, 1327087533514189467637507755375978129307988619949, scale precision,
    0, 128, 0, 128, ⟨-141002330020768712482414291523527045430941591239, -141002330020768712482414291523527045430939494086⟩, ⟨-141002330020768712482414291523527044220065892629, -141002330020768712482414291523527044220063795476⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨138185076934533291384460203659823029201118705568, 138185076934533291384460203659823029201118705569⟩
def centerBExp : DyadicInterval precision := ⟨1209690199028879381733560717407416113431654050014, 1209690199028879381733560717407416115630677305567⟩
def centerBLog : DyadicInterval precision := ⟨881373656190846597166423362808244089366623664363, 881373656190846597166423362808244091565646919916⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1209690199028879381733560717407416113981409863902, scale precision, 1209690199028879381733560717407416115080921491679, scale precision,
    0, 128, 0, 128, ⟨-276370153869066582768920407319646059066432501109, -276370153869066582768920407319646059066430403956⟩, ⟨-276370153869066582768920407319646057738044418317, -276370153869066582768920407319646057738042321164⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨65899215223265784759171254738762616571610796756, 75104735860464000039654512611793576370486962765⟩
def wholeCExp : DyadicInterval precision := ⟨1318753450381580412863595815200602612723987019566, 1335471322730389028688153556972687529559782755593⟩
def wholeCLog : DyadicInterval precision := ⟨939859923763028657024581547280875579540660982398, 948621721121932708792572285570935425958108880262⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1318753450381580412863595815200602613273742833454, scale precision, 1335471322730389028688153556972687529010026941705, scale precision,
    0, 128, 0, 128, ⟨-150209471720928000079309025223587153350238989224, -150209471720928000079309025223587153350236892071⟩, ⟨-131798430446531569518342509477525232541585595712, -131798430446531569518342509477525232541583498559⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨129554310903328861618553401759095070205044128551, 146826895900187411258321839193929239531070706026⟩
def wholeBExp : DyadicInterval precision := ⟨1195468726228719232833614102862965392793557276194, 1224062337940262835884041942228948969667752895904⟩
def wholeBLog : DyadicInterval precision := ⟨873571808438861005643647858596413659277366314966, 889216072642414855396552704879363497020149421829⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1195468726228719232833614102862965393343313090082, scale precision, 1224062337940262835884041942228948969117997082016, scale precision,
    0, 128, 0, 128, ⟨-293653791800374822516643678387858479734237852586, -293653791800374822516643678387858479734235755433⟩, ⟨-259108621806657723237106803518190139753693796050, -259108621806657723237106803518190139753691698897⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0052StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0053StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0053StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨93060243661692956280971654262782151528896450744, 93060243661692956280971654262782151528896450745⟩
def centerCExp : DyadicInterval precision := ⟨1286744802979717547961719690940519328670988088579, 1286744802979717547961719690940519330870011344132⟩
def centerCLog : DyadicInterval precision := ⟨922936273448315628379293384984004475445510603067, 922936273448315628379293384984004477644533858620⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1286744802979717547961719690940519329220743902467, scale precision, 1286744802979717547961719690940519330320255530244, scale precision,
    0, 128, 0, 128, ⟨-186120487323385912561943308525564303682213819701, -186120487323385912561943308525564303682211722548⟩, ⟨-186120487323385912561943308525564302433374080431, -186120487323385912561943308525564302433371983278⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨185064426463719250346989728470101064961088652396, 185064426463719250346989728470101064961088652397⟩
def centerBExp : DyadicInterval precision := ⟨1134522647737562452972969427658519787540728101147, 1134522647737562452972969427658519789739751356700⟩
def centerBLog : DyadicInterval precision := ⟨839657138242594801957739836814033177473451261900, 839657138242594801957739836814033179672474517453⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1134522647737562452972969427658519788090483915035, scale precision, 1134522647737562452972969427658519789189995542812, scale precision,
    0, 128, 0, 128, ⟨-370128852927438500693979456940202130630378426531, -370128852927438500693979456940202130630376329378⟩, ⟨-370128852927438500693979456940202129213978280209, -370128852927438500693979456940202129213976183056⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨88449342971355302470485152083509965479350191858, 97673285984124066128015298065358904033793501768⟩
def wholeCExp : DyadicInterval precision := ⟨1278647498360097009011004557740837223106938943214, 1294889590511360688191276887190755564896280638910⟩
def wholeCLog : DyadicInterval precision := ⟨918623817328114892230994065911876786226587449185, 927261218964308206823929778080634461381454879404⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1278647498360097009011004557740837223656694757102, scale precision, 1294889590511360688191276887190755564346524825022, scale precision,
    0, 128, 0, 128, ⟨-195346571968248132256030596130717808695962192100, -195346571968248132256030596130717808695960094947⟩, ⟨-176898685942710604940970304167019930338209130852, -176898685942710604940970304167019930338207033699⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨176365549723902348143424292968104815592821027151, 193778155013554683299889988710244792947684043084⟩
def wholeBExp : DyadicInterval precision := ⟨1121074541873184918683835318833754694517347845501, 1148108738982243371695955789645787237386737500354⟩
def wholeBLog : DyadicInterval precision := ⟨832066487812359628690065743459079145574258516651, 847285848658893358182028839792376454409643592298⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1121074541873184918683835318833754695067103659389, scale precision, 1148108738982243371695955789645787236836981686466, scale precision,
    0, 128, 0, 128, ⟨-387556310027109366599779977420489586612064583726, -387556310027109366599779977420489586612062486573⟩, ⟨-352731099447804696286848585936209630485823482272, -352731099447804696286848585936209630485821385119⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0053StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0054StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0054StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨85111691433159158394016801150788008928105402287, 85111691433159158394016801150788008928105402288⟩
def centerCExp : DyadicInterval precision := ⟨1300817432297474119005210366547864007590082087739, 1300817432297474119005210366547864009789105343292⟩
def centerCLog : DyadicInterval precision := ⟨930400921300965307774708698647047635767719069352, 930400921300965307774708698647047637966742324905⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1300817432297474119005210366547864008139837901627, scale precision, 1300817432297474119005210366547864009239349529404, scale precision,
    0, 128, 0, 128, ⟨-170223382866318316788033602301576018473876563187, -170223382866318316788033602301576018473874466034⟩, ⟨-170223382866318316788033602301576017238547143114, -170223382866318316788033602301576017238545045961⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨168966579214564108507863584541420384906064698992, 168966579214564108507863584541420384906064698993⟩
def centerBExp : DyadicInterval precision := ⟨1159792576655074951020382451607634707890152449828, 1159792576655074951020382451607634710089175705381⟩
def centerBLog : DyadicInterval precision := ⟨853814729464122702015098104940602687386091102459, 853814729464122702015098104940602689585114358012⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1159792576655074951020382451607634708439908263716, scale precision, 1159792576655074951020382451607634709539419891493, scale precision,
    0, 128, 0, 128, ⟨-337933158429128217015727169082840770504900031660, -337933158429128217015727169082840770504897934507⟩, ⟨-337933158429128217015727169082840769119360861462, -337933158429128217015727169082840769119358764309⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨80504233142141611642933172006386671113699818848, 89721107783089542081821969135731415731772400074⟩
def wholeCExp : DyadicInterval precision := ⟨1292637984625462899532542257724932183007340815649, 1309045129588817403044812046386576906128566349739⟩
def wholeCLog : DyadicInterval precision := ⟨926066878178749407023252589922216527015130097500, 934747602489940959407298357260346042603396706178⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1292637984625462899532542257724932183557096629537, scale precision, 1309045129588817403044812046386576905578810535851, scale precision,
    0, 128, 0, 128, ⟨-179442215566179084163643938271462832085118966398, -179442215566179084163643938271462832085116869245⟩, ⟨-161008466284283223285866344012773341613618163450, -161008466284283223285866344012773341613616066297⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨160293339111948018245674211080042528839685011782, 177653362642421903985383099533020772929530993742⟩
def wholeBExp : DyadicInterval precision := ⟨1146087191884889049255178951498653938876466375429, 1173640104298104188087122023740267537433953667589⟩
def wholeBLog : DyadicInterval precision := ⟨846153250717279300440655301955098258182650149252, 861515091957746564471801711065111147886994049810⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1146087191884889049255178951498653939426222189317, scale precision, 1173640104298104188087122023740267536884197853701, scale precision,
    0, 128, 0, 128, ⟨-355306725284843807970766199066041546560117046452, -355306725284843807970766199066041546560114949299⟩, ⟨-320586678223896036491348422160085056994775326659, -320586678223896036491348422160085056994773229506⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0054StableWitnesses

end


