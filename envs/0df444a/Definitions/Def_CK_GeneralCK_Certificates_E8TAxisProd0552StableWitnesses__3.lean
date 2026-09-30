-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0552StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0552StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:18:54.023222+00:00
-- url     : https://prove2.me/theorems/c5e4fad6-de23-43de-86ef-e7bf557a5805
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0552StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0553StableWitnesses, GeneralCK.Certificates.E8TAxisProd05…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0552StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0553StableWitnesses, GeneralCK.Certificates.E8TAxisProd0554StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0552StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0553StableWitnesses, GeneralCK.Certificates.E8TAxisProd0554StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0552StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0553StableWitnesses, GeneralCK.Certificates.E8TAxisProd0554StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0552StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0553StableWitnesses, GeneralCK/Certificates/E8TAxisProd0554StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0552StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0552StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨610560585232978838677636124558316081121189005779, 610560585232978838677636124558316081121189005780⟩
def centerDExp : DyadicInterval precision := ⟨633775439067498409587600235923873634184078301602, 633775439067498409587600235923873636383101557155⟩
def centerDLog : DyadicInterval precision := ⟨526464129056309766045029930608943037858964020595, 526464129056309766045029930608943040057987276148⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨633775439067498409587600235923873634733834115490, scale precision, 633775439067498409587600235923873635833345743267, scale precision,
    1, 128, 1, 128, ⟨-1221121170465957677355272249116632163510129390304, -1221121170465957677355272249116632163510127293151⟩, ⟨-1221121170465957677355272249116632160974628729968, -1221121170465957677355272249116632160974626632815⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨614144328244983549838110834227368845516570208150, 614144328244983549838110834227368845516570208151⟩
def centerCExp : DyadicInterval precision := ⟨630674891085369468090553265643349339401452989439, 630674891085369468090553265643349341600476244992⟩
def centerCLog : DyadicInterval precision := ⟨524299827211668529025060635728943056823684634528, 524299827211668529025060635728943059022707890081⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨630674891085369468090553265643349339951208803327, scale precision, 630674891085369468090553265643349341050720431104, scale precision,
    1, 128, 1, 128, ⟨-1228288656489967099676221668454737692307124357628, -1228288656489967099676221668454737692307122260475⟩, ⟨-1228288656489967099676221668454737689759158572127, -1228288656489967099676221668454737689759156474974⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1447950281753149197661591598776287711463890697154, 1447950281753149197661591598776287711463890697155⟩
def centerBExp : DyadicInterval precision := ⟨201494912385301975023102806332455267538560517632, 201494912385301975023102806332455269737583773185⟩
def centerBLog : DyadicInterval precision := ⟨188762727933107812431538691987869099241029589294, 188762727933107812431538691987869101440052844847⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨201494912385301975023102806332455268088316331520, scale precision, 201494912385301975023102806332455269187827959297, scale precision,
    2, 128, 2, 128, ⟨-2895900563506298395323183197552575426915322438906, -2895900563506298395323183197552575426915320341753⟩, ⟨-2895900563506298395323183197552575418940242446873, -2895900563506298395323183197552575418940240349720⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨605149690269836019889894242842311313124295302837, 615985792935344704096715461380744242879788980550⟩
def wholeDExp : DyadicInterval precision := ⟨629087614762237432177832619094338710911004411584, 638485690296710810307667032247350013857008098659⟩
def wholeDLog : DyadicInterval precision := ⟨523190605620864448684409715253755539004186757001, 529745944986552956313550471423206443941852059644⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨629087614762237432177832619094338711460760225472, scale precision, 638485690296710810307667032247350013307252284771, scale precision,
    1, 128, 1, 128, ⟨-1231971585870689408193430922761488487036776340025, -1231971585870689408193430922761488487036774242872⟩, ⟨-1210299380539672039779788485684622624990193800798, -1210299380539672039779788485684622624990191703645⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨608535712406863613780026749995151366517249283174, 619768358204472053069880958419278713734905123127⟩
def wholeCExp : DyadicInterval precision := ⟨625839699225833222945352786936769248667543916984, 635534033480750035766323538988544263535032008355⟩
def wholeCLog : DyadicInterval precision := ⟨520918267806775538561289918659906465733135984853, 527690272676836317108677112656713215382271874195⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨625839699225833222945352786936769249217299730872, scale precision, 635534033480750035766323538988544262985276194467, scale precision,
    1, 128, 1, 128, ⟨-1239536716408944106139761916838557428753636886470, -1239536716408944106139761916838557428753634789317⟩, ⟨-1217071424813727227560053499990302731770257293032, -1217071424813727227560053499990302731770255195879⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1431906225539347023523513417378235562564215287215, 1464075479239015014715438862741379860894144557564⟩
def wholeBExp : DyadicInterval precision := ⟨197097300242025195590307555409347231419250945626, 205967771976471162095358347048491587053432597456⟩
def wholeBLog : DyadicInterval precision := ⟨184892827984385156534905626802871801670217849601, 192688362139709359013393414519646659683008570444⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨197097300242025195590307555409347231969006759514, scale precision, 205967771976471162095358347048491586503676783568, scale precision,
    2, 128, 2, 128, ⟨-2928150958478030029430877725482759725864799690435, -2928150958478030029430877725482759725864797593282⟩, ⟨-2863812451078694047047026834756471121227486274030, -2863812451078694047047026834756471121227484176877⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0552StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0553StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0553StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨599752983055354003753543703993878049904129928193, 599752983055354003753543703993878049904129928194⟩
def centerDExp : DyadicInterval precision := ⟨643218459949503680164771431112985722806282727100, 643218459949503680164771431112985725005305982653⟩
def centerDLog : DyadicInterval precision := ⟨533036044781290419045280039370268756967708914819, 533036044781290419045280039370268759166732170372⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨643218459949503680164771431112985723356038540988, scale precision, 643218459949503680164771431112985724455550168765, scale precision,
    1, 128, 1, 128, ⟨-1199505966110708007507087407987756101057399529178, -1199505966110708007507087407987756101057397432025⟩, ⟨-1199505966110708007507087407987756098559122280751, -1199505966110708007507087407987756098559120183598⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨603317918974122819874558796509708596200073201546, 603317918974122819874558796509708596200073201547⟩
def centerCExp : DyadicInterval precision := ⟨640088188470087348316078221589157897134469605605, 640088188470087348316078221589157899333492861158⟩
def centerCLog : DyadicInterval precision := ⟨530860790070791768785846409390101267857598104815, 530860790070791768785846409390101270056621360368⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨640088188470087348316078221589157897684225419493, scale precision, 640088188470087348316078221589157898783737047270, scale precision,
    1, 128, 1, 128, ⟨-1206635837948245639749117593019417193655394832580, -1206635837948245639749117593019417193655392735427⟩, ⟨-1206635837948245639749117593019417191144900070755, -1206635837948245639749117593019417191144897973602⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1416488546313951723573033775428849424342035323447, 1416488546313951723573033775428849424342035323448⟩
def centerBExp : DyadicInterval precision := ⟨210359530799513583718861172688413789639438777306, 210359530799513583718861172688413791838462032859⟩
def centerBLog : DyadicInterval precision := ⟨196532585562590214046018095597047100033706047690, 196532585562590214046018095597047102232729303243⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨210359530799513583718861172688413790189194591194, scale precision, 210359530799513583718861172688413791288706218971, scale precision,
    2, 128, 2, 128, ⟨-2832977092627903447146067550857698852503575471109, -2832977092627903447146067550857698852503573373956⟩, ⟨-2832977092627903447146067550857698844864567919833, -2832977092627903447146067550857698844864565822680⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨594370338528145575810628189240163754488538282193, 605149690269836019889894242842311313124295302838⟩
def wholeDExp : DyadicInterval precision := ⟨638485690296710810307667032247350011657984843106, 647973841382699837641744325099416508397027426555⟩
def wholeDLog : DyadicInterval precision := ⟨529745944986552956313550471423206441742828804091, 536334420746670162773197764634792507319087016290⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨638485690296710810307667032247350012207740656994, scale precision, 647973841382699837641744325099416507847271612667, scale precision,
    1, 128, 1, 128, ⟨-1210299380539672039779788485684622627506989507705, -1210299380539672039779788485684622627506987410552⟩, ⟨-1188740677056291151621256378480327507737106227057, -1188740677056291151621256378480327507737104129904⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨597738702711983722292570871011260839992564352992, 608912281716833680520920355875808042733653141171⟩
def wholeCExp : DyadicInterval precision := ⟨635206615497407151070568431781365640304679082678, 644993907297760795738916604289247294941441866270⟩
def wholeCLog : DyadicInterval precision := ⟨527462065171355565909245144997282656082598127847, 534268382225324109892801122666003399835436195865⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨635206615497407151070568431781365640854434896566, scale precision, 644993907297760795738916604289247294391686052382, scale precision,
    1, 128, 1, 128, ⟨-1217824563433667361041840711751616086732201307974, -1217824563433667361041840711751616086732199210821⟩, ⟨-1195477405423967444585141742022521678739429581213, -1195477405423967444585141742022521678739427484060⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1400606551798693916152074311465248844794460113009, 1432453390941048766246276862493698424305845950650⟩
def wholeBExp : DyadicInterval precision := ⟨205813606899057869148378700710727644451985041010, 214981487872288050538812633139589334235584965651⟩
def wholeBLog : DyadicInterval precision := ⟨192553233466269960304064690861213724693636694386, 200567416827322955963145623872257001132334316428⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨205813606899057869148378700710727645001740854898, scale precision, 214981487872288050538812633139589333685829151763, scale precision,
    2, 128, 2, 128, ⟨-2864906781882097532492553724987396852515560309453, -2864906781882097532492553724987396852515558212300⟩, ⟨-2801213103597387832304148622930497685851534255450, -2801213103597387832304148622930497685851532158297⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0553StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0554StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0554StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2690879721921964209596752456793030551114759613, 2690879721921964209596752456793030551114759614⟩
def centerAExp : DyadicInterval precision := ⟨1456129774494643406468543322663438605390699476049, 1456129774494643406468543322663438607589722731602⟩
def centerALog : DyadicInterval precision := ⟨1010347336766062430648993258467353377680688109432, 1010347336766062430648993258467353379879711364985⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1456129774494643406468543322663438605940455289937, scale precision, 1456129774494643406468543322663438607039966917714, scale precision,
    0, 128, 0, 128, ⟨-5381759443843928419193504913586061654014506435, -5381759443843928419193504913586061654012409282⟩, ⟨-5381759443843928419193504913586060550446629170, -5381759443843928419193504913586060550444532017⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨610560585232978838677636124558316081121189005779, 610560585232978838677636124558316081121189005780⟩
def centerDExp : DyadicInterval precision := ⟨633775439067498409587600235923873634184078301602, 633775439067498409587600235923873636383101557155⟩
def centerDLog : DyadicInterval precision := ⟨526464129056309766045029930608943037858964020595, 526464129056309766045029930608943040057987276148⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨633775439067498409587600235923873634733834115490, scale precision, 633775439067498409587600235923873635833345743267, scale precision,
    1, 128, 1, 128, ⟨-1221121170465957677355272249116632163510129390304, -1221121170465957677355272249116632163510127293151⟩, ⟨-1221121170465957677355272249116632160974628729968, -1221121170465957677355272249116632160974626632815⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨613766796694194987540873882931927818718468364992, 613766796694194987540873882931927818718468364993⟩
def centerCExp : DyadicInterval precision := ⟨631000804077203115593529500514992098497637739521, 631000804077203115593529500514992100696660995074⟩
def centerCLog : DyadicInterval precision := ⟨524527477827445801539877111403732519987135440780, 524527477827445801539877111403732522186158696333⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨631000804077203115593529500514992099047393553409, scale precision, 631000804077203115593529500514992100146905181186, scale precision,
    1, 128, 1, 128, ⟨-1227533593388389975081747765863855638710262656975, -1227533593388389975081747765863855638710260559822⟩, ⟨-1227533593388389975081747765863855636163612900149, -1227533593388389975081747765863855636163610802996⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1447400422228783608129351305790327250713348410472, 1447400422228783608129351305790327250713348410473⟩
def centerBExp : DyadicInterval precision := ⟨201646585962951582114595701539889829993831386334, 201646585962951582114595701539889832192854641887⟩
def centerBLog : DyadicInterval precision := ⟨188896018091748609342345082034947707609895073724, 188896018091748609342345082034947709808918329277⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨201646585962951582114595701539889830543587200222, scale precision, 201646585962951582114595701539889831643098827999, scale precision,
    2, 128, 2, 128, ⟨-2894800844457567216258702611580654505411238536517, -2894800844457567216258702611580654505411236439364⟩, ⟨-2894800844457567216258702611580654497442157202526, -2894800844457567216258702611580654497442155105373⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 2849167218250950044280193223065006085312260898⟩
def wholeAExp : DyadicInterval precision := ⟨1455814397256041217437249255499380272227928609805, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1010189349275934740575240882696318021950304507166, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455814397256041217437249255499380272777684423693, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-5698334436501900088560386446130012722529043537, -5698334436501900088560386446130012722526946384⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨605149690269836019889894242842311313124295302837, 615985792935344704096715461380744242879788980550⟩
def wholeDExp : DyadicInterval precision := ⟨629087614762237432177832619094338710911004411584, 638485690296710810307667032247350013857008098659⟩
def wholeDLog : DyadicInterval precision := ⟨523190605620864448684409715253755539004186757001, 529745944986552956313550471423206443941852059644⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨629087614762237432177832619094338711460760225472, scale precision, 638485690296710810307667032247350013307252284771, scale precision,
    1, 128, 1, 128, ⟨-1231971585870689408193430922761488487036776340025, -1231971585870689408193430922761488487036774242872⟩, ⟨-1210299380539672039779788485684622624990193800798, -1210299380539672039779788485684622624990191703645⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨608159212134720796709109283542950176025056824843, 619389786072100452127649471854453118622074952992⟩
def wholeCExp : DyadicInterval precision := ⟨626164005192663221377113910155124220749121345018, 635861560158921722602223075614600782054276828306⟩
def wholeCLog : DyadicInterval precision := ⟨521145320697870792118799839398555590827517653863, 527918520295825513163945792379178015789783601251⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨626164005192663221377113910155124221298877158906, scale precision, 635861560158921722602223075614600781504521014418, scale precision,
    1, 128, 1, 128, ⟨-1238779572144200904255298943708906238527311620883, -1238779572144200904255298943708906238527309523730⟩, ⟨-1216318424269441593418218567085900350786523576433, -1216318424269441593418218567085900350786521479280⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1431359156020392063513118659368570536463277655873, 1463522860761660264482712880005358491770520480491⟩
def wholeBExp : DyadicInterval precision := ⟨197246408257913603404982497217460305430320457468, 206122025485996102388036974538431080424782185860⟩
def wholeBLog : DyadicInterval precision := ⟨185024211050801155979718007442820925978613454329, 192823555822176457392766213663046267134091357739⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨197246408257913603404982497217460305980076271356, scale precision, 206122025485996102388036974538431079875026371972, scale precision,
    2, 128, 2, 128, ⟨-2927045721523320528965425760010716987614469907312, -2927045721523320528965425760010716987614467810159⟩, ⟨-2862718312040784127026237318737141069028530323390, -2862718312040784127026237318737141069028528226237⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0554StableWitnesses

end


