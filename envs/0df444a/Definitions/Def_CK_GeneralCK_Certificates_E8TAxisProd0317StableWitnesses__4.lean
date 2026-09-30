-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0317StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0317StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T20:34:29.586683+00:00
-- url     : https://prove2.me/theorems/9fc545a5-16b4-49a7-a28a-ab295ae06f17
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0317StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0318StableWitnesses, GeneralCK.Certificates.E8TAxisProd03…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0317StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0318StableWitnesses, GeneralCK.Certificates.E8TAxisProd0319StableWitnesses, GeneralCK.Certificates.E8TAxisProd0320StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0317StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0318StableWitnesses, GeneralCK.Certificates.E8TAxisProd0319StableWitnesses, GeneralCK.Certificates.E8TAxisProd0320StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0317StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0318StableWitnesses, GeneralCK.Certificates.E8TAxisProd0319StableWitnesses, GeneralCK.Certificates.E8TAxisProd0320StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0317StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0318StableWitnesses, GeneralCK/Certificates/E8TAxisProd0319StableWitnesses, GeneralCK/Certificates/E8TAxisProd0320StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0317StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0317StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨760487303942681831516138360832277681860072236778, 760487303942681831516138360832277681860072236779⟩
def centerCExp : DyadicInterval precision := ⟨516216704403002518413644104738906840288761384112, 516216704403002518413644104738906842487784639665⟩
def centerCLog : DyadicInterval precision := ⟨442074140844737307681688053133711852521255069147, 442074140844737307681688053133711854720278324700⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨516216704403002518413644104738906840838517198000, scale precision, 516216704403002518413644104738906841938028825777, scale precision,
    1, 128, 1, 128, ⟨-1520974607885363663032276721664555365276602365310, -1520974607885363663032276721664555365276600268157⟩, ⟨-1520974607885363663032276721664555362163688678956, -1520974607885363663032276721664555362163686581803⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1882435215842619314603002293018139982040769318565, 1882435215842619314603002293018139982040769318566⟩
def centerBExp : DyadicInterval precision := ⟨111184481911468805560869929417553274427286167370, 111184481911468805560869929417553276626309422923⟩
def centerBLog : DyadicInterval precision := ⟨107158228877570430275510672984494586242697179546, 107158228877570430275510672984494588441720435099⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨111184481911468805560869929417553274977041981258, scale precision, 111184481911468805560869929417553276076553609035, scale precision,
    3, 128, 3, 128, ⟨-3764870431685238629206004586036279971307988991555, -3764870431685238629206004586036279971307986894402⟩, ⟨-3764870431685238629206004586036279956855090379859, -3764870431685238629206004586036279956855088282706⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨754450111391181169946783292707038783088639758433, 766543284056398443880337599899263821150731954392⟩
def wholeCExp : DyadicInterval precision := ⟨511956319337700100780229335505113421708133106588, 520499161256261253169269658260438628791576231262⟩
def wholeCLog : DyadicInterval precision := ⟨438922389724849711869975308050039347991091157722, 445235385327620924409651644573357758047416259455⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨511956319337700100780229335505113422257888920476, scale precision, 520499161256261253169269658260438628241820417374, scale precision,
    1, 128, 1, 128, ⟨-1533086568112796887760675199798527643870874283473, -1533086568112796887760675199798527643870872186320⟩, ⟨-1508900222782362339893566585414077564633629620471, -1508900222782362339893566585414077564633627523318⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1864676445364227704420480937126220622707374834964, 1900244131801229544260039015145987342780720627064⟩
def wholeBExp : DyadicInterval precision := ⟨108507588580371119240580468199774099806251192523, 113919596832567931978058761836681717786899758154⟩
def wholeBLog : DyadicInterval precision := ⟨104668464835658082301776798276656091145791785431, 109697771207304949602193661804549991142590568401⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨108507588580371119240580468199774100356007006411, scale precision, 113919596832567931978058761836681717237143944266, scale precision,
    3, 128, 3, 128, ⟨-3800488263602459088520078030291974692966168853562, -3800488263602459088520078030291974692966166756409⟩, ⟨-3729352890728455408840961874252441238361802459645, -3729352890728455408840961874252441238361800362492⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0317StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0318StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0318StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨771800280684947697843895494949491898355966741439, 771800280684947697843895494949491898355966741440⟩
def centerCExp : DyadicInterval precision := ⟨508286538888610112829933452911219759672273834611, 508286538888610112829933452911219761871297090164⟩
def centerCLog : DyadicInterval precision := ⟨436202097101630295875005730523255864306187687261, 436202097101630295875005730523255866505210942814⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨508286538888610112829933452911219760222029648499, scale precision, 508286538888610112829933452911219761321541276276, scale precision,
    1, 128, 1, 128, ⟨-1543600561369895395687790989898983798292674843579, -1543600561369895395687790989898983798292672746426⟩, ⟨-1543600561369895395687790989898983795131194219335, -1543600561369895395687790989898983795131192122182⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1916879315460695075160041272238346506213555328608, 1916879315460695075160041272238346506213555328609⟩
def centerBExp : DyadicInterval precision := ⟨106065370013270102981484580921591039718499941678, 106065370013270102981484580921591041917523197231⟩
def centerBLog : DyadicInterval precision := ⟨102393264560009716418977170590845533299195003763, 102393264560009716418977170590845535498218259316⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨106065370013270102981484580921591040268255755566, scale precision, 106065370013270102981484580921591041367767383343, scale precision,
    3, 128, 3, 128, ⟨-3833758630921390150320082544476693020002336513185, -3833758630921390150320082544476693020002334416032⟩, ⟨-3833758630921390150320082544476693004851886898391, -3833758630921390150320082544476693004851884801238⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨765727936829315915692114799486607819349242224112, 777891647546635597138833563221306289939779184490⟩
def wholeCExp : DyadicInterval precision := ⟨504067192084870322198404859237889764720391716032, 512527861803536836009769446247064090255970704872⟩
def wholeCLog : DyadicInterval precision := ⟨433068157986980978319671954459641923757447260598, 439345600825487142105703652106794861331213386012⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨504067192084870322198404859237889765270147529920, scale precision, 512527861803536836009769446247064089706214890984, scale precision,
    1, 128, 1, 128, ⟨-1555783295093271194277667126442612581473531480697, -1555783295093271194277667126442612581473529383544⟩, ⟨-1531455873658631831384229598973215637130826288377, -1531455873658631831384229598973215637130824191224⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1899024857815314031772153791710087955717351390865, 1934781404229217960038886135093835683716979535041⟩
def wholeBExp : DyadicInterval precision := ⟨103498527946832056235430089184964057586078781305, 108688787028880017197207872791361147540435506737⟩
def wholeBLog : DyadicInterval precision := ⟨99998139721020937227686094386315152976006686781, 104837130435916099779370170763421163014170775305⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨103498527946832056235430089184964058135834595193, scale precision, 108688787028880017197207872791361146990679692849, scale precision,
    3, 128, 3, 128, ⟨-3869562808458435920077772270187671375197056252195, -3869562808458435920077772270187671375197054155042⟩, ⟨-3798049715630628063544307583420175904042321928794, -3798049715630628063544307583420175904042319831641⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0318StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0319StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0319StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨760080854615659246266083619453782789480831647062, 760080854615659246266083619453782789480831647063⟩
def centerCExp : DyadicInterval precision := ⟨516503908040950815675114709332196376418851083723, 516503908040950815675114709332196378617874339276⟩
def centerCLog : DyadicInterval precision := ⟨442286364245472943289530630308266736193157789904, 442286364245472943289530630308266738392181045457⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨516503908040950815675114709332196376968606897611, scale precision, 516503908040950815675114709332196378068118525388, scale precision,
    1, 128, 1, 128, ⟨-1520161709231318492532167238907565580517255713110, -1520161709231318492532167238907565580517253615957⟩, ⟨-1520161709231318492532167238907565577406072972295, -1520161709231318492532167238907565577406070875142⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1881827243053898046347574435881005334086315585473, 1881827243053898046347574435881005334086315585474⟩
def centerBExp : DyadicInterval precision := ⟨111277024082429065589904070906744595385120223101, 111277024082429065589904070906744597584143478654⟩
def centerBLog : DyadicInterval precision := ⟨107244226047369550167606248061389478356812129349, 107244226047369550167606248061389480555835384902⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨111277024082429065589904070906744595934876036989, scale precision, 111277024082429065589904070906744597034387664766, scale precision,
    3, 128, 3, 128, ⟨-3763654486107796092695148871762010675393071737527, -3763654486107796092695148871762010675393069640374⟩, ⟨-3763654486107796092695148871762010660952192701527, -3763654486107796092695148871762010660952190604374⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨754044920530796484371218244622623171704223431580, 766135567721021778181278960307768552870433322903⟩
def wholeCExp : DyadicInterval precision := ⟨512242040804304655323460144559117784811376524422, 520787850614288707590483953409874766564331098546⟩
def wholeCLog : DyadicInterval precision := ⟨439133973743416442773927028379977702336076428408, 445448245607614205681134431267769453970408322324⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨512242040804304655323460144559117785361132338310, scale precision, 520787850614288707590483953409874766014575284658, scale precision,
    1, 128, 1, 128, ⟨-1532271135442043556362557920615537107309401625858, -1532271135442043556362557920615537107309399528705⟩, ⟨-1508089841061592968742436489245246341865652661844, -1508089841061592968742436489245246341865650564691⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1864070210126666839449572179346572379489540533930, 1899634466240213433072015561106460669947467232107⟩
def wholeBExp : DyadicInterval precision := ⟨108598154258471743876933062012947093973927682184, 114014144422747285173665181337363372992118709800⟩
def wholeBLog : DyadicInterval precision := ⟨104752768843021559259667036334154944073912710114, 109785479376142509125929713387053799952818913871⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨108598154258471743876933062012947094523683496072, scale precision, 114014144422747285173665181337363372442362895912, scale precision,
    3, 128, 3, 128, ⟨-3799268932480426866144031122212921347293486875065, -3799268932480426866144031122212921347293484777912⟩, ⟨-3728140420253333678899144358693144751931982599104, -3728140420253333678899144358693144751931980501951⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0319StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0320StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0320StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3640605953424817106904235978836837760282897367, 3640605953424817106904235978836837760282897368⟩
def centerAExp : DyadicInterval precision := ⟨1454238532866739696576544033316540574868034513622, 1454238532866739696576544033316540577067057769175⟩
def centerALog : DyadicInterval precision := ⟨1009399667722954236284698895375438337347134637797, 1009399667722954236284698895375438339546157893350⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454238532866739696576544033316540575417790327510, scale precision, 1454238532866739696576544033316540576517301955287, scale precision,
    0, 128, 0, 128, ⟨-7281211906849634213808471957673676073068378631, -7281211906849634213808471957673676073066281478⟩, ⟨-7281211906849634213808471957673674968065307991, -7281211906849634213808471957673674968063210838⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨745000746231477256788872225997272556554271720183, 745000746231477256788872225997272556554271720184⟩
def centerDExp : DyadicInterval precision := ⟨527273459613343376350322664808293438125402667750, 527273459613343376350322664808293440324425923303⟩
def centerDLog : DyadicInterval precision := ⟨450222147616224759094825146719602335307459476714, 450222147616224759094825146719602337506482732267⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨527273459613343376350322664808293438675158481638, scale precision, 527273459613343376350322664808293439774670109415, scale precision,
    1, 128, 1, 128, ⟨-1490001492462954513577744451994545114632362931693, -1490001492462954513577744451994545114632360834540⟩, ⟨-1490001492462954513577744451994545111584726046197, -1490001492462954513577744451994545111584723949044⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨749643904606130611430372427508761209429370060612, 749643904606130611430372427508761209429370060613⟩
def centerCExp : DyadicInterval precision := ⟨523933808609891397798093887215157987387431662628, 523933808609891397798093887215157989586454918181⟩
def centerCLog : DyadicInterval precision := ⟨447765857741351120453937630426455284453183345257, 447765857741351120453937630426455286652206600810⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨523933808609891397798093887215157987937187476516, scale precision, 523933808609891397798093887215157989036699104293, scale precision,
    1, 128, 1, 128, ⟨-1499287809212261222860744855017522420392272713151, -1499287809212261222860744855017522420392270615998⟩, ⟨-1499287809212261222860744855017522417325209626453, -1499287809212261222860744855017522417325207529300⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1848782861418956739957218445848683500118928041698, 1848782861418956739957218445848683500118928041699⟩
def centerBExp : DyadicInterval precision := ⟨116424450779786123696601754258538557466436897582, 116424450779786123696601754258538559665460153135⟩
def centerBLog : DyadicInterval precision := ⟨112019652396388945422021722101473280703708176778, 112019652396388945422021722101473282902731432331⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨116424450779786123696601754258538558016192711470, scale precision, 116424450779786123696601754258538559115704339247, scale precision,
    3, 128, 3, 128, ⟨-3697565722837913479914436891697367007139062306224, -3697565722837913479914436891697367007139060209071⟩, ⟨-3697565722837913479914436891697366993336651957732, -3697565722837913479914436891697366993336649860579⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3482318024844347500022322904444928295572395252, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1454553569581723058392238696431353226318692924653⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009557569928173087760872372803888452026676915366⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1454553569581723058392238696431353225768937110765, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-6964636049688695000044645808889856038763968154, -6964636049688695000044645808889856038761871001⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨739212305620516788391447838602016614455786978945, 750806424999049798752938234956163650116084001298⟩
def wholeDExp : DyadicInterval precision := ⟨523100967242339682629524513379347095252573454615, 531466696428681553786643034174516971757505971701⟩
def wholeDLog : DyadicInterval precision := ⟨447152665109602019123525890115620509603294783509, 453300409610535438784277685833236609207550076241⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨523100967242339682629524513379347095802329268503, scale precision, 531466696428681553786643034174516971207750157813, scale precision,
    1, 128, 1, 128, ⟨-1501612849998099597505876469912327301768142166202, -1501612849998099597505876469912327301768140069049⟩, ⟨-1478424611241033576782895677204033227399779389680, -1478424611241033576782895677204033227399777292527⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨743640176853088305713584024449537137481511845036, 755666190130685222728180668015462529393116495009⟩
def wholeCExp : DyadicInterval precision := ⟨519633693078741343203556538531702535130332350657, 528256093321136938591583775534217481548198040725⟩
def wholeCLog : DyadicInterval precision := ⟨444597060961543393279078530102797404567547498132, 450944082492356533225239494812990820276615264244⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨519633693078741343203556538531702535680088164545, scale precision, 528256093321136938591583775534217480998442226837, scale precision,
    1, 128, 1, 128, ⟨-1511332380261370445456361336030925060332455988465, -1511332380261370445456361336030925060332453891312⟩, ⟨-1487280353706176611427168048899074273442040821399, -1487280353706176611427168048899074273442038724246⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1831122853160934571055545818495106763469077934986, 1866495511738476614912647845304495047761287388660⟩
def wholeBExp : DyadicInterval precision := ⟨113636368145152325120593715857054953688938665576, 119272346884735835250754085466297055252112241659⟩
def wholeBLog : DyadicInterval precision := ⟨109434999324583928422048527764199786465846336340, 114655044078304241023680946016243566414708239283⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨113636368145152325120593715857054954238694479464, scale precision, 119272346884735835250754085466297054702356427771, scale precision,
    3, 128, 3, 128, ⟨-3732991023476953229825295690608990102593102940104, -3732991023476953229825295690608990102593100842951⟩, ⟨-3662245706321869142111091636990213520201733572185, -3662245706321869142111091636990213520201731475032⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0320StableWitnesses

end


