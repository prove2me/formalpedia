-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0030StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0030StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:22:56.042883+00:00
-- url     : https://prove2.me/theorems/8dfb2505-7512-42b6-96d7-be2aeb675f1e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0030StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0031StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0030StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0031StableWitnesses, GeneralCK.Certificates.E8TAxisProd0032StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0030StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0031StableWitnesses, GeneralCK.Certificates.E8TAxisProd0032StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0030StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0031StableWitnesses, GeneralCK.Certificates.E8TAxisProd0032StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0030StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0031StableWitnesses, GeneralCK/Certificates/E8TAxisProd0032StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0030StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0030StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1582869063071984205522252427078437298396921978, 1582869063071984205522252427078437298396921979⟩
def centerAExp : DyadicInterval precision := ⟨1458339325360928401721230227698749080144113015969, 1458339325360928401721230227698749082343136271522⟩
def centerALog : DyadicInterval precision := ⟨1011453727394019217297123487654775990758863259617, 1011453727394019217297123487654775992957886515170⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458339325360928401721230227698749080693868829857, scale precision, 1458339325360928401721230227698749081793380457634, scale precision,
    0, 128, 0, 128, ⟨-3165738126143968411044504854156875147742815392, -3165738126143968411044504854156875147740718239⟩, ⟨-3165738126143968411044504854156874045846969675, -3165738126143968411044504854156874045844872522⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨26516430580118506903128854198095173449986498411, 26516430580118506903128854198095173449986498412⟩
def centerDExp : DyadicInterval precision := ⟨1409419432745952657043289959536708377428786541143, 1409419432745952657043289959536708379627809796696⟩
def centerDLog : DyadicInterval precision := ⟨986759843010006569375564672930469553051891220885, 986759843010006569375564672930469555250914476438⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1409419432745952657043289959536708377978542355031, scale precision, 1409419432745952657043289959536708379078053982808, scale precision,
    0, 128, 0, 128, ⟨-53032861160237013806257708396190347470044957907, -53032861160237013806257708396190347470042860754⟩, ⟨-53032861160237013806257708396190346329903132893, -53032861160237013806257708396190346329901035740⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨28099942310751110249384095600611694255290659145, 28099942310751110249384095600611694255290659146⟩
def centerCExp : DyadicInterval precision := ⟨1406368576363232663225364689819466610117500367840, 1406368576363232663225364689819466612316523623393⟩
def centerCLog : DyadicInterval precision := ⟨985205915781021060639688910703815380301752160876, 985205915781021060639688910703815382500775416429⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1406368576363232663225364689819466610667256181728, scale precision, 1406368576363232663225364689819466611766767809505, scale precision,
    0, 128, 0, 128, ⟨-56199884621502220498768191201223389081889942729, -56199884621502220498768191201223389081887845576⟩, ⟨-56199884621502220498768191201223387939274791005, -56199884621502220498768191201223387939272693852⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨54638551894507817015462628165339991774672950346, 54638551894507817015462628165339991774672950347⟩
def centerBExp : DyadicInterval precision := ⟨1356209935601794162540585984315866242507156352424, 1356209935601794162540585984315866244706179607977⟩
def centerBLog : DyadicInterval precision := ⟨959418286566615773605534512956967188799387591442, 959418286566615773605534512956967190998410846995⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1356209935601794162540585984315866243056912166312, scale precision, 1356209935601794162540585984315866244156423794089, scale precision,
    0, 128, 0, 128, ⟨-109277103789015634030925256330679984141784005687, -109277103789015634030925256330679984141781908534⟩, ⟨-109277103789015634030925256330679982956909892854, -109277103789015634030925256330679982956907795701⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 1899443256066344012630337314537754309230277492⟩
def wholeAExp : DyadicInterval precision := ⟨1457707683773513925477741956702213444480153619489, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1011137530350683182654731711817158197559546439255, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1457707683773513925477741956702213445029909433377, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-3798886512132688025260674629075509169648258520, -3798886512132688025260674629075509169646161367⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨25328844546563792145364175869944518712165973939, 27704057351801426546684601097727000326331977356⟩
def wholeDExp : DyadicInterval precision := ⟨1407130684310035281592181556628555966755160121473, 1411711825212582109366700862001636148587605359971⟩
def wholeDLog : DyadicInterval precision := ⟨985594243690497964310298929048384649891451124795, 987926367053698422343402489929183443761757914490⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1407130684310035281592181556628555967304915935361, scale precision, 1411711825212582109366700862001636148037849546083, scale precision,
    0, 128, 0, 128, ⟨-55408114703602853093369202195454001223663156543, -55408114703602853093369202195454001223661059390⟩, ⟨-50657689093127584290728351739889036855187787228, -50657689093127584290728351739889036855185690075⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨26595604410632618910187420448248196288174885538, 29604349477686278840500225678485288188201714456⟩
def wholeCExp : DyadicInterval precision := ⟨1403476243515952084979548352513547537911280623745, 1409266736248666684550479720595435494971422906219⟩
def wholeCLog : DyadicInterval precision := ⟨983731203916706700343910178277001906743429159740, 986682107638548151409810827030040259120678595061⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1403476243515952084979548352513547538461036437633, scale precision, 1409266736248666684550479720595435494421667092331, scale precision,
    0, 128, 0, 128, ⟨-59208698955372557681000451356970576948889423950, -59208698955372557681000451356970576948887326797⟩, ⟨-53191208821265237820374840896496392006218138975, -53191208821265237820374840896496392006216041822⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨51943512041210050174785505275781221822567490118, 57334023265324906204241187355924973457080023361⟩
def wholeBExp : DyadicInterval precision := ⟨1351216590245120509540448040538346132899042949318, 1361220929768772064401502272743346534926878143150⟩
def wholeBLog : DyadicInterval precision := ⟨956826021113942824039684340222150680802123648181, 962015100189334406360768571156023684870871269968⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1351216590245120509540448040538346133448798763206, scale precision, 1361220929768772064401502272743346534377122329262, scale precision,
    0, 128, 0, 128, ⟨-114668046530649812408482374711849947508787469731, -114668046530649812408482374711849947508785372578⟩, ⟨-103887024082420100349571010551562443054879881146, -103887024082420100349571010551562443054877783993⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0030StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0031StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0031StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨949721161203312387564849132921065893757597830, 949721161203312387564849132921065893757597831⟩
def centerAExp : DyadicInterval precision := ⟨1459603428780171974367103696970164794154811336420, 1459603428780171974367103696970164796353834591973⟩
def centerALog : DyadicInterval precision := ⟨1012086326714990166522051059359330288660433386585, 1012086326714990166522051059359330290859456642138⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1459603428780171974367103696970164794704567150308, scale precision, 1459603428780171974367103696970164795804078778085, scale precision,
    0, 128, 0, 128, ⟨-1899442322406624775129698265842132337987013411, -1899442322406624775129698265842132337984916258⟩, ⟨-1899442322406624775129698265842131237045475062, -1899442322406624775129698265842131237043377909⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨28891726686864493073308866557218512689468036345, 28891726686864493073308866557218512689468036346⟩
def centerDExp : DyadicInterval precision := ⟨1404845570733299448806020978545363434893586848252, 1404845570733299448806020978545363437092610103805⟩
def centerDLog : DyadicInterval precision := ⟨984429567376195802766596711550261497182688044895, 984429567376195802766596711550261499381711300448⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1404845570733299448806020978545363435443342662140, scale precision, 1404845570733299448806020978545363436542854289917, scale precision,
    0, 128, 0, 128, ⟨-57783453373728986146617733114437025950864056774, -57783453373728986146617733114437025950861959621⟩, ⟨-57783453373728986146617733114437024807010185760, -57783453373728986146617733114437024807008088607⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨29841894027214748099038888242358015388363565254, 29841894027214748099038888242358015388363565255⟩
def centerCExp : DyadicInterval precision := ⟨1403020090827104076937071583717460463043903495226, 1403020090827104076937071583717460465242926750779⟩
def centerCLog : DyadicInterval precision := ⟨983498489736227470284932577857462563874239533484, 983498489736227470284932577857462566073262789037⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1403020090827104076937071583717460463593659309114, scale precision, 1403020090827104076937071583717460464693170936891, scale precision,
    0, 128, 0, 128, ⟨-59683788054429496198077776484716031349399252994, -59683788054429496198077776484716031349397155841⟩, ⟨-59683788054429496198077776484716030204057105176, -59683788054429496198077776484716030204055008023⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨58761219495079248357833439870695880083426023382, 58761219495079248357833439870695880083426023383⟩
def centerBExp : DyadicInterval precision := ⟨1348580165879773931238451259210745085514669156847, 1348580165879773931238451259210745087713692412400⟩
def centerBLog : DyadicInterval precision := ⟨955455480177780754458234389698037602454220516068, 955455480177780754458234389698037604653243771621⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1348580165879773931238451259210745086064424970735, scale precision, 1348580165879773931238451259210745087163936598512, scale precision,
    0, 128, 0, 128, ⟨-117522438990158496715666879741391760762641942352, -117522438990158496715666879741391760762639845199⟩, ⟨-117522438990158496715666879741391759571064248331, -117522438990158496715666879741391759571062151178⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669124066, 1266295042977660303900587558721132456011189596⟩
def wholeAExp : DyadicInterval precision := ⟨1458971240300741788424025014233787498548709353580, 1460235890986607494244084883518378978984154367596⟩
def wholeALog : DyadicInterval precision := ⟨1011769992837296815097311935000023817181636979342, 1012402729061596953461092784027353939761000525628⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458971240300741788424025014233787499098465167468, scale precision, 1460235890986607494244084883518378978434398553708, scale precision,
    0, 128, 0, 128, ⟨-2532590085955320607801175117442265462732722054, -2532590085955320607801175117442265462730624901⟩, ⟨-1266294766337831391377608966682622963106949258, -1266294766337831391377608966682622963104852105⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨27704057351801426546684601097727000326331977355, 30079440410711523067074041860544926828153469389⟩
def wholeDExp : DyadicInterval precision := ⟨1402564082875305177309105820725636620755742670220, 1407130684310035281592181556628555968954183377026⟩
def wholeDLog : DyadicInterval precision := ⟨983265812352629886822137551849227701825556338687, 985594243690497964310298929048384652090474380348⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1402564082875305177309105820725636621305498484108, scale precision, 1407130684310035281592181556628555968404427563138, scale precision,
    0, 128, 0, 128, ⟨-60158880821423046134148083721089854229165250662, -60158880821423046134148083721089854229163153509⟩, ⟨-55408114703602853093369202195454000081666850032, -55408114703602853093369202195454000081664752879⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨28337475584291120905871946103453046799811665547, 31346386032679070535045081536548693653924672479⟩
def wholeCExp : DyadicInterval precision := ⟨1400134481911348653688989637727172604516959305366, 1405911505313178891752593673021890840786746453285⟩
def wholeCLog : DyadicInterval precision := ⟨982025487201383144445202772375046409607479071485, 984972968235820479042473659614684326439985782491⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1400134481911348653688989637727172605066715119254, scale precision, 1405911505313178891752593673021890840236990639397, scale precision,
    0, 128, 0, 128, ⟨-62692772065358141070090163073097387881701714611, -62692772065358141070090163073097387881699617458⟩, ⟨-56674951168582241811743892206906093028131067970, -56674951168582241811743892206906093028128970817⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨56065511042826457004347540631643291441374840829, 61457392076055156498029487396398058132119341836⟩
def wholeBExp : DyadicInterval precision := ⟨1343613622801088944511759060966816953505464641366, 1353564207621696507596780595264882464142047930687⟩
def wholeBLog : DyadicInterval precision := ⟨952870134498076907370678439784785831638046765469, 958045345378871634782107617527196206228262788203⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1343613622801088944511759060966816954055220455254, scale precision, 1353564207621696507596780595264882463592292116799, scale precision,
    0, 128, 0, 128, ⟨-122914784152110312996058974792796116862230857444, -122914784152110312996058974792796116862228760291⟩, ⟨-112131022085652914008695081263286582289155673861, -112131022085652914008695081263286582289153576708⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0031StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0032StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0032StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨949721161203312387564849132921065893757597830, 949721161203312387564849132921065893757597831⟩
def centerAExp : DyadicInterval precision := ⟨1459603428780171974367103696970164794154811336420, 1459603428780171974367103696970164796353834591973⟩
def centerALog : DyadicInterval precision := ⟨1012086326714990166522051059359330288660433386585, 1012086326714990166522051059359330290859456642138⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1459603428780171974367103696970164794704567150308, scale precision, 1459603428780171974367103696970164795804078778085, scale precision,
    0, 128, 0, 128, ⟨-1899442322406624775129698265842132337987013411, -1899442322406624775129698265842132337984916258⟩, ⟨-1899442322406624775129698265842131237045475062, -1899442322406624775129698265842131237043377909⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨26516430580118506903128854198095173449986498411, 26516430580118506903128854198095173449986498412⟩
def centerDExp : DyadicInterval precision := ⟨1409419432745952657043289959536708377428786541143, 1409419432745952657043289959536708379627809796696⟩
def centerDLog : DyadicInterval precision := ⟨986759843010006569375564672930469553051891220885, 986759843010006569375564672930469555250914476438⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1409419432745952657043289959536708377978542355031, scale precision, 1409419432745952657043289959536708379078053982808, scale precision,
    0, 128, 0, 128, ⟨-53032861160237013806257708396190347470044957907, -53032861160237013806257708396190347470042860754⟩, ⟨-53032861160237013806257708396190346329903132893, -53032861160237013806257708396190346329901035740⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨27466528650804638884134946592252131447324001796, 27466528650804638884134946592252131447324001797⟩
def centerCExp : DyadicInterval precision := ⟨1407588142915443679182022975970707157656066590225, 1407588142915443679182022975970707159855089845778⟩
def centerCLog : DyadicInterval precision := ⟨985827289659040845099035067352292700110391222609, 985827289659040845099035067352292702309414478162⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1407588142915443679182022975970707158205822404113, scale precision, 1407588142915443679182022975970707159305334031890, scale precision,
    0, 128, 0, 128, ⟨-54933057301609277768269893184504263465461634084, -54933057301609277768269893184504263465459536931⟩, ⟨-54933057301609277768269893184504262323836470254, -54933057301609277768269893184504262323834373101⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨54004386838201810686191434458167706273952909008, 54004386838201810686191434458167706273952909009⟩
def centerBExp : DyadicInterval precision := ⟨1357387401610854475675992749803246938013775710979, 1357387401610854475675992749803246940212798966532⟩
def centerBLog : DyadicInterval precision := ⟨960028891661306865893799123924453126252807414744, 960028891661306865893799123924453128451830670297⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1357387401610854475675992749803246938563531524867, scale precision, 1357387401610854475675992749803246939663043152644, scale precision,
    0, 128, 0, 128, ⟨-108008773676403621372382868916335413139830013351, -108008773676403621372382868916335413139827916198⟩, ⟨-108008773676403621372382868916335411955983719837, -108008773676403621372382868916335411955981622684⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669124066, 1266295042977660303900587558721132456011189596⟩
def wholeAExp : DyadicInterval precision := ⟨1458971240300741788424025014233787498548709353580, 1460235890986607494244084883518378978984154367596⟩
def wholeALog : DyadicInterval precision := ⟨1011769992837296815097311935000023817181636979342, 1012402729061596953461092784027353939761000525628⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458971240300741788424025014233787499098465167468, scale precision, 1460235890986607494244084883518378978434398553708, scale precision,
    0, 128, 0, 128, ⟨-2532590085955320607801175117442265462732722054, -2532590085955320607801175117442265462730624901⟩, ⟨-1266294766337831391377608966682622963106949258, -1266294766337831391377608966682622963104852105⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨25328844546563792145364175869944518712165973939, 27704057351801426546684601097727000326331977356⟩
def wholeDExp : DyadicInterval precision := ⟨1407130684310035281592181556628555966755160121473, 1411711825212582109366700862001636148587605359971⟩
def wholeDLog : DyadicInterval precision := ⟨985594243690497964310298929048384649891451124795, 987926367053698422343402489929183443761757914490⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1407130684310035281592181556628555967304915935361, scale precision, 1411711825212582109366700862001636148037849546083, scale precision,
    0, 128, 0, 128, ⟨-55408114703602853093369202195454001223663156543, -55408114703602853093369202195454001223661059390⟩, ⟨-50657689093127584290728351739889036855187787228, -50657689093127584290728351739889036855185690075⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨25962218805867805495233154955753987475941518618, 28970906200610226455572444536056688958626202820⟩
def wholeCExp : DyadicInterval precision := ⟨1404693358843559643395315496180722839419800445730, 1410488761858508109328077807821978593605324517368⟩
def wholeCLog : DyadicInterval precision := ⟨984351955064518882387948220261005844902861346712, 987304105715524585824013929353200362439652742099⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1404693358843559643395315496180722839969556259618, scale precision, 1410488761858508109328077807821978593055568703480, scale precision,
    0, 128, 0, 128, ⟨-57941812401220452911144889072113378489242363448, -57941812401220452911144889072113378489240266295⟩, ⟨-51924437611735610990466309911507974382245359254, -51924437611735610990466309911507974382243262101⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨51309445420811149821965363311181569288639828368, 56699754757671754622654702159398489524282633261⟩
def wholeBExp : DyadicInterval precision := ⟨1352389912470905746515802614073206787004194289783, 1362402562817084022393337784221976293073763719669⟩
def wholeBLog : DyadicInterval precision := ⟨957435557743212078261424134828821329648629558790, 962626778180894861535355818863844522285974927821⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1352389912470905746515802614073206787553950103671, scale precision, 1362402562817084022393337784221976292524007905781, scale precision,
    0, 128, 0, 128, ⟨-113399509515343509245309404318796979642676796640, -113399509515343509245309404318796979642674699487⟩, ⟨-102618890841622299643930726622363137987536496033, -102618890841622299643930726622363137987534398880⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0032StableWitnesses

end


