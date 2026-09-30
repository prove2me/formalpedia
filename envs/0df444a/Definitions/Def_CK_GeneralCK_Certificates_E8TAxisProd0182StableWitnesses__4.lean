-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0182StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0182StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:47:45.716374+00:00
-- url     : https://prove2.me/theorems/3b5f1a76-4ec4-4e94-9295-c9c06351704b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0182StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0183StableWitnesses, GeneralCK.Certificates.E8TAxisProd01…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0182StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0183StableWitnesses, GeneralCK.Certificates.E8TAxisProd0184StableWitnesses, GeneralCK.Certificates.E8TAxisProd0185StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0182StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0183StableWitnesses, GeneralCK.Certificates.E8TAxisProd0184StableWitnesses, GeneralCK.Certificates.E8TAxisProd0185StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0182StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0183StableWitnesses, GeneralCK.Certificates.E8TAxisProd0184StableWitnesses, GeneralCK.Certificates.E8TAxisProd0185StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0182StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0183StableWitnesses, GeneralCK/Certificates/E8TAxisProd0184StableWitnesses, GeneralCK/Certificates/E8TAxisProd0185StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0182StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0182StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312260897, 2849167218250950044280193223065006085312260898⟩
def centerAExp : DyadicInterval precision := ⟨1455814397256041217437249255499380272227928609805, 1455814397256041217437249255499380274426951865358⟩
def centerALog : DyadicInterval precision := ⟨1010189349275934740575240882696318021950304507166, 1010189349275934740575240882696318024149327762719⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455814397256041217437249255499380272777684423693, scale precision, 1455814397256041217437249255499380273877196051470, scale precision,
    0, 128, 0, 128, ⟨-5698334436501900088560386446130012722529043537, -5698334436501900088560386446130012722526946384⟩, ⟨-5698334436501900088560386446130011618722097206, -5698334436501900088560386446130011618720000053⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨280899692551767667843547583927589246038699602854, 280899692551767667843547583927589246038699602855⟩
def centerDExp : DyadicInterval precision := ⟨995077841509260331069900400372341799476502701210, 995077841509260331069900400372341801675525956763⟩
def centerDLog : DyadicInterval precision := ⟨758965839592652166442507205173554655681704106112, 758965839592652166442507205173554657880727361665⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨995077841509260331069900400372341800026258515098, scale precision, 995077841509260331069900400372341801125770142875, scale precision,
    0, 128, 0, 128, ⟨-561799385103535335687095167855178492884843640736, -561799385103535335687095167855178492884841543583⟩, ⟨-561799385103535335687095167855178491269956867835, -561799385103535335687095167855178491269954770682⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨283871134724759237755935091389590224620654291174, 283871134724759237755935091389590224620654291175⟩
def centerCExp : DyadicInterval precision := ⟨991039785447791464819395115190855749355765331171, 991039785447791464819395115190855751554788586724⟩
def centerCLog : DyadicInterval precision := ⟨756561487777012649114008942824216057123817013927, 756561487777012649114008942824216059322840269480⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨991039785447791464819395115190855749905521145059, scale precision, 991039785447791464819395115190855751005032772836, scale precision,
    0, 128, 0, 128, ⟨-567742269449518475511870182779180450052042997970, -567742269449518475511870182779180450052040900817⟩, ⟨-567742269449518475511870182779180448430576263883, -567742269449518475511870182779180448430574166730⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨589328026376196034320194020334759842066581544462, 589328026376196034320194020334759842066581544463⟩
def centerBExp : DyadicInterval precision := ⟨652460438858663911083894388735850643276645988488, 652460438858663911083894388735850645475669244041⟩
def centerBLog : DyadicInterval precision := ⟨539439555811895311928276922284062148155298266312, 539439555811895311928276922284062150354321521865⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨652460438858663911083894388735850643826401802376, scale precision, 652460438858663911083894388735850644925913430153, scale precision,
    1, 128, 1, 128, ⟨-1178656052752392068640388040669519685364608948984, -1178656052752392068640388040669519685364606851831⟩, ⟨-1178656052752392068640388040669519682901719326019, -1178656052752392068640388040669519682901717228866⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 3165742448647063503620071141085134670978073809⟩
def wholeAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨272658858022120150330970042848572591083767790686, 289160022559818845156424937767397025574157886774⟩
def wholeDExp : DyadicInterval precision := ⟨983892922446469118853387927975743979589855262870, 1006363062196829127890208034234317471389852404954⟩
def wholeDLog : DyadicInterval precision := ⟨752296360822110031467471195763059030745434384007, 765664421925330452562213141131585421551189535260⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨983892922446469118853387927975743980139611076758, scale precision, 1006363062196829127890208034234317470840096591066, scale precision,
    0, 128, 0, 128, ⟨-578320045119637690312849875534794051964939244950, -578320045119637690312849875534794051964937147797⟩, ⟨-545317716044240300661940085697145181369147805567, -545317716044240300661940085697145181369145708414⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨275293839800143582953803650951007184676925300675, 292469745339287832750898622949857188568070755120⟩
def wholeCExp : DyadicInterval precision := ⟨979446742750594530073246032069957400534333385552, 1002740797131782167909766028290205811831733917263⟩
def wholeCLog : DyadicInterval precision := ⟨749636661828918999346616613489288628645341720858, 763517693506255177197831839603501952106542173140⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨979446742750594530073246032069957401084089199440, scale precision, 1002740797131782167909766028290205811281978103375, scale precision,
    0, 128, 0, 128, ⟨-584939490678575665501797245899714377956472023461, -584939490678575665501797245899714377956469926308⟩, ⟨-550587679600287165907607301902014368552578754252, -550587679600287165907607301902014368552576657099⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨570388425391957021472030702311555603474507573118, 608441580868175171101115292385503035792040508114⟩
def wholeBExp : DyadicInterval precision := ⟨635615904958952492906927750593163854143083894672, 669591958028013141922105032991401620840435484922⟩
def wholeBLog : DyadicInterval precision := ⟨527747330821057189438712369308479409001679784744, 551235810645475284980657031621799243102899811882⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨635615904958952492906927750593163854692839708560, scale precision, 669591958028013141922105032991401620290679671034, scale precision,
    1, 128, 1, 128, ⟨-1216883161736350342202230584771006072848161544032, -1216883161736350342202230584771006072848159446879⟩, ⟨-1140776850783914042944061404623111205749077915243, -1140776850783914042944061404623111205749075818090⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0182StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0183StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0183StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312260897, 2849167218250950044280193223065006085312260898⟩
def centerAExp : DyadicInterval precision := ⟨1455814397256041217437249255499380272227928609805, 1455814397256041217437249255499380274426951865358⟩
def centerALog : DyadicInterval precision := ⟨1010189349275934740575240882696318021950304507166, 1010189349275934740575240882696318024149327762719⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455814397256041217437249255499380272777684423693, scale precision, 1455814397256041217437249255499380273877196051470, scale precision,
    0, 128, 0, 128, ⟨-5698334436501900088560386446130012722529043537, -5698334436501900088560386446130012722526946384⟩, ⟨-5698334436501900088560386446130011618722097206, -5698334436501900088560386446130011618720000053⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨264436931605239354927088662990970038376004980339, 264436931605239354927088662990970038376004980340⟩
def centerDExp : DyadicInterval precision := ⟨1017749934528406450171674159073588388727957535413, 1017749934528406450171674159073588390926980790966⟩
def centerDLog : DyadicInterval precision := ⟨772392366462306324149504069119604065357703153956, 772392366462306324149504069119604067556726409509⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1017749934528406450171674159073588389277713349301, scale precision, 1017749934528406450171674159073588390377224977078, scale precision,
    0, 128, 0, 128, ⟨-528873863210478709854177325981940077541467235064, -528873863210478709854177325981940077541465137911⟩, ⟨-528873863210478709854177325981940075962554783446, -528873863210478709854177325981940075962552686293⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨267394683788496671523088778869818964226188093548, 267394683788496671523088778869818964226188093549⟩
def centerCExp : DyadicInterval precision := ⟨1013638863902541394655891421818773588804921832282, 1013638863902541394655891421818773591003945087835⟩
def centerCLog : DyadicInterval precision := ⟨769966907297493862546476590491917510535344241055, 769966907297493862546476590491917512734367496608⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1013638863902541394655891421818773589354677646170, scale precision, 1013638863902541394655891421818773590454189273947, scale precision,
    0, 128, 0, 128, ⟨-534789367576993343046177557739637929245035302311, -534789367576993343046177557739637929245033205158⟩, ⟨-534789367576993343046177557739637927659719169034, -534789367576993343046177557739637927659717071881⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨552350212664041971091390878440508207198447596176, 552350212664041971091390878440508207198447596177⟩
def centerBExp : DyadicInterval precision := ⟨686326183573433042345692650823774264199441085214, 686326183573433042345692650823774266398464340767⟩
def centerBLog : DyadicInterval precision := ⟨562667300193635839647100588746142446435322439253, 562667300193635839647100588746142448634345694806⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨686326183573433042345692650823774264749196899102, scale precision, 686326183573433042345692650823774265848708526879, scale precision,
    1, 128, 1, 128, ⟨-1104700425328083942182781756881016415567577239790, -1104700425328083942182781756881016415567575142637⟩, ⟨-1104700425328083942182781756881016413226215242068, -1104700425328083942182781756881016413226213144915⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 3165742448647063503620071141085134670978073809⟩
def wholeAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨256233328382592948799518632260864583083635375283, 272658858022120150330970042848572591083767790687⟩
def wholeDExp : DyadicInterval precision := ⟨1006363062196829127890208034234317469190829149401, 1029239839924196772159254586274144060399381080023⟩
def wholeDLog : DyadicInterval precision := ⟨765664421925330452562213141131585419352166279707, 779149939480909138582665574125961105420771432974⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1006363062196829127890208034234317469740584963289, scale precision, 1029239839924196772159254586274144059849625266135, scale precision,
    0, 128, 0, 128, ⟨-545317716044240300661940085697145182965925454334, -545317716044240300661940085697145182965923357181⟩, ⟨-512466656765185897599037264521729165386628657514, -512466656765185897599037264521729165386626560361⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨258856523389556057576596003104549794743303155871, 275952890023213657918162872037315490194966272903⟩
def wholeCExp : DyadicInterval precision := ⟨1001836852022489929581002918286635590698941039778, 1025551774732822142853509456880829106965098227895⟩
def wholeCLog : DyadicInterval precision := ⟨762981480182706404259605652287855778593802742651, 776984276000630970805974684708486431437270820557⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1001836852022489929581002918286635591248696853666, scale precision, 1025551774732822142853509456880829106415342414007, scale precision,
    0, 128, 0, 128, ⟨-551905780046427315836325744074630981191929468767, -551905780046427315836325744074630981191927371614⟩, ⟨-517713046779112115153192006209099588703156888168, -517713046779112115153192006209099588703154791015⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨533735477367524214415483762183972136785277995953, 571127946572204846234959112820593845869730227308⟩
def wholeBExp : DyadicInterval precision := ⟨668914672492773994045833077282685236511927208121, 704033850755750596856942594226690045489645620867⟩
def wholeBLog : DyadicInterval precision := ⟨550771255147986942070435863946541787510240324285, 574667184328729225728115524796933599540908085217⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨668914672492773994045833077282685237061683022009, scale precision, 704033850755750596856942594226690044939889806979, scale precision,
    1, 128, 1, 128, ⟨-1142255893144409692469918225641187692940614737184, -1142255893144409692469918225641187692940612640031⟩, ⟨-1067470954735048428830967524367944272429320690458, -1067470954735048428830967524367944272429318593305⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0183StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0184StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0184StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2216017656540843594568486214625237657012954244, 2216017656540843594568486214625237657012954245⟩
def centerAExp : DyadicInterval precision := ⟨1457076315351450948047082186788007224970773813488, 1457076315351450948047082186788007227169797069041⟩
def centerALog : DyadicInterval precision := ⟨1010821401672838003372446069258059721789517968263, 1010821401672838003372446069258059723988541223816⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457076315351450948047082186788007225520529627376, scale precision, 1457076315351450948047082186788007226620041255153, scale precision,
    0, 128, 0, 128, ⟨-4432035313081687189136972429250475865452447731, -4432035313081687189136972429250475865450350578⟩, ⟨-4432035313081687189136972429250474762601466399, -4432035313081687189136972429250474762599369246⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨381480886315733598228818968652248949197699359262, 381480886315733598228818968652248949197699359263⟩
def centerDExp : DyadicInterval precision := ⟨867122341474961541277039570779760212192757729340, 867122341474961541277039570779760214391780984893⟩
def centerDLog : DyadicInterval precision := ⟨680786608648623470121619561851525432077092876199, 680786608648623470121619561851525434276116131752⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨867122341474961541277039570779760212742513543228, scale precision, 867122341474961541277039570779760213842025171005, scale precision,
    0, 128, 0, 128, ⟨-762961772631467196457637937304497899321992225512, -762961772631467196457637937304497899321990128359⟩, ⟨-762961772631467196457637937304497897468807308690, -762961772631467196457637937304497897468805211537⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨383869649844851299850098643228997724790706756538, 383869649844851299850098643228997724790706756539⟩
def centerCExp : DyadicInterval precision := ⟨864292418713137556673888649355171293784368572383, 864292418713137556673888649355171295983391827936⟩
def centerCLog : DyadicInterval precision := ⟨679009399455720342795280865480758017215697697192, 679009399455720342795280865480758019414720952745⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨864292418713137556673888649355171294334124386271, scale precision, 864292418713137556673888649355171295433636014048, scale precision,
    0, 128, 0, 128, ⟨-767739299689702599700197286457995450511040929689, -767739299689702599700197286457995450511038832536⟩, ⟨-767739299689702599700197286457995448651788193615, -767739299689702599700197286457995448651786096462⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨825850270551290552568253522310123472684404929023, 825850270551290552568253522310123472684404929024⟩
def centerBExp : DyadicInterval precision := ⟨472047838817715924728378192594436280898543045723, 472047838817715924728378192594436283097566301276⟩
def centerBLog : DyadicInterval precision := ⟨409064070128224893203617006204895139894537396395, 409064070128224893203617006204895142093560651948⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨472047838817715924728378192594436281448298859611, scale precision, 472047838817715924728378192594436282547810487388, scale precision,
    1, 128, 1, 128, ⟨-1651700541102581105136507044620246947070903271123, -1651700541102581105136507044620246947070901173970⟩, ⟨-1651700541102581105136507044620246943666718542123, -1651700541102581105136507044620246943666716444970⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1457707683773513925477741956702213446679176875042⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1011137530350683182654731711817158199758569694808⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨372966609392870424646531471060848444542040850580, 390021907983024779256146395473341757167804190698⟩
def wholeDExp : DyadicInterval precision := ⟨857046406820575460675375243512252169980002923132, 877284626339432933560204346302551152435952374342⟩
def wholeDLog : DyadicInterval precision := ⟨674448983099953378325059509857368474307670227252, 687150831490084437187371430673459277974101520863⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨857046406820575460675375243512252170529758737020, scale precision, 877284626339432933560204346302551151886196560454, scale precision,
    0, 128, 0, 128, ⟨-780043815966049558512292790946683515273095446757, -780043815966049558512292790946683515273093349604⟩, ⟨-745933218785740849293062942121696888168223747987, -745933218785740849293062942121696888168221650834⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨375007629872915579465429227647113556197499662127, 392760784790180292139123525495050640775660750372⟩
def wholeCExp : DyadicInterval precision := ⟨853840182486705188164996754687631265688701292587, 874837748939270527343756194198458034256652363129⟩
def wholeCLog : DyadicInterval precision := ⟨672426534142843849849723373732993900147555703175, 685620983558290487877774249648825817987883387321⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨853840182486705188164996754687631266238457106475, scale precision, 874837748939270527343756194198458033706896549241, scale precision,
    0, 128, 0, 128, ⟨-785521569580360584278247050990101282492328885879, -785521569580360584278247050990101282492326788726⟩, ⟨-750015259745831158930858455294227111476579759290, -750015259745831158930858455294227111476577662137⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨804527743768603565702130195390504626303088734562, 847408844063416313893716486071623707147098706302⟩
def wholeBExp : DyadicInterval precision := ⟨458324929075381578872203088156420457561627329180, 486024611517000907519255281789072220438982193820⟩
def wholeBLog : DyadicInterval precision := ⟨398654424340000861397377527043933161832778105402, 419590617889510464714352889163563097924946598867⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨458324929075381578872203088156420458111383143068, scale precision, 486024611517000907519255281789072219889226379932, scale precision,
    1, 128, 1, 128, ⟨-1694817688126832627787432972143247416047253927203, -1694817688126832627787432972143247416047251830050⟩, ⟨-1609055487537207131404260390781009250953033793977, -1609055487537207131404260390781009250953031696824⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0184StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0185StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0185StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2216017656540843594568486214625237657012954244, 2216017656540843594568486214625237657012954245⟩
def centerAExp : DyadicInterval precision := ⟨1457076315351450948047082186788007224970773813488, 1457076315351450948047082186788007227169797069041⟩
def centerALog : DyadicInterval precision := ⟨1010821401672838003372446069258059721789517968263, 1010821401672838003372446069258059723988541223816⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457076315351450948047082186788007225520529627376, scale precision, 1457076315351450948047082186788007226620041255153, scale precision,
    0, 128, 0, 128, ⟨-4432035313081687189136972429250475865452447731, -4432035313081687189136972429250475865450350578⟩, ⟨-4432035313081687189136972429250474762601466399, -4432035313081687189136972429250474762599369246⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨364478458648618710654128585069611790600183100243, 364478458648618710654128585069611790600183100244⟩
def centerDExp : DyadicInterval precision := ⟨887534276475298848733503786031227102092850438854, 887534276475298848733503786031227104291873694407⟩
def centerDLog : DyadicInterval precision := ⟨693541818075819702070900853962455106453799173953, 693541818075819702070900853962455108652822429506⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨887534276475298848733503786031227102642606252742, scale precision, 887534276475298848733503786031227103742117880519, scale precision,
    0, 128, 0, 128, ⟨-728956917297237421308257170139223582105649493848, -728956917297237421308257170139223582105647396695⟩, ⟨-728956917297237421308257170139223580295085004280, -728956917297237421308257170139223580295082907127⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨366852542983161616689294523574259636371532219530, 366852542983161616689294523574259636371532219531⟩
def centerCExp : DyadicInterval precision := ⟨884655508365904550292029370980287998779934705503, 884655508365904550292029370980288000978957961056⟩
def centerCLog : DyadicInterval precision := ⟨691749634121177210173871200170603324482489170699, 691749634121177210173871200170603326681512426252⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨884655508365904550292029370980287999329690519391, scale precision, 884655508365904550292029370980288000429202147168, scale precision,
    0, 128, 0, 128, ⟨-733705085966323233378589047148519273651293622242, -733705085966323233378589047148519273651291525089⟩, ⟨-733705085966323233378589047148519271834837353034, -733705085966323233378589047148519271834835255881⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨784259327640378353138193847662631817756194532913, 784259327640378353138193847662631817756194532914⟩
def centerBExp : DyadicInterval precision := ⟨499693889414128217070386750639062339046241283984, 499693889414128217070386750639062341245264539537⟩
def centerBLog : DyadicInterval precision := ⟨429812759355055954897720691007119946305701111639, 429812759355055954897720691007119948504724367192⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨499693889414128217070386750639062339595997097872, scale precision, 499693889414128217070386750639062340695508725649, scale precision,
    1, 128, 1, 128, ⟨-1568518655280756706276387695325263637120312562828, -1568518655280756706276387695325263637120310465675⟩, ⟨-1568518655280756706276387695325263633904467665976, -1568518655280756706276387695325263633904465568823⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1457707683773513925477741956702213446679176875042⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1011137530350683182654731711817158199758569694808⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨356015818146773315735630103594046256346147492780, 372966609392870424646531471060848444542040850581⟩
def wholeDExp : DyadicInterval precision := ⟨877284626339432933560204346302551150236929118789, 897872332234039104779267097055247456527332583462⟩
def wholeDLog : DyadicInterval precision := ⟨687150831490084437187371430673459275775078265310, 699959742628865241142888209739517591976703657011⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨877284626339432933560204346302551150786684932677, scale precision, 897872332234039104779267097055247455977576769574, scale precision,
    0, 128, 0, 128, ⟨-745933218785740849293062942121696889999941751488, -745933218785740849293062942121696889999939654335⟩, ⟨-712031636293546631471260207188092511797437162463, -712031636293546631471260207188092511797435065310⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨358044558190719898392359023693497830097627184928, 375688305920702453893603035820021341674158539604⟩
def wholeCExp : DyadicInterval precision := ⟨874023238938816116161761791599617733994705546018, 895383079650601657819313742220858029218120798577⟩
def wholeCLog : DyadicInterval precision := ⟨685111376410286388140296339363941249801422932557, 698416974385628154897256113035766032485010108239⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨874023238938816116161761791599617734544461359906, scale precision, 895383079650601657819313742220858028668364984689, scale precision,
    0, 128, 0, 128, ⟨-751376611841404907787206071640042684267594625632, -751376611841404907787206071640042684267592528479⟩, ⟨-716089116381439796784718047386995659297908751526, -716089116381439796784718047386995659297906654373⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨763385715419221596005381651623863469753986400928, 805359532324045364349935299796127283205699780587⟩
def wholeBExp : DyadicInterval precision := ⟨485471701135904484933714645944766020186191260669, 514173264887947852703415841781641103589855615719⟩
def wholeBLog : DyadicInterval precision := ⟨419175632901281930098864794504698286196507622125, 440563291668490213331945155930551127482880644419⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨485471701135904484933714645944766020735947074557, scale precision, 514173264887947852703415841781641103040099801831, scale precision,
    1, 128, 1, 128, ⟨-1610719064648090728699870599592254568066428122683, -1610719064648090728699870599592254568066426025530⟩, ⟨-1526771430838443192010763303247726937945331299766, -1526771430838443192010763303247726937945329202613⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0185StableWitnesses

end


