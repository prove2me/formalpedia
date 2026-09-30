-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0049StableWitnesses__5
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0049StableWitnesses__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:49:18.995216+00:00
-- url     : https://prove2.me/theorems/ba600bfe-e875-408f-877b-fc80f9729371
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0049StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0050StableWitnesses, GeneralCK.Certificates.E8TAxisZero00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0049StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0050StableWitnesses, GeneralCK.Certificates.E8TAxisZero0051StableWitnesses, GeneralCK.Certificates.E8TAxisZero0052StableWitnesses, GeneralCK.Certificates.E8TAxisZero0053StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0049StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0050StableWitnesses, GeneralCK.Certificates.E8TAxisZero0051StableWitnesses, GeneralCK.Certificates.E8TAxisZero0052StableWitnesses, GeneralCK.Certificates.E8TAxisZero0053StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0049StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0050StableWitnesses, GeneralCK.Certificates.E8TAxisZero0051StableWitnesses, GeneralCK.Certificates.E8TAxisZero0052StableWitnesses, GeneralCK.Certificates.E8TAxisZero0053StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0049StableWitnesses (+4 modules: GeneralCK/Certificates/E8TAxisZero0050StableWitnesses, GeneralCK/Certificates/E8TAxisZero0051StableWitnesses, GeneralCK/Certificates/E8TAxisZero0052StableWitnesses, GeneralCK/Certificates/E8TAxisZero0053StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0049StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0049StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

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

def centerCAlpha : DyadicInterval precision := ⟨281229727521010614347226107824309390844763740543, 281229727521010614347226107824309390844763740544⟩
def centerCExp : DyadicInterval precision := ⟨994628527835930195533404265947217167506308051197, 994628527835930195533404265947217169705331306750⟩
def centerCLog : DyadicInterval precision := ⟨758698503349046068538925908273509365549093547853, 758698503349046068538925908273509367748116803406⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨994628527835930195533404265947217168056063865085, scale precision, 994628527835930195533404265947217169155575492862, scale precision,
    0, 128, 0, 128, ⟨-562459455042021228694452215648618782497336670737, -562459455042021228694452215648618782497334573584⟩, ⟨-562459455042021228694452215648618780881720388589, -562459455042021228694452215648618780881718291436⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨586345747832971553072810084814958221006583886279, 586345747832971553072810084814958221006583886280⟩
def centerBExp : DyadicInterval precision := ⟨655128646241930452861888543795671460832984394559, 655128646241930452861888543795671463032007650112⟩
def centerBLog : DyadicInterval precision := ⟨541283075416158881800115500364656247394562055986, 541283075416158881800115500364656249593585311539⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨655128646241930452861888543795671461382740208447, scale precision, 655128646241930452861888543795671462482251836224, scale precision,
    0, 128, 0, 128, ⟨-1172691495665943106145620169629916443239598205256, -1172691495665943106145620169629916443239596108103⟩, ⟨-1172691495665943106145620169629916440786739437015, -1172691495665943106145620169629916440786737339862⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

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

def wholeCAlpha : DyadicInterval precision := ⟨272658858022120150330970042848572591083767790686, 289821708815072720468221936650414567978851753461⟩
def wholeCExp : DyadicInterval precision := ⟨983002422228797412925137426354918999584925951059, 1006363062196829127890208034234317471389852404954⟩
def wholeCLog : DyadicInterval precision := ⟨751764052223558962742893770839715827587696880995, 765664421925330452562213141131585421551189535260⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨983002422228797412925137426354919000134681764947, scale precision, 1006363062196829127890208034234317470840096591066, scale precision,
    0, 128, 0, 128, ⟨-579643417630145440936443873300829136775066755185, -579643417630145440936443873300829136775064658032⟩, ⟨-545317716044240300661940085697145181369147805567, -545317716044240300661940085697145181369145708414⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨567432926519181715580394811546823259563268503719, 605431645944060642830475516575250844744428501845⟩
def wholeBExp : DyadicInterval precision := ⟨638239382071719336254913965627636767094299187016, 672305585690377046487188416595132107112161604664⟩
def wholeBLog : DyadicInterval precision := ⟨529574514910709885545224575151705633489087057977, 553095629654514435062742310017686416445408794317⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨638239382071719336254913965627636767644055000904, scale precision, 672305585690377046487188416595132106562405790776, scale precision,
    0, 128, 0, 128, ⟨-1210863291888121285660951033150501690747741544416, -1210863291888121285660951033150501690747739447263⟩, ⟨-1134865853038363431160789623093646517931443088442, -1134865853038363431160789623093646517931440991289⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0049StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0050StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0050StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

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

def centerCAlpha : DyadicInterval precision := ⟨264765452971270480650238705671629167219911907656, 264765452971270480650238705671629167219911907657⟩
def centerCExp : DyadicInterval precision := ⟨1017292490698628958068816631798387228768996244107, 1017292490698628958068816631798387230968019499660⟩
def centerCLog : DyadicInterval precision := ⟨772122681611229325990422615270340480051886148458, 772122681611229325990422615270340482250909404011⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1017292490698628958068816631798387229318752057995, scale precision, 1017292490698628958068816631798387230418263685772, scale precision,
    0, 128, 0, 128, ⟨-529530905942540961300477411343258335229636082862, -529530905942540961300477411343258335229633985709⟩, ⟨-529530905942540961300477411343258333650013644917, -529530905942540961300477411343258333650011547764⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨549419617637370643720094875025248000125400593949, 549419617637370643720094875025248000125400593950⟩
def centerBExp : DyadicInterval precision := ⟨689084145086126137692400925919802869021637506493, 689084145086126137692400925919802871220660762046⟩
def centerBLog : DyadicInterval precision := ⟨564542766908384243005941697091905306238397842131, 564542766908384243005941697091905308437421097684⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨689084145086126137692400925919802869571393320381, scale precision, 689084145086126137692400925919802870670904948158, scale precision,
    0, 128, 0, 128, ⟨-1098839235274741287440189750050496001416797750753, -1098839235274741287440189750050496001416795653600⟩, ⟨-1098839235274741287440189750050495999084806722198, -1098839235274741287440189750050495999084804625045⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

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

def wholeCAlpha : DyadicInterval precision := ⟨256233328382592948799518632260864583083635375283, 273317421200188951886965822796529956432845743031⟩
def wholeCExp : DyadicInterval precision := ⟨1005456521844459780778513696130757998904511114880, 1029239839924196772159254586274144060399381080023⟩
def wholeCLog : DyadicInterval precision := ⟨765127458284635026651998529297265610474764901239, 779149939480909138582665574125961105420771432974⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1005456521844459780778513696130757999454266928768, scale precision, 1029239839924196772159254586274144059849625266135, scale precision,
    0, 128, 0, 128, ⟨-546634842400377903773931645593059913664801202863, -546634842400377903773931645593059913664799105710⟩, ⟨-512466656765185897599037264521729165386628657514, -512466656765185897599037264521729165386626560361⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨530829944683894805437507571749273968698214433227, 568171414034215943204650226253966784153927364518⟩
def wholeBExp : DyadicInterval precision := ⟨671626505379762610309279954216804843506388612625, 706838726837510462039096914346652693399387599334⟩
def wholeBLog : DyadicInterval precision := ⟨552630435359708772284793273908962784632290044761, 576558946667156773600005109862481907627324132952⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨671626505379762610309279954216804844056144426513, scale precision, 706838726837510462039096914346652692849631785446, scale precision,
    0, 128, 0, 128, ⟨-1136342828068431886409300452507933569504159103484, -1136342828068431886409300452507933569504157006331⟩, ⟨-1061659889367789610875015143498547936259722216904, -1061659889367789610875015143498547936259720119751⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0050StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0051StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0051StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨889351442612263296687940979624415955523303356852, 889351442612263296687940979624415955523303356853⟩
def centerDExp : DyadicInterval precision := ⟨432759351678313928226043309926168445711221586154, 432759351678313928226043309926168447910244841707⟩
def centerDLog : DyadicInterval precision := ⟨379061432685197727184727484874290046165241739981, 379061432685197727184727484874290048364264995534⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨432759351678313928226043309926168446260977400042, scale precision, 432759351678313928226043309926168447360489027819, scale precision,
    1, 128, 1, 128, ⟨-1778702885224526593375881959248831912903226270963, -1778702885224526593375881959248831912903224173810⟩, ⟨-1778702885224526593375881959248831909189989253603, -1778702885224526593375881959248831909189987156450⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨889568579085315104981341544877329197109791270322, 889568579085315104981341544877329197109791270323⟩
def centerCExp : DyadicInterval precision := ⟨432630779971777265842043369804865285964292096300, 432630779971777265842043369804865288163315351853⟩
def centerCLog : DyadicInterval precision := ⟨378962230865567891886960631990596729657896743696, 378962230865567891886960631990596731856919999249⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨432630779971777265842043369804865286514047910188, scale precision, 432630779971777265842043369804865287613559537965, scale precision,
    1, 128, 1, 128, ⟨-1779137158170630209962683089754658396076753858482, -1779137158170630209962683089754658396076751761329⟩, ⟨-1779137158170630209962683089754658392362413319963, -1779137158170630209962683089754658392362411222810⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2270908830027593634566325072869940492360130760138, 2270908830027593634566325072869940492360130760139⟩
def centerBExp : DyadicInterval precision := ⟨65338533038737916198760478190090576481159338436, 65338533038737916198760478190090578680182593989⟩
def centerBLog : DyadicInterval precision := ⟨63920127221162978068403086142923874841495271280, 63920127221162978068403086142923877040518526833⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨65338533038737916198760478190090577030915152324, scale precision, 65338533038737916198760478190090578130426780101, scale precision,
    4, 128, 4, 128, ⟨-4541817660055187269132650145739880997017279118860, -4541817660055187269132650145739880997017277021707⟩, ⟨-4541817660055187269132650145739880972423246018855, -4541817660055187269132650145739880972423243921702⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨883118980747789020882084464779538700246874405266, 895603670620266646532188138393358736598408063638⟩
def wholeDExp : DyadicInterval precision := ⟨429072502312048699316189665111836193246265566837, 436466074505762269046786189274013978256547303798⟩
def wholeDLog : DyadicInterval precision := ⟨376214102269711135965559641860188009991436493933, 381918529993447746751868483809797876669420495502⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨429072502312048699316189665111836193796021380725, scale precision, 436466074505762269046786189274013977706791489910, scale precision,
    1, 128, 1, 128, ⟨-1791207341240533293064376276786717475069388868982, -1791207341240533293064376276786717475069386771829⟩, ⟨-1766237961495578041764168929559077398652898830676, -1766237961495578041764168929559077398652896733523⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨883118980747789020882084464779538700246874405266, 896039345883247891012692341783045457574233923247⟩
def wholeCExp : DyadicInterval precision := ⟨428816764575366300703274760689464914813467547249, 436466074505762269046786189274013978256547303798⟩
def wholeCLog : DyadicInterval precision := ⟨376016391746414710875486605814044608118607772702, 381918529993447746751868483809797876669420495502⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨428816764575366300703274760689464915363223361137, scale precision, 436466074505762269046786189274013977706791489910, scale precision,
    1, 128, 1, 128, ⟨-1792078691766495782025384683566090917022157352483, -1792078691766495782025384683566090917022155255330⟩, ⟨-1766237961495578041764168929559077398652898830676, -1766237961495578041764168929559077398652896733523⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2252344891692604840925366006970977595417110077970, 2289498348206320816860169387570737970765253330303⟩
def wholeBExp : DyadicInterval precision := ⟨63697354158507276092122189314858434240452236681, 67019651263419624089891999519086677965175844684⟩
def wholeBLog : DyadicInterval precision := ⟨62348334904882759125899443768122579547254410291, 65528419607421522813609600873594906488902107800⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨63697354158507276092122189314858434790208050569, scale precision, 67019651263419624089891999519086677415420030796, scale precision,
    4, 128, 4, 128, ⟨-4578996696412641633720338775141475954144360085698, -4578996696412641633720338775141475954144357988545⟩, ⟨-4504689783385209681850732013941955178845662520844, -4504689783385209681850732013941955178845660423691⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0051StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0052StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0052StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨876906193579724784222253173988686333103956064712, 876906193579724784222253173988686333103956064713⟩
def centerDExp : DyadicInterval precision := ⟨440192694720248252032582341812381160071591754974, 440192694720248252032582341812381162270615010527⟩
def centerDLog : DyadicInterval precision := ⟨384785344583078380142629370287541215891742295997, 384785344583078380142629370287541218090765551550⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨440192694720248252032582341812381160621347568862, scale precision, 440192694720248252032582341812381161720859196639, scale precision,
    1, 128, 1, 128, ⟨-1753812387159449568444506347977372668033179775489, -1753812387159449568444506347977372668033177678336⟩, ⟨-1753812387159449568444506347977372664382646580517, -1753812387159449568444506347977372664382644483364⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨877121961275332815348515408942289040848495324819, 877121961275332815348515408942289040848495324820⟩
def centerCExp : DyadicInterval precision := ⟨440062738871947185827516025087252185475384312922, 440062738871947185827516025087252187674407568475⟩
def centerCLog : DyadicInterval precision := ⟨384685466715325414884351721285691055570098649746, 384685466715325414884351721285691057769121905299⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨440062738871947185827516025087252186025140126810, scale precision, 440062738871947185827516025087252187124651754587, scale precision,
    1, 128, 1, 128, ⟨-1754243922550665630697030817884578083522797319001, -1754243922550665630697030817884578083522795221848⟩, ⟨-1754243922550665630697030817884578079871186077432, -1754243922550665630697030817884578079871183980279⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2234440797417960962512456499575835485272394016066, 2234440797417960962512456499575835485272394016067⟩
def centerBExp : DyadicInterval precision := ⟨68681977988023915269716644193796990464240079605, 68681977988023915269716644193796992663263335158⟩
def centerBLog : DyadicInterval precision := ⟨67116996175154394811740681640706694929648140156, 67116996175154394811740681640706697128671395709⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨68681977988023915269716644193796991013995893493, scale precision, 68681977988023915269716644193796992113507521270, scale precision,
    4, 128, 4, 128, ⟨-4468881594835921925024912999151670982243185744107, -4468881594835921925024912999151670982243183646954⟩, ⟨-4468881594835921925024912999151670958846392417324, -4468881594835921925024912999151670958846390320171⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨870712988176454679833831807012927217752922944018, 883118980747789020882084464779538700246874405267⟩
def wholeDExp : DyadicInterval precision := ⟨436466074505762269046786189274013976057524048245, 443939237141351316813290285207320726677583911584⟩
def wholeDLog : DyadicInterval precision := ⟨381918529993447746751868483809797874470397239949, 387661827478115861734404726101104697816790214517⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨436466074505762269046786189274013976607279862133, scale precision, 443939237141351316813290285207320726127828097696, scale precision,
    1, 128, 1, 128, ⟨-1766237961495578041764168929559077402334600887543, -1766237961495578041764168929559077402334598790390⟩, ⟨-1741425976352909359667663614025854433695984336263, -1741425976352909359667663614025854433695982239110⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨870712988176454679833831807012927217752922944018, 883551905517596028616811380983627993011479866867⟩
def wholeCExp : DyadicInterval precision := ⟨436207571869314072928007112569681796571117648792, 443939237141351316813290285207320726677583911584⟩
def wholeCLog : DyadicInterval precision := ⟨381719460349288307753606987078005788446444707167, 387661827478115861734404726101104697816790214517⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨436207571869314072928007112569681797120873462680, scale precision, 443939237141351316813290285207320726127828097696, scale precision,
    1, 128, 1, 128, ⟨-1767103811035192057233622761967255987864902724508, -1767103811035192057233622761967255987864900627355⟩, ⟨-1741425976352909359667663614025854433695984336263, -1741425976352909359667663614025854433695982239110⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2215929949949202375694063104874887815254864937640, 2252979123662759141363780668401055367420983327973⟩
def wholeBExp : DyadicInterval precision := ⟨66961508920173399729056217016390022878533067561, 70444002772177930070674313482323918990846719046⟩
def wholeBLog : DyadicInterval precision := ⟨65472825520062582058540430242163461037130422212, 68798964620298951320326275511361484915049658345⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨66961508920173399729056217016390023428288881449, scale precision, 70444002772177930070674313482323918441090905158, scale precision,
    4, 128, 4, 128, ⟨-4505958247325518282727561336802110746840935993713, -4505958247325518282727561336802110746840933896560⟩, ⟨-4431859899898404751388126209749775619103947741309, -4431859899898404751388126209749775619103945644156⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0052StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0053StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0053StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨864539270161105163740168296694370154034029348165, 864539270161105163740168296694370154034029348166⟩
def centerDExp : DyadicInterval precision := ⟨447705727508954974656542730347776284626226541037, 447705727508954974656542730347776286825249796590⟩
def centerDLog : DyadicInterval precision := ⟨390547930354595539952804600044570644160315185441, 390547930354595539952804600044570646359338440994⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨447705727508954974656542730347776285175982354925, scale precision, 447705727508954974656542730347776286275493982702, scale precision,
    1, 128, 1, 128, ⟨-1729078540322210327480336593388740309862696205336, -1729078540322210327480336593388740309862694108183⟩, ⟨-1729078540322210327480336593388740306273423284479, -1729078540322210327480336593388740306273421187326⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨864753682105473134926531948268092697857259622693, 864753682105473134926531948268092697857259622694⟩
def centerCExp : DyadicInterval precision := ⟨447574384003629321525936368629525800801052325967, 447574384003629321525936368629525803000075581520⟩
def centerCLog : DyadicInterval precision := ⟨390447383208798558243275011766813448027711060324, 390447383208798558243275011766813450226734315877⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨447574384003629321525936368629525801350808139855, scale precision, 447574384003629321525936368629525802450319767632, scale precision,
    1, 128, 1, 128, ⟨-1729507364210946269853063896536185397509683401697, -1729507364210946269853063896536185397509681304544⟩, ⟨-1729507364210946269853063896536185393919357186228, -1729507364210946269853063896536185393919355089075⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2198078974265077670796151698551412219080312820800, 2198078974265077670796151698551412219080312820801⟩
def centerBExp : DyadicInterval precision := ⟨72186018221563420262904968289895656226832979592, 72186018221563420262904968289895658425856235145⟩
def centerBLog : DyadicInterval precision := ⟨70459932166004994217086871073398752731018636856, 70459932166004994217086871073398754930041892409⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨72186018221563420262904968289895656776588793480, scale precision, 72186018221563420262904968289895657876100421257, scale precision,
    4, 128, 4, 128, ⟨-4396157948530155341592303397102824449291161964539, -4396157948530155341592303397102824449291159867386⟩, ⟨-4396157948530155341592303397102824427030091415832, -4396157948530155341592303397102824427030089318679⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨858384943750592238779991986336301839154815993316, 870712988176454679833831807012927217752922944019⟩
def wholeDExp : DyadicInterval precision := ⟨443939237141351316813290285207320724478560656031, 451492192509468156215846209344698069605083336703⟩
def wholeDLog : DyadicInterval precision := ⟨387661827478115861734404726101104695617766958964, 393443605556601543377574216062392477640846281111⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨443939237141351316813290285207320725028316469919, scale precision, 451492192509468156215846209344698069055327522815, scale precision,
    1, 128, 1, 128, ⟨-1741425976352909359667663614025854437315709536964, -1741425976352909359667663614025854437315707439811⟩, ⟨-1716769887501184477559983972672603676530047395724, -1716769887501184477559983972672603676530045298571⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨858384943750592238779991986336301839154815993316, 871143188090492117311131821217990885949978337620⟩
def wholeCExp : DyadicInterval precision := ⟨443677962831186878806869585703732164200127572139, 451492192509468156215846209344698069605083336703⟩
def wholeCLog : DyadicInterval precision := ⟨387461412435348922626507055203030607648325319005, 393443605556601543377574216062392477640846281111⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨443677962831186878806869585703732164749883386027, scale precision, 451492192509468156215846209344698069055327522815, scale precision,
    1, 128, 1, 128, ⟨-1742286376180984234622263642435981773710886121079, -1742286376180984234622263642435981773710884023926⟩, ⟨-1716769887501184477559983972672603676530047395724, -1716769887501184477559983972672603676530045298571⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2179625075014223488918515620806299281281280813354, 2216562335033091387254814734775112079611609589194⟩
def wholeBExp : DyadicInterval precision := ⟨70383067545802394134786824794382050344540803156, 74032168944826087643371182989772774338945362286⟩
def wholeBLog : DyadicInterval precision := ⟨68740830243977076441342451274240014611701302209, 72218132194102709194069679294865357969448489766⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨70383067545802394134786824794382050894296617044, scale precision, 74032168944826087643371182989772773789189548398, scale precision,
    4, 128, 4, 128, ⟨-4433124670066182774509629469550224170638878142235, -4433124670066182774509629469550224170638876045082⟩, ⟨-4359250150028446977837031241612598551709591141662, -4359250150028446977837031241612598551709589044509⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0053StableWitnesses

end


