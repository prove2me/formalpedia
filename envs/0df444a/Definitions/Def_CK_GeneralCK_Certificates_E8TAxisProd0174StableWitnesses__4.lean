-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0174StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0174StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:53:54.695289+00:00
-- url     : https://prove2.me/theorems/75e9ed27-3055-4c08-9eb9-8a028fdff92d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0174StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0175StableWitnesses, GeneralCK.Certificates.E8TAxisProd01…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0174StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0175StableWitnesses, GeneralCK.Certificates.E8TAxisProd0176StableWitnesses, GeneralCK.Certificates.E8TAxisProd0177StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0174StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0175StableWitnesses, GeneralCK.Certificates.E8TAxisProd0176StableWitnesses, GeneralCK.Certificates.E8TAxisProd0177StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0174StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0175StableWitnesses, GeneralCK.Certificates.E8TAxisProd0176StableWitnesses, GeneralCK.Certificates.E8TAxisProd0177StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0174StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0175StableWitnesses, GeneralCK/Certificates/E8TAxisProd0176StableWitnesses, GeneralCK/Certificates/E8TAxisProd0177StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0174StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0174StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4115470352964345628383522602588716836376905846, 4115470352964345628383522602588716836376905847⟩
def centerAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453293830838237185210198542808669484539789010133⟩
def centerALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1008926063354791867585944205900164502304869828050⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453293830838237185210198542808669483990033196245, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-8230940705928691256767045205177433119894175747, -8230940705928691256767045205177433119892078594⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨285192593881366198366266551507570054859771280736, 285192593881366198366266551507570054859771280737⟩
def centerCExp : DyadicInterval precision := ⟨989249250084191454782878915757453835081293639377, 989249250084191454782878915757453837280316894930⟩
def centerCLog : DyadicInterval precision := ⟨755494094557775419733629936915105549646895953847, 755494094557775419733629936915105551845919209400⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨989249250084191454782878915757453835631049453265, scale precision, 989249250084191454782878915757453836730561081042, scale precision,
    0, 128, 0, 128, ⟨-570385187762732396732533103015140110531744399752, -570385187762732396732533103015140110531742302599⟩, ⟨-570385187762732396732533103015140108907342820348, -570385187762732396732533103015140108907340723195⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨590820769409479240391595982954345684372803415357, 590820769409479240391595982954345684372803415358⟩
def centerBExp : DyadicInterval precision := ⟨651128984070679706119718143228295382850779896366, 651128984070679706119718143228295385049803151919⟩
def centerBLog : DyadicInterval precision := ⟨538518755746088644794944072837836816144653996920, 538518755746088644794944072837836818343677252473⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨651128984070679706119718143228295383400535710254, scale precision, 651128984070679706119718143228295384500047338031, scale precision,
    1, 128, 1, 128, ⟨-1181641538818958480783191965908691369979570798752, -1181641538818958480783191965908691369979568701599⟩, ⟨-1181641538818958480783191965908691367511644959828, -1181641538818958480783191965908691367511642862675⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4432047174048269527644776165804031130864675905⟩
def wholeAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨276612062758662568906369624396592009937292335738, 293794542745046640067294646993992613811650700681⟩
def wholeCExp : DyadicInterval precision := ⟨977672686556378899154880479700583293524917980231, 1000933553987258952345939520956286575061748668116⟩
def wholeCLog : DyadicInterval precision := ⟨748574071273698567109675504566805884354344410173, 762445454105232810722635421847765875875382051583⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨977672686556378899154880479700583294074673794119, scale precision, 1000933553987258952345939520956286574511992854228, scale precision,
    0, 128, 0, 128, ⟨-587589085490093280134589293987985228445120460382, -587589085490093280134589293987985228445118363229⟩, ⟨-553224125517325137812739248793184019071866080044, -553224125517325137812739248793184019071863982891⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨571867727011376782524101799745689538714186439501, 609948203639037705369913311370273420421707818261⟩
def wholeBExp : DyadicInterval precision := ⟨634306776250422930396265232704260356947137617423, 668237834944705656718489889486917624797957715275⟩
def wholeBLog : DyadicInterval precision := ⟨526834701390773474742213048548690856015111287941, 550306859363594067466694575029638277360867137954⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨634306776250422930396265232704260357496893431311, scale precision, 668237834944705656718489889486917624248201901387, scale precision,
    1, 128, 1, 128, ⟨-1219896407278075410739826622740546842110105063993, -1219896407278075410739826622740546842110102966840⟩, ⟨-1143735454022753565048203599491379076226004082423, -1143735454022753565048203599491379076226001985270⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0174StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0175StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0175StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4115470352964345628383522602588716836376905846, 4115470352964345628383522602588716836376905847⟩
def centerAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453293830838237185210198542808669484539789010133⟩
def centerALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1008926063354791867585944205900164502304869828050⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453293830838237185210198542808669483990033196245, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-8230940705928691256767045205177433119894175747, -8230940705928691256767045205177433119892078594⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨268710009678593781895538666619641291235894670402, 268710009678593781895538666619641291235894670403⟩
def centerCExp : DyadicInterval precision := ⟨1011815990481221450291314665696010399365269729665, 1011815990481221450291314665696010401564292985218⟩
def centerCLog : DyadicInterval precision := ⟨768890154684483194496653352947833578580675641014, 768890154684483194496653352947833580779698896567⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1011815990481221450291314665696010399915025543553, scale precision, 1011815990481221450291314665696010401014537171330, scale precision,
    0, 128, 0, 128, ⟨-537420019357187563791077333239282583265876497615, -537420019357187563791077333239282583265874400462⟩, ⟨-537420019357187563791077333239282581677704281147, -537420019357187563791077333239282581677702183994⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨553817012846239572030632039512777462798488380065, 553817012846239572030632039512777462798488380066⟩
def centerBExp : DyadicInterval precision := ⟨684949936475228418391665946591395601575889715208, 684949936475228418391665946591395603774912970761⟩
def centerBLog : DyadicInterval precision := ⟨561730524883329463403743135343508856784159602856, 561730524883329463403743135343508858983182858409⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨684949936475228418391665946591395602125645529096, scale precision, 684949936475228418391665946591395603225157156873, scale precision,
    1, 128, 1, 128, ⟨-1107634025692479144061264079025554926770011017915, -1107634025692479144061264079025554926770008920762⟩, ⟨-1107634025692479144061264079025554924423944599499, -1107634025692479144061264079025554924423942502346⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4432047174048269527644776165804031130864675905⟩
def wholeAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨260168808084051724207340356924670106199222168443, 277271358307143331511699022410631785361523651159⟩
def wholeCExp : DyadicInterval precision := ⟨1000030902333961399782025547003040621404574319551, 1023711738189858330509771486033612624930537471063⟩
def wholeCLog : DyadicInterval precision := ⟨761909615141175183101165194030151438310789443093, 775902589655979148194684620099574952915501182542⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1000030902333961399782025547003040621954330133439, scale precision, 1023711738189858330509771486033612624380781657175, scale precision,
    0, 128, 0, 128, ⟨-554542716614286663023398044821263571526492544724, -554542716614286663023398044821263571526490447571⟩, ⟨-520337616168103448414680713849340211613586726374, -520337616168103448414680713849340211613584629221⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨535189694952680963304873857541902184088170916889, 572607767046543353332268274684614845757899707892⟩
def wholeBExp : DyadicInterval precision := ⟨667561445102611042047300304069486736956553634379, 702634193937220187064536449449028086391984188306⟩
def wholeBLog : DyadicInterval precision := ⟨549842623298499205295380975719932217036023695291, 573722262346269697173879383144077550070318533733⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨667561445102611042047300304069486737506309448267, scale precision, 702634193937220187064536449449028085842228374418, scale precision,
    1, 128, 1, 128, ⟨-1145215534093086706664536549369229692719388580518, -1145215534093086706664536549369229692719386483365⟩, ⟨-1070379389905361926609747715083804367032833174086, -1070379389905361926609747715083804367032831076933⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0175StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0176StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0176StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3482318024844347500022322904444928295572395252, 3482318024844347500022322904444928295572395253⟩
def centerAExp : DyadicInterval precision := ⟨1454553569581723058392238696431353224119669669100, 1454553569581723058392238696431353226318692924653⟩
def centerALog : DyadicInterval precision := ⟨1009557569928173087760872372803888449827653659813, 1009557569928173087760872372803888452026676915366⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454553569581723058392238696431353224669425482988, scale precision, 1454553569581723058392238696431353225768937110765, scale precision,
    0, 128, 0, 128, ⟨-6964636049688695000044645808889857143527710010, -6964636049688695000044645808889857143525612857⟩, ⟨-6964636049688695000044645808889856038763968154, -6964636049688695000044645808889856038761871001⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨314063896595388511688731668307850747220145675387, 314063896595388511688731668307850747220145675388⟩
def centerDExp : DyadicInterval precision := ⟨950926933437474332245963667891130159890397626751, 950926933437474332245963667891130162089420882304⟩
def centerDLog : DyadicInterval precision := ⟨732460073978448216291062163497299207879791564564, 732460073978448216291062163497299210078814820117⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨950926933437474332245963667891130160440153440639, scale precision, 950926933437474332245963667891130161539665068416, scale precision,
    0, 128, 0, 128, ⟨-628127793190777023377463336615701495285224847764, -628127793190777023377463336615701495285222750611⟩, ⟨-628127793190777023377463336615701493595359950940, -628127793190777023377463336615701493595357853787⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨317732630513434704967453952884466923458080761012, 317732630513434704967453952884466923458080761013⟩
def centerCExp : DyadicInterval precision := ⟨946164769728362764799933754019820743928033313662, 946164769728362764799933754019820746127056569215⟩
def centerCLog : DyadicInterval precision := ⟨729572200459498790870213889183536750846577658467, 729572200459498790870213889183536753045600914020⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨946164769728362764799933754019820744477789127550, scale precision, 946164769728362764799933754019820745577300755327, scale precision,
    0, 128, 0, 128, ⟨-635465261026869409934907905768933847765347667994, -635465261026869409934907905768933847765345570841⟩, ⟨-635465261026869409934907905768933846066977473211, -635465261026869409934907905768933846066975376058⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨666106756383862673558305051225837220619481698959, 666106756383862673558305051225837220619481698960⟩
def centerBExp : DyadicInterval precision := ⟨587386026335439094808983666597445456064503441302, 587386026335439094808983666597445458263526696855⟩
def centerBLog : DyadicInterval precision := ⟨493742922774325109331702915909518651850828301866, 493742922774325109331702915909518654049851557419⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨587386026335439094808983666597445456614259255190, scale precision, 587386026335439094808983666597445457713770882967, scale precision,
    1, 128, 1, 128, ⟨-1332213512767725347116610102451674442606836656775, -1332213512767725347116610102451674442606834559622⟩, ⟨-1332213512767725347116610102451674439871092236217, -1332213512767725347116610102451674439871090139064⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1455183847209450510423929547351191477780877052172⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009873425488092576137085252579843092274389747387⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨305741530935075953839244385929164159203164552709, 322408132378444526209018649139695484921606350583⟩
def wholeDExp : DyadicInterval precision := ⟨940130328208408204655831711119657709679621898349, 961818742565408613466907997915298000639465600973⟩
def wholeDLog : DyadicInterval precision := ⟨725904575743015811666185701912516249682142746744, 739043717569107002066769324458966200204494229375⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨940130328208408204655831711119657710229377712237, scale precision, 961818742565408613466907997915298000089709787085, scale precision,
    0, 128, 0, 128, ⟨-644816264756889052418037298279390970697849535889, -644816264756889052418037298279390970697847438736⟩, ⟨-611483061870151907678488771858328317570965873209, -611483061870151907678488771858328317570963776056⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨309067891082506609001259954034646670914709424586, 326421309931081011329908709873818033517884938469⟩
def wholeCExp : DyadicInterval precision := ⟨934981420214208148924752773574616555275528441997, 957450516359962807439347788495256247582058839168⟩
def wholeCLog : DyadicInterval precision := ⟨722767868800246844242748713431166334776712265638, 736406868263745359049599811702686317853918479869⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨934981420214208148924752773574616555825284255885, scale precision, 957450516359962807439347788495256247032303025280, scale precision,
    0, 128, 0, 128, ⟨-652842619862162022659817419747636067895113159229, -652842619862162022659817419747636067895111062076⟩, ⟨-618135782165013218002519908069293340990244391129, -618135782165013218002519908069293340990242293976⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨646445472228829654634772553930930557688303760500, 685963999756797209752584202718138649636232751543⟩
def wholeBExp : DyadicInterval precision := ⟨571639458269859880067295969679856098763554867968, 603404522986363053747953111358900317535848866917⟩
def wholeBLog : DyadicInterval precision := ⟨482467279940599822739468415949780307967224533273, 505124717004032677652167272468249729031735785440⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨571639458269859880067295969679856099313310681856, scale precision, 603404522986363053747953111358900316986093053029, scale precision,
    1, 128, 1, 128, ⟨-1371927999513594419505168405436277300678018618627, -1371927999513594419505168405436277300678016521474⟩, ⟨-1292890944457659309269545107861861114045049074210, -1292890944457659309269545107861861114045046977057⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0176StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0177StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0177StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3482318024844347500022322904444928295572395252, 3482318024844347500022322904444928295572395253⟩
def centerAExp : DyadicInterval precision := ⟨1454553569581723058392238696431353224119669669100, 1454553569581723058392238696431353226318692924653⟩
def centerALog : DyadicInterval precision := ⟨1009557569928173087760872372803888449827653659813, 1009557569928173087760872372803888452026676915366⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454553569581723058392238696431353224669425482988, scale precision, 1454553569581723058392238696431353225768937110765, scale precision,
    0, 128, 0, 128, ⟨-6964636049688695000044645808889857143527710010, -6964636049688695000044645808889857143525612857⟩, ⟨-6964636049688695000044645808889856038763968154, -6964636049688695000044645808889856038761871001⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨297440437897247181273022509268442947544064301498, 297440437897247181273022509268442947544064301499⟩
def centerDExp : DyadicInterval precision := ⟨972806985794329725044362385369131888111738659096, 972806985794329725044362385369131890310761914649⟩
def centerDLog : DyadicInterval precision := ⟨745655734605380757184922339086747309072128874695, 745655734605380757184922339086747311271152130248⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨972806985794329725044362385369131888661494472984, scale precision, 972806985794329725044362385369131889761006100761, scale precision,
    0, 128, 0, 128, ⟨-594880875794494362546045018536885895914058159347, -594880875794494362546045018536885895914056062194⟩, ⟨-594880875794494362546045018536885894262201143797, -594880875794494362546045018536885894262199046644⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨301090336219049733479024143974588845684788984672, 301090336219049733479024143974588845684788984673⟩
def centerCExp : DyadicInterval precision := ⟨967960198093100774725826814412892945283814203732, 967960198093100774725826814412892947482837459285⟩
def centerCLog : DyadicInterval precision := ⟨742742936575026580338283659927493989573932517243, 742742936575026580338283659927493991772955772796⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨967960198093100774725826814412892945833570017620, scale precision, 967960198093100774725826814412892946933081645397, scale precision,
    0, 128, 0, 128, ⟨-602180672438099466958048287949177692199643129766, -602180672438099466958048287949177692199641032613⟩, ⟨-602180672438099466958048287949177690539514906079, -602180672438099466958048287949177690539512808926⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨627734674313845276713891603396326954025701914681, 627734674313845276713891603396326954025701914682⟩
def centerBExp : DyadicInterval precision := ⟨619054130668966518376295543884085235165411274213, 619054130668966518376295543884085237364434529766⟩
def centerBLog : DyadicInterval precision := ⟨516159451516783793070293039370052249991364757062, 516159451516783793070293039370052252190388012615⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨619054130668966518376295543884085235715167088101, scale precision, 619054130668966518376295543884085236814678715878, scale precision,
    1, 128, 1, 128, ⟨-1255469348627690553427783206792653909349302722935, -1255469348627690553427783206792653909349300625782⟩, ⟨-1255469348627690553427783206792653906753507032946, -1255469348627690553427783206792653906753504935793⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1455183847209450510423929547351191477780877052172⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009873425488092576137085252579843092274389747387⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨289160022559818845156424937767397025574157886773, 305741530935075953839244385929164159203164552710⟩
def wholeDExp : DyadicInterval precision := ⟨961818742565408613466907997915297998440442345420, 983892922446469118853387927975743981788878518423⟩
def wholeDLog : DyadicInterval precision := ⟨739043717569107002066769324458966198005470973822, 752296360822110031467471195763059032944457639560⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨961818742565408613466907997915297998990198159308, scale precision, 983892922446469118853387927975743981239122704535, scale precision,
    0, 128, 0, 128, ⟨-611483061870151907678488771858328319241694434782, -611483061870151907678488771858328319241692337629⟩, ⟨-578320045119637690312849875534794050331694399297, -578320045119637690312849875534794050331692302144⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨292469745339287832750898622949857188568070755119, 309733574902450231722473605348773919922730774136⟩
def wholeCExp : DyadicInterval precision := ⟨956578715624353311846366700153450025297824923590, 979446742750594530073246032069957402733356641105⟩
def wholeCLog : DyadicInterval precision := ⟨735880041861580198236598054257202695547244734903, 749636661828918999346616613489288630844364976411⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨956578715624353311846366700153450025847580737478, scale precision, 979446742750594530073246032069957402183600827217, scale precision,
    0, 128, 0, 128, ⟨-619467149804900463444947210697547840685402906000, -619467149804900463444947210697547840685400808847⟩, ⟨-584939490678575665501797245899714376315813094168, -584939490678575665501797245899714376315810997015⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨608441580868175171101115292385503035792040508113, 647212879114126499197397516204537987317879341456⟩
def wholeBExp : DyadicInterval precision := ⟨602771182979807624150637266322980183187884312742, 635615904958952492906927750593163856342107150225⟩
def wholeBLog : DyadicInterval precision := ⟨504676382132539218648431185351501377367190344454, 527747330821057189438712369308479411200703040297⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨602771182979807624150637266322980183737640126630, scale precision, 635615904958952492906927750593163855792351336337, scale precision,
    1, 128, 1, 128, ⟨-1294425758228252998394795032409075975968718314805, -1294425758228252998394795032409075975968716217652⟩, ⟨-1216883161736350342202230584771006070320002585574, -1216883161736350342202230584771006070320000488421⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0177StableWitnesses

end


