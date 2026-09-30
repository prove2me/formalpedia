-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0026StableWitnesses__5
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0026StableWitnesses__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:49:14.079184+00:00
-- url     : https://prove2.me/theorems/916be08c-6a05-4471-b0c6-d18d8ef5a6b3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0026StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0027StableWitnesses, GeneralCK.Certificates.E8TAxisZero00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0026StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0027StableWitnesses, GeneralCK.Certificates.E8TAxisZero0028StableWitnesses, GeneralCK.Certificates.E8TAxisZero0029StableWitnesses, GeneralCK.Certificates.E8TAxisZero0030StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0026StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0027StableWitnesses, GeneralCK.Certificates.E8TAxisZero0028StableWitnesses, GeneralCK.Certificates.E8TAxisZero0029StableWitnesses, GeneralCK.Certificates.E8TAxisZero0030StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0026StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0027StableWitnesses, GeneralCK.Certificates.E8TAxisZero0028StableWitnesses, GeneralCK.Certificates.E8TAxisZero0029StableWitnesses, GeneralCK.Certificates.E8TAxisZero0030StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0026StableWitnesses (+4 modules: GeneralCK/Certificates/E8TAxisZero0027StableWitnesses, GeneralCK/Certificates/E8TAxisZero0028StableWitnesses, GeneralCK/Certificates/E8TAxisZero0029StableWitnesses, GeneralCK/Certificates/E8TAxisZero0030StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0026StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0026StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨231726644506236789334274380203310872944649121715, 231726644506236789334274380203310872944649121716⟩
def centerDExp : DyadicInterval precision := ⟨1064342052735172538949525898691347990568366073785, 1064342052735172538949525898691347992767389329338⟩
def centerDLog : DyadicInterval precision := ⟨799603206825097674192041553707670067993043651350, 799603206825097674192041553707670070192066906903⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1064342052735172538949525898691347991118121887673, scale precision, 1064342052735172538949525898691347992217633515450, scale precision,
    0, 128, 0, 128, ⟨-463453289012473578668548760406621746644196667401, -463453289012473578668548760406621746644194570248⟩, ⟨-463453289012473578668548760406621745134401916614, -463453289012473578668548760406621745134399819461⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨232378217379230243663107254932754002013508711525, 232378217379230243663107254932754002013508711526⟩
def centerCExp : DyadicInterval precision := ⟨1063393456707912304681398863877223320762677058436, 1063393456707912304681398863877223322961700313989⟩
def centerCLog : DyadicInterval precision := ⟨799054227864764035979759280699562560575947932882, 799054227864764035979759280699562562774971188435⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1063393456707912304681398863877223321312432872324, scale precision, 1063393456707912304681398863877223322411944500101, scale precision,
    0, 128, 0, 128, ⟨-464756434758460487326214509865508004782589250309, -464756434758460487326214509865508004782587153156⟩, ⟨-464756434758460487326214509865508003271447692945, -464756434758460487326214509865508003271445595792⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨477749886812595267904089875359623307557272545269, 477749886812595267904089875359623307557272545270⟩
def centerBExp : DyadicInterval precision := ⟨760092570798305895630605365076300357376013098497, 760092570798305895630605365076300359575036354050⟩
def centerBLog : DyadicInterval precision := ⟨612019337710713729234559670735098353520536379884, 612019337710713729234559670735098355719559635437⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨760092570798305895630605365076300357925768912385, scale precision, 760092570798305895630605365076300359025280540162, scale precision,
    0, 128, 0, 128, ⟨-955499773625190535808179750719246616171613466175, -955499773625190535808179750719246616171611369022⟩, ⟨-955499773625190535808179750719246614057478812059, -955499773625190535808179750719246614057476714906⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨223590532296792858273138350117122513977217811276, 239878763828786629732963390089367294542248751091⟩
def wholeDExp : DyadicInterval precision := ⟨1052534436295863801714746685306812131164545959179, 1076258554488359441934578352032876250046492487573⟩
def wholeDLog : DyadicInterval precision := ⟨792755074273575496363197836249071886194744303106, 806482109433465224369192354012429701629745321451⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1052534436295863801714746685306812131714301773067, scale precision, 1076258554488359441934578352032876249496736673685, scale precision,
    0, 128, 0, 128, ⟨-479757527657573259465926780178734589847864569410, -479757527657573259465926780178734589847862472257⟩, ⟨-447181064593585716546276700234245027207897636639, -447181064593585716546276700234245027207895539486⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨223590532296792858273138350117122513977217811276, 241184626806749055639611155786176124284241534581⟩
def wholeCExp : DyadicInterval precision := ⟨1050655220626468140158581794906027347133078478426, 1076258554488359441934578352032876250046492487573⟩
def wholeCLog : DyadicInterval precision := ⟨791662208582552229743762264383106989815954966690, 806482109433465224369192354012429701629745321451⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1050655220626468140158581794906027347682834292314, scale precision, 1076258554488359441934578352032876249496736673685, scale precision,
    0, 128, 0, 128, ⟨-482369253613498111279222311572352249333215502836, -482369253613498111279222311572352249333213405683⟩, ⟨-447181064593585716546276700234245027207897636639, -447181064593585716546276700234245027207895539486⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨459387967798615484561738103898747303530785179429, 496257886122708299080717656232804391559802806574⟩
def wholeBExp : DyadicInterval precision := ⟨741083167255899678520967171438347783723339308077, 779433753649515438129873373659005449491648691216⟩
def wholeBLog : DyadicInterval precision := ⟨599459970066116025774948586559345270603711332384, 624688092853175616303270580088334960516446661035⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨741083167255899678520967171438347784273095121965, scale precision, 779433753649515438129873373659005448941892877328, scale precision,
    0, 128, 0, 128, ⟨-992515772245416598161435312465608784203788650508, -992515772245416598161435312465608784203786553355⟩, ⟨-918775935597230969123476207797494606030734574454, -918775935597230969123476207797494606030732477301⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0026StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0027StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0027StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨215469853832861228733019240262249168447508352861, 215469853832861228733019240262249168447508352862⟩
def centerDExp : DyadicInterval precision := ⟨1088285489568234168416510694967649720478852956927, 1088285489568234168416510694967649722677876212480⟩
def centerDLog : DyadicInterval precision := ⟨813392086659747652895796213383370383407954793069, 813392086659747652895796213383370385606978048622⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1088285489568234168416510694967649721028608770815, scale precision, 1088285489568234168416510694967649722128120398592, scale precision,
    0, 128, 0, 128, ⟨-430939707665722457466038480524498337633306585522, -430939707665722457466038480524498337633304488369⟩, ⟨-430939707665722457466038480524498336156728923076, -430939707665722457466038480524498336156726825923⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨216118953614859556917907414642547971679695779635, 216118953614859556917907414642547971679695779636⟩
def centerCExp : DyadicInterval precision := ⟨1087319233751136707494100311630733283140787244042, 1087319233751136707494100311630733285339810499595⟩
def centerCLog : DyadicInterval precision := ⟨812838137630430626470014391721701505254155460434, 812838137630430626470014391721701507453178715987⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1087319233751136707494100311630733283690543057930, scale precision, 1087319233751136707494100311630733284790054685707, scale precision,
    0, 128, 0, 128, ⟨-432237907229719113835814829285095944098337525944, -432237907229719113835814829285095944098335428791⟩, ⟨-432237907229719113835814829285095942620447689749, -432237907229719113835814829285095942620445592596⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨442563149837559596326653161341442316960877870587, 442563149837559596326653161341442316960877870588⟩
def centerBExp : DyadicInterval precision := ⟨797587633904908293168880243258517544858995729766, 797587633904908293168880243258517547058018985319⟩
def centerBLog : DyadicInterval precision := ⟨636480059183099424004489343384240018080280825458, 636480059183099424004489343384240020279304081011⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨797587633904908293168880243258517545408751543654, scale precision, 797587633904908293168880243258517546508263171431, scale precision,
    0, 128, 0, 128, ⟨-885126299675119192653306322682884634929130760931, -885126299675119192653306322682884634929128663778⟩, ⟨-885126299675119192653306322682884632914382818573, -885126299675119192653306322682884632914380721420⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨207364037900146833805279022757379167895402526013, 223590532296792858273138350117122513977217811277⟩
def wholeDExp : DyadicInterval precision := ⟨1076258554488359441934578352032876247847469232020, 1100424441361699833197968540687666015087121635409⟩
def wholeDLog : DyadicInterval precision := ⟨806482109433465224369192354012429699430722065898, 820333450761233184846212780159319759056095221943⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1076258554488359441934578352032876248397225045908, scale precision, 1100424441361699833197968540687666014537365821521, scale precision,
    0, 128, 0, 128, ⟨-447181064593585716546276700234245028700975705620, -447181064593585716546276700234245028700973608467⟩, ⟨-414728075800293667610558045514758335060661447385, -414728075800293667610558045514758335060659350232⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨207364037900146833805279022757379167895402526013, 224891258230253913064710509213309086355856044063⟩
def wholeCExp : DyadicInterval precision := ⟨1074344533730943943617918492684994410200193259747, 1100424441361699833197968540687666015087121635409⟩
def wholeCLog : DyadicInterval precision := ⟨805379404807415472260164889560497952148103862327, 820333450761233184846212780159319759056095221943⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1074344533730943943617918492684994410749949073635, scale precision, 1100424441361699833197968540687666014537365821521, scale precision,
    0, 128, 0, 128, ⟨-449782516460507826129421018426618173459582183273, -449782516460507826129421018426618173459580086120⟩, ⟨-414728075800293667610558045514758335060661447385, -414728075800293667610558045514758335060659350232⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨424465904280623337412236094991656409259795096049, 460795368920412028518162504643854518865778764228⟩
def wholeBExp : DyadicInterval precision := ⟨777934035523977631609093955857762633040195656609, 817586731060820878424464751762154419137555379748⟩
def wholeBLog : DyadicInterval precision := ⟨623709673634481061734914998481739642729657739711, 649361398245907818978439547465799274251803053932⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨777934035523977631609093955857762633589951470497, scale precision, 817586731060820878424464751762154418587799565860, scale precision,
    0, 128, 0, 128, ⟨-921590737840824057036325009287709038764382679643, -921590737840824057036325009287709038764380582490⟩, ⟨-848931808561246674824472189983312817536858777432, -848931808561246674824472189983312817536856680279⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0027StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0028StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0028StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨199272515379397466243712200840066988851184259851, 199272515379397466243712200840066988851184259852⟩
def centerDExp : DyadicInterval precision := ⟨1112677029363765823963422130229284076021359517329, 1112677029363765823963422130229284078220382772882⟩
def centerDLog : DyadicInterval precision := ⟨827306521710622256038181567611853437995191413469, 827306521710622256038181567611853440194214669022⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1112677029363765823963422130229284076571115331217, scale precision, 1112677029363765823963422130229284077670626958994, scale precision,
    0, 128, 0, 128, ⟨-398545030758794932487424401680133978424474007328, -398545030758794932487424401680133978424471910175⟩, ⟨-398545030758794932487424401680133976980265129232, -398545030758794932487424401680133976980263032079⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨199919324552184362978580257775708484377034756313, 199919324552184362978580257775708484377034756314⟩
def centerCExp : DyadicInterval precision := ⟨1111692601737834304960484805256848518456948593643, 1111692601737834304960484805256848520655971849196⟩
def centerCLog : DyadicInterval precision := ⟨826747501553732937550752135409491201983324755094, 826747501553732937550752135409491204182348010647⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1111692601737834304960484805256848519006704407531, scale precision, 1111692601737834304960484805256848520106216035308, scale precision,
    0, 128, 0, 128, ⟨-399838649104368725957160515551416969476814439210, -399838649104368725957160515551416969476812342057⟩, ⟨-399838649104368725957160515551416968031326683198, -399838649104368725957160515551416968031324586045⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨407875610928507622577018057544997525448495147745, 407875610928507622577018057544997525448495147746⟩
def centerBExp : DyadicInterval precision := ⟨836360774879119121246522016681364385138060996934, 836360774879119121246522016681364387337084252487⟩
def centerBLog : DyadicInterval precision := ⟨661351236451547867877716675701243489880618219060, 661351236451547867877716675701243492079641474613⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨836360774879119121246522016681364385687816810822, scale precision, 836360774879119121246522016681364386787328438599, scale precision,
    0, 128, 0, 128, ⟨-815751221857015245154036115089995051857664113839, -815751221857015245154036115089995051857662016686⟩, ⟨-815751221857015245154036115089995049936318574299, -815751221857015245154036115089995049936316477146⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨191194719185872429583518944051791718612165764688, 207364037900146833805279022757379167895402526014⟩
def wholeDExp : DyadicInterval precision := ⟨1100424441361699833197968540687666012888098379856, 1125044909933745912773463128462173915391977363052⟩
def wholeDLog : DyadicInterval precision := ⟨820333450761233184846212780159319756857071966390, 834311627217828832252519695712052890740898632922⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1100424441361699833197968540687666013437854193744, scale precision, 1125044909933745912773463128462173914842221549164, scale precision,
    0, 128, 0, 128, ⟨-414728075800293667610558045514758336520950753820, -414728075800293667610558045514758336520948656667⟩, ⟨-382389438371744859167037888103583436510166401088, -382389438371744859167037888103583436510164303935⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨191194719185872429583518944051791718612165764688, 208659993168738163327113473155546913729082918463⟩
def wholeCExp : DyadicInterval precision := ⟨1098474615239151709131967435382893979535030622907, 1125044909933745912773463128462173915391977363052⟩
def wholeCLog : DyadicInterval precision := ⟨819220710211348203542880090538222363061315522711, 834311627217828832252519695712052890740898632922⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1098474615239151709131967435382893980084786436795, scale precision, 1125044909933745912773463128462173914842221549164, scale precision,
    0, 128, 0, 128, ⟨-417319986337476326654226946311093828189607567866, -417319986337476326654226946311093828189605470713⟩, ⟨-382389438371744859167037888103583436510166401088, -382389438371744859167037888103583436510164303935⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨390021907983024779256146395473341757167804190697, 425853338453922988105921025000462397676821471069⟩
def wholeBExp : DyadicInterval precision := ⟨816035899282844599192681770600671260965702902819, 857046406820575460675375243512252172179026178685⟩
def wholeBLog : DyadicInterval precision := ⟨648366564209713227240650953399208860371951583755, 674448983099953378325059509857368476506693482805⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨816035899282844599192681770600671261515458716707, scale precision, 857046406820575460675375243512252171629270364797, scale precision,
    0, 128, 0, 128, ⟨-851706676907845976211842050000924796338244083475, -851706676907845976211842050000924796338241986322⟩, ⟨-780043815966049558512292790946683513398123413187, -780043815966049558512292790946683513398121316034⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0028StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0029StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0029StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨183130084206664803338173257357542686520853245489, 183130084206664803338173257357542686520853245490⟩
def centerDExp : DyadicInterval precision := ⟨1137529777074302590783266488860820386533899110215, 1137529777074302590783266488860820388732922365768⟩
def centerDLog : DyadicInterval precision := ⟨841349102754395012997791326891731422922496904416, 841349102754395012997791326891731425121520159969⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1137529777074302590783266488860820387083654924103, scale precision, 1137529777074302590783266488860820388183166551880, scale precision,
    0, 128, 0, 128, ⟨-366260168413329606676346514715085373748035442635, -366260168413329606676346514715085373748033345482⟩, ⟨-366260168413329606676346514715085372335379636478, -366260168413329606676346514715085372335377539325⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨183774783948819465474550779147620767677048104908, 183774783948819465474550779147620767677048104909⟩
def centerCExp : DyadicInterval precision := ⟨1136526642042149742250331323084048518896921023046, 1136526642042149742250331323084048521095944278599⟩
def centerCLog : DyadicInterval precision := ⟨840784905459560157136219384057041625482494978223, 840784905459560157136219384057041627681518233776⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1136526642042149742250331323084048519446676836934, scale precision, 1136526642042149742250331323084048520546188464711, scale precision,
    0, 128, 0, 128, ⟨-367549567897638930949101558295241536061048589235, -367549567897638930949101558295241536061046492082⟩, ⟨-367549567897638930949101558295241534647145927549, -367549567897638930949101558295241534647143830396⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨373646781925249351030950326683961254976679459701, 373646781925249351030950326683961254976679459702⟩
def centerBExp : DyadicInterval precision := ⟨876468442115516198200232507263586159353508440903, 876468442115516198200232507263586161552531696456⟩
def centerBLog : DyadicInterval precision := ⟨686640711011610567336990065024320224698217460537, 686640711011610567336990065024320226897240716090⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨876468442115516198200232507263586159903264254791, scale precision, 876468442115516198200232507263586161002775882568, scale precision,
    0, 128, 0, 128, ⟨-747293563850498702061900653367922510870071835200, -747293563850498702061900653367922510870069738047⟩, ⟨-747293563850498702061900653367922509036648100762, -747293563850498702061900653367922509036646003609⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨175078047236001450214222015517899197240067851934, 191194719185872429583518944051791718612165764689⟩
def wholeDExp : DyadicInterval precision := ⟨1125044909933745912773463128462173913192954107499, 1150133363234016597447468800724884781224161812840⟩
def wholeDLog : DyadicInterval precision := ⟨834311627217828832252519695712052888541875377369, 848419291580521843596292009329506550515087162287⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1125044909933745912773463128462173913742709921387, scale precision, 1150133363234016597447468800724884780674405998952, scale precision,
    0, 128, 0, 128, ⟨-382389438371744859167037888103583437938498754820, -382389438371744859167037888103583437938496657667⟩, ⟨-350156094472002900428444031035798393781549051388, -350156094472002900428444031035798393781546954235⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨175078047236001450214222015517899197240067851934, 192486267482474676822962020884762084766255799608⟩
def wholeCExp : DyadicInterval precision := ⟨1123058232017299231234434758861740122068523594703, 1150133363234016597447468800724884781224161812840⟩
def wholeCLog : DyadicInterval precision := ⟨833188643880544430188545489483369906970376730420, 848419291580521843596292009329506550515087162287⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1123058232017299231234434758861740122618279408591, scale precision, 1150133363234016597447468800724884780674405998952, scale precision,
    0, 128, 0, 128, ⟨-384972534964949353645924041769524170247942176933, -384972534964949353645924041769524170247940079780⟩, ⟨-350156094472002900428444031035798393781549051388, -350156094472002900428444031035798393781546954235⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨356015818146773315735630103594046256346147492780, 391390994830230264090034133324584929749196342429⟩
def wholeBExp : DyadicInterval precision := ⟨855442204069468392391412930235862394581513556601, 897872332234039104779267097055247456527332583462⟩
def wholeBLog : DyadicInterval precision := ⟨673437420530613622463329923875635176971565091256, 699959742628865241142888209739517591976703657011⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨855442204069468392391412930235862395131269370489, scale precision, 897872332234039104779267097055247455977576769574, scale precision,
    0, 128, 0, 128, ⟨-782781989660460528180068266649169860437637808962, -782781989660460528180068266649169860437635711809⟩, ⟨-712031636293546631471260207188092511797437162463, -712031636293546631471260207188092511797435065310⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0029StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0030StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0030StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨167038046908639942077002110251729919039591159538, 167038046908639942077002110251729919039591159539⟩
def centerDExp : DyadicInterval precision := ⟨1162857440134179458176971713073092284742695293446, 1162857440134179458176971713073092286941718548999⟩
def centerDLog : DyadicInterval precision := ⟨855522544774716820728738318780154511038543003600, 855522544774716820728738318780154513237566259153⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1162857440134179458176971713073092285292451107334, scale precision, 1162857440134179458176971713073092286391962735111, scale precision,
    0, 128, 0, 128, ⟨-334076093817279884154004220503459838770127067543, -334076093817279884154004220503459838770124970390⟩, ⟨-334076093817279884154004220503459837388239667764, -334076093817279884154004220503459837388237570611⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨167680817176903094497100275096363859604686988375, 167680817176903094497100275096363859604686988376⟩
def centerCExp : DyadicInterval precision := ⟨1161835037508704920972156174832617139686325084795, 1161835037508704920972156174832617141885348340348⟩
def centerCLog : DyadicInterval precision := ⟨854953059346986941317017404658810989773707707048, 854953059346986941317017404658810991972730962601⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1161835037508704920972156174832617140236080898683, scale precision, 1161835037508704920972156174832617141335592526460, scale precision,
    0, 128, 0, 128, ⟨-335361634353806188994200550192727719900926748413, -335361634353806188994200550192727719900924651260⟩, ⟨-335361634353806188994200550192727718517823302242, -335361634353806188994200550192727718517821205089⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨339836814519446808266072208879269812676505942047, 339836814519446808266072208879269812676505942048⟩
def centerBExp : DyadicInterval precision := ⟨917973144834696536071405984720458804174720225603, 917973144834696536071405984720458806373743481156⟩
def centerBLog : DyadicInterval precision := ⟨712358343325056846011863535961593443757137395038, 712358343325056846011863535961593445956160650591⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨917973144834696536071405984720458804724476039491, scale precision, 917973144834696536071405984720458805823987667268, scale precision,
    0, 128, 0, 128, ⟨-679673629038893616532144417758539626228277123843, -679673629038893616532144417758539626228275026690⟩, ⟨-679673629038893616532144417758539624477748741501, -679673629038893616532144417758539624477746644348⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨159009523631476834293416684122073812609720086984, 175078047236001450214222015517899197240067851935⟩
def wholeDExp : DyadicInterval precision := ⟨1150133363234016597447468800724884779025138557287, 1175703819620526499056916402241341507477966942436⟩
def wholeDLog : DyadicInterval precision := ⟨848419291580521843596292009329506548316063906734, 862659221266056220624571274243273532289421478776⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1150133363234016597447468800724884779574894371175, scale precision, 1175703819620526499056916402241341506928211128548, scale precision,
    0, 128, 0, 128, ⟨-350156094472002900428444031035798395178724453502, -350156094472002900428444031035798395178722356349⟩, ⟨-318019047262953668586833368244147624536047149377, -318019047262953668586833368244147624536045052224⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨159009523631476834293416684122073812609720086984, 176365549723902348143424292968104815592821027152⟩
def wholeCExp : DyadicInterval precision := ⟨1148108738982243371695955789645787235187714244801, 1175703819620526499056916402241341507477966942436⟩
def wholeCLog : DyadicInterval precision := ⟨847285848658893358182028839792376452210620336745, 862659221266056220624571274243273532289421478776⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1148108738982243371695955789645787235737470058689, scale precision, 1175703819620526499056916402241341506928211128548, scale precision,
    0, 128, 0, 128, ⟨-352731099447804696286848585936209631885462723486, -352731099447804696286848585936209631885460626333⟩, ⟨-318019047262953668586833368244147624536047149377, -318019047262953668586833368244147624536045052224⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨322408132378444526209018649139695484921606350582, 357368151647964377800168166755575814690708449891⟩
def wholeBExp : DyadicInterval precision := ⟨896212258825935063445621868699349681683645879192, 940130328208408204655831711119657711878645153902⟩
def wholeBLog : DyadicInterval precision := ⟨698931057061302088777017185007738617177030672913, 725904575743015811666185701912516251881166002297⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨896212258825935063445621868699349682233401693080, scale precision, 940130328208408204655831711119657711328889340014, scale precision,
    0, 128, 0, 128, ⟨-714736303295928755600336333511151630277934386531, -714736303295928755600336333511151630277932289378⟩, ⟨-644816264756889052418037298279390968988577963593, -644816264756889052418037298279390968988575866440⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0030StableWitnesses

end


