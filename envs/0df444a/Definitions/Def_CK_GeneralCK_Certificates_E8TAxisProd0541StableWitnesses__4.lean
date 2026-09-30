-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0541StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0541StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:42:09.032183+00:00
-- url     : https://prove2.me/theorems/bfab188f-730d-4d20-9a7a-75883daa56ed
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0541StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0542StableWitnesses, GeneralCK.Certificates.E8TAxisProd05…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0541StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0542StableWitnesses, GeneralCK.Certificates.E8TAxisProd0543StableWitnesses, GeneralCK.Certificates.E8TAxisProd0544StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0541StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0542StableWitnesses, GeneralCK.Certificates.E8TAxisProd0543StableWitnesses, GeneralCK.Certificates.E8TAxisProd0544StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0541StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0542StableWitnesses, GeneralCK.Certificates.E8TAxisProd0543StableWitnesses, GeneralCK.Certificates.E8TAxisProd0544StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0541StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0542StableWitnesses, GeneralCK/Certificates/E8TAxisProd0543StableWitnesses, GeneralCK/Certificates/E8TAxisProd0544StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0541StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0541StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4273758705152157645723775860095423839948701825, 4273758705152157645723775860095423839948701826⟩
def centerAExp : DyadicInterval precision := ⟨1452979066123426753084482090982379267943336487380, 1452979066123426753084482090982379270142359742933⟩
def centerALog : DyadicInterval precision := ⟨1008768229300280628272830658947964075013109562599, 1008768229300280628272830658947964077212132818152⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452979066123426753084482090982379268493092301268, scale precision, 1452979066123426753084482090982379269592603929045, scale precision,
    0, 128, 0, 128, ⟨-8547517410304315291447551720190848232878905189, -8547517410304315291447551720190848232876808036⟩, ⟨-8547517410304315291447551720190847126917999264, -8547517410304315291447551720190847126915902111⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨536053595931077576481867337467978800983992300722, 536053595931077576481867337467978800983992300723⟩
def centerDExp : DyadicInterval precision := ⟨701804023530382254660990345893463172517499932104, 701804023530382254660990345893463174716523187657⟩
def centerDLog : DyadicInterval precision := ⟨573161517422994399504898462730524988803441785707, 573161517422994399504898462730524991002465041260⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨701804023530382254660990345893463173067255745992, scale precision, 701804023530382254660990345893463174166767373769, scale precision,
    1, 128, 1, 128, ⟨-1072107191862155152963734674935957603112848026398, -1072107191862155152963734674935957603112845929245⟩, ⟨-1072107191862155152963734674935957600823123273644, -1072107191862155152963734674935957600823121176491⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨540970721883223069660431328457232899521537719765, 540970721883223069660431328457232899521537719766⟩
def centerCExp : DyadicInterval precision := ⟨697097529196056582294895581264758236342410579856, 697097529196056582294895581264758238541433835409⟩
def centerCLog : DyadicInterval precision := ⟨569978406193340801690666174090227982766515121867, 569978406193340801690666174090227984965538377420⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨697097529196056582294895581264758236892166393744, scale precision, 697097529196056582294895581264758237991678021521, scale precision,
    1, 128, 1, 128, ⟨-1081941443766446139320862656914465800195668469113, -1081941443766446139320862656914465800195666371960⟩, ⟨-1081941443766446139320862656914465797890484507102, -1081941443766446139320862656914465797890482409949⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1236664515870506604496763334367210203835899728652, 1236664515870506604496763334367210203835899728653⟩
def centerBExp : DyadicInterval precision := ⟨269050557334394533688082950305090988106125215654, 269050557334394533688082950305090990305148471207⟩
def centerBLog : DyadicInterval precision := ⟨246958875130372519871257300984791487510515637248, 246958875130372519871257300984791489709538892801⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨269050557334394533688082950305090988655881029542, scale precision, 269050557334394533688082950305090989755392657319, scale precision,
    2, 128, 2, 128, ⟨-2473329031741013208993526668734420410658112930176, -2473329031741013208993526668734420410658110833023⟩, ⟨-2473329031741013208993526668734420404685488081593, -2473329031741013208993526668734420404685485984440⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4115470352964345628383522602588716836376905846, 4432047174048269527644776165804031130864675905⟩
def wholeAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1453293830838237185210198542808669484539789010133⟩
def wholeALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1008926063354791867585944205900164502304869828050⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1453293830838237185210198542808669483990033196245, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-8230940705928691256767045205177433119894175747, -8230940705928691256767045205177433119892078594⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨530829944683894805437507571749273968698214433227, 541289809268942399956535792498120861936820641713⟩
def wholeDExp : DyadicInterval precision := ⟨696793203199184192771083052087923259249531509367, 706838726837510462039096914346652693399387599334⟩
def wholeDLog : DyadicInterval precision := ⟨569772344639491636839148332004312889556812159164, 576558946667156773600005109862481907627324132952⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨696793203199184192771083052087923259799287323255, scale precision, 706838726837510462039096914346652692849631785446, scale precision,
    1, 128, 1, 128, ⟨-1082579618537884799913071584996241725026737710144, -1082579618537884799913071584996241725026735612991⟩, ⟨-1061659889367789610875015143498547936259722216904, -1061659889367789610875015143498547936259720119751⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨535553400974678793009190768153096992952396708154, 546401619392085897506840809385864583516963959249⟩
def wholeCExp : DyadicInterval precision := ⟨691935945027991918118654058539810648207156943556, 702284569009747352924567969959510391274408578837⟩
def wholeCLog : DyadicInterval precision := ⟨566479517962491295017609498851617411753160949619, 573486131750281831641429272151163117750271230232⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨691935945027991918118654058539810648756912757444, scale precision, 702284569009747352924567969959510390724652764949, scale precision,
    1, 128, 1, 128, ⟨-1092803238784171795013681618771729168195118854523, -1092803238784171795013681618771729168195116757370⟩, ⟨-1071106801949357586018381536306193984760715472429, -1071106801949357586018381536306193984760713375276⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1221795931144030462646057064618272276466780367496, 1251622469881269061424085779610899873860215539036⟩
def wholeBExp : DyadicInterval precision := ⟨263599264527506127722865872246850404429052548340, 274581001386679327913715318472937462700739934846⟩
def wholeBLog : DyadicInterval precision := ⟨242347833599863464987323661291755362075066573189, 251622048659282135342588361709761100992031322802⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨263599264527506127722865872246850404978808362228, scale precision, 274581001386679327913715318472937462150984120958, scale precision,
    2, 128, 2, 128, ⟨-2503244939762538122848171559221799750768502171798, -2503244939762538122848171559221799750768500074645⟩, ⟨-2443591862288060925292114129236544550007397853537, -2443591862288060925292114129236544550007395756384⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0541StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0542StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0542StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3957182113162240766624229437560720104187299711, 3957182113162240766624229437560720104187299712⟩
def centerAExp : DyadicInterval precision := ⟨1453608663518239684990297266292415545523124059933, 1453608663518239684990297266292415547722147315486⟩
def centerALog : DyadicInterval precision := ⟨1009083914440550911538268226967653949061006604559, 1009083914440550911538268226967653951260029860112⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453608663518239684990297266292415546072879873821, scale precision, 1453608663518239684990297266292415547172391501598, scale precision,
    0, 128, 0, 128, ⟨-7914364226324481533248458875121440761116590109, -7914364226324481533248458875121440761114492956⟩, ⟨-7914364226324481533248458875121439655634705892, -7914364226324481533248458875121439655632608739⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨546538709428945749870773924191788198118687927157, 546538709428945749870773924191788198118687927158⟩
def centerDExp : DyadicInterval precision := ⟨691806148899640566657527120936512860452889890625, 691806148899640566657527120936512862651913146178⟩
def centerDLog : DyadicInterval precision := ⟨566391424872267910855012963449734473930997225626, 566391424872267910855012963449734476130020481179⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨691806148899640566657527120936512861002645704513, scale precision, 691806148899640566657527120936512862102157332290, scale precision,
    1, 128, 1, 128, ⟨-1093077418857891499741547848383576397398784651881, -1093077418857891499741547848383576397398782554728⟩, ⟨-1093077418857891499741547848383576395075969153903, -1093077418857891499741547848383576395075967056750⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨551113380033424210358861076900893208397801453848, 551113380033424210358861076900893208397801453849⟩
def centerCExp : DyadicInterval precision := ⟨687488808891167890173757938134554326104308034207, 687488808891167890173757938134554328303331289760⟩
def centerCLog : DyadicInterval precision := ⟨563458201153976097449858352809122795203885992896, 563458201153976097449858352809122797402909248449⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨687488808891167890173757938134554326654063848095, scale precision, 687488808891167890173757938134554327753575475872, scale precision,
    1, 128, 1, 128, ⟨-1102226760066848420717722153801786417964305194372, -1102226760066848420717722153801786417964303097219⟩, ⟨-1102226760066848420717722153801786415626902718174, -1102226760066848420717722153801786415626900621021⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1265637807813157044742571763591955914665253087055, 1265637807813157044742571763591955914665253087056⟩
def centerBExp : DyadicInterval precision := ⟨258591771339000681889091683183742482279144100658, 258591771339000681889091683183742484478167356211⟩
def centerBLog : DyadicInterval precision := ⟨238099327426973485000968729050588434844797594688, 238099327426973485000968729050588437043820850241⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨258591771339000681889091683183742482828899914546, scale precision, 258591771339000681889091683183742483928411542323, scale precision,
    2, 128, 2, 128, ⟨-2531275615626314089485143527183911832437601535742, -2531275615626314089485143527183911832437599438589⟩, ⟨-2531275615626314089485143527183911826223412909632, -2531275615626314089485143527183911826223410812479⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4115470352964345628383522602588716836376905847⟩
def wholeAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨541289809268942399956535792498120861936820641712, 551800421242914454820810459967297938576086292891⟩
def wholeDExp : DyadicInterval precision := ⟨686842745746340006938348233447115251068009001225, 696793203199184192771083052087923261448554764920⟩
def wholeDLog : DyadicInterval precision := ⟨563018755595924057929845042473976395760693996545, 569772344639491636839148332004312891755835414717⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨686842745746340006938348233447115251617764815113, scale precision, 696793203199184192771083052087923260898798951032, scale precision,
    1, 128, 1, 128, ⟨-1103600842485828909641620919934595878321974184929, -1103600842485828909641620919934595878321972087776⟩, ⟨-1082579618537884799913071584996241722720546953858, -1082579618537884799913071584996241722720544856705⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨545670619686481230314324718314518457952700581178, 556569975089840128439242242176707225591119196536⟩
def wholeCExp : DyadicInterval precision := ⟨682374374700059046691284209616347693297163575149, 692628462959122813045316584567788630608460478540⟩
def wholeCLog : DyadicInterval precision := ⟨559975792579873263973208432215525532768157911234, 566949442603733948025781996420997542769449813829⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨682374374700059046691284209616347693846919389037, scale precision, 692628462959122813045316584567788630058704664652, scale precision,
    1, 128, 1, 128, ⟨-1113139950179680256878484484353414452359700161041, -1113139950179680256878484484353414452359698063888⟩, ⟨-1091341239372962460628649436629036914745373328065, -1091341239372962460628649436629036914745371230912⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1250596863203672707838717960535866711244399595779, 1280767498976359067186329898555505526994729663143⟩
def wholeBExp : DyadicInterval precision := ⟨253292851778778050088485988243151703822463514009, 263969485080018583197108197421415440052457284447⟩
def wholeBLog : DyadicInterval precision := ⟨233590076477705864589284692672109730060114138406, 242661449975317224473730962000971188902524562751⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨253292851778778050088485988243151704372219327897, scale precision, 263969485080018583197108197421415439502701470559, scale precision,
    2, 128, 2, 128, ⟨-2561534997952718134372659797111011057161555506992, -2561534997952718134372659797111011057161553409839⟩, ⟨-2501193726407345415677435921071733419445005151901, -2501193726407345415677435921071733419445003054748⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0542StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0543StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0543StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3957182113162240766624229437560720104187299711, 3957182113162240766624229437560720104187299712⟩
def centerAExp : DyadicInterval precision := ⟨1453608663518239684990297266292415545523124059933, 1453608663518239684990297266292415547722147315486⟩
def centerALog : DyadicInterval precision := ⟨1009083914440550911538268226967653949061006604559, 1009083914440550911538268226967653951260029860112⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453608663518239684990297266292415546072879873821, scale precision, 1453608663518239684990297266292415547172391501598, scale precision,
    0, 128, 0, 128, ⟨-7914364226324481533248458875121440761116590109, -7914364226324481533248458875121440761114492956⟩, ⟨-7914364226324481533248458875121439655634705892, -7914364226324481533248458875121439655632608739⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨536053595931077576481867337467978800983992300722, 536053595931077576481867337467978800983992300723⟩
def centerDExp : DyadicInterval precision := ⟨701804023530382254660990345893463172517499932104, 701804023530382254660990345893463174716523187657⟩
def centerDLog : DyadicInterval precision := ⟨573161517422994399504898462730524988803441785707, 573161517422994399504898462730524991002465041260⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨701804023530382254660990345893463173067255745992, scale precision, 701804023530382254660990345893463174166767373769, scale precision,
    1, 128, 1, 128, ⟨-1072107191862155152963734674935957603112848026398, -1072107191862155152963734674935957603112845929245⟩, ⟨-1072107191862155152963734674935957600823123273644, -1072107191862155152963734674935957600823121176491⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨540606108107481498657353860407597366016007338820, 540606108107481498657353860407597366016007338821⟩
def centerCExp : DyadicInterval precision := ⟨697445438191322965371137366859911675620399266962, 697445438191322965371137366859911677819422522515⟩
def centerCLog : DyadicInterval precision := ⟨570213942555347739787680098453933651141271986119, 570213942555347739787680098453933653340295241672⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨697445438191322965371137366859911676170155080850, scale precision, 697445438191322965371137366859911677269666708627, scale precision,
    1, 128, 1, 128, ⟨-1081212216214962997314707720815194733184032755984, -1081212216214962997314707720815194733184030658831⟩, ⟨-1081212216214962997314707720815194730879998696449, -1081212216214962997314707720815194730879996599296⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1236154711180115104377748668762360489561309511327, 1236154711180115104377748668762360489561309511328⟩
def centerBExp : DyadicInterval precision := ⟨269238324613378522321381995442111107575998485482, 269238324613378522321381995442111109775021741035⟩
def centerBLog : DyadicInterval precision := ⟨247117441453886951306962367455164419947787606293, 247117441453886951306962367455164422146810861846⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨269238324613378522321381995442111108125754299370, scale precision, 269238324613378522321381995442111109225265927147, scale precision,
    2, 128, 2, 128, ⟨-2472309422360230208755497337524720982106849836010, -2472309422360230208755497337524720982106847738857⟩, ⟨-2472309422360230208755497337524720976138390306454, -2472309422360230208755497337524720976138388209301⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4115470352964345628383522602588716836376905847⟩
def wholeAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨530829944683894805437507571749273968698214433227, 541289809268942399956535792498120861936820641713⟩
def wholeDExp : DyadicInterval precision := ⟨696793203199184192771083052087923259249531509367, 706838726837510462039096914346652693399387599334⟩
def wholeDLog : DyadicInterval precision := ⟨569772344639491636839148332004312889556812159164, 576558946667156773600005109862481907627324132952⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨696793203199184192771083052087923259799287323255, scale precision, 706838726837510462039096914346652692849631785446, scale precision,
    1, 128, 1, 128, ⟨-1082579618537884799913071584996241725026737710144, -1082579618537884799913071584996241725026735612991⟩, ⟨-1061659889367789610875015143498547936259722216904, -1061659889367789610875015143498547936259720119751⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨535189694952680963304873857541902184088170916889, 546036088568359868563557417653691444700192798517⟩
def wholeCExp : DyadicInterval precision := ⟨692282146739865687136386266145463897029264927278, 702634193937220187064536449449028086391984188306⟩
def wholeCLog : DyadicInterval precision := ⟨566714460319428615427648751105297632199640764599, 573722262346269697173879383144077550070318533733⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨692282146739865687136386266145463897579020741166, scale precision, 702634193937220187064536449449028085842228374418, scale precision,
    1, 128, 1, 128, ⟨-1092072177136719737127114835307382890560995836405, -1092072177136719737127114835307382890560993739252⟩, ⟨-1070379389905361926609747715083804367032833174086, -1070379389905361926609747715083804367032831076933⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1221289186495237552333633986829731818392043970365, 1251109614479902482450087089454370519389941499340⟩
def wholeBExp : DyadicInterval precision := ⟨263784328646725125594385198566969095481065592425, 274771477682294003200162104212412093504310575380⟩
def wholeBLog : DyadicInterval precision := ⟨242504611099818860322266425478546456226951724020, 251782390189895003793018217259747601888115127218⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨263784328646725125594385198566969096030821406313, scale precision, 274771477682294003200162104212412092954554761492, scale precision,
    2, 128, 2, 128, ⟨-2502219228959804964900174178908741041825815646953, -2502219228959804964900174178908741041825813549800⟩, ⟨-2442578372990475104667267973659463633859953526240, -2442578372990475104667267973659463633859951429087⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0543StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0544StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0544StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨614899600379008269805806303663110304550585682120, 614899600379008269805806303663110304550585682121⟩
def centerCExp : DyadicInterval precision := ⟨630023389799375733331181083259263315823384041562, 630023389799375733331181083259263318022407297115⟩
def centerCLog : DyadicInterval precision := ⟨523844646462631899478621863658448116320781668475, 523844646462631899478621863658448118519804924028⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨630023389799375733331181083259263316373139855450, scale precision, 630023389799375733331181083259263317472651483227, scale precision,
    1, 128, 1, 128, ⟨-1229799200758016539611612607326220610376472719344, -1229799200758016539611612607326220610376470622191⟩, ⟨-1229799200758016539611612607326220607825872106291, -1229799200758016539611612607326220607825870009138⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1449050285296061261902869726808353223886549525093, 1449050285296061261902869726808353223886549525094⟩
def centerBExp : DyadicInterval precision := ⟨201191829071996422782496815063135779246054694885, 201191829071996422782496815063135781445077950438⟩
def centerBLog : DyadicInterval precision := ⟨188496343057955222875892074281113329134379695123, 188496343057955222875892074281113331333402950676⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨201191829071996422782496815063135779795810508773, scale precision, 201191829071996422782496815063135780895322136550, scale precision,
    2, 128, 2, 128, ⟨-2898100570592122523805739453616706451766647082437, -2898100570592122523805739453616706451766644985284⟩, ⟨-2898100570592122523805739453616706443779553115090, -2898100570592122523805739453616706443779551017937⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨609288920106705212564097463503137419540489809136, 620525713376993890726243486230669236751766393152⟩
def wholeCExp : DyadicInterval precision := ⟨625191410662174971289828163227692437861777483424, 634879306178190624363134265676241259102563958610⟩
def wholeCLog : DyadicInterval precision := ⟨520464282660713953631994375554950653215185680471, 527233897782339346655528651295673577157862421294⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨625191410662174971289828163227692438411533297312, scale precision, 634879306178190624363134265676241258552808144722, scale precision,
    1, 128, 1, 128, ⟨-1241051426753987781452486972461338474788690681931, -1241051426753987781452486972461338474788688584778⟩, ⟨-1218577840213410425128194927006274837815434579096, -1218577840213410425128194927006274837815432481943⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1433000652190747133140296461528537022294471401472, 1465180997430506552453207816301520971106496417913⟩
def wholeBExp : DyadicInterval precision := ⟨196799346538514621922072675398441820336719748364, 205659530237786753191261073116839340344574148073⟩
def wholeBLog : DyadicInterval precision := ⟨184630257610232035645693494506114308839978168135, 192418169807048564429480969397941889393836832578⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨196799346538514621922072675398441820886475562252, scale precision, 205659530237786753191261073116839339794818334185, scale precision,
    2, 128, 2, 128, ⟨-2930361994861013104906415632603041946295675236051, -2930361994861013104906415632603041946295673138898⟩, ⟨-2866001304381494266280592923057074040682151780174, -2866001304381494266280592923057074040682149683021⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0544StableWitnesses

end


