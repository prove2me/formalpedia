-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0652StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0652StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:33:22.051245+00:00
-- url     : https://prove2.me/theorems/3d684c48-a8fb-4d54-b7b5-4f4f60c4fb76
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0652StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0653StableWitnesses, GeneralCK.Certificates.E8TAxisProd06…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0652StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0653StableWitnesses, GeneralCK.Certificates.E8TAxisProd0654StableWitnesses, GeneralCK.Certificates.E8TAxisProd0655StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0652StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0653StableWitnesses, GeneralCK.Certificates.E8TAxisProd0654StableWitnesses, GeneralCK.Certificates.E8TAxisProd0655StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0652StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0653StableWitnesses, GeneralCK.Certificates.E8TAxisProd0654StableWitnesses, GeneralCK.Certificates.E8TAxisProd0655StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0652StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0653StableWitnesses, GeneralCK/Certificates/E8TAxisProd0654StableWitnesses, GeneralCK/Certificates/E8TAxisProd0655StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0652StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0652StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2374304945389442440708671056104672722900487814, 2374304945389442440708671056104672722900487815⟩
def centerAExp : DyadicInterval precision := ⟨1456760733519020528598233539146530576837684754745, 1456760733519020528598233539146530579036708010298⟩
def centerALog : DyadicInterval precision := ⟨1010663362960215057194405650418097343575557659645, 1010663362960215057194405650418097345774580915198⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1456760733519020528598233539146530577387440568633, scale precision, 1456760733519020528598233539146530578486952196410, scale precision,
    0, 128, 0, 128, ⟨-4748609890778884881417342112209345997346971596, -4748609890778884881417342112209345997344874443⟩, ⟨-4748609890778884881417342112209344894257076814, -4748609890778884881417342112209344894254979661⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨549282344042170289440662302542899180401941949193, 549282344042170289440662302542899180401941949194⟩
def centerCExp : DyadicInterval precision := ⟨689213603638778301213540502830207308588153178229, 689213603638778301213540502830207310787176433782⟩
def centerCLog : DyadicInterval precision := ⟨564630742098075004752425936453137214399308044820, 564630742098075004752425936453137216598331300373⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨689213603638778301213540502830207309137908992117, scale precision, 689213603638778301213540502830207310237420619894, scale precision,
    1, 128, 1, 128, ⟨-1098564688084340578881324605085798361969661446278, -1098564688084340578881324605085798361969659349125⟩, ⟨-1098564688084340578881324605085798359638108447648, -1098564688084340578881324605085798359638106350495⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1263060407406764255432854797445978848917981740372, 1263060407406764255432854797445978848917981740373⟩
def centerBExp : DyadicInterval precision := ⟨259505449825532528488884310145749338051250736678, 259505449825532528488884310145749340250273992231⟩
def centerBLog : DyadicInterval precision := ⟨238875441136561856467943330623429473393376724792, 238875441136561856467943330623429475592399980345⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨259505449825532528488884310145749338601006550566, scale precision, 259505449825532528488884310145749339700518178343, scale precision,
    2, 128, 2, 128, ⟨-2526120814813528510865709594891957700932119244645, -2526120814813528510865709594891957700932117147492⟩, ⟨-2526120814813528510865709594891957694739809813992, -2526120814813528510865709594891957694739807716839⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2216017656540843594568486214625237657012954244, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1457076315351450948047082186788007227169797069041⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1010821401672838003372446069258059723988541223816⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1457076315351450948047082186788007226620041255153, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-4432035313081687189136972429250474762601466399, -4432035313081687189136972429250474762599369246⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨543844202933599035176968211190236987371778719262, 554734273328331502164107668343037439982063327024⟩
def wholeCExp : DyadicInterval precision := ⟨684090706021575985218184972241422411932245292239, 694361763012555474722707227201811128601734368842⟩
def wholeCLog : DyadicInterval precision := ⟨561145364639925166834061548187022173224532413643, 568124952962286624034354755673867578731382121043⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨684090706021575985218184972241422412482001106127, scale precision, 694361763012555474722707227201811128051978554954, scale precision,
    1, 128, 1, 128, ⟨-1109468546656663004328215336686074881138634263023, -1109468546656663004328215336686074881138632165870⟩, ⟨-1087688405867198070353936422380473973586425325498, -1087688405867198070353936422380473973586423228345⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1248034669146898836202101627063051534790264486991, 1278174954891244969637367499274995374729814630365⟩
def wholeBExp : DyadicInterval precision := ⟨254193075374225100548559002829774548186068570732, 264896652214809129993293588620555933527224468631⟩
def wholeBLog : DyadicInterval precision := ⟨234357126429773610823202007234628417486276024455, 243446564448923353740056641428957115393955863809⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨254193075374225100548559002829774548735824384620, scale precision, 264896652214809129993293588620555932977468654743, scale precision,
    2, 128, 2, 128, ⟨-2556349909782489939274734998549990752620491481260, -2556349909782489939274734998549990752620489384107⟩, ⟨-2496069338293797672404203254126103066547388548658, -2496069338293797672404203254126103066547386451505⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0652StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0653StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0653StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2374304945389442440708671056104672722900487814, 2374304945389442440708671056104672722900487815⟩
def centerAExp : DyadicInterval precision := ⟨1456760733519020528598233539146530576837684754745, 1456760733519020528598233539146530579036708010298⟩
def centerALog : DyadicInterval precision := ⟨1010663362960215057194405650418097343575557659645, 1010663362960215057194405650418097345774580915198⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1456760733519020528598233539146530577387440568633, scale precision, 1456760733519020528598233539146530578486952196410, scale precision,
    0, 128, 0, 128, ⟨-4748609890778884881417342112209345997346971596, -4748609890778884881417342112209345997344874443⟩, ⟨-4748609890778884881417342112209344894257076814, -4748609890778884881417342112209344894254979661⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨538783958140502420018328648759198668182032862550, 538783958140502420018328648759198668182032862551⟩
def centerCExp : DyadicInterval precision := ⟨699186710208734543707532183498115789544429361967, 699186710208734543707532183498115791743452617520⟩
def centerCLog : DyadicInterval precision := ⟨571392223494864777907266840264539692329958519757, 571392223494864777907266840264539694528981775310⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨699186710208734543707532183498115790094185175855, scale precision, 699186710208734543707532183498115791193696803632, scale precision,
    1, 128, 1, 128, ⟨-1077567916281004840036657297518397337513214791508, -1077567916281004840036657297518397337513212694355⟩, ⟨-1077567916281004840036657297518397335214918755846, -1077567916281004840036657297518397335214916658693⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1233607255032333811012438418585430860812205651363, 1233607255032333811012438418585430860812205651364⟩
def centerBExp : DyadicInterval precision := ⟨270178548971737309278149014039793665494027726104, 270178548971737309278149014039793667693050981657⟩
def centerBLog : DyadicInterval precision := ⟨247911186530533347339733647983355469145160302677, 247911186530533347339733647983355471344183558230⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨270178548971737309278149014039793666043783539992, scale precision, 270178548971737309278149014039793667143295167769, scale precision,
    2, 128, 2, 128, ⟨-2467214510064667622024876837170861724598256963278, -2467214510064667622024876837170861724598254866125⟩, ⟨-2467214510064667622024876837170861718650567739333, -2467214510064667622024876837170861718650565642180⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2216017656540843594568486214625237657012954244, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1457076315351450948047082186788007227169797069041⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1010821401672838003372446069258059723988541223816⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1457076315351450948047082186788007226620041255153, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-4432035313081687189136972429250474762601466399, -4432035313081687189136972429250474762599369246⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨533372074387137994637866509680158145333272348649, 544209362736744214752453187508164965939615431488⟩
def wholeCExp : DyadicInterval precision := ⟨694014873679114856474664263840981322072152857557, 704384054437193602305067516655979929156731563269⟩
def wholeCLog : DyadicInterval precision := ⟨567889771029673807732766185198493961028035707575, 574903514731011044074691124887453040651770717053⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨694014873679114856474664263840981322621908671445, scale precision, 704384054437193602305067516655979928606975749381, scale precision,
    1, 128, 1, 128, ⟨-1088418725473488429504906375016329933036943442821, -1088418725473488429504906375016329933036941345668⟩, ⟨-1066744148774275989275733019360316289525876792527, -1066744148774275989275733019360316289525874695374⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1218757034843403099186150005328673494201416534253, 1248546899606078484208944453434785391891157898083⟩
def wholeBExp : DyadicInterval precision := ⟨264711034101007909911063320205842176657861673968, 275725249999718371129330882602844264104931671599⟩
def wholeBLog : DyadicInterval precision := ⟨243289418925974944098443966582951158978311491121, 252585004174434537354109355326939629749357906413⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨264711034101007909911063320205842177207617487856, scale precision, 275725249999718371129330882602844263555175857711, scale precision,
    2, 128, 2, 128, ⟨-2497093799212156968417888906869570786817585188803, -2497093799212156968417888906869570786817583091650⟩, ⟨-2437514069686806198372300010657346985488813648767, -2437514069686806198372300010657346985488811551614⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0653StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0654StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0654StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2057730428207317882804005838293844500353867260, 2057730428207317882804005838293844500353867261⟩
def centerAExp : DyadicInterval precision := ⟨1457391965428497307986584889920415113297923882582, 1457391965428497307986584889920415115496947138135⟩
def centerALog : DyadicInterval precision := ⟨1010979457468226488278372104764954114338219249334, 1010979457468226488278372104764954116537242504887⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457391965428497307986584889920415113847679696470, scale precision, 1457391965428497307986584889920415114947191324247, scale precision,
    0, 128, 0, 128, ⟨-4115460856414635765608011676587689552014842957, -4115460856414635765608011676587689552012745804⟩, ⟨-4115460856414635765608011676587688449402723240, -4115460856414635765608011676587688449400626087⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨548916323957182175736005329320512286739389640347, 548916323957182175736005329320512286739389640348⟩
def centerCExp : DyadicInterval precision := ⟨689558904942128771652419360619666461871740808869, 689558904942128771652419360619666464070764064422⟩
def centerCLog : DyadicInterval precision := ⟨564865370050219298855652471884248133448847477363, 564865370050219298855652471884248135647870732916⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨689558904942128771652419360619666462421496622757, scale precision, 689558904942128771652419360619666463521008250534, scale precision,
    1, 128, 1, 128, ⟨-1097832647914364351472010658641024574643973058088, -1097832647914364351472010658641024574643970960935⟩, ⟨-1097832647914364351472010658641024572313587600452, -1097832647914364351472010658641024572313585503299⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1262545238688307122022528506158370969291129078321, 1262545238688307122022528506158370969291129078322⟩
def centerBExp : DyadicInterval precision := ⟨259688461903128663925468681854923745542466751554, 259688461903128663925468681854923747741490007107⟩
def centerBLog : DyadicInterval precision := ⟨239030849113982571042000756497265507392003785410, 239030849113982571042000756497265509591027040963⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨259688461903128663925468681854923746092222565442, scale precision, 259688461903128663925468681854923747191734193219, scale precision,
    2, 128, 2, 128, ⟨-2525090477376614244045057012316741941676231945640, -2525090477376614244045057012316741941676229848487⟩, ⟨-2525090477376614244045057012316741935488286464797, -2525090477376614244045057012316741935488284367644⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 2216017656540843594568486214625237657012954245⟩
def wholeAExp : DyadicInterval precision := ⟨1457076315351450948047082186788007224970773813488, 1457707683773513925477741956702213446679176875042⟩
def wholeALog : DyadicInterval precision := ⟨1010821401672838003372446069258059721789517968263, 1011137530350683182654731711817158199758569694808⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1457076315351450948047082186788007225520529627376, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-4432035313081687189136972429250475865452447731, -4432035313081687189136972429250475865450350578⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨543479104820114982152937417998735313320844945623, 554367321966725412501404840560804935824041534925⟩
def wholeCExp : DyadicInterval precision := ⟨684434312963729813210720852513958324590126258192, 694708767084621674124513518123287226730327319133⟩
def wholeCLog : DyadicInterval precision := ⟨561379398799910820490017985325895773946871372774, 568360174827005297736903883188741743198366054171⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨684434312963729813210720852513958325139882072080, scale precision, 694708767084621674124513518123287226180571505245, scale precision,
    1, 128, 1, 128, ⟨-1108734643933450825002809681121609872822001040637, -1108734643933450825002809681121609872821998943484⟩, ⟨-1086958209640229964305874835997470625485135761311, -1086958209640229964305874835997470625485133664158⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1247522542888921187994469339366283873242165079068, 1277656756070646627611520284835694411902701476045⟩
def wholeBExp : DyadicInterval precision := ⟨254373395756878607421932818328389430580727717487, 265082362686605076784619213339191670968271919062⟩
def wholeBLog : DyadicInterval precision := ⟨234510722920159910963279584564601630815738836406, 243603771255156524408818265845549818807761762077⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨254373395756878607421932818328389431130483531375, scale precision, 265082362686605076784619213339191670418516105174, scale precision,
    2, 128, 2, 128, ⟨-2555313512141293255223040569671388826964024499240, -2555313512141293255223040569671388826964022402087⟩, ⟨-2495045085777842375988938678732567743453314680427, -2495045085777842375988938678732567743453312583274⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0654StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0655StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0655StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2057730428207317882804005838293844500353867260, 2057730428207317882804005838293844500353867261⟩
def centerAExp : DyadicInterval precision := ⟨1457391965428497307986584889920415113297923882582, 1457391965428497307986584889920415115496947138135⟩
def centerALog : DyadicInterval precision := ⟨1010979457468226488278372104764954114338219249334, 1010979457468226488278372104764954116537242504887⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457391965428497307986584889920415113847679696470, scale precision, 1457391965428497307986584889920415114947191324247, scale precision,
    0, 128, 0, 128, ⟨-4115460856414635765608011676587689552014842957, -4115460856414635765608011676587689552012745804⟩, ⟨-4115460856414635765608011676587688449402723240, -4115460856414635765608011676587688449400626087⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨538419711635466277215089895717684249263094450416, 538419711635466277215089895717684249263094450417⟩
def centerCExp : DyadicInterval precision := ⟨699535310295059028543415814293430526110610531011, 699535310295059028543415814293430528309633786564⟩
def centerCLog : DyadicInterval precision := ⟨571627999516358696397900458532893105860028865345, 571627999516358696397900458532893108059052120898⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨699535310295059028543415814293430526660366344899, scale precision, 699535310295059028543415814293430527759877972676, scale precision,
    1, 128, 1, 128, ⟨-1076839423270932554430179791435368499674765311233, -1076839423270932554430179791435368499674763214080⟩, ⟨-1076839423270932554430179791435368497377614587586, -1076839423270932554430179791435368497377612490433⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1233098077338508549017403026009662980884586691958, 1233098077338508549017403026009662980884586691959⟩
def centerBExp : DyadicInterval precision := ⟨270366871483617721002174240091579824347347868712, 270366871483617721002174240091579826546371124265⟩
def centerBLog : DyadicInterval precision := ⟨248070118125818115032233978312221143586551121858, 248070118125818115032233978312221145785574377411⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨270366871483617721002174240091579824897103682600, scale precision, 270366871483617721002174240091579825996615310377, scale precision,
    2, 128, 2, 128, ⟨-2466196154677017098034806052019325964740947629859, -2466196154677017098034806052019325964740945532706⟩, ⟨-2466196154677017098034806052019325958797401235131, -2466196154677017098034806052019325958797399137978⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 2216017656540843594568486214625237657012954245⟩
def wholeAExp : DyadicInterval precision := ⟨1457076315351450948047082186788007224970773813488, 1457707683773513925477741956702213446679176875042⟩
def wholeALog : DyadicInterval precision := ⟨1010821401672838003372446069258059721789517968263, 1011137530350683182654731711817158199758569694808⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1457076315351450948047082186788007225520529627376, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-4432035313081687189136972429250475865452447731, -4432035313081687189136972429250475865450350578⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨533008731889200177169737340137644319360173349608, 543844202933599035176968211190236987371778719263⟩
def wholeCExp : DyadicInterval precision := ⟨694361763012555474722707227201811126402711113289, 704734373989391721077640680448260700530421726654⟩
def wholeCLog : DyadicInterval precision := ⟨568124952962286624034354755673867576532358865490, 575139885098850706495175911027853123858973028093⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨694361763012555474722707227201811126952466927177, scale precision, 704734373989391721077640680448260699980665912766, scale precision,
    1, 128, 1, 128, ⟨-1087688405867198070353936422380473975900691648702, -1087688405867198070353936422380473975900689551549⟩, ⟨-1066017463778400354339474680275288637580245814663, -1066017463778400354339474680275288637580243717510⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1218250918892268462401905278726414159159161126440, 1248034669146898836202101627063051534790264486992⟩
def wholeBExp : DyadicInterval precision := ⟨264896652214809129993293588620555931328201213078, 275916282675086681217134601296609477707398748471⟩
def wholeBLog : DyadicInterval precision := ⟨243446564448923353740056641428957113194932608256, 252745708121799910443545622213305424235035708758⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨264896652214809129993293588620555931877957026966, scale precision, 275916282675086681217134601296609477157642934583, scale precision,
    2, 128, 2, 128, ⟨-2496069338293797672404203254126103072613671496460, -2496069338293797672404203254126103072613669399307⟩, ⟨-2436501837784536924803810557452828315406320376728, -2436501837784536924803810557452828315406318279575⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0655StableWitnesses

end


