-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0081StableWitnesses__2
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0081StableWitnesses__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:20:15.18526+00:00
-- url     : https://prove2.me/theorems/97c3dbf6-0f52-4746-8921-b5a612126265
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0081StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisZero0082StableWitnesses)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0081StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisZero0082StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0081StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisZero0082StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0081StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisZero0082StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0081StableWitnesses (+1 modules: GeneralCK/Certificates/E8TAxisZero0082StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0081StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0081StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨546538709428945749870773924191788198118687927157, 546538709428945749870773924191788198118687927158⟩
def centerDExp : DyadicInterval precision := ⟨691806148899640566657527120936512860452889890625, 691806148899640566657527120936512862651913146178⟩
def centerDLog : DyadicInterval precision := ⟨566391424872267910855012963449734473930997225626, 566391424872267910855012963449734476130020481179⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨691806148899640566657527120936512861002645704513, scale precision, 691806148899640566657527120936512862102157332290, scale precision,
    0, 256, 0, 256, ⟨-1093077418857891499741547848383576397398784651881, -1093077418857891499741547848383576397398782554728⟩, ⟨-1093077418857891499741547848383576395075969153903, -1093077418857891499741547848383576395075967056750⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨546721509707565669767024801623781259977529604108, 546721509707565669767024801623781259977529604109⟩
def centerCExp : DyadicInterval precision := ⟨691633112431773042084336716781667166426104054451, 691633112431773042084336716781667168625127310004⟩
def centerCLog : DyadicInterval precision := ⟨566273976152528235628806908453516484356973407102, 566273976152528235628806908453516486555996662655⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨691633112431773042084336716781667166975859868339, scale precision, 691633112431773042084336716781667168075371496116, scale precision,
    0, 256, 0, 256, ⟨-1093443019415131339534049603247562521116758572978, -1093443019415131339534049603247562521116756475825⟩, ⟨-1093443019415131339534049603247562518793361940606, -1093443019415131339534049603247562518793359843453⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1259456407129290380777631460213833902443052008500, 1259456407129290380777631460213833902443052008501⟩
def centerBExp : DyadicInterval precision := ⟨260788469687798993047025594160253126830819202705, 260788469687798993047025594160253129029842458258⟩
def centerBLog : DyadicInterval precision := ⟨239964592383444929300132883132702387142707672381, 239964592383444929300132883132702389341730927934⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨260788469687798993047025594160253127380575016593, scale precision, 260788469687798993047025594160253128480086644370, scale precision,
    0, 256, 0, 256, ⟨-2518912814258580761555262920427667807967027405019, -2518912814258580761555262920427667807967025307866⟩, ⟨-2518912814258580761555262920427667801805182726133, -2518912814258580761555262920427667801805180628980⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨541289809268942399956535792498120861936820641712, 551800421242914454820810459967297938576086292891⟩
def wholeDExp : DyadicInterval precision := ⟨686842745746340006938348233447115251068009001225, 696793203199184192771083052087923261448554764920⟩
def wholeDLog : DyadicInterval precision := ⟨563018755595924057929845042473976395760693996545, 569772344639491636839148332004312891755835414717⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨686842745746340006938348233447115251617764815113, scale precision, 696793203199184192771083052087923260898798951032, scale precision,
    0, 256, 0, 256, ⟨-1103600842485828909641620919934595878321974184929, -1103600842485828909641620919934595878321972087776⟩, ⟨-1082579618537884799913071584996241722720546953858, -1082579618537884799913071584996241722720544856705⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨541289809268942399956535792498120861936820641712, 552166933197188683374850990452555196994927225220⟩
def wholeCExp : DyadicInterval precision := ⟨686498342495103149037812478669294547910626267207, 696793203199184192771083052087923261448554764920⟩
def wholeCLog : DyadicInterval precision := ⟨562784442014820528870121302404999929920133187368, 569772344639491636839148332004312891755835414717⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨686498342495103149037812478669294548460382081095, scale precision, 696793203199184192771083052087923260898798951032, scale precision,
    0, 256, 0, 256, ⟨-1104333866394377366749701980905110395160242916427, -1104333866394377366749701980905110395160240819274⟩, ⟨-1082579618537884799913071584996241722720546953858, -1082579618537884799913071584996241722720544856705⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1244451974257948572139785370051839801708650263728, 1274549734501976508539636586264995992738465663454⟩
def wholeBExp : DyadicInterval precision := ⟨255457248406065143391072622331457002727399674752, 266198565440130320016283716749756650026795166660⟩
def wholeBLog : DyadicInterval precision := ⟨235433606177261909204081416755181237309411989461, 244548298174703522559708255035931768535980384784⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨255457248406065143391072622331457003277155488640, scale precision, 266198565440130320016283716749756649477039352772, scale precision,
    0, 256, 0, 256, ⟨-2549099469003953017079273172529991988622151495877, -2549099469003953017079273172529991988622149398724⟩, ⟨-2488903948515897144279570740103679600398994468323, -2488903948515897144279570740103679600398992371170⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0081StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0082StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0082StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨536053595931077576481867337467978800983992300722, 536053595931077576481867337467978800983992300723⟩
def centerDExp : DyadicInterval precision := ⟨701804023530382254660990345893463172517499932104, 701804023530382254660990345893463174716523187657⟩
def centerDLog : DyadicInterval precision := ⟨573161517422994399504898462730524988803441785707, 573161517422994399504898462730524991002465041260⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨701804023530382254660990345893463173067255745992, scale precision, 701804023530382254660990345893463174166767373769, scale precision,
    0, 256, 0, 256, ⟨-1072107191862155152963734674935957603112848026398, -1072107191862155152963734674935957603112845929245⟩, ⟨-1072107191862155152963734674935957600823123273644, -1072107191862155152963734674935957600823121176491⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨536235513496608192541756811331217861449689408154, 536235513496608192541756811331217861449689408155⟩
def centerCExp : DyadicInterval precision := ⟨701629333901627403555062187641964952872528328299, 701629333901627403555062187641964955071551583852⟩
def centerCLog : DyadicInterval precision := ⟨573043494578654192962974944950753451008034219714, 573043494578654192962974944950753453207057475267⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨701629333901627403555062187641964953422284142187, scale precision, 701629333901627403555062187641964954521795769964, scale precision,
    0, 256, 0, 256, ⟨-1072471026993216385083513622662435724044527285764, -1072471026993216385083513622662435724044525188611⟩, ⟨-1072471026993216385083513622662435721754232444007, -1072471026993216385083513622662435721754230346854⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1230045206805631073922989316837739317109290107093, 1230045206805631073922989316837739317109290107094⟩
def centerBExp : DyadicInterval precision := ⟨271498750601770517270640630447189965612015312025, 271498750601770517270640630447189967811038567578⟩
def centerBLog : DyadicInterval precision := ⟨249024984409410141212718613797804388347975623541, 249024984409410141212718613797804390546998879094⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨271498750601770517270640630447189966161771125913, scale precision, 271498750601770517270640630447189967261282753690, scale precision,
    0, 256, 0, 256, ⟨-2460090413611262147845978633675478637177965128615, -2460090413611262147845978633675478637177963031462⟩, ⟨-2460090413611262147845978633675478631259197396908, -2460090413611262147845978633675478631259195299755⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨530829944683894805437507571749273968698214433227, 541289809268942399956535792498120861936820641713⟩
def wholeDExp : DyadicInterval precision := ⟨696793203199184192771083052087923259249531509367, 706838726837510462039096914346652693399387599334⟩
def wholeDLog : DyadicInterval precision := ⟨569772344639491636839148332004312889556812159164, 576558946667156773600005109862481907627324132952⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨696793203199184192771083052087923259799287323255, scale precision, 706838726837510462039096914346652692849631785446, scale precision,
    0, 256, 0, 256, ⟨-1082579618537884799913071584996241725026737710144, -1082579618537884799913071584996241725026735612991⟩, ⟨-1061659889367789610875015143498547936259722216904, -1061659889367789610875015143498547936259720119751⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨530829944683894805437507571749273968698214433227, 541654538126871809569398101492862979540654997331⟩
def wholeCExp : DyadicInterval precision := ⟨696445509880808157272503859764899400897483133808, 706838726837510462039096914346652693399387599334⟩
def wholeCLog : DyadicInterval precision := ⟨569536883163217644656607860660718212071718375353, 576558946667156773600005109862481907627324132952⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨696445509880808157272503859764899401447238947696, scale precision, 706838726837510462039096914346652692849631785446, scale precision,
    0, 256, 0, 256, ⟨-1083309076253743619138796202985725960234982092487, -1083309076253743619138796202985725960234979995334⟩, ⟨-1061659889367789610875015143498547936259722216904, -1061659889367789610875015143498547936259720119751⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1215216424550990911711063448635784916504731868758, 1244963475049946801553682196125291092267488633170⟩
def wholeBExp : DyadicInterval precision := ⟨266012300668708602943229969657795116622101131823, 277064426734178251172838884216083334227608299640⟩
def wholeBLog : DyadicInterval precision := ⟨244390723994011558162339590715447088470134608937, 253711198464085284108121392437488998412855774297⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨266012300668708602943229969657795117171856945711, scale precision, 277064426734178251172838884216083333677852485752, scale precision,
    0, 256, 0, 256, ⟨-2489926950099893603107364392250582187555398874833, -2489926950099893603107364392250582187555396777680⟩, ⟨-2430432849101981823422126897271569830109529086656, -2430432849101981823422126897271569830109526989503⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0082StableWitnesses

end


