-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0133StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0133StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:05:04.023716+00:00
-- url     : https://prove2.me/theorems/80538c27-15d3-4530-b760-ddb5e7090fb9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0133StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0134StableWitnesses, GeneralCK.Certificates.E8TAxisProd01…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0133StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0134StableWitnesses, GeneralCK.Certificates.E8TAxisProd0135StableWitnesses, GeneralCK.Certificates.E8TAxisProd0136StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0133StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0134StableWitnesses, GeneralCK.Certificates.E8TAxisProd0135StableWitnesses, GeneralCK.Certificates.E8TAxisProd0136StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0133StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0134StableWitnesses, GeneralCK.Certificates.E8TAxisProd0135StableWitnesses, GeneralCK.Certificates.E8TAxisProd0136StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0133StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0134StableWitnesses, GeneralCK/Certificates/E8TAxisProd0135StableWitnesses, GeneralCK/Certificates/E8TAxisProd0136StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0133StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0133StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨468197947567212351774406011872494977440423975668, 468197947567212351774406011872494977440423975669⟩
def centerDExp : DyadicInterval precision := ⟨770093267120006045819929989156897110520154385328, 770093267120006045819929989156897112719177640881⟩
def centerDLog : DyadicInterval precision := ⟨618583648477847123240200594096127216349000772546, 618583648477847123240200594096127218548024028099⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨770093267120006045819929989156897111069910199216, scale precision, 770093267120006045819929989156897112169421826993, scale precision,
    0, 128, 0, 128, ⟨-936395895134424703548812023744989955924188886698, -936395895134424703548812023744989955924186789545⟩, ⟨-936395895134424703548812023744989953837509113130, -936395895134424703548812023744989953837507015977⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨470670639963713368888541291203335431626484470374, 470670639963713368888541291203335431626484470375⟩
def centerCExp : DyadicInterval precision := ⟨767491852718541282789490619297160670694669092357, 767491852718541282789490619297160672893692347910⟩
def centerCLog : DyadicInterval precision := ⟨616878953266403986000571822973837909071664612708, 616878953266403986000571822973837911270687868261⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨767491852718541282789490619297160671244424906245, scale precision, 767491852718541282789490619297160672343936534022, scale precision,
    0, 128, 0, 128, ⟨-941341279927426737777082582406670864299846277698, -941341279927426737777082582406670864299844180545⟩, ⟨-941341279927426737777082582406670862206093700953, -941341279927426737777082582406670862206091603800⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1048035918945644949049918457930746431148228286462, 1048035918945644949049918457930746431148228286463⟩
def centerBExp : DyadicInterval precision := ⟨348287801676573551457999297088004538394757235265, 348287801676573551457999297088004540593780490818⟩
def centerBLog : DyadicInterval precision := ⟨312390246760482174922853692090841787506580988986, 312390246760482174922853692090841789705604244539⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨348287801676573551457999297088004538944513049153, scale precision, 348287801676573551457999297088004540044024676930, scale precision,
    2, 128, 2, 128, ⟨-2096071837891289898099836915861492864603368797437, -2096071837891289898099836915861492864603366700284⟩, ⟨-2096071837891289898099836915861492859989546445563, -2096071837891289898099836915861492859989544348410⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨459387967798615484561738103898747303530785179429, 477040995173626483635311023942643508471660670040⟩
def wholeDExp : DyadicInterval precision := ⟨760830284245465294695388294487623569773224656589, 779433753649515438129873373659005449491648691216⟩
def wholeDLog : DyadicInterval precision := ⟨612504570538325940964339858761912610036415505489, 624688092853175616303270580088334960516446661035⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨760830284245465294695388294487623570322980470477, scale precision, 779433753649515438129873373659005448941892877328, scale precision,
    0, 128, 0, 128, ⟨-954081990347252967270622047885287017999364766000, -954081990347252967270622047885287017999362668847⟩, ⟨-918775935597230969123476207797494606030734574454, -918775935597230969123476207797494606030732477301⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨461499381581860949131485878842069002795670661618, 479877859596601426615371866855283257178900142787⟩
def wholeCExp : DyadicInterval precision := ⟨757882373421220111793627325274791608812836214669, 777184926985868258238253560692459595808130635662⟩
def wholeCLog : DyadicInterval precision := ⟨610564609858910174562243627150037684900056617453, 623220708256935174856006921084270613920437639130⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨757882373421220111793627325274791609362592028557, scale precision, 777184926985868258238253560692459595258374821774, scale precision,
    0, 128, 0, 128, ⟨-959755719193202853230743733710566515417951365747, -959755719193202853230743733710566515417949268594⟩, ⟨-922998763163721898262971757684138004557522756646, -922998763163721898262971757684138004557520659493⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1024228741177052029276836569204746508120070996098, 1072112829804862998812524346003829014177160817669⟩
def wholeBExp : DyadicInterval precision := ⟨336999340187064891066402648784844349501454646541, 359821551546058612869382418447838202297969532839⟩
def wholeBLog : DyadicInterval precision := ⟨303245662001428707220514499779441663150111122417, 321674811981732307275408381779594077983564273339⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨336999340187064891066402648784844350051210460429, scale precision, 359821551546058612869382418447838201748213718951, scale precision,
    2, 128, 2, 128, ⟨-2144225659609725997625048692007658030738508426484, -2144225659609725997625048692007658030738506329331⟩, ⟨-2048457482354104058553673138409493014007177787084, -2048457482354104058553673138409493014007175689931⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0133StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0134StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0134StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨485917755434160891773462032334740628415117575842, 485917755434160891773462032334740628415117575843⟩
def centerDExp : DyadicInterval precision := ⟨751644042802555100556006121456236859448629838317, 751644042802555100556006121456236861647653093870⟩
def centerDLog : DyadicInterval precision := ⟨606450780028547033690895338790838686899984128629, 606450780028547033690895338790838689099007384182⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨751644042802555100556006121456236859998385652205, scale precision, 751644042802555100556006121456236861097897279982, scale precision,
    0, 128, 0, 128, ⟨-971835510868321783546924064669481257899185032921, -971835510868321783546924064669481257899182935768⟩, ⟨-971835510868321783546924064669481255761287367599, -971835510868321783546924064669481255761285270446⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨487697209886689993354265177427928986880810357816, 487697209886689993354265177427928986880810357817⟩
def centerCExp : DyadicInterval precision := ⟨749815937886732350512304485613596548240987980155, 749815937886732350512304485613596550440011235708⟩
def centerCLog : DyadicInterval precision := ⟨605243050039379591231317421334642591322967226651, 605243050039379591231317421334642593521990482204⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨749815937886732350512304485613596548790743794043, scale precision, 749815937886732350512304485613596549890255421820, scale precision,
    0, 128, 0, 128, ⟨-975394419773379986708530354855857974833176770621, -975394419773379986708530354855857974833174673468⟩, ⟨-975394419773379986708530354855857972690066757797, -975394419773379986708530354855857972690064660644⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1094541628866367962985536806328740593267704969039, 1094541628866367962985536806328740593267704969040⟩
def centerBExp : DyadicInterval precision := ⟨326813005369542485426228404327750583437315970767, 326813005369542485426228404327750585636339226320⟩
def centerBLog : DyadicInterval precision := ⟨294944490927082116270546503068509700769893897537, 294944490927082116270546503068509702968917153090⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨326813005369542485426228404327750583987071784655, scale precision, 326813005369542485426228404327750585086583412432, scale precision,
    2, 128, 2, 128, ⟨-2189083257732735925971073612657481188993908686961, -2189083257732735925971073612657481188993906589808⟩, ⟨-2189083257732735925971073612657481184076913286354, -2189083257732735925971073612657481184076911189201⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨477040995173626483635311023942643508471660670039, 494828875109284674194281948410566590218630888610⟩
def wholeDExp : DyadicInterval precision := ⟨742533801492811413004049823802046283438332233585, 760830284245465294695388294487623571972247912142⟩
def wholeDLog : DyadicInterval precision := ⟨600422206098217740957049834384989020037338221569, 612504570538325940964339858761912612235438761042⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨742533801492811413004049823802046283988088047473, scale precision, 760830284245465294695388294487623571422492098254, scale precision,
    0, 128, 0, 128, ⟨-989657750218569348388563896821133181519326727149, -989657750218569348388563896821133181519324629996⟩, ⟨-954081990347252967270622047885287015887280011311, -954081990347252967270622047885287015887277914158⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨478458994542216572420101618630227318965760431275, 496972728536424257573486884023855659610055911358⟩
def wholeCExp : DyadicInterval precision := ⟨740358571896512958580575371536953667486773992755, 759355348100787594485829608227292428698468988208⟩
def wholeCLog : DyadicInterval precision := ⟨598979093446983066373001071770068300103572014895, 611534266680129103556842684329580875308563270871⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨740358571896512958580575371536953668036529806643, scale precision, 759355348100787594485829608227292428148713174320, scale precision,
    0, 128, 0, 128, ⟨-993945457072848515146973768047711320305355958398, -993945457072848515146973768047711320305353861245⟩, ⟨-956917989084433144840203237260454636873428326693, -956917989084433144840203237260454636873426229540⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1070214655428945250809954185107274242530860726639, 1119141178981667648123611132975238308851399549593⟩
def wholeBExp : DyadicInterval precision := ⟨315994487203783086164606373333095495742321390600, 337875856540075881664697066351840845444895820184⟩
def wholeBLog : DyadicInterval precision := ⟨286076196135867207802422460457386278154787762228, 303957765048045373044145779769888238336958993156⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨315994487203783086164606373333095496292077204488, scale precision, 337875856540075881664697066351840844895140006296, scale precision,
    2, 128, 2, 128, ⟨-2238282357963335296247222265950476620245467993772, -2238282357963335296247222265950476620245465896619⟩, ⟨-2140429310857890501619908370214548482683721805511, -2140429310857890501619908370214548482683719708358⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0134StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0135StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0135StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨468197947567212351774406011872494977440423975668, 468197947567212351774406011872494977440423975669⟩
def centerDExp : DyadicInterval precision := ⟨770093267120006045819929989156897110520154385328, 770093267120006045819929989156897112719177640881⟩
def centerDLog : DyadicInterval precision := ⟨618583648477847123240200594096127216349000772546, 618583648477847123240200594096127218548024028099⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨770093267120006045819929989156897111069910199216, scale precision, 770093267120006045819929989156897112169421826993, scale precision,
    0, 128, 0, 128, ⟨-936395895134424703548812023744989955924188886698, -936395895134424703548812023744989955924186789545⟩, ⟨-936395895134424703548812023744989953837509113130, -936395895134424703548812023744989953837507015977⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨469963891056194552582472665051408868706991777175, 469963891056194552582472665051408868706991777176⟩
def centerCExp : DyadicInterval precision := ⟨768234494947693660605198453268811786174159075963, 768234494947693660605198453268811788373182331516⟩
def centerCLog : DyadicInterval precision := ⟨617365806220419776712376583636845485906060286692, 617365806220419776712376583636845488105083542245⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨768234494947693660605198453268811786723914889851, scale precision, 768234494947693660605198453268811787823426517628, scale precision,
    0, 128, 0, 128, ⟨-939927782112389105164945330102817738459848889696, -939927782112389105164945330102817738459846792543⟩, ⟨-939927782112389105164945330102817736368120316157, -939927782112389105164945330102817736368118219004⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1047097234846893185191241168818805273629517911628, 1047097234846893185191241168818805273629517911629⟩
def centerBExp : DyadicInterval precision := ⟨348735481354489200834865139438468664452206252021, 348735481354489200834865139438468666651229507574⟩
def centerBLog : DyadicInterval precision := ⟨312751727304992849260105623063210905530247370252, 312751727304992849260105623063210907729270625805⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨348735481354489200834865139438468665001962065909, scale precision, 348735481354489200834865139438468666101473693686, scale precision,
    2, 128, 2, 128, ⟨-2094194469693786370382482337637610549562986613368, -2094194469693786370382482337637610549562984516215⟩, ⟨-2094194469693786370382482337637610544955087130301, -2094194469693786370382482337637610544955085033148⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨459387967798615484561738103898747303530785179429, 477040995173626483635311023942643508471660670040⟩
def wholeDExp : DyadicInterval precision := ⟨760830284245465294695388294487623569773224656589, 779433753649515438129873373659005449491648691216⟩
def wholeDLog : DyadicInterval precision := ⟨612504570538325940964339858761912610036415505489, 624688092853175616303270580088334960516446661035⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨760830284245465294695388294487623570322980470477, scale precision, 779433753649515438129873373659005448941892877328, scale precision,
    0, 128, 0, 128, ⟨-954081990347252967270622047885287017999364766000, -954081990347252967270622047885287017999362668847⟩, ⟨-918775935597230969123476207797494606030734574454, -918775935597230969123476207797494606030732477301⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨460795368920412028518162504643854518865778764227, 479168318693266819909468923991435055930292470700⟩
def wholeCExp : DyadicInterval precision := ⟨758618615769333099692909444315793069628551477508, 777934035523977631609093955857762635239218912162⟩
def wholeCLog : DyadicInterval precision := ⟨611049357408705379871225940480394931196929469489, 623709673634481061734914998481739644928680995264⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨758618615769333099692909444315793070178307291396, scale precision, 777934035523977631609093955857762634689463098274, scale precision,
    0, 128, 0, 128, ⟨-958336637386533639818937847982870112919707141801, -958336637386533639818937847982870112919705044648⟩, ⟨-921590737840824057036325009287709036698734474422, -921590737840824057036325009287709036698732377269⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1023300595444368493082805525999753225833125465962, 1071163533946626840883335333769298938372431694814⟩
def wholeBExp : DyadicInterval precision := ⟨337437410119603305838424924508241190567843822375, 360278860670989033437235515920200312527006085327⟩
def wholeBLog : DyadicInterval precision := ⟨303601603961484349785233611543151596068501125631, 322041728817379791829666077192241612076255596277⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨337437410119603305838424924508241191117599636263, scale precision, 360278860670989033437235515920200311977250271439, scale precision,
    2, 128, 2, 128, ⟨-2142327067893253681766670667538597879125954969468, -2142327067893253681766670667538597879125952872315⟩, ⟨-2046601190888736986165611051999506449436121074032, -2046601190888736986165611051999506449436118976879⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0135StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0136StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0136StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨521774884976969249658675544420781985592392356176, 521774884976969249658675544420781985592392356177⟩
def centerDExp : DyadicInterval precision := ⟨715651972798857079113875938009045310901254744990, 715651972798857079113875938009045313100278000543⟩
def centerDLog : DyadicInterval precision := ⟨582487198387037182294075308140412786716139382242, 582487198387037182294075308140412788915162637795⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨715651972798857079113875938009045311451010558878, scale precision, 715651972798857079113875938009045312550522186655, scale precision,
    1, 128, 1, 128, ⟨-1043549769953938499317351088841563972307494916592, -1043549769953938499317351088841563972307492819439⟩, ⟨-1043549769953938499317351088841563970062076605264, -1043549769953938499317351088841563970062074508111⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨522859527575814142947524500459698736552373898789, 522859527575814142947524500459698736552373898790⟩
def centerCExp : DyadicInterval precision := ⟨714590529130345256383845588160315300077095085965, 714590529130345256383845588160315302276118341518⟩
def centerCLog : DyadicInterval precision := ⟨581774488023404968976419863579878489441297774787, 581774488023404968976419863579878491640321030340⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨714590529130345256383845588160315300626850899853, scale precision, 714590529130345256383845588160315301726362527630, scale precision,
    1, 128, 1, 128, ⟨-1045719055151628285895049000919397474229125659696, -1045719055151628285895049000919397474229123562543⟩, ⟨-1045719055151628285895049000919397471980372032613, -1045719055151628285895049000919397471980369935460⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1191576947845851287139810413168730921751281574760, 1191576947845851287139810413168730921751281574761⟩
def centerBExp : DyadicInterval precision := ⟨286173891785747333259846901360025708607346652669, 286173891785747333259846901360025710806369908222⟩
def centerBLog : DyadicInterval precision := ⟨261348952780467300384800937745306829400244792744, 261348952780467300384800937745306831599268048297⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨286173891785747333259846901360025709157102466557, scale precision, 286173891785747333259846901360025710256614094334, scale precision,
    2, 128, 2, 128, ⟨-2383153895691702574279620826337461846310189370042, -2383153895691702574279620826337461846310187272889⟩, ⟨-2383153895691702574279620826337461840694939026158, -2383153895691702574279620826337461840694936929005⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨512756788786713314020267203907621024217207656619, 530829944683894805437507571749273968698214433228⟩
def wholeDExp : DyadicInterval precision := ⟨706838726837510462039096914346652691200364343781, 724538456853667540563062557829026726602043072281⟩
def wholeDLog : DyadicInterval precision := ⟨576558946667156773600005109862481905428300877399, 588440465573623044036052405976243775513762722746⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨706838726837510462039096914346652691750120157669, scale precision, 724538456853667540563062557829026726052287258393, scale precision,
    1, 128, 1, 128, ⟨-1061659889367789610875015143498547938533137613158, -1061659889367789610875015143498547938533135516005⟩, ⟨-1025513577573426628040534407815242047325477264753, -1025513577573426628040534407815242047325475167600⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨513476891620287433729744816122965384439477635574, 532282228172866116854382691727110279060616762141⟩
def wholeCExp : DyadicInterval precision := ⟨705435360866505781316672671624606262796841225806, 723824827532911875227338360353220506327890513273⟩
def wholeCLog : DyadicInterval precision := ⟨575612745737157315624533178384052510356302283242, 587963282790660940513969362008894094604522860251⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨705435360866505781316672671624606263346597039694, scale precision, 723824827532911875227338360353220505778134699385, scale precision,
    1, 128, 1, 128, ⟨-1064564456345732233708765383454220559260203593553, -1064564456345732233708765383454220559260201496400⟩, ⟨-1026953783240574867459489632245930767768923903638, -1026953783240574867459489632245930767768921806485⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1166188388182342115326847483651789008827456546753, 1217239001437486599715214062593104088327201605188⟩
def wholeBExp : DyadicInterval precision := ⟨276298626287712738569478063235137592488924852544, 296291199908713716536122412645638004364915959711⟩
def wholeBLog : DyadicInterval precision := ⟨253067297034268024660477759355581071594123168536, 269785202604095038338480629940283766784164298274⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨276298626287712738569478063235137593038680666432, scale precision, 296291199908713716536122412645638003815160145823, scale precision,
    2, 128, 2, 128, ⟨-2434478002874973199430428125186208179562377537450, -2434478002874973199430428125186208179562375440297⟩, ⟨-2332376776364684230653694967303578014943159549381, -2332376776364684230653694967303578014943157452228⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0136StableWitnesses

end


