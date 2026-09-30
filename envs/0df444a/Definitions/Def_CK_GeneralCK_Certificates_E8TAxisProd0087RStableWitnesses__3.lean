-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0087RStableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0087RStableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:39:05.330551+00:00
-- url     : https://prove2.me/theorems/e193f523-08bd-401a-957d-2cee8973f4eb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0087RStableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0088RStableWitnesses, GeneralCK.Certificates.E8TAxisProd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0087RStableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0088RStableWitnesses, GeneralCK.Certificates.E8TAxisProd0093RStableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0087RStableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0088RStableWitnesses, GeneralCK.Certificates.E8TAxisProd0093RStableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0087RStableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0088RStableWitnesses, GeneralCK.Certificates.E8TAxisProd0093RStableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0087RStableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0088RStableWitnesses, GeneralCK/Certificates/E8TAxisProd0093RStableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0087RStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0087RStableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨154999391481232912176531096462725419644778483979, 154999391481232912176531096462725419644778483980⟩
def centerDExp : DyadicInterval precision := ⟨1182173450222225673505629770194260121401539327798, 1182173450222225673505629770194260123600562583351⟩
def centerDLog : DyadicInterval precision := ⟨866240207568659899353028711382600099926261785804, 866240207568659899353028711382600102125285041357⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1182173450222225673505629770194260121951295141686, scale precision, 1182173450222225673505629770194260123050806769463, scale precision,
    0, 128, 0, 128, ⟨-309998782962465824353062192925450839969212107887, -309998782962465824353062192925450839969210010734⟩, ⟨-309998782962465824353062192925450838609903925185, -309998782962465824353062192925450838609901828032⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨157244733295521903000720040089847598423183204002, 157244733295521903000720040089847598423183204003⟩
def centerCExp : DyadicInterval precision := ⟨1178546619312001448987319314324937404703469866033, 1178546619312001448987319314324937406902493121586⟩
def centerCLog : DyadicInterval precision := ⟨864233811775084010581360466101583112684997101073, 864233811775084010581360466101583114884020356626⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1178546619312001448987319314324937405253225679921, scale precision, 1178546619312001448987319314324937406352737307698, scale precision,
    0, 128, 0, 128, ⟨-314489466591043806001440080179695197528113099023, -314489466591043806001440080179695197528111001870⟩, ⟨-314489466591043806001440080179695196164621814140, -314489466591043806001440080179695196164619716987⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨316398052345387929849670259953483340945355832488, 316398052345387929849670259953483340945355832489⟩
def centerBExp : DyadicInterval precision := ⟨947894339623578062129362528373931603913698248572, 947894339623578062129362528373931606112721504125⟩
def centerBLog : DyadicInterval precision := ⟨730621707042908945843621572463752907093090828621, 730621707042908945843621572463752909292114084174⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨947894339623578062129362528373931604463454062460, scale precision, 947894339623578062129362528373931605562965690237, scale precision,
    0, 128, 0, 128, ⟨-632796104690775859699340519906966682738348350296, -632796104690775859699340519906966682738346253143⟩, ⟨-632796104690775859699340519906966681043077076813, -632796104690775859699340519906966681043074979660⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨150991919513477176104051187712444417195036210428, 159009523631476834293416684122073812609720086985⟩
def wholeDExp : DyadicInterval precision := ⟨1175703819620526499056916402241341505278943686883, 1188674354540648287330851150581954943606665789757⟩
def wholeDLog : DyadicInterval precision := ⟨862659221266056220624571274243273530090398223223, 869829687869058094079061307765923603360191874427⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1175703819620526499056916402241341505828699500771, scale precision, 1188674354540648287330851150581954943056909975869, scale precision,
    0, 128, 0, 128, ⟨-318019047262953668586833368244147625902835295714, -318019047262953668586833368244147625902833198561⟩, ⟨-301983839026954352208102375424888833714136431622, -301983839026954352208102375424888833714134334469⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨152915178463027122650990311385075366485501069608, 161577436401748847597890018140472027124415234622⟩
def wholeCExp : DyadicInterval precision := ⟨1171579559607242623643396951962840838141676836280, 1185550002510866574450539697030115402009109857272⟩
def wholeCLog : DyadicInterval precision := ⟨860371826143762983574909401721668985274065389503, 868105674307971667134088694511406445502019316429⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1171579559607242623643396951962840838691432650168, scale precision, 1185550002510866574450539697030115401459354043384, scale precision,
    0, 128, 0, 128, ⟨-323154872803497695195780036280944054934631313097, -323154872803497695195780036280944054934629215944⟩, ⟨-305830356926054245301980622770150732293284811996, -305830356926054245301980622770150732293282714843⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨307736936149958299472359103669327302219619088326, 325083004739724723125590110073889241739908452156⟩
def wholeBExp : DyadicInterval precision := ⟨936695324557495237835579476887656903466268381545, 959195960437400828672252673820504666491392669613⟩
def wholeBLog : DyadicInterval precision := ⟨723812724390392070070417718976900626092731918135, 737461064174050379733680055126500325440906489671⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨936695324557495237835579476887656904016024195433, scale precision, 959195960437400828672252673820504665941636855725, scale precision,
    0, 128, 0, 128, ⟨-650166009479449446251180220147778484337587817929, -650166009479449446251180220147778484337585720776⟩, ⟨-615473872299916598944718207338654603601590762069, -615473872299916598944718207338654603601588664916⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0087RStableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0088RStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0088RStableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨154999391481232912176531096462725419644778483979, 154999391481232912176531096462725419644778483980⟩
def centerDExp : DyadicInterval precision := ⟨1182173450222225673505629770194260121401539327798, 1182173450222225673505629770194260123600562583351⟩
def centerDLog : DyadicInterval precision := ⟨866240207568659899353028711382600099926261785804, 866240207568659899353028711382600102125285041357⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1182173450222225673505629770194260121951295141686, scale precision, 1182173450222225673505629770194260123050806769463, scale precision,
    0, 128, 0, 128, ⟨-309998782962465824353062192925450839969212107887, -309998782962465824353062192925450839969210010734⟩, ⟨-309998782962465824353062192925450838609903925185, -309998782962465824353062192925450838609901828032⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨156603121225106199738590946150321163956857984080, 156603121225106199738590946150321163956857984081⟩
def centerCExp : DyadicInterval precision := ⟨1179581858383264958461268133309573640953660710807, 1179581858383264958461268133309573643152683966360⟩
def centerCLog : DyadicInterval precision := ⟨864806796388234369263960019875732095793156700599, 864806796388234369263960019875732097992179956152⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1179581858383264958461268133309573641503416524695, scale precision, 1179581858383264958461268133309573642602928152472, scale precision,
    0, 128, 0, 128, ⟨-313206242450212399477181892300642328594864337221, -313206242450212399477181892300642328594862240068⟩, ⟨-313206242450212399477181892300642327232569696252, -313206242450212399477181892300642327232567599099⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨315730974976522442942747309381042402605852428662, 315730974976522442942747309381042402605852428663⟩
def centerBExp : DyadicInterval precision := ⟨948760034939719047339748701215345623284741224228, 948760034939719047339748701215345625483764479781⟩
def centerBLog : DyadicInterval precision := ⟨731146729867208297956737916270976171068232700779, 731146729867208297956737916270976173267255956332⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨948760034939719047339748701215345623834497038116, scale precision, 948760034939719047339748701215345624934008665893, scale precision,
    0, 128, 0, 128, ⟨-631461949953044885885494618762084806058568118201, -631461949953044885885494618762084806058566021048⟩, ⟨-631461949953044885885494618762084804364843693603, -631461949953044885885494618762084804364841596450⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨150991919513477176104051187712444417195036210428, 159009523631476834293416684122073812609720086985⟩
def wholeDExp : DyadicInterval precision := ⟨1175703819620526499056916402241341505278943686883, 1188674354540648287330851150581954943606665789757⟩
def wholeDLog : DyadicInterval precision := ⟨862659221266056220624571274243273530090398223223, 869829687869058094079061307765923603360191874427⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1175703819620526499056916402241341505828699500771, scale precision, 1188674354540648287330851150581954943056909975869, scale precision,
    0, 128, 0, 128, ⟨-318019047262953668586833368244147625902835295714, -318019047262953668586833368244147625902833198561⟩, ⟨-301983839026954352208102375424888833714136431622, -301983839026954352208102375424888833714134334469⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨152274025350693602568853898076835468511984896974, 160935352387999983375778532309915876359281887839⟩
def wholeCExp : DyadicInterval precision := ⟨1172609436101435838584046542384058696971054941586, 1186590648121264655519234724293073080225821323837⟩
def wholeCLog : DyadicInterval precision := ⟨860943351208515288862709081076038717935566861761, 868680127166861396265070107977234576364288322915⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1172609436101435838584046542384058697520810755474, scale precision, 1186590648121264655519234724293073079676065509949, scale precision,
    0, 128, 0, 128, ⟨-321870704775999966751557064619831753403762296996, -321870704775999966751557064619831753403760199843⟩, ⟨-304548050701387205137707796153670936346846828947, -304548050701387205137707796153670936346844731794⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨307071664425993428826262081180784357445038659393, 324414069859130179241454812482021708860680101600⟩
def wholeBExp : DyadicInterval precision := ⟨937553175193314205694480171750604709920938472382, 960069605044216067758791316721619527131774660002⟩
def wholeBLog : DyadicInterval precision := ⟨724335419542181150711051587565465266165304045573, 737988433917165373290026871067955249071269362563⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨937553175193314205694480171750604710470694286270, scale precision, 960069605044216067758791316721619526582018846114, scale precision,
    0, 128, 0, 128, ⟨-648828139718260358482909624964043418578346267015, -648828139718260358482909624964043418578344169862⟩, ⟨-614143328851986857652524162361568714053192147959, -614143328851986857652524162361568714053190050806⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0088RStableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0093RStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0093RStableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨154999391481232912176531096462725419644778483979, 154999391481232912176531096462725419644778483980⟩
def centerDExp : DyadicInterval precision := ⟨1182173450222225673505629770194260121401539327798, 1182173450222225673505629770194260123600562583351⟩
def centerDLog : DyadicInterval precision := ⟨866240207568659899353028711382600099926261785804, 866240207568659899353028711382600102125285041357⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1182173450222225673505629770194260121951295141686, scale precision, 1182173450222225673505629770194260123050806769463, scale precision,
    0, 128, 0, 128, ⟨-309998782962465824353062192925450839969212107887, -309998782962465824353062192925450839969210010734⟩, ⟨-309998782962465824353062192925450838609903925185, -309998782962465824353062192925450838609901828032⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨155961577967361688031034026587002510566797587873, 155961577967361688031034026587002510566797587874⟩
def centerCExp : DyadicInterval precision := ⟨1180617895636451388033439674256312956800578684687, 1180617895636451388033439674256312958999601940240⟩
def centerCLog : DyadicInterval precision := ⟨865379997968055140054217642761787182513979994567, 865379997968055140054217642761787184713003250120⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1180617895636451388033439674256312957350334498575, scale precision, 1180617895636451388033439674256312958449846126352, scale precision,
    0, 128, 0, 128, ⟨-311923155934723376062068053174005021814145812044, -311923155934723376062068053174005021814143714891⟩, ⟨-311923155934723376062068053174005020453046636604, -311923155934723376062068053174005020453044539451⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨315064038341855424107327819982611679513196559210, 315064038341855424107327819982611679513196559211⟩
def centerBExp : DyadicInterval precision := ⟨949626337993123806397778588008838425028622195395, 949626337993123806397778588008838427227645450948⟩
def centerBLog : DyadicInterval precision := ⟨731671932531644544969007351596136164823520449655, 731671932531644544969007351596136167022543705208⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨949626337993123806397778588008838425578378009283, scale precision, 949626337993123806397778588008838426677889637060, scale precision,
    0, 128, 0, 128, ⟨-630128076683710848214655639965223359872483823513, -630128076683710848214655639965223359872481726360⟩, ⟨-630128076683710848214655639965223358180304510483, -630128076683710848214655639965223358180302413330⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨150991919513477176104051187712444417195036210428, 159009523631476834293416684122073812609720086985⟩
def wholeDExp : DyadicInterval precision := ⟨1175703819620526499056916402241341505278943686883, 1188674354540648287330851150581954943606665789757⟩
def wholeDLog : DyadicInterval precision := ⟨862659221266056220624571274243273530090398223223, 869829687869058094079061307765923603360191874427⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1175703819620526499056916402241341505828699500771, scale precision, 1188674354540648287330851150581954943056909975869, scale precision,
    0, 128, 0, 128, ⟨-318019047262953668586833368244147625902835295714, -318019047262953668586833368244147625902833198561⟩, ⟨-301983839026954352208102375424888833714136431622, -301983839026954352208102375424888833714134334469⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨151632939129008056697517373665649318183483033498, 160293339111948018245674211080042528839685011783⟩
def wholeCExp : DyadicInterval precision := ⟨1173640104298104188087122023740267535234930412036, 1187632098471748154820948330413552639206431171915⟩
def wholeCLog : DyadicInterval precision := ⟨861515091957746564471801711065111145687970794257, 869254798289420289309708762878379529856622402189⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1173640104298104188087122023740267535784686225924, scale precision, 1187632098471748154820948330413552638656675358027, scale precision,
    0, 128, 0, 128, ⟨-320586678223896036491348422160085058363966817624, -320586678223896036491348422160085058363964720471⟩, ⟨-303265878258016113395034747331298635690436881031, -303265878258016113395034747331298635690434783878⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨306406529456171130952351701227325511683437947574, 323745279710826766446985521470106618369709766891⟩
def wholeBExp : DyadicInterval precision := ⟨938411625610146292314081985138210582434817627778, 960943865541731091515367813263173043883997422569⟩
def wholeBLog : DyadicInterval precision := ⟨724858293078083165410598662537004364670207960208, 738515985009427417807501760964090833030536662261⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨938411625610146292314081985138210582984573441666, scale precision, 960943865541731091515367813263173043334241608681, scale precision,
    0, 128, 0, 128, ⟨-647490559421653532893971042940213237595621635502, -647490559421653532893971042940213237595619538349⟩, ⟨-612813058912342261904703402454651022530752117977, -612813058912342261904703402454651022530750020824⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0093RStableWitnesses

end


