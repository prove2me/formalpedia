-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0579StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0579StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:34:32.442511+00:00
-- url     : https://prove2.me/theorems/69d2f4a8-b998-486a-bb2b-f3033846ffaf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0579StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0580StableWitnesses, GeneralCK.Certificates.E8TAxisProd05…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0579StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0580StableWitnesses, GeneralCK.Certificates.E8TAxisProd0581StableWitnesses, GeneralCK.Certificates.E8TAxisProd0582StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0579StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0580StableWitnesses, GeneralCK.Certificates.E8TAxisProd0581StableWitnesses, GeneralCK.Certificates.E8TAxisProd0582StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0579StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0580StableWitnesses, GeneralCK.Certificates.E8TAxisProd0581StableWitnesses, GeneralCK.Certificates.E8TAxisProd0582StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0579StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0580StableWitnesses, GeneralCK/Certificates/E8TAxisProd0581StableWitnesses, GeneralCK/Certificates/E8TAxisProd0582StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0579StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0579StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨687872580056255843160164202748380391008755458653, 687872580056255843160164202748380391008755458654⟩
def centerDExp : DyadicInterval precision := ⟨570148394211525905172999746249825252784123887881, 570148394211525905172999746249825254983147143434⟩
def centerDLog : DyadicInterval precision := ⟨481395051335389284017617212273304505633359993607, 481395051335389284017617212273304507832383249160⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨570148394211525905172999746249825253333879701769, scale precision, 570148394211525905172999746249825254433391329546, scale precision,
    1, 128, 1, 128, ⟨-1375745160112511686320328405496760783426739862143, -1375745160112511686320328405496760783426737764990⟩, ⟨-1375745160112511686320328405496760780608284069625, -1375745160112511686320328405496760780608281972472⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨690420225029326113498094440548775752758242060760, 690420225029326113498094440548775752758242060761⟩
def centerCExp : DyadicInterval precision := ⟨568164124639057697496789727097072710991949309507, 568164124639057697496789727097072713190972565060⟩
def centerCLog : DyadicInterval precision := ⟨479966936110046153240148432476386013469957452529, 479966936110046153240148432476386015668980708082⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨568164124639057697496789727097072711541705123395, scale precision, 568164124639057697496789727097072712641216751172, scale precision,
    1, 128, 1, 128, ⟨-1380840450058652226996188881097551506930634686561, -1380840450058652226996188881097551506930632589408⟩, ⟨-1380840450058652226996188881097551504102335653634, -1380840450058652226996188881097551504102333556481⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1674770145210684617805094395269786724228671003686, 1674770145210684617805094395269786724228671003687⟩
def centerBExp : DyadicInterval precision := ⟨147727777006488180888095965886964826069122538796, 147727777006488180888095965886964828268145794349⟩
def centerBLog : DyadicInterval precision := ⟨140729474485073544482957688388711193960806290709, 140729474485073544482957688388711196159829546262⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨147727777006488180888095965886964826618878352684, scale precision, 147727777006488180888095965886964827718389980461, scale precision,
    3, 128, 3, 128, ⟨-3349540290421369235610188790539573453896191716722, -3349540290421369235610188790539573453896189619569⟩, ⟨-3349540290421369235610188790539573443018494395183, -3349540290421369235610188790539573443018492298030⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨682249998762477519670394645145297230397519416513, 693511205829020257423882496604739492695821414415⟩
def wholeDExp : DyadicInterval precision := ⟨565765939962058116901418666290376202748638649045, 574552180098098577953261580846255154870927737058⟩
def wholeDLog : DyadicInterval precision := ⟨478239054014281969770673762969782321702426146976, 484559560373994267607098493867261018654665103074⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨565765939962058116901418666290376203298394462933, scale precision, 574552180098098577953261580846255154321171923170, scale precision,
    1, 128, 1, 128, ⟨-1387022411658040514847764993209478986811787730860, -1387022411658040514847764993209478986811785633707⟩, ⟨-1364499997524955039340789290290594459396613333134, -1364499997524955039340789290290594459396611235981⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨684594872300561171838437370748108155026371343726, 696262816686547090870872380131302362861070126219⟩
def wholeCExp : DyadicInterval precision := ⟨563639578461141381360942648133449988444470864571, 572711480217088851984186630529794725895886424011⟩
def wholeCLog : DyadicInterval precision := ⟨476705308896731673081340389599391016546221880935, 483237688311891739592908426502673934888282706054⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨563639578461141381360942648133449988994226678459, scale precision, 572711480217088851984186630529794725346130610123, scale precision,
    1, 128, 1, 128, ⟨-1392525633373094181741744760262604727147642725744, -1392525633373094181741744760262604727147640628591⟩, ⟨-1369189744601122343676874741496216308649822631978, -1369189744601122343676874741496216308649820534825⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1657709236296638544083461313715792801174096393445, 1691896848727378798997214532612377099957263578156⟩
def wholeBExp : DyadicInterval precision := ⟨144305719818644634263846933735655641789563336681, 151217368883941845965704331274674999347018495821⟩
def wholeBLog : DyadicInterval precision := ⟨137618254037362686682730296612034056762356888557, 143895289433671906440189242040939704946879037180⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨144305719818644634263846933735655642339319150569, scale precision, 151217368883941845965704331274674998797262681933, scale precision,
    3, 128, 3, 128, ⟨-3383793697454757597994429065224754205482353396714, -3383793697454757597994429065224754205482351299561⟩, ⟨-3315418472593277088166922627431585597034855638539, -3315418472593277088166922627431585597034853541386⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0579StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0580StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0580StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨676643340013426075185609328596269506214112195118, 676643340013426075185609328596269506214112195119⟩
def centerDExp : DyadicInterval precision := ⟨578977364869803800462989438501500576320691752033, 578977364869803800462989438501500578519715007586⟩
def centerDLog : DyadicInterval precision := ⟨487732559398326774108745629110692920177628439235, 487732559398326774108745629110692922376651694788⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨578977364869803800462989438501500576870447565921, scale precision, 578977364869803800462989438501500577969959193698, scale precision,
    1, 128, 1, 128, ⟨-1353286680026852150371218657192539013815963666390, -1353286680026852150371218657192539013815961569237⟩, ⟨-1353286680026852150371218657192539011040487211240, -1353286680026852150371218657192539011040485114087⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨679566574228455183323120305307117602182255386579, 679566574228455183323120305307117602182255386580⟩
def centerCExp : DyadicInterval precision := ⟨576665898814967021601045591579053715527514829224, 576665898814967021601045591579053717726538084777⟩
def centerCLog : DyadicInterval precision := ⟨486076023705084300541786651621491143788108453401, 486076023705084300541786651621491145987131708954⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨576665898814967021601045591579053716077270643112, scale precision, 576665898814967021601045591579053717176782270889, scale precision,
    1, 128, 1, 128, ⟨-1359133148456910366646240610614235205757812559270, -1359133148456910366646240610614235205757810462117⟩, ⟨-1359133148456910366646240610614235202971211084200, -1359133148456910366646240610614235202971208987047⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1641875204019742804213465385465328434395821174906, 1641875204019742804213465385465328434395821174907⟩
def centerBExp : DyadicInterval precision := ⟨154529729191008206662419955509646960357460901715, 154529729191008206662419955509646962556484157268⟩
def centerBLog : DyadicInterval precision := ⟨146893986236877606374664290804433993095526552455, 146893986236877606374664290804433995294549808008⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨154529729191008206662419955509646960907216715603, scale precision, 154529729191008206662419955509646962006728343380, scale precision,
    3, 128, 3, 128, ⟨-3283750408039485608426930770930656873991089655989, -3283750408039485608426930770930656873991087558836⟩, ⟨-3283750408039485608426930770930656863592197140788, -3283750408039485608426930770930656863592195043635⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨671052481512572809340093335645151882932874114537, 682249998762477519670394645145297230397519416514⟩
def wholeDExp : DyadicInterval precision := ⟨574552180098098577953261580846255152671904481505, 583424017396714902499808941799093865790753691861⟩
def wholeDLog : DyadicInterval precision := ⟨484559560373994267607098493867261016455641847521, 490914027605645316992013980560028282815828884161⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨574552180098098577953261580846255153221660295393, scale precision, 583424017396714902499808941799093865240997877973, scale precision,
    1, 128, 1, 128, ⟨-1364499997524955039340789290290594462193466430073, -1364499997524955039340789290290594462193464332920⟩, ⟨-1342104963025145618680186671290303764488587902438, -1342104963025145618680186671290303764488585805285⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨673773020553136319730328951363436841108620280458, 685377114782674024387392371034154755132132905564⟩
def wholeCExp : DyadicInterval precision := ⟨572098741181601743730797072450556793553747044568, 581256004902067266365327486349618149445875858257⟩
def wholeCLog : DyadicInterval precision := ⟨482797393243663433012663072289808117806305959332, 489363734259709393247918045035976980660326677960⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨572098741181601743730797072450556794103502858456, scale precision, 581256004902067266365327486349618148896120044369, scale precision,
    1, 128, 1, 128, ⟨-1370754229565348048774784742068309511668690544450, -1370754229565348048774784742068309511668688447297⟩, ⟨-1347546041106272639460657902726873680834943593896, -1347546041106272639460657902726873680834941496743⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1624944972862367938326473237346743102186011629858, 1658873672423295159653623691861144237792348967725⟩
def wholeBExp : DyadicInterval precision := ⟨150976599055103116296656705655941530566374958259, 158151710955300090858760112455127385456955907764⟩
def wholeBLog : DyadicInterval precision := ⟨143677079213798588979249843766245828983577060679, 150165957987183888509913807428172428964079221962⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨150976599055103116296656705655941531116130772147, scale precision, 158151710955300090858760112455127384907200093876, scale precision,
    3, 128, 3, 128, ⟨-3317747344846590319307247383722288480906510623439, -3317747344846590319307247383722288480906508526286⟩, ⟨-3249889945724735876652946474693486199291655482208, -3249889945724735876652946474693486199291653385055⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0580StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0581StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0581StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨665477300625433477361232002502002625345921467119, 665477300625433477361232002502002625345921467120⟩
def centerDExp : DyadicInterval precision := ⟨587892208188294475401269251844616962692532348577, 587892208188294475401269251844616964891555604130⟩
def centerDLog : DyadicInterval precision := ⟨494103945124224218680176638976803110922563855190, 494103945124224218680176638976803113121587110743⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨587892208188294475401269251844616963242288162465, scale precision, 587892208188294475401269251844616964341799790242, scale precision,
    1, 128, 1, 128, ⟨-1330954601250866954722464005004005252058538439621, -1330954601250866954722464005004005252058536342468⟩, ⟨-1330954601250866954722464005004005249325149526009, -1330954601250866954722464005004005249325147428856⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨668384142207865498293774882608366904702404124206, 668384142207865498293774882608366904702404124207⟩
def centerCExp : DyadicInterval precision := ⟨585558286618712600922404181926003047947521316330, 585558286618712600922404181926003050146544571883⟩
def centerCLog : DyadicInterval precision := ⟨492438587350703748719733631343621002830761477248, 492438587350703748719733631343621005029784732801⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨585558286618712600922404181926003048497277130218, scale precision, 585558286618712600922404181926003049596788757995, scale precision,
    1, 128, 1, 128, ⟨-1336768284415730996587549765216733810776951132382, -1336768284415730996587549765216733810776949035229⟩, ⟨-1336768284415730996587549765216733808032667461597, -1336768284415730996587549765216733808032665364444⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1608659494400475599963769062577962445345735431819, 1608659494400475599963769062577962445345735431820⟩
def centerBExp : DyadicInterval precision := ⟨161715840059788589643933178994560349934747997239, 161715840059788589643933178994560352133771252792⟩
def centerBLog : DyadicInterval precision := ⟨153378532831679663589237463484758603298942991259, 153378532831679663589237463484758605497966246812⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨161715840059788589643933178994560350484503811127, scale precision, 161715840059788589643933178994560351584015438904, scale precision,
    3, 128, 3, 128, ⟨-3217318988800951199927538125155924895659872174267, -3217318988800951199927538125155924895659870077114⟩, ⟨-3217318988800951199927538125155924885723071650172, -3217318988800951199927538125155924885723069553019⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨659917674403335303398947154306570012946022027567, 671052481512572809340093335645151882932874114538⟩
def wholeDExp : DyadicInterval precision := ⟨583424017396714902499808941799093863591730436308, 592382009410612930615839145836493983293758080466⟩
def wholeDLog : DyadicInterval precision := ⟨490914027605645316992013980560028280616805628608, 497302293015079090720897450218278679747777485235⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨583424017396714902499808941799093864141486250196, scale precision, 592382009410612930615839145836493982744002266578, scale precision,
    1, 128, 1, 128, ⟨-1342104963025145618680186671290303767242910652864, -1342104963025145618680186671290303767242908555711⟩, ⟨-1319835348806670606797894308613140024535709142512, -1319835348806670606797894308613140024535707045359⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨662623035398286831751652389035954589091240196328, 674161973290306817594945360483944194001444873342⟩
def wholeCExp : DyadicInterval precision := ⟨580946705272801798938130771386608089814145208231, 590192967346016485656449927180617540824674033199⟩
def wholeCLog : DyadicInterval precision := ⟨489142427467768450313992404540201966338381462404, 495743784727647238417256752005641847682790918432⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨580946705272801798938130771386608090363901022119, scale precision, 590192967346016485656449927180617540274918219311, scale precision,
    1, 128, 1, 128, ⟨-1348323946580613635189890720967888389385924754895, -1348323946580613635189890720967888389385922657742⟩, ⟨-1325246070796573663503304778071909176821114792384, -1325246070796573663503304778071909176821112695231⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1591867000330174148021782611381705423145895772385, 1625522644149961592504990608112356307370169461413⟩
def wholeBExp : DyadicInterval precision := ⟨158026738667944215513495997841071261774415999272, 165475062339919478462078684400071848625131354997⟩
def wholeBLog : DyadicInterval precision := ⟨150053184318875705652722808315823772269488075552, 156759322820295063833163021737420001987760958916⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨158026738667944215513495997841071262324171813160, scale precision, 165475062339919478462078684400071848075375541109, scale precision,
    3, 128, 3, 128, ⟨-3251045288299923185009981216224712619824726505620, -3251045288299923185009981216224712619824724408467⟩, ⟨-3183734000660348296043565222763410841436263241865, -3183734000660348296043565222763410841436261144712⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0581StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0582StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0582StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨676643340013426075185609328596269506214112195118, 676643340013426075185609328596269506214112195119⟩
def centerDExp : DyadicInterval precision := ⟨578977364869803800462989438501500576320691752033, 578977364869803800462989438501500578519715007586⟩
def centerDLog : DyadicInterval precision := ⟨487732559398326774108745629110692920177628439235, 487732559398326774108745629110692922376651694788⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨578977364869803800462989438501500576870447565921, scale precision, 578977364869803800462989438501500577969959193698, scale precision,
    1, 128, 1, 128, ⟨-1353286680026852150371218657192539013815963666390, -1353286680026852150371218657192539013815961569237⟩, ⟨-1353286680026852150371218657192539011040487211240, -1353286680026852150371218657192539011040485114087⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨679176560538049434298754292480188616526505768349, 679176560538049434298754292480188616526505768350⟩
def centerCExp : DyadicInterval precision := ⟨576973757005058434872754088447578235027833032848, 576973757005058434872754088447578237226856288401⟩
def centerCLog : DyadicInterval precision := ⟨486296761825843119183828939037044661351004059138, 486296761825843119183828939037044663550027314691⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨576973757005058434872754088447578235577588846736, scale precision, 576973757005058434872754088447578236677100474513, scale precision,
    1, 128, 1, 128, ⟨-1358353121076098868597508584960377234445569893775, -1358353121076098868597508584960377234445567796622⟩, ⟨-1358353121076098868597508584960377231660455276774, -1358353121076098868597508584960377231660453179621⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1641295259021001504731069651773000605290639754804, 1641295259021001504731069651773000605290639754805⟩
def centerBExp : DyadicInterval precision := ⟨154652417134333082511022127549926276401439718828, 154652417134333082511022127549926278600462974381⟩
def centerBLog : DyadicInterval precision := ⟨147004938182252956517805990361934444623275076078, 147004938182252956517805990361934446822298331631⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨154652417134333082511022127549926276951195532716, scale precision, 154652417134333082511022127549926278050707160493, scale precision,
    3, 128, 3, 128, ⟨-3282590518042003009462139303546001215776602021752, -3282590518042003009462139303546001215776599924599⟩, ⟨-3282590518042003009462139303546001205385959094622, -3282590518042003009462139303546001205385956997469⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨671052481512572809340093335645151882932874114537, 682249998762477519670394645145297230397519416514⟩
def wholeDExp : DyadicInterval precision := ⟨574552180098098577953261580846255152671904481505, 583424017396714902499808941799093865790753691861⟩
def wholeDLog : DyadicInterval precision := ⟨484559560373994267607098493867261016455641847521, 490914027605645316992013980560028282815828884161⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨574552180098098577953261580846255153221660295393, scale precision, 583424017396714902499808941799093865240997877973, scale precision,
    1, 128, 1, 128, ⟨-1364499997524955039340789290290594462193466430073, -1364499997524955039340789290290594462193464332920⟩, ⟨-1342104963025145618680186671290303764488587902438, -1342104963025145618680186671290303764488585805285⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨673384143974267632835288320649971651582545055528, 684985954870617584802498872018885315023417237469⟩
def wholeCExp : DyadicInterval precision := ⟨572405059001372272001862759608803118967479409700, 581565408594060303575192225503827280039127960050⟩
def wholeCLog : DyadicInterval precision := ⟨483017520209761787288607159680220021728537458773, 489585081986457933554545942528691479507885313566⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨572405059001372272001862759608803119517235223588, scale precision, 581565408594060303575192225503827279489372146162, scale precision,
    1, 128, 1, 128, ⟨-1369971909741235169604997744037770631450507642576, -1369971909741235169604997744037770631450505545423⟩, ⟨-1346768287948535265670576641299943301783528552475, -1346768287948535265670576641299943301783526455322⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1624367382782845750333116617740305195409713843341, 1658291415190113609575446851504546909330072322078⟩
def wholeBExp : DyadicInterval precision := ⟨151096944110943745149648601412741545973516392795, 158276764485251271946382982255468250722452117817⟩
def wholeBLog : DyadicInterval precision := ⟨143786152272316218687329923163830430427790449648, 150278796258194026828842905544743503577792101048⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨151096944110943745149648601412741546523272206683, scale precision, 158276764485251271946382982255468250172696303929, scale precision,
    3, 128, 3, 128, ⟨-3316582830380227219150893703009093823977718638088, -3316582830380227219150893703009093823977716540935⟩, ⟨-3248734765565691500666233235480610385743073878350, -3248734765565691500666233235480610385743071781197⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0582StableWitnesses

end


