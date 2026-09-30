-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0140StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0140StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:45:55.953402+00:00
-- url     : https://prove2.me/theorems/dc3ec442-e9be-4402-8abe-ca7fcedbdfa9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0140StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0141StableWitnesses, GeneralCK.Certificates.E8TAxisProd01…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0140StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0141StableWitnesses, GeneralCK.Certificates.E8TAxisProd0142StableWitnesses, GeneralCK.Certificates.E8TAxisProd0143StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0140StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0141StableWitnesses, GeneralCK.Certificates.E8TAxisProd0142StableWitnesses, GeneralCK.Certificates.E8TAxisProd0143StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0140StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0141StableWitnesses, GeneralCK.Certificates.E8TAxisProd0142StableWitnesses, GeneralCK.Certificates.E8TAxisProd0143StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0140StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0141StableWitnesses, GeneralCK/Certificates/E8TAxisProd0142StableWitnesses, GeneralCK/Certificates/E8TAxisProd0143StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0140StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0140StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨450610413097730743244362126978975884668402912586, 450610413097730743244362126978975884668402912587⟩
def centerDExp : DyadicInterval precision := ⟨788852527298295547523937279792077535251368933655, 788852527298295547523937279792077537450392189208⟩
def centerDLog : DyadicInterval precision := ⟨630817990789549768708034337561797068071575978800, 630817990789549768708034337561797070270599234353⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨788852527298295547523937279792077535801124747543, scale precision, 788852527298295547523937279792077536900636375320, scale precision,
    0, 128, 0, 128, ⟨-901220826195461486488724253957951770355335678976, -901220826195461486488724253957951770355333581823⟩, ⟨-901220826195461486488724253957951768318278068520, -901220826195461486488724253957951768318275971367⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨453064897030940381306389064497901127868101985729, 453064897030940381306389064497901127868101985730⟩
def centerCExp : DyadicInterval precision := ⟨786207333212900708765463902921190428148174530935, 786207333212900708765463902921190430347197786488⟩
def centerCLog : DyadicInterval precision := ⟨629099048295262256519769521103085342480939262392, 629099048295262256519769521103085344679962517945⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨786207333212900708765463902921190428697930344823, scale precision, 786207333212900708765463902921190429797441972600, scale precision,
    0, 128, 0, 128, ⟨-906129794061880762612778128995802256758160664798, -906129794061880762612778128995802256758158567645⟩, ⟨-906129794061880762612778128995802254714249375274, -906129794061880762612778128995802254714247278121⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1001607345064894442862830551774958178686402601900, 1001607345064894442862830551774958178686402601901⟩
def centerBExp : DyadicInterval precision := ⟨371134523175903124867127655211163842593778707113, 371134523175903124867127655211163844792801962666⟩
def centerBLog : DyadicInterval precision := ⟨330724709810071145282130701222212502142320937278, 330724709810071145282130701222212504341344192831⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨371134523175903124867127655211163843143534521001, scale precision, 371134523175903124867127655211163844243046148778, scale precision,
    1, 128, 1, 128, ⟨-2003214690129788885725661103549916359537705963822, -2003214690129788885725661103549916359537703866669⟩, ⟨-2003214690129788885725661103549916355207906540935, -2003214690129788885725661103549916355207904443782⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨441864642833471825996809190961403572059602547859, 459387967798615484561738103898747303530785179430⟩
def wholeDExp : DyadicInterval precision := ⟨779433753649515438129873373659005447292625435663, 798350393094904597531547569261377275013063266071⟩
def wholeDLog : DyadicInterval precision := ⟨624688092853175616303270580088334958317423405482, 636973437495070745585836635514540158238274439736⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨779433753649515438129873373659005447842381249551, scale precision, 798350393094904597531547569261377274463307452183, scale precision,
    0, 128, 0, 128, ⟨-918775935597230969123476207797494608092408240415, -918775935597230969123476207797494608092406143262⟩, ⟨-883729285666943651993618381922807143112794637420, -883729285666943651993618381922807143112792540267⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨443960763151251609132321977767296496917259278939, 462203602748688269141792523640124819118951699960⟩
def wholeCExp : DyadicInterval precision := ⟨776436318258027888796895818405699247830777530902, 796063648222342499064779916955612179055315278354⟩
def wholeCLog : DyadicInterval precision := ⟨622731905639341251634754391147859034047642699034, 635493794846582383137405903634672748976759047050⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨776436318258027888796895818405699248380533344790, scale precision, 796063648222342499064779916955612178505559464466, scale precision,
    0, 128, 0, 128, ⟨-924407205497376538283585047280249639272720831033, -924407205497376538283585047280249639272718733880⟩, ⟨-887921526302503218264643955534592992825217116731, -887921526302503218264643955534592992825215019578⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨978322747145986376526184164015472182615945010843, 1025157298611099341016983916793889384549374022059⟩
def wholeBExp : DyadicInterval precision := ⟨359364620428407329698854526253830413642458944930, 383150755746047970564433541193932081215996892364⟩
def wholeBLog : DyadicInterval precision := ⟨321308106410875709719075059399881098728119246244, 340276207239311583016751120621871949042607930428⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨359364620428407329698854526253830414192214758818, scale precision, 383150755746047970564433541193932080666241078476, scale precision,
    2, 128, 1, 128, ⟨-2050314597222198682033967833587778771334553555504, -2050314597222198682033967833587778771334551458351⟩, ⟨-1956645494291972753052368328030944363134886144446, -1956645494291972753052368328030944363134884047293⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0140StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0141StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0141StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨433150018597706032584967812015361721770461165013, 433150018597706032584967812015361721770461165014⟩
def centerDExp : DyadicInterval precision := ⟨807928177963092639274651197161192176096781955567, 807928177963092639274651197161192178295805211120⟩
def centerDLog : DyadicInterval precision := ⟨643154536224866812603613452556143370937466856601, 643154536224866812603613452556143373136490112154⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨807928177963092639274651197161192176646537769455, scale precision, 807928177963092639274651197161192177746049397232, scale precision,
    0, 128, 0, 128, ⟨-866300037195412065169935624030723444535404130786, -866300037195412065169935624030723444535402033633⟩, ⟨-866300037195412065169935624030723442546442626421, -866300037195412065169935624030723442546440529268⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨435587010669316532787888872890434762531713388002, 435587010669316532787888872890434762531713388003⟩
def centerCExp : DyadicInterval precision := ⟨805238293697697931770004487592236917604827700742, 805238293697697931770004487592236919803850956295⟩
def centerCLog : DyadicInterval precision := ⟨641421236573953555118909857517245624790047484710, 641421236573953555118909857517245626989070740263⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨805238293697697931770004487592236918154583514630, scale precision, 805238293697697931770004487592236919254095142407, scale precision,
    0, 128, 0, 128, ⟨-871174021338633065575777745780869526061230622112, -871174021338633065575777745780869526061228524959⟩, ⟨-871174021338633065575777745780869524065625027051, -871174021338633065575777745780869524065622929898⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨956198658621282653324757455959647474556586985940, 956198658621282653324757455959647474556586985941⟩
def centerBExp : DyadicInterval precision := ⟨394928352033601493868294618046208671941033434515, 394928352033601493868294618046208674140056690068⟩
def centerBLog : DyadicInterval precision := ⟨349577829079464886193231118072754211880485716902, 349577829079464886193231118072754214079508972455⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨394928352033601493868294618046208672490789248403, scale precision, 394928352033601493868294618046208673590300876180, scale precision,
    1, 128, 1, 128, ⟨-1912397317242565306649514911919294951147642837196, -1912397317242565306649514911919294951147640740043⟩, ⟨-1912397317242565306649514911919294947078707203718, -1912397317242565306649514911919294947078705106565⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨424465904280623337412236094991656409259795096049, 441864642833471825996809190961403572059602547860⟩
def wholeDExp : DyadicInterval precision := ⟨798350393094904597531547569261377272814040010518, 817586731060820878424464751762154419137555379748⟩
def wholeDLog : DyadicInterval precision := ⟨636973437495070745585836635514540156039251184183, 649361398245907818978439547465799274251803053932⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨798350393094904597531547569261377273363795824406, scale precision, 817586731060820878424464751762154418587799565860, scale precision,
    0, 128, 0, 128, ⟨-883729285666943651993618381922807145125617651173, -883729285666943651993618381922807145125615554020⟩, ⟨-848931808561246674824472189983312817536858777432, -848931808561246674824472189983312817536856680279⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨426547343159800146998773904909486888712338641587, 444659870113802983563502728531033170858443627735⟩
def wholeCExp : DyadicInterval precision := ⟨795302420875344595689568771195795642913858941934, 815261265991049296897286108825060932654566966015⟩
def wholeCLog : DyadicInterval precision := ⟨635000908713505589120855184510613440504691246783, 647869395500648726046723642993382018933830984413⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨795302420875344595689568771195795643463614755822, scale precision, 815261265991049296897286108825060932104811152127, scale precision,
    0, 128, 0, 128, ⟨-889319740227605967127005457062066342727156852261, -889319740227605967127005457062066342727154755108⟩, ⟨-853094686319600293997547809818973776439142705755, -853094686319600293997547809818973776439140608602⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨933426049150971184732480149862724658721618794396, 979230902525630537707852084081340734867436234931⟩
def wholeBExp : DyadicInterval precision := ⟨382674883145873958876060246751087975829594074488, 407429399369393723300082706529017946211565569297⟩
def wholeBLog : DyadicInterval precision := ⟨339899128982514190730797457669082362458697990606, 359386472912675088760426916075431094702049978943⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨382674883145873958876060246751087976379349888376, scale precision, 407429399369393723300082706529017945661809755409, scale precision,
    1, 128, 1, 128, ⟨-1958461805051261075415704168162681471834486159657, -1958461805051261075415704168162681471834484062504⟩, ⟨-1866852098301942369464960299725449315471193852740, -1866852098301942369464960299725449315471191755587⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0141StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0142StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0142StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨450610413097730743244362126978975884668402912586, 450610413097730743244362126978975884668402912587⟩
def centerDExp : DyadicInterval precision := ⟨788852527298295547523937279792077535251368933655, 788852527298295547523937279792077537450392189208⟩
def centerDLog : DyadicInterval precision := ⟨630817990789549768708034337561797068071575978800, 630817990789549768708034337561797070270599234353⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨788852527298295547523937279792077535801124747543, scale precision, 788852527298295547523937279792077536900636375320, scale precision,
    0, 128, 0, 128, ⟨-901220826195461486488724253957951770355335678976, -901220826195461486488724253957951770355333581823⟩, ⟨-901220826195461486488724253957951768318278068520, -901220826195461486488724253957951768318275971367⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨452363360814287342526917867113253712874417012034, 452363360814287342526917867113253712874417012035⟩
def centerCExp : DyadicInterval precision := ⟨786962471270797719953552952758049000634447917558, 786962471270797719953552952758049002833471173111⟩
def centerCLog : DyadicInterval precision := ⟨629589970463504982696410470733874500853259217019, 629589970463504982696410470733874503052282472572⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨786962471270797719953552952758049001184203731446, scale precision, 786962471270797719953552952758049002283715359223, scale precision,
    0, 128, 0, 128, ⟨-904726721628574685053835734226507426769810089194, -904726721628574685053835734226507426769807992041⟩, ⟨-904726721628574685053835734226507424727860056093, -904726721628574685053835734226507424727857958940⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1000689241486444894021575334287102903169361420266, 1000689241486444894021575334287102903169361420267⟩
def centerBExp : DyadicInterval precision := ⟨371601103663893251954356288137037839020885665660, 371601103663893251954356288137037841219908921213⟩
def centerBLog : DyadicInterval precision := ⟨331096753847657850214261389791228460754420742607, 331096753847657850214261389791228462953443998160⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨371601103663893251954356288137037839570641479548, scale precision, 371601103663893251954356288137037840670153107325, scale precision,
    1, 128, 1, 128, ⟨-2001378482972889788043150668574205808500905363297, -2001378482972889788043150668574205808500903266144⟩, ⟨-2001378482972889788043150668574205804176542414919, -2001378482972889788043150668574205804176540317766⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨441864642833471825996809190961403572059602547859, 459387967798615484561738103898747303530785179430⟩
def wholeDExp : DyadicInterval precision := ⟨779433753649515438129873373659005447292625435663, 798350393094904597531547569261377275013063266071⟩
def wholeDLog : DyadicInterval precision := ⟨624688092853175616303270580088334958317423405482, 636973437495070745585836635514540158238274439736⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨779433753649515438129873373659005447842381249551, scale precision, 798350393094904597531547569261377274463307452183, scale precision,
    0, 128, 0, 128, ⟨-918775935597230969123476207797494608092408240415, -918775935597230969123476207797494608092406143262⟩, ⟨-883729285666943651993618381922807143112794637420, -883729285666943651993618381922807143112792540267⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨443261856501343956161376671696244203127204536354, 461499381581860949131485878842069002795670661619⟩
def wholeCExp : DyadicInterval precision := ⟨777184926985868258238253560692459593609107380109, 796825385756610397812969454156942675925934910418⟩
def wholeCLog : DyadicInterval precision := ⟨623220708256935174856006921084270611721414383577, 635986844985079880340620748322159901760742880855⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨777184926985868258238253560692459594158863193997, scale precision, 796825385756610397812969454156942675376179096530, scale precision,
    0, 128, 0, 128, ⟨-922998763163721898262971757684138006625161986981, -922998763163721898262971757684138006625159889828⟩, ⟨-886523713002687912322753343392488405246072489864, -886523713002687912322753343392488405246070392711⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨977414995646579752871425924598711585174850155742, 1024228741177052029276836569204746508120070996099⟩
def wholeBExp : DyadicInterval precision := ⟨359821551546058612869382418447838200098946277286, 383627008086480608895458465871208978765685626725⟩
def wholeBLog : DyadicInterval precision := ⟨321674811981732307275408381779594075784541017786, 340653489019411114531854089637731480557480467817⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨359821551546058612869382418447838200648702091174, scale precision, 383627008086480608895458465871208978215929812837, scale precision,
    2, 128, 1, 128, ⟨-2048457482354104058553673138409493018473108294458, -2048457482354104058553673138409493018473106197305⟩, ⟨-1954829991293159505742851849197423168255299753310, -1954829991293159505742851849197423168255297656157⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0142StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0143StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0143StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨433150018597706032584967812015361721770461165013, 433150018597706032584967812015361721770461165014⟩
def centerDExp : DyadicInterval precision := ⟨807928177963092639274651197161192176096781955567, 807928177963092639274651197161192178295805211120⟩
def centerDLog : DyadicInterval precision := ⟨643154536224866812603613452556143370937466856601, 643154536224866812603613452556143373136490112154⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨807928177963092639274651197161192176646537769455, scale precision, 807928177963092639274651197161192177746049397232, scale precision,
    0, 128, 0, 128, ⟨-866300037195412065169935624030723444535404130786, -866300037195412065169935624030723444535402033633⟩, ⟨-866300037195412065169935624030723442546442626421, -866300037195412065169935624030723442546440529268⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨434890482329511609456605291303914073573726052559, 434890482329511609456605291303914073573726052560⟩
def centerCExp : DyadicInterval precision := ⟨806006187027095890136017821623926159613340635136, 806006187027095890136017821623926161812363890689⟩
def centerCLog : DyadicInterval precision := ⟨641916259091241730357353524155037233223580572314, 641916259091241730357353524155037235422603827867⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨806006187027095890136017821623926160163096449024, scale precision, 806006187027095890136017821623926161262608076801, scale precision,
    0, 128, 0, 128, ⟨-869780964659023218913210582607828148144305330593, -869780964659023218913210582607828148144303233440⟩, ⟨-869780964659023218913210582607828146150600976800, -869780964659023218913210582607828146150598879647⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨955300745008501844875000509466984997425744709421, 955300745008501844875000509466984997425744709422⟩
def centerBExp : DyadicInterval precision := ⟨395413920422838184775211778943650636690332240894, 395413920422838184775211778943650638889355496447⟩
def centerBLog : DyadicInterval precision := ⟨349960049904834127756367078041159118098456822104, 349960049904834127756367078041159120297480077657⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨395413920422838184775211778943650637240088054782, scale precision, 395413920422838184775211778943650638339599682559, scale precision,
    1, 128, 1, 128, ⟨-1910601490017003689750001018933969996883459957190, -1910601490017003689750001018933969996883457860037⟩, ⟨-1910601490017003689750001018933969992819520977647, -1910601490017003689750001018933969992819518880494⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨424465904280623337412236094991656409259795096049, 441864642833471825996809190961403572059602547860⟩
def wholeDExp : DyadicInterval precision := ⟨798350393094904597531547569261377272814040010518, 817586731060820878424464751762154419137555379748⟩
def wholeDLog : DyadicInterval precision := ⟨636973437495070745585836635514540156039251184183, 649361398245907818978439547465799274251803053932⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨798350393094904597531547569261377273363795824406, scale precision, 817586731060820878424464751762154418587799565860, scale precision,
    0, 128, 0, 128, ⟨-883729285666943651993618381922807145125617651173, -883729285666943651993618381922807145125615554020⟩, ⟨-848931808561246674824472189983312817536858777432, -848931808561246674824472189983312817536856680279⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨425853338453922988105921025000462397676821471068, 443960763151251609132321977767296496917259278940⟩
def wholeCExp : DyadicInterval precision := ⟨796063648222342499064779916955612176856292022801, 816035899282844599192681770600671263164726158372⟩
def wholeCLog : DyadicInterval precision := ⟨635493794846582383137405903634672746777735791497, 648366564209713227240650953399208862570974839308⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨796063648222342499064779916955612177406047836689, scale precision, 816035899282844599192681770600671262614970344484, scale precision,
    0, 128, 0, 128, ⟨-887921526302503218264643955534592994843822096180, -887921526302503218264643955534592994843819999027⟩, ⟨-851706676907845976211842050000924794369043897953, -851706676907845976211842050000924794369041800800⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨932538250269953775680376616181880825197150579198, 978322747145986376526184164015472182615945010844⟩
def wholeBExp : DyadicInterval precision := ⟨383150755746047970564433541193932079016973636811, 407924691568896865343428683474592038274436951913⟩
def wholeBLog : DyadicInterval precision := ⟨340276207239311583016751120621871946843584674875, 359773739454620754603506557408147124654607896269⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨383150755746047970564433541193932079566729450699, scale precision, 407924691568896865343428683474592037724681138025, scale precision,
    1, 128, 1, 128, ⟨-1956645494291972753052368328030944367328895996081, -1956645494291972753052368328030944367328893898928⟩, ⟨-1865076500539907551360753232363761648424651830970, -1865076500539907551360753232363761648424649733817⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0143StableWitnesses

end


