-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0037StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0037StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:28:20.780534+00:00
-- url     : https://prove2.me/theorems/dd4be047-f10c-4a8a-91ae-5e7cda467c56
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0037StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisZero0038StableWitnesses, GeneralCK.Certificates.E8TAxisZero00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0037StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisZero0038StableWitnesses, GeneralCK.Certificates.E8TAxisZero0039StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0037StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisZero0038StableWitnesses, GeneralCK.Certificates.E8TAxisZero0039StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0037StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisZero0038StableWitnesses, GeneralCK.Certificates.E8TAxisZero0039StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0037StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisZero0038StableWitnesses, GeneralCK/Certificates/E8TAxisZero0039StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0037StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0037StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨485917755434160891773462032334740628415117575842, 485917755434160891773462032334740628415117575843⟩
def centerDExp : DyadicInterval precision := ⟨751644042802555100556006121456236859448629838317, 751644042802555100556006121456236861647653093870⟩
def centerDLog : DyadicInterval precision := ⟨606450780028547033690895338790838686899984128629, 606450780028547033690895338790838689099007384182⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨751644042802555100556006121456236859998385652205, scale precision, 751644042802555100556006121456236861097897279982, scale precision,
    0, 256, 0, 256, ⟨-971835510868321783546924064669481257899185032921, -971835510868321783546924064669481257899182935768⟩, ⟨-971835510868321783546924064669481255761287367599, -971835510868321783546924064669481255761285270446⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨486273536209192166680464206287651354647406316357, 486273536209192166680464206287651354647406316358⟩
def centerCExp : DyadicInterval precision := ⟨751278178811303202069614492706893299032789506843, 751278178811303202069614492706893301231812762396⟩
def centerCLog : DyadicInterval precision := ⟨606209153356826975803026439085656112348028729088, 606209153356826975803026439085656114547051984641⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨751278178811303202069614492706893299582545320731, scale precision, 751278178811303202069614492706893300682056948508, scale precision,
    0, 256, 0, 256, ⟨-972547072418384333360928412575302710364283079967, -972547072418384333360928412575302710364280982814⟩, ⟨-972547072418384333360928412575302708225344282619, -972547072418384333360928412575302708225342185466⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1092623794257389517889489728286932508917604978984, 1092623794257389517889489728286932508917604978985⟩
def centerBExp : DyadicInterval precision := ⟨327671843253274303990038085448304225573240791279, 327671843253274303990038085448304227772264046832⟩
def centerBLog : DyadicInterval precision := ⟨295646208419430710786416186813562526010241603045, 295646208419430710786416186813562528209264858598⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨327671843253274303990038085448304226122996605167, scale precision, 327671843253274303990038085448304227222508232944, scale precision,
    0, 256, 0, 256, ⟨-2185247588514779035778979456573865020287264909476, -2185247588514779035778979456573865020287262812323⟩, ⟨-2185247588514779035778979456573865015383157103611, -2185247588514779035778979456573865015383155006458⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨477040995173626483635311023942643508471660670039, 494828875109284674194281948410566590218630888610⟩
def wholeDExp : DyadicInterval precision := ⟨742533801492811413004049823802046283438332233585, 760830284245465294695388294487623571972247912142⟩
def wholeDLog : DyadicInterval precision := ⟨600422206098217740957049834384989020037338221569, 612504570538325940964339858761912612235438761042⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨742533801492811413004049823802046283988088047473, scale precision, 760830284245465294695388294487623571422492098254, scale precision,
    0, 256, 0, 256, ⟨-989657750218569348388563896821133181519326727149, -989657750218569348388563896821133181519324629996⟩, ⟨-954081990347252967270622047885287015887280011311, -954081990347252967270622047885287015887277914158⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨477040995173626483635311023942643508471660670039, 495543268424541307964823262387162562286101825386⟩
def wholeCExp : DyadicInterval precision := ⟨741808243667164317623916619935340826716953057533, 760830284245465294695388294487623571972247912142⟩
def wholeCLog : DyadicInterval precision := ⟨599941007606703218084900534397005014525915958618, 612504570538325940964339858761912612235438761042⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨741808243667164317623916619935340827266708871421, scale precision, 760830284245465294695388294487623571422492098254, scale precision,
    0, 256, 0, 256, ⟨-991086536849082615929646524774325125655326960376, -991086536849082615929646524774325125655324863223⟩, ⟨-954081990347252967270622047885287015887280011311, -954081990347252967270622047885287015887277914158⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1068318150054420709967239969515113973503824951291, 1117201928718692108021617223385872370067790757794⟩
def wholeBExp : DyadicInterval precision := ⟨316834180029148107033218414422959581363397952235, 338753878963658712732956507308121636431738209503⟩
def wholeBLog : DyadicInterval precision := ⟨286766449489789062861980362452480264128048187251, 304670743972010732452706440580196738860804112331⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨316834180029148107033218414422959581913153766123, scale precision, 338753878963658712732956507308121635881982395615, scale precision,
    0, 256, 0, 256, ⟨-2234403857437384216043234446771744742671511680323, -2234403857437384216043234446771744742671509583170⟩, ⟨-2136636300108841419934479939030227944635813838656, -2136636300108841419934479939030227944635811741503⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0037StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0038StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0038StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨468197947567212351774406011872494977440423975668, 468197947567212351774406011872494977440423975669⟩
def centerDExp : DyadicInterval precision := ⟨770093267120006045819929989156897110520154385328, 770093267120006045819929989156897112719177640881⟩
def centerDLog : DyadicInterval precision := ⟨618583648477847123240200594096127216349000772546, 618583648477847123240200594096127218548024028099⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨770093267120006045819929989156897111069910199216, scale precision, 770093267120006045819929989156897112169421826993, scale precision,
    0, 256, 0, 256, ⟨-936395895134424703548812023744989955924188886698, -936395895134424703548812023744989955924186789545⟩, ⟨-936395895134424703548812023744989953837509113130, -936395895134424703548812023744989953837507015977⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨468551030283629433578860177876522960566631622424, 468551030283629433578860177876522960566631622425⟩
def centerCExp : DyadicInterval precision := ⟨769721264877058473166145119527705987687618980947, 769721264877058473166145119527705989886642236500⟩
def centerCLog : DyadicInterval precision := ⟨618339998877091907492415108284967462932692970498, 618339998877091907492415108284967465131716226051⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨769721264877058473166145119527705988237374794835, scale precision, 769721264877058473166145119527705989336886422612, scale precision,
    0, 256, 0, 256, ⟨-937102060567258867157720355753045922177108420895, -937102060567258867157720355753045922177106323742⟩, ⟨-937102060567258867157720355753045920089420165956, -937102060567258867157720355753045920089418068803⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1045221110789093729184619959242090342385094389587, 1045221110789093729184619959242090342385094389588⟩
def centerBExp : DyadicInterval precision := ⟨349631972489482817401656153658575982815989308314, 349631972489482817401656153658575985015012563867⟩
def centerBLog : DyadicInterval precision := ⟨313475333578218346761028451929384722498508891102, 313475333578218346761028451929384724697532146655⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨349631972489482817401656153658575983365745122202, scale precision, 349631972489482817401656153658575984465256749979, scale precision,
    0, 256, 0, 256, ⟨-2090442221578187458369239918484180687068232013106, -2090442221578187458369239918484180687068229915953⟩, ⟨-2090442221578187458369239918484180682472147642393, -2090442221578187458369239918484180682472145545240⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨459387967798615484561738103898747303530785179429, 477040995173626483635311023942643508471660670040⟩
def wholeDExp : DyadicInterval precision := ⟨760830284245465294695388294487623569773224656589, 779433753649515438129873373659005449491648691216⟩
def wholeDLog : DyadicInterval precision := ⟨612504570538325940964339858761912610036415505489, 624688092853175616303270580088334960516446661035⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨760830284245465294695388294487623570322980470477, scale precision, 779433753649515438129873373659005448941892877328, scale precision,
    0, 256, 0, 256, ⟨-954081990347252967270622047885287017999364766000, -954081990347252967270622047885287017999362668847⟩, ⟨-918775935597230969123476207797494606030734574454, -918775935597230969123476207797494606030732477301⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨459387967798615484561738103898747303530785179429, 477749886812595267904089875359623307557272545270⟩
def wholeCExp : DyadicInterval precision := ⟨760092570798305895630605365076300357376013098497, 779433753649515438129873373659005449491648691216⟩
def wholeCLog : DyadicInterval precision := ⟨612019337710713729234559670735098353520536379884, 624688092853175616303270580088334960516446661035⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨760092570798305895630605365076300357925768912385, scale precision, 779433753649515438129873373659005448941892877328, scale precision,
    0, 256, 0, 256, ⟨-955499773625190535808179750719246616171613466175, -955499773625190535808179750719246616171611369022⟩, ⟨-918775935597230969123476207797494606030734574454, -918775935597230969123476207797494606030732477301⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1021445538539008934043661388348683314089808721882, 1069266194161851377821362925880269549299729057281⟩
def wholeBExp : DyadicInterval precision := ⟨338314679478191600369134409702645554319964739956, 361194613070145617150272744707730464248387114177⟩
def wholeBLog : DyadicInterval precision := ⟨304314145103950816978222069600431630587734539540, 322776195656555334781180755902779107349353520031⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨338314679478191600369134409702645554869720553844, scale precision, 361194613070145617150272744707730463698631300289, scale precision,
    0, 256, 0, 256, ⟨-2138532388323702755642725851760539100974375390152, -2138532388323702755642725851760539100974373292999⟩, ⟨-2042891077078017868087322776697366625955141733675, -2042891077078017868087322776697366625955139636522⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0038StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0039StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0039StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

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

def centerCAlpha : DyadicInterval precision := ⟨450960900767686460981800962203976686314762873237, 450960900767686460981800962203976686314762873238⟩
def centerCExp : DyadicInterval precision := ⟨788474263212340418825579119833731672893290083169, 788474263212340418825579119833731675092313338722⟩
def centerCLog : DyadicInterval precision := ⟨630572304995724508112042466520156676471517599583, 630572304995724508112042466520156678670540855136⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨788474263212340418825579119833731673443045897057, scale precision, 788474263212340418825579119833731674542557524834, scale precision,
    0, 128, 0, 128, ⟨-901921801535372921963601924407953373648544231154, -901921801535372921963601924407953373648542134001⟩, ⟨-901921801535372921963601924407953371610509358952, -901921801535372921963601924407953371610507261799⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨998854258083938015240870627282002735755220979444, 998854258083938015240870627282002735755220979445⟩
def centerBExp : DyadicInterval precision := ⟨372535401226950634800060743805797322666215353726, 372535401226950634800060743805797324865238609279⟩
def centerBLog : DyadicInterval precision := ⟨331841463637735094799562694145926611227503839384, 331841463637735094799562694145926613426527094937⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨372535401226950634800060743805797323215971167614, scale precision, 372535401226950634800060743805797324315482795391, scale precision,
    0, 128, 0, 128, ⟨-1997708516167876030481741254564005473667201853696, -1997708516167876030481741254564005473667199756543⟩, ⟨-1997708516167876030481741254564005469353684161235, -1997708516167876030481741254564005469353682064082⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

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

def wholeCAlpha : DyadicInterval precision := ⟨441864642833471825996809190961403572059602547859, 460091564435561259240709968794075934566944012037⟩
def wholeCExp : DyadicInterval precision := ⟨778683644276763750590717162547461274953091984572, 798350393094904597531547569261377275013063266071⟩
def wholeCLog : DyadicInterval precision := ⟨624198801817832807762057890746298065097017900788, 636973437495070745585836635514540158238274439736⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨778683644276763750590717162547461275502847798460, scale precision, 798350393094904597531547569261377274463307452183, scale precision,
    0, 128, 0, 128, ⟨-920183128871122518481419937588151870165718915275, -920183128871122518481419937588151870165716818122⟩, ⟨-883729285666943651993618381922807143112794637420, -883729285666943651993618381922807143112792540267⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨975600703579453276531743651610475769628580187227, 1022372861277245739002886928894538520949876104749⟩
def wholeBExp : DyadicInterval precision := ⟨360736547835041306824950537159995614709244784274, 384580652141547931179027400214492856938661282966⟩
def wholeBLog : DyadicInterval precision := ⟨322408856761182563500821520578483379686404646759, 341408662540245513176818329390234880577527784567⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨360736547835041306824950537159995615259000598162, scale precision, 384580652141547931179027400214492856388905469078, scale precision,
    0, 128, 0, 128, ⟨-2044745722554491478005773857789077044127054669459, -2044745722554491478005773857789077044127052572306⟩, ⟨-1951201407158906553063487303220951537167953300739, -1951201407158906553063487303220951537167951203586⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0039StableWitnesses

end


