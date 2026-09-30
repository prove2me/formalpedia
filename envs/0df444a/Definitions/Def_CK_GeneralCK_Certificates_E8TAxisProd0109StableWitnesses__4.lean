-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0109StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0109StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:07:25.456654+00:00
-- url     : https://prove2.me/theorems/0bc75ddd-019d-411b-ad8d-f59fc4593c8e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0109StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0110StableWitnesses, GeneralCK.Certificates.E8TAxisProd01…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0109StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0110StableWitnesses, GeneralCK.Certificates.E8TAxisProd0111StableWitnesses, GeneralCK.Certificates.E8TAxisProd0112StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0109StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0110StableWitnesses, GeneralCK.Certificates.E8TAxisProd0111StableWitnesses, GeneralCK.Certificates.E8TAxisProd0112StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0109StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0110StableWitnesses, GeneralCK.Certificates.E8TAxisProd0111StableWitnesses, GeneralCK.Certificates.E8TAxisProd0112StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0109StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0110StableWitnesses, GeneralCK/Certificates/E8TAxisProd0111StableWitnesses, GeneralCK/Certificates/E8TAxisProd0112StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0109StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0109StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨472084776470646789278527173883319283684034059134, 472084776470646789278527173883319283684034059135⟩
def centerCExp : DyadicInterval precision := ⟨766008051766045442324929056403968874339120250581, 766008051766045442324929056403968876538143506134⟩
def centerCLog : DyadicInterval precision := ⟨615905733899332805144033566590604212072026145606, 615905733899332805144033566590604214271049401159⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨766008051766045442324929056403968874888876064469, scale precision, 766008051766045442324929056403968875988387692246, scale precision,
    0, 128, 0, 128, ⟨-944169552941293578557054347766638568416973313841, -944169552941293578557054347766638568416971216688⟩, ⟨-944169552941293578557054347766638566319165019848, -944169552941293578557054347766638566319162922695⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1049914531847662335746546611338606482172437957141, 1049914531847662335746546611338606482172437957142⟩
def centerBExp : DyadicInterval precision := ⟨347393573948887879975015359899622426343210317389, 347393573948887879975015359899622428542233572942⟩
def centerBLog : DyadicInterval precision := ⟨311667931642662796437957643538506989973136314785, 311667931642662796437957643538506992172159570338⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨347393573948887879975015359899622426892966131277, scale precision, 347393573948887879975015359899622427992477759054, scale precision,
    2, 128, 2, 128, ⟨-2099829063695324671493093222677212966657726371663, -2099829063695324671493093222677212966657724274510⟩, ⟨-2099829063695324671493093222677212962032027554054, -2099829063695324671493093222677212962032025456901⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨462908032749761032844270152027538372596821185650, 481297592983938212432061297252090574559776049476⟩
def wholeCExp : DyadicInterval precision := ⟨756411357148398302304613844355483062950210150975, 775688208936928796442199326484265717778476265742⟩
def wholeCLog : DyadicInterval precision := ⟨609595599775748008924932949287084153979341650590, 622243265736176823157812533480257573678672147659⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨756411357148398302304613844355483063499965964863, scale precision, 775688208936928796442199326484265717228720451854, scale precision,
    0, 128, 0, 128, ⟨-962595185967876424864122594504181150181764885277, -962595185967876424864122594504181150181762788124⟩, ⟨-925816065499522065688540304055076744157829012912, -925816065499522065688540304055076744157826915759⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1026086267881439742907649378959825778185245304554, 1074012673898068697820645011996430754133410924489⟩
def wholeBExp : DyadicInterval precision := ⟨336124329666940265954268279137445003081684110910, 358908067286278198959061957580162084230865382260⟩
def wholeBLog : DyadicInterval precision := ⟨302534436089322494075283319868365496964609504303, 320941612261494403699863268898768043828032320343⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨336124329666940265954268279137445003631439924798, scale precision, 358908067286278198959061957580162083681109568372, scale precision,
    2, 128, 2, 128, ⟨-2148025347796137395641290023992861510657215235190, -2148025347796137395641290023992861510657213138037⟩, ⟨-2052172535762879485815298757919651554131843114048, -2052172535762879485815298757919651554131841016895⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0109StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0110StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0110StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312260897, 2849167218250950044280193223065006085312260898⟩
def centerAExp : DyadicInterval precision := ⟨1455814397256041217437249255499380272227928609805, 1455814397256041217437249255499380274426951865358⟩
def centerALog : DyadicInterval precision := ⟨1010189349275934740575240882696318021950304507166, 1010189349275934740575240882696318024149327762719⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455814397256041217437249255499380272777684423693, scale precision, 1455814397256041217437249255499380273877196051470, scale precision,
    0, 128, 0, 128, ⟨-5698334436501900088560386446130012722529043537, -5698334436501900088560386446130012722526946384⟩, ⟨-5698334436501900088560386446130011618722097206, -5698334436501900088560386446130011618720000053⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨489121766478577070403207566244624990843129716705, 489121766478577070403207566244624990843129716706⟩
def centerCExp : DyadicInterval precision := ⟨748355638790978630883941713898573904382355876415, 748355638790978630883941713898573906581379131968⟩
def centerCLog : DyadicInterval precision := ⟨604277591911704706630937178601730644218924495879, 604277591911704706630937178601730646417947751432⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨748355638790978630883941713898573904932111690303, scale precision, 748355638790978630883941713898573906031623318080, scale precision,
    0, 128, 0, 128, ⟨-978243532957154140806415132489249982759906460561, -978243532957154140806415132489249982759904363408⟩, ⟨-978243532957154140806415132489249980612614503415, -978243532957154140806415132489249980612612406262⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1096461140439817000271602705184952315267272960212, 1096461140439817000271602705184952315267272960213⟩
def centerBExp : DyadicInterval precision := ⟨325955670505414072017693732649458409857813687594, 325955670505414072017693732649458412056836943147⟩
def centerBLog : DyadicInterval precision := ⟨294243665287747745562395864161772763161263354485, 294243665287747745562395864161772765360286610038⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨325955670505414072017693732649458410407569501482, scale precision, 325955670505414072017693732649458411507081129259, scale precision,
    2, 128, 2, 128, ⟨-2192922280879634000543205410369904632999511057168, -2192922280879634000543205410369904632999508960015⟩, ⟨-2192922280879634000543205410369904628069582880835, -2192922280879634000543205410369904628069580783682⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 3165742448647063503620071141085134670978073809⟩
def wholeAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨479877859596601426615371866855283257178900142786, 498403088841403716691900621082853263505200073821⟩
def wholeCExp : DyadicInterval precision := ⟨738910822887504142320836990661289071497830294266, 757882373421220111793627325274791611011859470222⟩
def wholeCLog : DyadicInterval precision := ⟨598017822856874087207046540887019994495367333067, 610564609858910174562243627150037687099079873006⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨738910822887504142320836990661289072047586108154, scale precision, 757882373421220111793627325274791610462103656334, scale precision,
    0, 128, 0, 128, ⟨-996806177682807433383801242165706528097770601624, -996806177682807433383801242165706528097768504471⟩, ⟨-959755719193202853230743733710566513297651302551, -959755719193202853230743733710566513297649205398⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1072112829804862998812524346003829014177160817668, 1121082111583694487816978874813616567839818458995⟩
def wholeBExp : DyadicInterval precision := ⟨315156294226780944930623079599417866502463183793, 336999340187064891066402648784844351700477902094⟩
def wholeBLog : DyadicInterval precision := ⟨285386850422842140637473368842542939084265026820, 303245662001428707220514499779441665349134377970⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨315156294226780944930623079599417867052218997681, scale precision, 336999340187064891066402648784844351150722088206, scale precision,
    2, 128, 2, 128, ⟨-2242164223167388975633957749627233138229068318579, -2242164223167388975633957749627233138229066221426⟩, ⟨-2144225659609725997625048692007658025970136941340, -2144225659609725997625048692007658025970134844187⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0110StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0111StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0111StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312260897, 2849167218250950044280193223065006085312260898⟩
def centerAExp : DyadicInterval precision := ⟨1455814397256041217437249255499380272227928609805, 1455814397256041217437249255499380274426951865358⟩
def centerALog : DyadicInterval precision := ⟨1010189349275934740575240882696318021950304507166, 1010189349275934740575240882696318024149327762719⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455814397256041217437249255499380272777684423693, scale precision, 1455814397256041217437249255499380273877196051470, scale precision,
    0, 128, 0, 128, ⟨-5698334436501900088560386446130012722529043537, -5698334436501900088560386446130012722526946384⟩, ⟨-5698334436501900088560386446130011618722097206, -5698334436501900088560386446130011618720000053⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨471377601658541626504415668935103060536313009635, 471377601658541626504415668935103060536313009636⟩
def centerCExp : DyadicInterval precision := ⟨766749705122053107469250764832971369821884812779, 766749705122053107469250764832971372020908068332⟩
def centerCLog : DyadicInterval precision := ⟨616392262506442687178593856543177082845278427928, 616392262506442687178593856543177085044301683481⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨766749705122053107469250764832971370371640626667, scale precision, 766749705122053107469250764832971371471152254444, scale precision,
    0, 128, 0, 128, ⟨-942755203317083253008831337870206122120516642194, -942755203317083253008831337870206122120514545041⟩, ⟨-942755203317083253008831337870206120024737493502, -942755203317083253008831337870206120024735396349⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1048975017908553564927895804972698981342995429365, 1048975017908553564927895804972698981342995429366⟩
def centerBExp : DyadicInterval precision := ⟨347840499218093772398601272479435463320900280868, 347840499218093772398601272479435465519923536421⟩
def centerBLog : DyadicInterval precision := ⟨312028981487235784767898742281801845601786638741, 312028981487235784767898742281801847800809894294⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨347840499218093772398601272479435463870656094756, scale precision, 347840499218093772398601272479435464970167722533, scale precision,
    2, 128, 2, 128, ⟨-2097950035817107129855791609945397964995869635568, -2097950035817107129855791609945397964995867538415⟩, ⟨-2097950035817107129855791609945397960376114179051, -2097950035817107129855791609945397960376112081898⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 3165742448647063503620071141085134670978073809⟩
def wholeAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨462203602748688269141792523640124819118951699959, 480587617583154446417785413694201341604360523169⟩
def wholeCExp : DyadicInterval precision := ⟨757146620674580303634324056305096653975843228393, 776436318258027888796895818405699250029800786455⟩
def wholeCLog : DyadicInterval precision := ⟨610080023993545524805315611001473672646929834568, 622731905639341251634754391147859036246665954587⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨757146620674580303634324056305096654525599042281, scale precision, 776436318258027888796895818405699249480044972567, scale precision,
    0, 128, 0, 128, ⟨-961175235166308892835570827388402684269902321030, -961175235166308892835570827388402684269900223877⟩, ⟨-924407205497376538283585047280249637203088065959, -924407205497376538283585047280249637203085968806⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1025157298611099341016983916793889384549374022058, 1073062543092661343514112144831798520728251141348⟩
def wholeBExp : DyadicInterval precision := ⟨336561646712749141840991121443245688966921743050, 359364620428407329698854526253830415841482200483⟩
def wholeBLog : DyadicInterval precision := ⟨302889939325008755919040991410275141123401335505, 321308106410875709719075059399881100927142501797⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨336561646712749141840991121443245689516677556938, scale precision, 359364620428407329698854526253830415291726386595, scale precision,
    2, 128, 2, 128, ⟨-2146125086185322687028224289663597043843789672355, -2146125086185322687028224289663597043843787575202⟩, ⟨-2050314597222198682033967833587778766862944629882, -2050314597222198682033967833587778766862942532729⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0111StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0112StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0112StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4748624479255801076876082777124010865681651338, 4748624479255801076876082777124010865681651339⟩
def centerAExp : DyadicInterval precision := ⟨1452035179538035812075122148102075716455422985340, 1452035179538035812075122148102075718654446240893⟩
def centerALog : DyadicInterval precision := ⟨1008294829281404787796718047455216463185937117999, 1008294829281404787796718047455216465384960373552⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452035179538035812075122148102075717005178799228, scale precision, 1452035179538035812075122148102075718104690427005, scale precision,
    0, 128, 0, 128, ⟨-9497248958511602153752165554248022284704265776, -9497248958511602153752165554248022284702168623⟩, ⟨-9497248958511602153752165554248021178024436730, -9497248958511602153752165554248021178022339577⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨455873090834334127127606761975766984386926651515, 455873090834334127127606761975766984386926651516⟩
def centerCExp : DyadicInterval precision := ⟨783191824059676683726901135246277035837985638356, 783191824059676683726901135246277038037008893909⟩
def centerCLog : DyadicInterval precision := ⟨627136992449414334485792704193317175374221128694, 627136992449414334485792704193317177573244384247⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨783191824059676683726901135246277036387741452244, scale precision, 783191824059676683726901135246277037487253080021, scale precision,
    0, 128, 0, 128, ⟨-911746181668668254255213523951533969799744813494, -911746181668668254255213523951533969799742716341⟩, ⟨-911746181668668254255213523951533967747963889722, -911746181668668254255213523951533967747961792569⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1005283842204879700312858893364603257548549485353, 1005283842204879700312858893364603257548549485354⟩
def centerBExp : DyadicInterval precision := ⟨369271989044416151279002006980631591568190923238, 369271989044416151279002006980631593767214178791⟩
def centerBLog : DyadicInterval precision := ⟨329238609659854963824388381929627944858427309316, 329238609659854963824388381929627947057450564869⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨369271989044416151279002006980631592117946737126, scale precision, 369271989044416151279002006980631593217458364903, scale precision,
    1, 128, 1, 128, ⟨-2010567684409759400625717786729206517272919052320, -2010567684409759400625717786729206517272916955167⟩, ⟨-2010567684409759400625717786729206512921280986246, -2010567684409759400625717786729206512921278889093⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1452664369350591901250217311774540050861815457867⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1008610412272733567070593870872814922068705325217⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨446758396143924564664295531329901350112173885284, 465022579048418109843785227554347945752391019349⟩
def wholeCExp : DyadicInterval precision := ⟨773446873391979796336261237240710449401174426331, 793021795703973532967486569668771476597611169175⟩
def wholeCLog : DyadicInterval precision := ⟨620778321863009711612674686753872664233332323840, 633523233810714225471076050968041108349364443991⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨773446873391979796336261237240710449950930240219, scale precision, 793021795703973532967486569668771476047855355287, scale precision,
    0, 128, 0, 128, ⟨-930045158096836219687570455108695892543599132396, -930045158096836219687570455108695892543597035243⟩, ⟨-893516792287849129328591062659802699211174873003, -893516792287849129328591062659802699211172775850⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨981957793704943887900796543837743973923757106624, 1028875648046368950410864822745891051770237671642⟩
def wholeBExp : DyadicInterval precision := ⟨357540675396703288152454084246107782437732367250, 381249543406319507828826343076981528469654899842⟩
def wholeBLog : DyadicInterval precision := ⟨319843399909746591860566682882877279844983535561, 338769116877203086834939915851727321443387565601⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨357540675396703288152454084246107782987488181138, scale precision, 381249543406319507828826343076981527919899085954, scale precision,
    2, 128, 1, 128, ⟨-2057751296092737900821729645491782105787686506452, -2057751296092737900821729645491782105787684409299⟩, ⟨-1963915587409887775801593087675487945740053007703, -1963915587409887775801593087675487945740050910550⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0112StableWitnesses

end


