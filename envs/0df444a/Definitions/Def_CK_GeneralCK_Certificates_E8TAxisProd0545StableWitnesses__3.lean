-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0545StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0545StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:34:21.47917+00:00
-- url     : https://prove2.me/theorems/2213162b-555a-4ab2-aeef-56d901c0ce93
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0545StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0546StableWitnesses, GeneralCK.Certificates.E8TAxisProd05…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0545StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0546StableWitnesses, GeneralCK.Certificates.E8TAxisProd0547StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0545StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0546StableWitnesses, GeneralCK.Certificates.E8TAxisProd0547StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0545StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0546StableWitnesses, GeneralCK.Certificates.E8TAxisProd0547StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0545StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0546StableWitnesses, GeneralCK/Certificates/E8TAxisProd0547StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0545StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0545StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨599752983055354003753543703993878049904129928193, 599752983055354003753543703993878049904129928194⟩
def centerDExp : DyadicInterval precision := ⟨643218459949503680164771431112985722806282727100, 643218459949503680164771431112985725005305982653⟩
def centerDLog : DyadicInterval precision := ⟨533036044781290419045280039370268756967708914819, 533036044781290419045280039370268759166732170372⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨643218459949503680164771431112985723356038540988, scale precision, 643218459949503680164771431112985724455550168765, scale precision,
    1, 128, 1, 128, ⟨-1199505966110708007507087407987756101057399529178, -1199505966110708007507087407987756101057397432025⟩, ⟨-1199505966110708007507087407987756098559122280751, -1199505966110708007507087407987756098559120183598⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨604069217808099829601902851033359521019839673918, 604069217808099829601902851033359521019839673919⟩
def centerCExp : DyadicInterval precision := ⟨639430439792812859868573130905867543787558683779, 639430439792812859868573130905867545986581939332⟩
def centerCLog : DyadicInterval precision := ⟨530403302496024189030308370887750254586518707880, 530403302496024189030308370887750256785541963433⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨639430439792812859868573130905867544337314497667, scale precision, 639430439792812859868573130905867545436826125444, scale precision,
    1, 128, 1, 128, ⟨-1208138435616199659203805702066719043296218984708, -1208138435616199659203805702066719043296216887555⟩, ⟨-1208138435616199659203805702066719040783141808118, -1208138435616199659203805702066719040783139710965⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1417577530221505555473950028773059131848406651970, 1417577530221505555473950028773059131848406651971⟩
def centerBExp : DyadicInterval precision := ⟨210046281010882203042333366103339101186938206796, 210046281010882203042333366103339103385961462349⟩
def centerBLog : DyadicInterval precision := ⟨196258724321876189347582691875769181380782606285, 196258724321876189347582691875769183579805861838⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨210046281010882203042333366103339101736694020684, scale precision, 210046281010882203042333366103339102836205648461, scale precision,
    2, 128, 2, 128, ⟨-2835155060443011110947900057546118267522014295424, -2835155060443011110947900057546118267522012198271⟩, ⟨-2835155060443011110947900057546118259871614409614, -2835155060443011110947900057546118259871612312461⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨594370338528145575810628189240163754488538282193, 605149690269836019889894242842311313124295302838⟩
def wholeDExp : DyadicInterval precision := ⟨638485690296710810307667032247350011657984843106, 647973841382699837641744325099416508397027426555⟩
def wholeDLog : DyadicInterval precision := ⟨529745944986552956313550471423206441742828804091, 536334420746670162773197764634792507319087016290⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨638485690296710810307667032247350012207740656994, scale precision, 647973841382699837641744325099416507847271612667, scale precision,
    1, 128, 1, 128, ⟨-1210299380539672039779788485684622627506989507705, -1210299380539672039779788485684622627506987410552⟩, ⟨-1188740677056291151621256378480327507737106227057, -1188740677056291151621256378480327507737104129904⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨598487973107424181807943955095342636841394169377, 609665627618550486571971357084281122678191402165⟩
def wholeCExp : DyadicInterval precision := ⟨634552105492441236072089342456863757669008639037, 644332906104182102158577104317479471078435806521⟩
def wholeCLog : DyadicInterval precision := ⟨527005770512765689437559740867935230085053415178, 533809702912722378361306789022958388683263223360⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨634552105492441236072089342456863758218764452925, scale precision, 644332906104182102158577104317479470528679992633, scale precision,
    1, 128, 1, 128, ⟨-1219331255237100973143942714168562246622582507320, -1219331255237100973143942714168562246622580410167⟩, ⟨-1196975946214848363615887910190685272435811288715, -1196975946214848363615887910190685272435809191562⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1401689844540869625488678195496165281603119130962, 1433548009253636178442357407744745378681619746521⟩
def wholeBExp : DyadicInterval precision := ⟨205505541976659229770712574176694369524423199408, 214663027264487065344846141145651376548044252661⟩
def wholeBLog : DyadicInterval precision := ⟨192283171167199750624939818841680199893722975232, 200289767202126682560184273997061162231399208670⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨205505541976659229770712574176694370074179013296, scale precision, 214663027264487065344846141145651375998288438773, scale precision,
    2, 128, 2, 128, ⟨-2867096018507272356884714815489490761272960028511, -2867096018507272356884714815489490761272957931358⟩, ⟨-2803379689081739250977356390992330559463307738311, -2803379689081739250977356390992330559463305641158⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0545StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0546StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0546StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3324030191359282881556817859241043973740987770, 3324030191359282881556817859241043973740987771⟩
def centerAExp : DyadicInterval precision := ⟨1454868674354870198336951421367206718659928330939, 1454868674354870198336951421367206720858951586492⟩
def centerALog : DyadicInterval precision := ⟨1009715489181788885783740077569471416073335956070, 1009715489181788885783740077569471418272359211623⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454868674354870198336951421367206719209684144827, scale precision, 1454868674354870198336951421367206720309195772604, scale precision,
    0, 128, 0, 128, ⟨-6648060382718565763113635718482088499745256643, -6648060382718565763113635718482088499743159490⟩, ⟨-6648060382718565763113635718482087395220791593, -6648060382718565763113635718482087395218694440⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨614521929459240509791534245666894735049576177871, 614521929459240509791534245666894735049576177872⟩
def centerCExp : DyadicInterval precision := ⟨630349086336114425586602803031903256506489070073, 630349086336114425586602803031903258705512325626⟩
def centerCLog : DyadicInterval precision := ⟨524072216755636364236365839760963812932021227778, 524072216755636364236365839760963815131044483331⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨630349086336114425586602803031903257056244883961, scale precision, 630349086336114425586602803031903258155756511738, scale precision,
    1, 128, 1, 128, ⟨-1229043858918481019583068491333789471373794772962, -1229043858918481019583068491333789471373792675809⟩, ⟨-1229043858918481019583068491333789468824512035676, -1229043858918481019583068491333789468824509938523⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1448500236121026294284584277726109675455237766000, 1448500236121026294284584277726109675455237766001⟩
def centerBExp : DyadicInterval precision := ⟨201343326760591904209543665820518007798336036615, 201343326760591904209543665820518009997359292168⟩
def centerBLog : DyadicInterval precision := ⟨188629502920464702928074250102157120382393231005, 188629502920464702928074250102157122581416486558⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨201343326760591904209543665820518008348091850503, scale precision, 201343326760591904209543665820518009447603478280, scale precision,
    2, 128, 2, 128, ⟨-2897000472242052588569168555452219354901018681263, -2897000472242052588569168555452219354901016584110⟩, ⟨-2897000472242052588569168555452219346919934479892, -2897000472242052588569168555452219346919932382739⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3482318024844347500022322904444928295572395253⟩
def wholeAExp : DyadicInterval precision := ⟨1454553569581723058392238696431353224119669669100, 1455183847209450510423929547351191477780877052172⟩
def wholeALog : DyadicInterval precision := ⟨1009557569928173087760872372803888449827653659813, 1009873425488092576137085252579843092274389747387⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1454553569581723058392238696431353224669425482988, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-6964636049688695000044645808889857143527710010, -6964636049688695000044645808889857143525612857⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨608912281716833680520920355875808042733653141170, 620147000625435167268220529674147902694474565283⟩
def wholeCExp : DyadicInterval precision := ⟨625515501058813146130620533630963151157468837371, 635206615497407151070568431781365642503702338231⟩
def wholeCLog : DyadicInterval precision := ⟨520691255126520165462341919941114712732135096250, 527462065171355565909245144997282658281621383400⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨625515501058813146130620533630963151707224651259, scale precision, 635206615497407151070568431781365641953946524343, scale precision,
    1, 128, 1, 128, ⟨-1240294001250870334536441059348295806673441164211, -1240294001250870334536441059348295806673439067058⟩, ⟨-1217824563433667361041840711751616084202413353858, -1217824563433667361041840711751616084202411256705⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1432453390941048766246276862493698424305845950649, 1464628191474595856146348944423271746888965021501⟩
def wholeBExp : DyadicInterval precision := ⟨196948279674787721664414623367534025444325686732, 205813606899057869148378700710727646651008296563⟩
def wholeBLog : DyadicInterval precision := ⟨184761510169840793488040226900295535189408785157, 192553233466269960304064690861213726892659949939⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨196948279674787721664414623367534025994081500620, scale precision, 205813606899057869148378700710727646101252482675, scale precision,
    2, 128, 2, 128, ⟨-2929256382949191712292697888846543497857525102033, -2929256382949191712292697888846543497857523004880⟩, ⟨-2864906781882097532492553724987396844707825590297, -2864906781882097532492553724987396844707823493144⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0546StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0547StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0547StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3324030191359282881556817859241043973740987770, 3324030191359282881556817859241043973740987771⟩
def centerAExp : DyadicInterval precision := ⟨1454868674354870198336951421367206718659928330939, 1454868674354870198336951421367206720858951586492⟩
def centerALog : DyadicInterval precision := ⟨1009715489181788885783740077569471416073335956070, 1009715489181788885783740077569471418272359211623⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454868674354870198336951421367206719209684144827, scale precision, 1454868674354870198336951421367206720309195772604, scale precision,
    0, 128, 0, 128, ⟨-6648060382718565763113635718482088499745256643, -6648060382718565763113635718482088499743159490⟩, ⟨-6648060382718565763113635718482087395220791593, -6648060382718565763113635718482087395218694440⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨599752983055354003753543703993878049904129928193, 599752983055354003753543703993878049904129928194⟩
def centerDExp : DyadicInterval precision := ⟨643218459949503680164771431112985722806282727100, 643218459949503680164771431112985725005305982653⟩
def centerDLog : DyadicInterval precision := ⟨533036044781290419045280039370268756967708914819, 533036044781290419045280039370268759166732170372⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨643218459949503680164771431112985723356038540988, scale precision, 643218459949503680164771431112985724455550168765, scale precision,
    1, 128, 1, 128, ⟨-1199505966110708007507087407987756101057399529178, -1199505966110708007507087407987756101057397432025⟩, ⟨-1199505966110708007507087407987756098559122280751, -1199505966110708007507087407987756098559120183598⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨603693534143130787589944944854123906884861811418, 603693534143130787589944944854123906884861811419⟩
def centerCExp : DyadicInterval precision := ⟨639759259584452344959424210991730277896058051660, 639759259584452344959424210991730280095081307213⟩
def centerCLog : DyadicInterval precision := ⟨530632026244703841891933072477235535281036701872, 530632026244703841891933072477235537480059957425⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨639759259584452344959424210991730278445813865548, scale precision, 639759259584452344959424210991730279545325493325, scale precision,
    1, 128, 1, 128, ⟨-1207387068286261575179889889708247815025617431218, -1207387068286261575179889889708247815025615334065⟩, ⟨-1207387068286261575179889889708247812513831911608, -1207387068286261575179889889708247812513829814455⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1417032989863744748109431996860364887659036514594, 1417032989863744748109431996860364887659036514595⟩
def centerBExp : DyadicInterval precision := ⟨210202861477139830281639130160898390695020744426, 210202861477139830281639130160898392894043999979⟩
def centerBLog : DyadicInterval precision := ⟨196395622515265949544075965238108510754423656419, 196395622515265949544075965238108512953446911972⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨210202861477139830281639130160898391244776558314, scale precision, 210202861477139830281639130160898392344288186091, scale precision,
    2, 128, 2, 128, ⟨-2834065979727489496218863993720729779140424622777, -2834065979727489496218863993720729779140422525624⟩, ⟨-2834065979727489496218863993720729771495723532753, -2834065979727489496218863993720729771495721435600⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3482318024844347500022322904444928295572395253⟩
def wholeAExp : DyadicInterval precision := ⟨1454553569581723058392238696431353224119669669100, 1455183847209450510423929547351191477780877052172⟩
def wholeALog : DyadicInterval precision := ⟨1009557569928173087760872372803888449827653659813, 1009873425488092576137085252579843092274389747387⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1454553569581723058392238696431353224669425482988, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-6964636049688695000044645808889857143527710010, -6964636049688695000044645808889857143525612857⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨594370338528145575810628189240163754488538282193, 605149690269836019889894242842311313124295302838⟩
def wholeDExp : DyadicInterval precision := ⟨638485690296710810307667032247350011657984843106, 647973841382699837641744325099416508397027426555⟩
def wholeDLog : DyadicInterval precision := ⟨529745944986552956313550471423206441742828804091, 536334420746670162773197764634792507319087016290⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨638485690296710810307667032247350012207740656994, scale precision, 647973841382699837641744325099416507847271612667, scale precision,
    1, 128, 1, 128, ⟨-1210299380539672039779788485684622627506989507705, -1210299380539672039779788485684622627506987410552⟩, ⟨-1188740677056291151621256378480327507737106227057, -1188740677056291151621256378480327507737104129904⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨598113303974901217915534016505274355515745863120, 609288920106705212564097463503137419540489809137⟩
def wholeCExp : DyadicInterval precision := ⟨634879306178190624363134265676241256903540703057, 644663351918886140824961859264356224537425641310⟩
def wholeCLog : DyadicInterval precision := ⟨527233897782339346655528651295673574958839165741, 534039022548910507962908532708828215182071689697⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨634879306178190624363134265676241257453296516945, scale precision, 644663351918886140824961859264356223987669827422, scale precision,
    1, 128, 1, 128, ⟨-1218577840213410425128194927006274840346526754606, -1218577840213410425128194927006274840346524657453⟩, ⟨-1196226607949802435831068033010548709785153860499, -1196226607949802435831068033010548709785151763346⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1401148149293055066965999826179586348532041277064, 1433000652190747133140296461528537022294471401473⟩
def wholeBExp : DyadicInterval precision := ⟨205659530237786753191261073116839338145550892520, 214822212924647051705015338656991962286592635421⟩
def wholeBLog : DyadicInterval precision := ⟨192418169807048564429480969397941887194813577025, 200428559685446262723142904916507787880532192250⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨205659530237786753191261073116839338695306706408, scale precision, 214822212924647051705015338656991961736836821533, scale precision,
    2, 128, 2, 128, ⟨-2866001304381494266280592923057074048495735922871, -2866001304381494266280592923057074048495733825718⟩, ⟨-2802296298586110133931999652359172693323925584630, -2802296298586110133931999652359172693323923487477⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0547StableWitnesses

end


