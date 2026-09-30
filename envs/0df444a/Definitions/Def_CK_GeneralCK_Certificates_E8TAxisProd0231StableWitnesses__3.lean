-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0231StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0231StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:55:47.689641+00:00
-- url     : https://prove2.me/theorems/f3cf0646-374f-4764-9a01-de164e7e85b2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0231StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0232StableWitnesses, GeneralCK.Certificates.E8TAxisProd02…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0231StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0232StableWitnesses, GeneralCK.Certificates.E8TAxisProd0233StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0231StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0232StableWitnesses, GeneralCK.Certificates.E8TAxisProd0233StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0231StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0232StableWitnesses, GeneralCK.Certificates.E8TAxisProd0233StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0231StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0232StableWitnesses, GeneralCK/Certificates/E8TAxisProd0233StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0231StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0231StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4590335763975281399345081579386246932603875055, 4590335763975281399345081579386246932603875056⟩
def centerAExp : DyadicInterval precision := ⟨1452349740496526708002027977982130829907047701826, 1452349740496526708002027977982130832106070957379⟩
def centerALog : DyadicInterval precision := ⟨1008452612267868520487407126245153689838327381286, 1008452612267868520487407126245153692037350636839⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452349740496526708002027977982130830456803515714, scale precision, 1452349740496526708002027977982130831556315143491, scale precision,
    0, 128, 0, 128, ⟨-9180671527950562798690163158772494418428866641, -9180671527950562798690163158772494418426769488⟩, ⟨-9180671527950562798690163158772493311988730734, -9180671527950562798690163158772493311986633581⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨803852177515934255585547919467375235228063974291, 803852177515934255585547919467375235228063974292⟩
def centerDExp : DyadicInterval precision := ⟨486474140463139135434442039725801311744313926422, 486474140463139135434442039725801313943337181975⟩
def centerDLog : DyadicInterval precision := ⟨419927923473864759956554512738531498009528841884, 419927923473864759956554512738531500208552097437⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨486474140463139135434442039725801312294069740310, scale precision, 486474140463139135434442039725801313393581368087, scale precision,
    1, 128, 1, 128, ⟨-1607704355031868511171095838934750472107746123950, -1607704355031868511171095838934750472107744026797⟩, ⟨-1607704355031868511171095838934750468804511870366, -1607704355031868511171095838934750468804509773213⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨809888621204814113380484052006476708179769641209, 809888621204814113380484052006476708179769641210⟩
def centerCExp : DyadicInterval precision := ⟨482472122167252737237129983652548046315613761607, 482472122167252737237129983652548048514637017160⟩
def centerCLog : DyadicInterval precision := ⟨416922253283379649460218035410240070774667956521, 416922253283379649460218035410240072973691212074⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨482472122167252737237129983652548046865369575495, scale precision, 482472122167252737237129983652548047964881203272, scale precision,
    1, 128, 1, 128, ⟨-1619777242409628226760968104012953418024857320754, -1619777242409628226760968104012953418024855223601⟩, ⟨-1619777242409628226760968104012953414694223341236, -1619777242409628226760968104012953414694221244083⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2026822533235937853922658152466370866689069005595, 2026822533235937853922658152466370866689069005596⟩
def centerBExp : DyadicInterval precision := ⟨91250018732241762554605377334107504122200463831, 91250018732241762554605377334107506321223719384⟩
def centerBLog : DyadicInterval precision := ⟨88514667401554968434809710615735831714677229902, 88514667401554968434809710615735833913700485455⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨91250018732241762554605377334107504671956277719, scale precision, 91250018732241762554605377334107505771467905496, scale precision,
    4, 128, 4, 128, ⟨-4053645066471875707845316304932741742183277220758, -4053645066471875707845316304932741742183275123605⟩, ⟨-4053645066471875707845316304932741724573000898780, -4053645066471875707845316304932741724572998801627⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 4748624479255801076876082777124010865681651339⟩
def wholeAExp : DyadicInterval precision := ⟨1452035179538035812075122148102075716455422985340, 1452664369350591901250217311774540050861815457867⟩
def wholeALog : DyadicInterval precision := ⟨1008294829281404787796718047455216463185937117999, 1008610412272733567070593870872814922068705325217⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452035179538035812075122148102075717005178799228, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-9497248958511602153752165554248022284704265776, -9497248958511602153752165554248022284702168623⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨797886217135535601213561462349015058648188303747, 809836502735595761416983074307699172577520882056⟩
def wholeDExp : DyadicInterval precision := ⟨482506534178222248007502303634473306418081574606, 490462045819898463991457369988920388736986392916⟩
def wholeDLog : DyadicInterval precision := ⟨416948124396604742320674577430730284979084793064, 422916858198723400101802834922666848815462481446⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨482506534178222248007502303634473306967837388494, scale precision, 490462045819898463991457369988920388187230579028, scale precision,
    1, 128, 1, 128, ⟨-1619673005471191522833966148615398346820241033264, -1619673005471191522833966148615398346820238936111⟩, ⟨-1595772434271071202427122924698030115658189688259, -1595772434271071202427122924698030115658187591106⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨803696310944812440969022459738225718904065351189, 816100712451065231583769515852576908630373977137⟩
def wholeCExp : DyadicInterval precision := ⟨478388024818681307253634944007464434584886626876, 486577914747696709790903248729443374910932363346⟩
def wholeCLog : DyadicInterval precision := ⟨413848552427284792140153405959388129118696432823, 420005779804942359384841535882528922602205548967⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨478388024818681307253634944007464435134642440764, scale precision, 486577914747696709790903248729443374361176549458, scale precision,
    1, 128, 1, 128, ⟨-1632201424902130463167539031705153818940283147616, -1632201424902130463167539031705153818940281050463⟩, ⟨-1607392621889624881938044919476451436156866870702, -1607392621889624881938044919476451436156864773549⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2008697193698693596943215232503748635648535803242, 2044987844475906101620209456222347648922278069936⟩
def wholeBExp : DyadicInterval precision := ⟨89009648778591189001521249406744905888699606349, 93541661902616612035010359993628658153883006840⟩
def wholeBLog : DyadicInterval precision := ⟨86404433763377888901088096256528794719237217718, 90670048242886782630462508916152542144100353682⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨89009648778591189001521249406744906438455420237, scale precision, 93541661902616612035010359993628657604127192952, scale precision,
    4, 128, 3, 128, ⟨-4089975688951812203240418912444695306871320389461, -4089975688951812203240418912444695306871318292308⟩, ⟨-4017394387397387193886430465007497262707648373012, -4017394387397387193886430465007497262707646275859⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0231StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0232StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0232StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨840037336037815392922282998599371946229808718837, 840037336037815392922282998599371946229808718838⟩
def centerDExp : DyadicInterval precision := ⟨462971716911096059979186904937436744746229273838, 462971716911096059979186904937436746945252529391⟩
def centerDLog : DyadicInterval precision := ⟨402187598898660414610829051743418455419293862475, 402187598898660414610829051743418457618317118028⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨462971716911096059979186904937436745295985087726, scale precision, 462971716911096059979186904937436746395496715503, scale precision,
    1, 128, 1, 128, ⟨-1680074672075630785844565997198743894195078759054, -1680074672075630785844565997198743894195076661901⟩, ⟨-1680074672075630785844565997198743890724158213450, -1680074672075630785844565997198743890724156116297⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨845762425116904020794359909009300774113549926793, 845762425116904020794359909009300774113549926794⟩
def centerCExp : DyadicInterval precision := ⟨459358722725350792875854109781412074809038893758, 459358722725350792875854109781412077008062149311⟩
def centerCLog : DyadicInterval precision := ⟨399441206068118904738968876122520403950679645210, 399441206068118904738968876122520406149702900763⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨459358722725350792875854109781412075358794707646, scale precision, 459358722725350792875854109781412076458306335423, scale precision,
    1, 128, 1, 128, ⟨-1691524850233808041588719818018601549976211090740, -1691524850233808041588719818018601549976208993587⟩, ⟨-1691524850233808041588719818018601546477990713588, -1691524850233808041588719818018601546477988616435⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2133861477590803020783536622622029295512397135055, 2133861477590803020783536622622029295512397135056⟩
def centerBExp : DyadicInterval precision := ⟨78816720406262006907901741193341961838959968122, 78816720406262006907901741193341964037983223675⟩
def centerBLog : DyadicInterval precision := ⟨76764927723807453984237636447976986492704654441, 76764927723807453984237636447976988691727909994⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨78816720406262006907901741193341962388715782010, scale precision, 78816720406262006907901741193341963488227409787, scale precision,
    4, 128, 4, 128, ⟨-4267722955181606041567073245244058601218939632081, -4267722955181606041567073245244058601218937534928⟩, ⟨-4267722955181606041567073245244058580830651005284, -4267722955181606041567073245244058580830648908131⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨833959591445470778384083818034390997094871334898, 846134075813431409586727826645377644661771969771⟩
def wholeDExp : DyadicInterval precision := ⟨459125158042315647897421247370792077462727192388, 466838367135635595432846250236128804162502981146⟩
def wholeDLog : DyadicInterval precision := ⟨399263485746125009998379766489542014905988654738, 405121100734994108525530084726425877554191840093⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨459125158042315647897421247370792078012483006276, scale precision, 466838367135635595432846250236128803612747167258, scale precision,
    1, 128, 1, 128, ⟨-1692268151626862819173455653290755291073544978437, -1692268151626862819173455653290755291073542881284⟩, ⟨-1667919182890941556768167636068781992468657623715, -1667919182890941556768167636068781992468655526562⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨839455166592395805407217682950670359384428464509, 852090124827301153547353151499115520457570392329⟩
def wholeCExp : DyadicInterval precision := ⟨455398226910767438238576585413262372489254244666, 463340700937036937766412117641448265761159898704⟩
def wholeCLog : DyadicInterval precision := ⟨396424721017376553380732861801118638588552803516, 402467789354726448713087751549657185699397140439⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨455398226910767438238576585413262373039010058554, scale precision, 463340700937036937766412117641448265211404084816, scale precision,
    1, 128, 1, 128, ⟨-1704180249654602307094706302998231042679463639183, -1704180249654602307094706302998231042679461542030⟩, ⟨-1678910333184791610814435365901340717034779748538, -1678910333184791610814435365901340717034777651385⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2115518591256460508615860472941704621906352270018, 2152237543968770886651991331139393231748711797658⟩
def wholeBExp : DyadicInterval precision := ⟨76859442569630898314732826494395769950838071724, 80820171893873056249601671183920390389047563830⟩
def wholeBLog : DyadicInterval precision := ⟨74906621130810359123933349859288224897306979558, 78664629202491672562325196314298823243743870489⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨76859442569630898314732826494395770500593885612, scale precision, 80820171893873056249601671183920389839291749942, scale precision,
    4, 128, 4, 128, ⟨-4304475087937541773303982662278786473951169756625, -4304475087937541773303982662278786473951167659472⟩, ⟨-4231037182512921017231720945883409233871263949689, -4231037182512921017231720945883409233871261852536⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0232StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0233StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0233StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨827900739799584217789378743685278152778005680170, 827900739799584217789378743685278152778005680171⟩
def centerDExp : DyadicInterval precision := ⟨470725140515848859951996893419642374006683999039, 470725140515848859951996893419642376205707254592⟩
def centerDLog : DyadicInterval precision := ⟨408063947160780491089293755661542510045178856930, 408063947160780491089293755661542512244202112483⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨470725140515848859951996893419642374556439812927, scale precision, 470725140515848859951996893419642375655951440704, scale precision,
    1, 128, 1, 128, ⟨-1655801479599168435578757487370556307262887510703, -1655801479599168435578757487370556307262885413550⟩, ⟨-1655801479599168435578757487370556303849137307135, -1655801479599168435578757487370556303849135209982⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨833590252817064147929547074815284551486230317993, 833590252817064147929547074815284551486230317994⟩
def centerCExp : DyadicInterval precision := ⟨467074377849637589845343130318733982708329371062, 467074377849637589845343130318733984907352626615⟩
def centerCLog : DyadicInterval precision := ⟨405299963870004049489458150568615129108504197913, 405299963870004049489458150568615131307527453466⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨467074377849637589845343130318733983258085184950, scale precision, 467074377849637589845343130318733984357596812727, scale precision,
    1, 128, 1, 128, ⟨-1667180505634128295859094149630569104692678121676, -1667180505634128295859094149630569104692676024523⟩, ⟨-1667180505634128295859094149630569101252245247455, -1667180505634128295859094149630569101252243150302⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2097835353750356164498215665553638641862567089503, 2097835353750356164498215665553638641862567089504⟩
def centerBExp : DyadicInterval precision := ⟨82799772243269199948369293147353332243623146992, 82799772243269199948369293147353334442646402545⟩
def centerBLog : DyadicInterval precision := ⟨80539292446755079472678452331203080234704989691, 80539292446755079472678452331203082433728245244⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨82799772243269199948369293147353332793378960880, scale precision, 82799772243269199948369293147353333892890588657, scale precision,
    4, 128, 4, 128, ⟨-4195670707500712328996431331107277293428894070909, -4195670707500712328996431331107277293428891973756⟩, ⟨-4195670707500712328996431331107277274021376384276, -4195670707500712328996431331107277274021374287123⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨821860677686075647293949968540300351172223479071, 833959591445470778384083818034390997094871334899⟩
def wholeDExp : DyadicInterval precision := ⟨466838367135635595432846250236128801963479725593, 474632069948069015840646238761706424600391594793⟩
def wholeDLog : DyadicInterval precision := ⟨405121100734994108525530084726425875355168584540, 411016094834480306545789264008568525844426144161⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨466838367135635595432846250236128802513235539481, scale precision, 474632069948069015840646238761706424050635780905, scale precision,
    1, 128, 1, 128, ⟨-1667919182890941556768167636068781995910829813032, -1667919182890941556768167636068781995910827715879⟩, ⟨-1643721355372151294587899937080600700651623031325, -1643721355372151294587899937080600700651620934172⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨827322183697041457303215688908814632595492677180, 839878545320647635022140068963565399041721898608⟩
def wholeCExp : DyadicInterval precision := ⟨463072330686758284346753539973697735424329934821, 471097974502707476372857093044409774759814944922⟩
def wholeCLog : DyadicInterval precision := ⟨402264005960247566147076127930220586972150445199, 408345924889659456129950362778658755857494421751⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨463072330686758284346753539973697735974085748709, scale precision, 471097974502707476372857093044409774210059131034, scale precision,
    1, 128, 1, 128, ⟨-1679757090641295270044280137927130799818528047456, -1679757090641295270044280137927130799818525950303⟩, ⟨-1654644367394082914606431377817629263485462147652, -1654644367394082914606431377817629263485460050499⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2079560954082934868703548101493191175091947559254, 2116145138714690132284995274365497689374717462045⟩
def wholeBExp : DyadicInterval precision := ⟨80750906188308018010415608134044535028166901248, 84896512438718004356591175435427333209295796945⟩
def wholeBLog : DyadicInterval precision := ⟨78598991658678767065311509805182104128769703290, 82522267265223326059503117341531965510453573723⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨80750906188308018010415608134044535577922715136, scale precision, 84896512438718004356591175435427332659539983057, scale precision,
    4, 128, 4, 128, ⟨-4232290277429380264569990548730995388699405082080, -4232290277429380264569990548730995388699402984927⟩, ⟨-4159121908165869737407096202986382340719796888452, -4159121908165869737407096202986382340719794791299⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0233StableWitnesses

end


