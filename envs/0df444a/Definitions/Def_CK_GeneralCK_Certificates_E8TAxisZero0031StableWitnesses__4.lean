-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0031StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0031StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:03:43.312614+00:00
-- url     : https://prove2.me/theorems/cd130298-ace9-4753-afae-629ff64421c4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0031StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisZero0032StableWitnesses, GeneralCK.Certificates.E8TAxisZero00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0031StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisZero0032StableWitnesses, GeneralCK.Certificates.E8TAxisZero0033StableWitnesses, GeneralCK.Certificates.E8TAxisZero0034StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0031StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisZero0032StableWitnesses, GeneralCK.Certificates.E8TAxisZero0033StableWitnesses, GeneralCK.Certificates.E8TAxisZero0034StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0031StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisZero0032StableWitnesses, GeneralCK.Certificates.E8TAxisZero0033StableWitnesses, GeneralCK.Certificates.E8TAxisZero0034StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0031StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisZero0032StableWitnesses, GeneralCK/Certificates/E8TAxisZero0033StableWitnesses, GeneralCK/Certificates/E8TAxisZero0034StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0031StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0031StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

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

def centerCAlpha : DyadicInterval precision := ⟨155320103237356503596006017379859640825929150398, 155320103237356503596006017379859640825929150399⟩
def centerCExp : DyadicInterval precision := ⟨1181654732038150922850539664685759978039014723338, 1181654732038150922850539664685759980238037978891⟩
def centerCLog : DyadicInterval precision := ⟨865953416705758978934595820677861739385690079302, 865953416705758978934595820677861741584713334855⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1181654732038150922850539664685759978588770537226, scale precision, 1181654732038150922850539664685759979688282165003, scale precision,
    0, 128, 0, 128, ⟨-310640206474713007192012034759719282331811792627, -310640206474713007192012034759719282331809695474⟩, ⟨-310640206474713007192012034759719280971906906122, -310640206474713007192012034759719280971904808969⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨314397242134590218325088087467422076356226119954, 314397242134590218325088087467422076356226119955⟩
def centerBExp : DyadicInterval precision := ⟨950493249403931478792492530656457401907922158490, 950493249403931478792492530656457404106945414043⟩
def centerBLog : DyadicInterval precision := ⟨732197315150415128172888168055822346999131260552, 732197315150415128172888168055822349198154516105⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨950493249403931478792492530656457402457677972378, scale precision, 950493249403931478792492530656457403557189600155, scale precision,
    0, 128, 0, 128, ⟨-628794484269180436650176174934844153557771256428, -628794484269180436650176174934844153557769159275⟩, ⟨-628794484269180436650176174934844151867135320541, -628794484269180436650176174934844151867133223388⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

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

def wholeCAlpha : DyadicInterval precision := ⟨150991919513477176104051187712444417195036210428, 159651396288211647973703921921881298484828879846⟩
def wholeCExp : DyadicInterval precision := ⟨1174671565152235155130184470635190536603009146086, 1188674354540648287330851150581954943606665789757⟩
def wholeCLog : DyadicInterval precision := ⟨862087048580478295800139445438908750833409520835, 869829687869058094079061307765923603360191874427⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1174671565152235155130184470635190537152764959974, scale precision, 1188674354540648287330851150581954943056909975869, scale precision,
    0, 128, 0, 128, ⟨-319302792576423295947407843843762597653653420861, -319302792576423295947407843843762597653651323708⟩, ⟨-301983839026954352208102375424888833714136431622, -301983839026954352208102375424888833714134334469⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨305741530935075953839244385929164159203164552709, 323076633986625420554114277919708384865414881160⟩
def wholeBExp : DyadicInterval precision := ⟨939270676413094436586014141796240664978946895696, 961818742565408613466907997915298000639465600973⟩
def wholeBLog : DyadicInterval precision := ⟨725381345108217079989914971185021320376069454424, 739043717569107002066769324458966200204494229375⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨939270676413094436586014141796240665528702709584, scale precision, 961818742565408613466907997915298000089709787085, scale precision,
    0, 128, 0, 128, ⟨-646153267973250841108228555839416770586248788170, -646153267973250841108228555839416770586246691017⟩, ⟨-611483061870151907678488771858328317570965873209, -611483061870151907678488771858328317570963776056⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0031StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0032StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0032StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨146987038246024121844160689604839910465058611105, 146987038246024121844160689604839910465058611106⟩
def centerDExp : DyadicInterval precision := ⟨1195206770736568477483493079521979997730413799104, 1195206770736568477483493079521979999929437054657⟩
def centerDLog : DyadicInterval precision := ⟨873427709257314482190114267347085618455089893048, 873427709257314482190114267347085620654113148601⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1195206770736568477483493079521979998280169612992, scale precision, 1195206770736568477483493079521979999379681240769, scale precision,
    0, 128, 0, 128, ⟨-293974076492048243688321379209679821602360967033, -293974076492048243688321379209679821602358869880⟩, ⟨-293974076492048243688321379209679820257875574543, -293974076492048243688321379209679820257873477390⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨147307335044411473182108922772063685530326845473, 147307335044411473182108922772063685530326845474⟩
def centerCExp : DyadicInterval precision := ⟨1194683012148723380101911510546559169321831423057, 1194683012148723380101911510546559171520854678610⟩
def centerCLog : DyadicInterval precision := ⟨873139552116604068393114985696711946987788993556, 873139552116604068393114985696711949186812249109⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1194683012148723380101911510546559169871587236945, scale precision, 1194683012148723380101911510546559170971098864722, scale precision,
    0, 128, 0, 128, ⟨-294614670088822946364217845544127371733192152344, -294614670088822946364217845544127371733190055191⟩, ⟨-294614670088822946364217845544127370388117326705, -294614670088822946364217845544127370388115229552⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨297772080655470080886655242884286810656065954419, 297772080655470080886655242884286810656065954420⟩
def centerBExp : DyadicInterval precision := ⟨972365588829511186945740568321555181717282345971, 972365588829511186945740568321555183916305601524⟩
def centerBLog : DyadicInterval precision := ⟨745390706221635068087184311689716868610987276159, 745390706221635068087184311689716870810010531712⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨972365588829511186945740568321555182267038159859, scale precision, 972365588829511186945740568321555183366549787636, scale precision,
    0, 128, 0, 128, ⟨-595544161310940161773310485768573622138436388308, -595544161310940161773310485768573622138434291155⟩, ⟨-595544161310940161773310485768573620485829526525, -595544161310940161773310485768573620485827429372⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨142984678294030808430193174439689638732873799524, 150991919513477176104051187712444417195036210429⟩
def wholeDExp : DyadicInterval precision := ⟨1188674354540648287330851150581954941407642534204, 1201770939647839765988959733979548166667559706770⟩
def wholeDLog : DyadicInterval precision := ⟨869829687869058094079061307765923601161168618874, 877034319321159546816789449956018118197948476500⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1188674354540648287330851150581954941957398348092, scale precision, 1201770939647839765988959733979548166117803892882, scale precision,
    0, 128, 0, 128, ⟨-301983839026954352208102375424888835066010507244, -301983839026954352208102375424888835066008410091⟩, ⟨-285969356588061616860386348879379276797177794708, -285969356588061616860386348879379276797175697555⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨142984678294030808430193174439689638732873799524, 151632939129008056697517373665649318183483033499⟩
def wholeCExp : DyadicInterval precision := ⟨1187632098471748154820948330413552637007407916362, 1201770939647839765988959733979548166667559706770⟩
def wholeCLog : DyadicInterval precision := ⟨869254798289420289309708762878379527657599146636, 877034319321159546816789449956018118197948476500⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1187632098471748154820948330413552637557163730250, scale precision, 1201770939647839765988959733979548166117803892882, scale precision,
    0, 128, 0, 128, ⟨-303265878258016113395034747331298637043497350117, -303265878258016113395034747331298637043495252964⟩, ⟨-285969356588061616860386348879379276797177794708, -285969356588061616860386348879379276797175697555⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨289160022559818845156424937767397025574157886773, 306406529456171130952351701227325511683437947575⟩
def wholeBExp : DyadicInterval precision := ⟨960943865541731091515367813263173041684974167016, 983892922446469118853387927975743981788878518423⟩
def wholeBLog : DyadicInterval precision := ⟨738515985009427417807501760964090830831513406708, 752296360822110031467471195763059032944457639560⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨960943865541731091515367813263173042234729980904, scale precision, 983892922446469118853387927975743981239122704535, scale precision,
    0, 128, 0, 128, ⟨-612813058912342261904703402454651024203001769474, -612813058912342261904703402454651024202999672321⟩, ⟨-578320045119637690312849875534794050331694399297, -578320045119637690312849875534794050331692302144⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0032StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0033StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0033StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨138984770367679047606875056826648434719489737964, 138984770367679047606875056826648434719489737965⟩
def centerDExp : DyadicInterval precision := ⟨1208367104819141335120726173598708722736266317802, 1208367104819141335120726173598708724935289573355⟩
def centerDLog : DyadicInterval precision := ⟨880649566147303539816976282535028842882764309855, 880649566147303539816976282535028845081787565408⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1208367104819141335120726173598708723286022131690, scale precision, 1208367104819141335120726173598708724385533759467, scale precision,
    0, 128, 0, 128, ⟨-277969540735358095213750113653296870103901821126, -277969540735358095213750113653296870103899723973⟩, ⟨-277969540735358095213750113653296868774059227885, -277969540735358095213750113653296868774057130732⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨139304674397555093248917659957715349505540815682, 139304674397555093248917659957715349505540815683⟩
def centerCExp : DyadicInterval precision := ⟨1207838228360159608549699050312226782838357166529, 1207838228360159608549699050312226785037380422082⟩
def centerCLog : DyadicInterval precision := ⟨880360027427224137336487895461590630171820117367, 880360027427224137336487895461590632370843372920⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1207838228360159608549699050312226783388112980417, scale precision, 1207838228360159608549699050312226784487624608194, scale precision,
    0, 128, 0, 128, ⟨-278609348795110186497835319915430699676295125836, -278609348795110186497835319915430699676293028683⟩, ⟨-278609348795110186497835319915430698345870234050, -278609348795110186497835319915430698345868136897⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨281229727521010614347226107824309390844763740543, 281229727521010614347226107824309390844763740544⟩
def centerBExp : DyadicInterval precision := ⟨994628527835930195533404265947217167506308051197, 994628527835930195533404265947217169705331306750⟩
def centerBLog : DyadicInterval precision := ⟨758698503349046068538925908273509365549093547853, 758698503349046068538925908273509367748116803406⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨994628527835930195533404265947217168056063865085, scale precision, 994628527835930195533404265947217169155575492862, scale precision,
    0, 128, 0, 128, ⟨-562459455042021228694452215648618782497336670737, -562459455042021228694452215648618782497334573584⟩, ⟨-562459455042021228694452215648618780881720388589, -562459455042021228694452215648618780881718291436⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨134987245269836870215393179468011326867547174258, 142984678294030808430193174439689638732873799525⟩
def wholeDExp : DyadicInterval precision := ⟨1201770939647839765988959733979548164468536451217, 1214995512532168524628632240632930004533537374880⟩
def wholeDLog : DyadicInterval precision := ⟨877034319321159546816789449956018115998925220947, 884273498322789745939213484257675327336644869096⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1201770939647839765988959733979548165018292265105, scale precision, 1214995512532168524628632240632930003983781560992, scale precision,
    0, 128, 0, 128, ⟨-285969356588061616860386348879379278134319500540, -285969356588061616860386348879379278134317403387⟩, ⟨-269974490539673740430786358936022653073801578439, -269974490539673740430786358936022653073799481286⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨134987245269836870215393179468011326867547174258, 143624889310919960230471164280159196827619120960⟩
def wholeCExp : DyadicInterval precision := ⟨1200718528834184853391310342751497741093288764464, 1214995512532168524628632240632930004533537374880⟩
def wholeCLog : DyadicInterval precision := ⟨876456682575976142298361162756131020179469060019, 884273498322789745939213484257675327336644869096⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1200718528834184853391310342751497741643044578352, scale precision, 1214995512532168524628632240632930003983781560992, scale precision,
    0, 128, 0, 128, ⟨-287249778621839920460942328560318394324396135198, -287249778621839920460942328560318394324394038045⟩, ⟨-269974490539673740430786358936022653073801578439, -269974490539673740430786358936022653073799481286⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨272658858022120150330970042848572591083767790686, 289821708815072720468221936650414567978851753461⟩
def wholeBExp : DyadicInterval precision := ⟨983002422228797412925137426354918999584925951059, 1006363062196829127890208034234317471389852404954⟩
def wholeBLog : DyadicInterval precision := ⟨751764052223558962742893770839715827587696880995, 765664421925330452562213141131585421551189535260⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨983002422228797412925137426354919000134681764947, scale precision, 1006363062196829127890208034234317470840096591066, scale precision,
    0, 128, 0, 128, ⟨-579643417630145440936443873300829136775066755185, -579643417630145440936443873300829136775064658032⟩, ⟨-545317716044240300661940085697145181369147805567, -545317716044240300661940085697145181369145708414⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0033StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0034StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0034StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨130992033893699994791369923976531926829092122734, 130992033893699994791369923976531926829092122735⟩
def centerDExp : DyadicInterval precision := ⟨1221656411836274069288773586476386668146918568609, 1221656411836274069288773586476386670345941824162⟩
def centerDLog : DyadicInterval precision := ⟨887906164936387943905585824070712899195502313636, 887906164936387943905585824070712901394525569189⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1221656411836274069288773586476386668696674382497, scale precision, 1221656411836274069288773586476386669796186010274, scale precision,
    0, 128, 0, 128, ⟨-261984067787399989582739847953063854315873506824, -261984067787399989582739847953063854315871409671⟩, ⟨-261984067787399989582739847953063853000497081267, -261984067787399989582739847953063853000494984114⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨131311567284914649502665877971305210847657001217, 131311567284914649502665877971305210847657001218⟩
def centerCExp : DyadicInterval precision := ⟨1221122338287781298159968712095575742482912964124, 1221122338287781298159968712095575744681936219677⟩
def centerCLog : DyadicInterval precision := ⟨887615229015193471289061716161839048181904119440, 887615229015193471289061716161839050380927374993⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1221122338287781298159968712095575743032668778012, scale precision, 1221122338287781298159968712095575744132180405789, scale precision,
    0, 128, 0, 128, ⟨-262623134569829299005331755942610422353290912183, -262623134569829299005331755942610422353288815030⟩, ⟨-262623134569829299005331755942610421037339189841, -262623134569829299005331755942610421037337092688⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨264765452971270480650238705671629167219911907656, 264765452971270480650238705671629167219911907657⟩
def centerBExp : DyadicInterval precision := ⟨1017292490698628958068816631798387228768996244107, 1017292490698628958068816631798387230968019499660⟩
def centerBLog : DyadicInterval precision := ⟨772122681611229325990422615270340480051886148458, 772122681611229325990422615270340482250909404011⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1017292490698628958068816631798387229318752057995, scale precision, 1017292490698628958068816631798387230418263685772, scale precision,
    0, 128, 0, 128, ⟨-529530905942540961300477411343258335229636082862, -529530905942540961300477411343258335229633985709⟩, ⟨-529530905942540961300477411343258333650013644917, -529530905942540961300477411343258333650011547764⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨126999067220414009923202423697912773180597398746, 134987245269836870215393179468011326867547174259⟩
def wholeDExp : DyadicInterval precision := ⟨1214995512532168524628632240632930002334514119327, 1228350054579566692017908102915209767793957734212⟩
def wholeDLog : DyadicInterval precision := ⟨884273498322789745939213484257675325137621613543, 891547615580027951955449639520829064234092557127⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1214995512532168524628632240632930002884269933215, scale precision, 1228350054579566692017908102915209767244201920324, scale precision,
    0, 128, 0, 128, ⟨-269974490539673740430786358936022654396389215748, -269974490539673740430786358936022654396387118595⟩, ⟨-253998134440828019846404847395825545707091570879, -253998134440828019846404847395825545707089473726⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨126999067220414009923202423697912773180597398746, 135626692008785377142630029624202994261554904100⟩
def wholeCExp : DyadicInterval precision := ⟨1213932790367752907470564320597495059540259597038, 1228350054579566692017908102915209767793957734212⟩
def wholeCLog : DyadicInterval precision := ⟨883693083502000011870295132974730813598893353803, 891547615580027951955449639520829064234092557127⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1213932790367752907470564320597495060090015410926, scale precision, 1228350054579566692017908102915209767244201920324, scale precision,
    0, 128, 0, 128, ⟨-271253384017570754285260059248405989184983596771, -271253384017570754285260059248405989184981499618⟩, ⟨-253998134440828019846404847395825545707091570879, -253998134440828019846404847395825545707089473726⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨256233328382592948799518632260864583083635375283, 273317421200188951886965822796529956432845743031⟩
def wholeBExp : DyadicInterval precision := ⟨1005456521844459780778513696130757998904511114880, 1029239839924196772159254586274144060399381080023⟩
def wholeBLog : DyadicInterval precision := ⟨765127458284635026651998529297265610474764901239, 779149939480909138582665574125961105420771432974⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1005456521844459780778513696130757999454266928768, scale precision, 1029239839924196772159254586274144059849625266135, scale precision,
    0, 128, 0, 128, ⟨-546634842400377903773931645593059913664801202863, -546634842400377903773931645593059913664799105710⟩, ⟨-512466656765185897599037264521729165386628657514, -512466656765185897599037264521729165386626560361⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0034StableWitnesses

end


