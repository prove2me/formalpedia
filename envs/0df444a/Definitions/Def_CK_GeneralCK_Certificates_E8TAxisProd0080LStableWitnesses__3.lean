-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0080LStableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0080LStableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:14:32.866651+00:00
-- url     : https://prove2.me/theorems/507fe764-0176-411d-a86d-1fe1a8f10f80
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0080LStableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0087LStableWitnesses, GeneralCK.Certificates.E8TAxisProd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0080LStableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0087LStableWitnesses, GeneralCK.Certificates.E8TAxisProd0088LStableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0080LStableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0087LStableWitnesses, GeneralCK.Certificates.E8TAxisProd0088LStableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0080LStableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0087LStableWitnesses, GeneralCK.Certificates.E8TAxisProd0088LStableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0080LStableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0087LStableWitnesses, GeneralCK/Certificates/E8TAxisProd0088LStableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0080LStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0080LStableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨149870294601883869240195065526084414516177559366, 149870294601883869240195065526084414516177559367⟩
def centerCExp : DyadicInterval precision := ⟨1190500244370057353066121936822736429057719826259, 1190500244370057353066121936822736431256743081812⟩
def centerCLog : DyadicInterval precision := ⟨870836270878675153406727850421785870860253654942, 870836270878675153406727850421785873059276910495⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1190500244370057353066121936822736429607475640147, scale precision, 1190500244370057353066121936822736430706987267924, scale precision,
    0, 128, 0, 128, ⟨-299740589203767738480390131052168829707256509355, -299740589203767738480390131052168829707254412202⟩, ⟨-299740589203767738480390131052168828357455825265, -299740589203767738480390131052168828357453728112⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨300426418305483197906266584742714344045151064362, 300426418305483197906266584742714344045151064363⟩
def centerBExp : DyadicInterval precision := ⟨968840030346013441168229531646548358874485901872, 968840030346013441168229531646548361073509157425⟩
def centerBLog : DyadicInterval precision := ⟨743272125169354209900142554196799700759673679881, 743272125169354209900142554196799702958696935434⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨968840030346013441168229531646548359424241715760, scale precision, 968840030346013441168229531646548360523753343537, scale precision,
    0, 128, 0, 128, ⟨-600852836610966395812533169485428688919613483403, -600852836610966395812533169485428688919611386250⟩, ⟨-600852836610966395812533169485428687260992871199, -600852836610966395812533169485428687260990774046⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨145545901828368143194963992409340935150072244213, 154197686497932961536819931575887586175858849818⟩
def wholeCExp : DyadicInterval precision := ⟨1183471121605739864066405757523309461858073347133, 1197566200971201614847448590493226407053042434139⟩
def wholeCLog : DyadicInterval precision := ⟨866957422609189959781681149222032679416400610503, 874725096964288106315511122625193817639653271191⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1183471121605739864066405757523309462407829161021, scale precision, 1197566200971201614847448590493226406503286620251, scale precision,
    0, 128, 0, 128, ⟨-308395372995865923073639863151775173030627601552, -308395372995865923073639863151775173030625504399⟩, ⟨-291091803656736286389927984818681869629227285071, -291091803656736286389927984818681869629225187918⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨291807541876947883091319163960599378983261660199, 309067891082506609001259954034646670914709424587⟩
def wholeBExp : DyadicInterval precision := ⟨957450516359962807439347788495256245383035583615, 980334715740349356444873263819631440328006536724⟩
def wholeBLog : DyadicInterval precision := ⟨736406868263745359049599811702686315654895224316, 750168233079204747346576826424831420899687180994⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨957450516359962807439347788495256245932791397503, scale precision, 980334715740349356444873263819631439778250722836, scale precision,
    0, 128, 0, 128, ⟨-618135782165013218002519908069293342668595404370, -618135782165013218002519908069293342668593307217⟩, ⟨-583615083753895766182638327921198757146937946880, -583615083753895766182638327921198757146935849727⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0080LStableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0087LStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0087LStableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨149229456686881644311523955806507635972722949488, 149229456686881644311523955806507635972722949489⟩
def centerCExp : DyadicInterval precision := ⟨1191544721223432422566383341935569058926633286121, 1191544721223432422566383341935569061125656541674⟩
def centerCLog : DyadicInterval precision := ⟨871411762215211038337141323136122529433795022705, 871411762215211038337141323136122531632818278258⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1191544721223432422566383341935569059476389100009, scale precision, 1191544721223432422566383341935569060575900727786, scale precision,
    0, 128, 0, 128, ⟨-298458913373763288623047911613015272619755689658, -298458913373763288623047911613015272619753592505⟩, ⟨-298458913373763288623047911613015271271138205447, -298458913373763288623047911613015271271136108294⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨299762634096651696725568302549997531330384539968, 299762634096651696725568302549997531330384539969⟩
def centerBExp : DyadicInterval precision := ⟨969720484898055058596997620186108529284355249722, 969720484898055058596997620186108531483378505275⟩
def centerBLog : DyadicInterval precision := ⟨743801496309621673368809356979317582466883280739, 743801496309621673368809356979317584665906536292⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨969720484898055058596997620186108529834111063610, scale precision, 969720484898055058596997620186108530933622691387, scale precision,
    0, 128, 0, 128, ⟨-599525268193303393451136605099995063489327465027, -599525268193303393451136605099995063489325367874⟩, ⟨-599525268193303393451136605099995061832212791999, -599525268193303393451136605099995061832210694846⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨144905500794347715182706141919846628971144367136, 153556398750566205741514519544252603104850649527⟩
def wholeCExp : DyadicInterval precision := ⟨1184510160663970923559104633505172249696912350664, 1198616160495418846851243315457668779286983541480⟩
def wholeCLog : DyadicInterval precision := ⟨867531439519667230961090412510273875214052708558, 875302071594871397998691257579190997457078716262⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1184510160663970923559104633505172250246668164552, scale precision, 1198616160495418846851243315457668778737227727592, scale precision,
    0, 128, 0, 128, ⟨-307112797501132411483029039088505206888015669720, -307112797501132411483029039088505206888013572567⟩, ⟨-289811001588695430365412283839693257271959239502, -289811001588695430365412283839693257271957142349⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨291145468170785886189725348343662532983178579943, 308402344933586987341878295350818749064874893140⟩
def wholeBExp : DyadicInterval precision := ⟨958322931087011801974061944595498986167682324819, 981223319540892445972471542215359697615807964807⟩
def wholeBLog : DyadicInterval precision := ⟨736933875662125097118239462317175084622205750568, 750699988478042889630716549908019612594709002382⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨958322931087011801974061944595498986717438138707, scale precision, 981223319540892445972471542215359697066052150919, scale precision,
    0, 128, 0, 128, ⟨-616804689867173974683756590701637498968162393283, -616804689867173974683756590701637498968160296130⟩, ⟨-582290936341571772379450696687325065147514010482, -582290936341571772379450696687325065147511913329⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0087LStableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0088LStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0088LStableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨148588684311752543723876391055642810609806546761, 148588684311752543723876391055642810609806546762⟩
def centerCExp : DyadicInterval precision := ⟨1192590007479589074604733777994743674092641705267, 1192590007479589074604733777994743676291664960820⟩
def centerCLog : DyadicInterval precision := ⟨871987472737017034663638698217394463514341038084, 871987472737017034663638698217394465713364293637⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1192590007479589074604733777994743674642397519155, scale precision, 1192590007479589074604733777994743675741909146932, scale precision,
    0, 128, 0, 128, ⟨-297177368623505087447752782111285621893331863270, -297177368623505087447752782111285621893329766117⟩, ⟨-297177368623505087447752782111285620545896420929, -297177368623505087447752782111285620545894323776⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨299098983288193084504193693066047438536723730911, 299098983288193084504193693066047438536723730912⟩
def centerBExp : DyadicInterval precision := ⟨970601562396676875017945824263811609110087377863, 970601562396676875017945824263811611309110633416⟩
def centerBLog : DyadicInterval precision := ⟨744331050117229714654309368182727278395229349971, 744331050117229714654309368182727280594252605524⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨970601562396676875017945824263811609659843191751, scale precision, 970601562396676875017945824263811610759354819528, scale precision,
    0, 128, 0, 128, ⟨-598197966576386169008387386132094877901253712098, -598197966576386169008387386132094877901251614945⟩, ⟨-598197966576386169008387386132094876245643308698, -598197966576386169008387386132094876245641211545⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨144265163383122164482546534975845208150899296286, 152915178463027122650990311385075366485501069609⟩
def wholeCExp : DyadicInterval precision := ⟨1185550002510866574450539697030115399810086601719, 1199666936116860123325924274283438623773957684532⟩
def wholeCLog : DyadicInterval precision := ⟨868105674307971667134088694511406443302996060876, 875879266733045019226793172335071309313097160060⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1185550002510866574450539697030115400359842415607, scale precision, 1199666936116860123325924274283438623224201870644, scale precision,
    0, 128, 0, 128, ⟨-305830356926054245301980622770150733648721563594, -305830356926054245301980622770150733648719466441⟩, ⟨-288530326766244328965093069951690415632056233257, -288530326766244328965093069951690415632054136104⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨290483523917795193092868089669284608761847021738, 307736936149958299472359103669327302219619088327⟩
def wholeBExp : DyadicInterval precision := ⟨959195960437400828672252673820504664292369414060, 982112554815529200933538642394290481583857745665⟩
def wholeBLog : DyadicInterval precision := ⟨737461064174050379733680055126500323241883234118, 751231928150900893187639013654524028153976849067⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨959195960437400828672252673820504664842125227948, scale precision, 982112554815529200933538642394290481034101931777, scale precision,
    0, 128, 0, 128, ⟨-615473872299916598944718207338654605276887688390, -615473872299916598944718207338654605276885591237⟩, ⟨-580967047835590386185736179338569216705592301095, -580967047835590386185736179338569216705590203942⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0088LStableWitnesses

end


