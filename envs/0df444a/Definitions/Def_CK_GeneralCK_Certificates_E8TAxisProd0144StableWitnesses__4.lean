-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0144StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0144StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:27:33.175385+00:00
-- url     : https://prove2.me/theorems/45e1cdc0-bc91-4338-8487-b6516f2ebe53
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0144StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0145StableWitnesses, GeneralCK.Certificates.E8TAxisProd01…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0144StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0145StableWitnesses, GeneralCK.Certificates.E8TAxisProd0146StableWitnesses, GeneralCK.Certificates.E8TAxisProd0147StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0144StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0145StableWitnesses, GeneralCK.Certificates.E8TAxisProd0146StableWitnesses, GeneralCK.Certificates.E8TAxisProd0147StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0144StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0145StableWitnesses, GeneralCK.Certificates.E8TAxisProd0146StableWitnesses, GeneralCK.Certificates.E8TAxisProd0147StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0144StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0145StableWitnesses, GeneralCK/Certificates/E8TAxisProd0146StableWitnesses, GeneralCK/Certificates/E8TAxisProd0147StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0144StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0144StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨415811666137855580659299169097621045230774887708, 415811666137855580659299169097621045230774887709⟩
def centerDExp : DyadicInterval precision := ⟨827326924127804017482711149170086570224978765524, 827326924127804017482711149170086572424002021077⟩
def centerDLog : DyadicInterval precision := ⟨655594142802634878792195049006890681368280371847, 655594142802634878792195049006890683567303627400⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨827326924127804017482711149170086570774734579412, scale precision, 827326924127804017482711149170086571874246207189, scale precision,
    0, 128, 0, 128, ⟨-831623332275711161318598338195242091432713491011, -831623332275711161318598338195242091432711393858⟩, ⟨-831623332275711161318598338195242089490388156978, -831623332275711161318598338195242089490386059825⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨418231877830077131219916649534479056386433563940, 418231877830077131219916649534479056386433563941⟩
def centerCExp : DyadicInterval precision := ⟨824591389482770082850572206208146481784209898712, 824591389482770082850572206208146483983233154265⟩
def centerCLog : DyadicInterval precision := ⟨653846358163259505767576598675801807674516363366, 653846358163259505767576598675801809873539618919⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨824591389482770082850572206208146482333965712600, scale precision, 824591389482770082850572206208146483433477340377, scale precision,
    0, 128, 0, 128, ⟨-836463755660154262439833299068958113747252619926, -836463755660154262439833299068958113747250522773⟩, ⟨-836463755660154262439833299068958111798483732989, -836463755660154262439833299068958111798481635836⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨911787901901246971742203383304590422892845541796, 911787901901246971742203383304590422892845541797⟩
def centerBExp : DyadicInterval precision := ⟨419674120646618657723430229905257165961569742051, 419674120646618657723430229905257168160592997604⟩
def centerBLog : DyadicInterval precision := ⟨368930597799068007439522853462427022866738632711, 368930597799068007439522853462427025065761888264⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨419674120646618657723430229905257166511325555939, scale precision, 419674120646618657723430229905257167610837183716, scale precision,
    1, 128, 1, 128, ⟨-1823575803802493943484406766609180847700199085546, -1823575803802493943484406766609180847700196988393⟩, ⟨-1823575803802493943484406766609180843871185178793, -1823575803802493943484406766609180843871183081640⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨407186672849656374487538180028229486749868035095, 424465904280623337412236094991656409259795096050⟩
def wholeDExp : DyadicInterval precision := ⟨817586731060820878424464751762154416938532124195, 837149651842014699656242248506338776332018800396⟩
def wholeDLog : DyadicInterval precision := ⟨649361398245907818978439547465799272052779798379, 661852897083560210399534374966476335226142823792⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨817586731060820878424464751762154417488287938083, scale precision, 837149651842014699656242248506338775782262986508, scale precision,
    0, 128, 0, 128, ⟨-848931808561246674824472189983312819502323703918, -848931808561246674824472189983312819502321606765⟩, ⟨-814373345699312748975076360056458972539969626347, -814373345699312748975076360056458972539967529194⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨409254037795233993269467823541571913821038544816, 427241540043944272767980241125254450224304692814⟩
def wholeCExp : DyadicInterval precision := ⟨814487153830654407329274835310961497689453399530, 834784621304994955524714233082077749347093599244⟩
def wholeCLog : DyadicInterval precision := ⟨647372392247794569856006880382232489040091914188, 660348416871823013646048448585952558172428969355⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨814487153830654407329274835310961498239209213418, scale precision, 834784621304994955524714233082077748797337785356, scale precision,
    0, 128, 0, 128, ⟨-854483080087888545535960482250508901435082741779, -854483080087888545535960482250508901435080644626⟩, ⟨-818508075590467986538935647083143826679591525946, -818508075590467986538935647083143826679589428793⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨889514292724922434205498086129107937680265830373, 934314242149173526118848129028552386391200119661⟩
def wholeBExp : DyadicInterval precision := ⟨406934489068798146908583306206591912726540287711, 432662920644394876300664183322305670418752764415⟩
def wholeBLog : DyadicInterval precision := ⟨358999402449798587171162702996359667789562255684, 378987030212590169329660539401363294847113568205⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨406934489068798146908583306206591913276296101599, scale precision, 432662920644394876300664183322305669868996950527, scale precision,
    1, 128, 1, 128, ⟨-1868628484298347052237696258057104774756844456793, -1868628484298347052237696258057104774756842359640⟩, ⟨-1779028585449844868410996172258215873503500401278, -1779028585449844868410996172258215873503498304125⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0144StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0145StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0145StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨398590295572446657843406049747194007801292752073, 398590295572446657843406049747194007801292752074⟩
def centerDExp : DyadicInterval precision := ⟨847055832185589353041431034353733246155211165949, 847055832185589353041431034353733248354234421502⟩
def centerDLog : DyadicInterval precision := ⟨668137796188982437048462187236859676234037540057, 668137796188982437048462187236859678433060795610⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨847055832185589353041431034353733246704966979837, scale precision, 847055832185589353041431034353733247804478607614, scale precision,
    0, 128, 0, 128, ⟨-797180591144893315686812099494388016551129720247, -797180591144893315686812099494388016551127623094⟩, ⟨-797180591144893315686812099494388014654043385201, -797180591144893315686812099494388014654041288048⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨400994432959638811991118381986649252431169353853, 400994432959638811991118381986649252431169353854⟩
def centerCExp : DyadicInterval precision := ⟨844273635685581947195718871156655756351036570039, 844273635685581947195718871156655758550059825592⟩
def centerCLog : DyadicInterval precision := ⟨666375380923432359958421517843046859199547258758, 666375380923432359958421517843046861398570514311⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨844273635685581947195718871156655756900792383927, scale precision, 844273635685581947195718871156655758000304011704, scale precision,
    0, 128, 0, 128, ⟨-801988865919277623982236763973298505814008727301, -801988865919277623982236763973298505814006630148⟩, ⟨-801988865919277623982236763973298503910670785266, -801988865919277623982236763973298503910668688113⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨868348573514121057395905078727492006787562096446, 868348573514121057395905078727492006787562096447⟩
def centerBExp : DyadicInterval precision := ⟨445377971631770962514004515544251904512344278780, 445377971631770962514004515544251906711367534333⟩
def centerBLog : DyadicInterval precision := ⟨388764941931580507783179865381097852714456413268, 388764941931580507783179865381097854913479668821⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨445377971631770962514004515544251905062100092668, scale precision, 445377971631770962514004515544251906161611720445, scale precision,
    1, 128, 1, 128, ⟨-1736697147028242114791810157454984015379141320635, -1736697147028242114791810157454984015379139223482⟩, ⟨-1736697147028242114791810157454984011771109162302, -1736697147028242114791810157454984011771107065149⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨390021907983024779256146395473341757167804190697, 407186672849656374487538180028229486749868035096⟩
def wholeDExp : DyadicInterval precision := ⟨837149651842014699656242248506338774132995544843, 857046406820575460675375243512252172179026178685⟩
def wholeDLog : DyadicInterval precision := ⟨661852897083560210399534374966476333027119568239, 674448983099953378325059509857368476506693482805⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨837149651842014699656242248506338774682751358731, scale precision, 857046406820575460675375243512252171629270364797, scale precision,
    0, 128, 0, 128, ⟨-814373345699312748975076360056458974459504611190, -814373345699312748975076360056458974459502514037⟩, ⟨-780043815966049558512292790946683513398123413187, -780043815966049558512292790946683513398121316034⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨392075801761638546678368963705776883596264828182, 409943527226177432185621695170239210992121518614⟩
def wholeCExp : DyadicInterval precision := ⟨833997343745599858584413854167126992880701219141, 854640920881250307716842165284237165019896626171⟩
def wholeCLog : DyadicInterval precision := ⟨659847257783016669418359171739257332679080539892, 672931892853288014779347199596696748905057436768⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨833997343745599858584413854167126993430457033029, scale precision, 854640920881250307716842165284237164470140812283, scale precision,
    0, 128, 0, 128, ⟨-819887054452354864371243390340478422947639267042, -819887054452354864371243390340478422947637169889⟩, ⟨-784151603523277093356737927411553766252406025092, -784151603523277093356737927411553766252403927939⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨846558906105246096241254902365722108228378969843, 890383053906861011304981145854085152341339310931⟩
def wholeBExp : DyadicInterval precision := ⟨432148850192125891665144792388294670020712303467, 458858317987499830828034589092883412380008170114⟩
def wholeBLog : DyadicInterval precision := ⟨378590329316013759971508990892664985773832858684, 399060419605594343747619764800622440818815045061⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨432148850192125891665144792388294670570468117355, scale precision, 458858317987499830828034589092883411830252356226, scale precision,
    1, 128, 1, 128, ⟨-1780766107813722022609962291708170306541921044731, -1780766107813722022609962291708170306541918947578⟩, ⟨-1693117812210492192482509804731444214705741319772, -1693117812210492192482509804731444214705739222619⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0145StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0146StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0146StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨415811666137855580659299169097621045230774887708, 415811666137855580659299169097621045230774887709⟩
def centerDExp : DyadicInterval precision := ⟨827326924127804017482711149170086570224978765524, 827326924127804017482711149170086572424002021077⟩
def centerDLog : DyadicInterval precision := ⟨655594142802634878792195049006890681368280371847, 655594142802634878792195049006890683567303627400⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨827326924127804017482711149170086570774734579412, scale precision, 827326924127804017482711149170086571874246207189, scale precision,
    0, 128, 0, 128, ⟨-831623332275711161318598338195242091432713491011, -831623332275711161318598338195242091432711393858⟩, ⟨-831623332275711161318598338195242089490388156978, -831623332275711161318598338195242089490386059825⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨417540154011164069926533048218640986009396975088, 417540154011164069926533048218640986009396975089⟩
def centerCExp : DyadicInterval precision := ⟨825372311705557386170378711629150559991398260556, 825372311705557386170378711629150562190421516109⟩
def centerCLog : DyadicInterval precision := ⟨654345517297516753796471255400054889114963015769, 654345517297516753796471255400054891313986271322⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨825372311705557386170378711629150560541154074444, scale precision, 825372311705557386170378711629150561640665702221, scale precision,
    0, 128, 0, 128, ⟨-835080308022328139853066096437281972992257532854, -835080308022328139853066096437281972992255435701⟩, ⟨-835080308022328139853066096437281971045332464651, -835080308022328139853066096437281971045330367498⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨910909690633639506373210051495486856617602075581, 910909690633639506373210051495486856617602075582⟩
def centerBExp : DyadicInterval precision := ⟨420178785285720103157447913542504060412943377022, 420178785285720103157447913542504062611966632575⟩
def centerBLog : DyadicInterval precision := ⟨369322623518560504627556724126285206152053276892, 369322623518560504627556724126285208351076532445⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨420178785285720103157447913542504060962699190910, scale precision, 420178785285720103157447913542504062062210818687, scale precision,
    1, 128, 1, 128, ⟨-1821819381267279012746420102990973715147412693948, -1821819381267279012746420102990973715147410596795⟩, ⟨-1821819381267279012746420102990973711322997705534, -1821819381267279012746420102990973711322995608381⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨407186672849656374487538180028229486749868035095, 424465904280623337412236094991656409259795096050⟩
def wholeDExp : DyadicInterval precision := ⟨817586731060820878424464751762154416938532124195, 837149651842014699656242248506338776332018800396⟩
def wholeDLog : DyadicInterval precision := ⟨649361398245907818978439547465799272052779798379, 661852897083560210399534374966476335226142823792⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨817586731060820878424464751762154417488287938083, scale precision, 837149651842014699656242248506338775782262986508, scale precision,
    0, 128, 0, 128, ⟨-848931808561246674824472189983312819502323703918, -848931808561246674824472189983312819502321606765⟩, ⟨-814373345699312748975076360056458972539969626347, -814373345699312748975076360056458972539967529194⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨408564732469872611568202250363970390565957589811, 426547343159800146998773904909486888712338641588⟩
def wholeCExp : DyadicInterval precision := ⟨815261265991049296897286108825060930455543710462, 835572431524968186400871469418026145335339795274⟩
def wholeCLog : DyadicInterval precision := ⟨647869395500648726046723642993382016734807728860, 660849743071204938736063078205368169020150900695⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨815261265991049296897286108825060931005299524350, scale precision, 835572431524968186400871469418026144785583981386, scale precision,
    0, 128, 0, 128, ⟨-853094686319600293997547809818973778410213957750, -853094686319600293997547809818973778410211860597⟩, ⟨-817129464939745223136404500727940780170337085787, -817129464939745223136404500727940780170334988634⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨888645914209915849662997451096338762038134360287, 933426049150971184732480149862724658721618794397⟩
def wholeBExp : DyadicInterval precision := ⟨407429399369393723300082706529017944012542313744, 433177375779549308458726172553366256383373008197⟩
def wholeBLog : DyadicInterval precision := ⟨359386472912675088760426916075431092503026723390, 379383920193860483998336416513768196115966800576⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨407429399369393723300082706529017944562298127632, scale precision, 433177375779549308458726172553366255833617194309, scale precision,
    1, 128, 1, 128, ⟨-1866852098301942369464960299725449319415283421994, -1866852098301942369464960299725449319415281324841⟩, ⟨-1777291828419831699325994902192677522221442931338, -1777291828419831699325994902192677522221440834185⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0146StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0147StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0147StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨398590295572446657843406049747194007801292752073, 398590295572446657843406049747194007801292752074⟩
def centerDExp : DyadicInterval precision := ⟨847055832185589353041431034353733246155211165949, 847055832185589353041431034353733248354234421502⟩
def centerDLog : DyadicInterval precision := ⟨668137796188982437048462187236859676234037540057, 668137796188982437048462187236859678433060795610⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨847055832185589353041431034353733246704966979837, scale precision, 847055832185589353041431034353733247804478607614, scale precision,
    0, 128, 0, 128, ⟨-797180591144893315686812099494388016551129720247, -797180591144893315686812099494388016551127623094⟩, ⟨-797180591144893315686812099494388014654043385201, -797180591144893315686812099494388014654041288048⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨400307311847136633027189874469253106552374411081, 400307311847136633027189874469253106552374411082⟩
def centerCExp : DyadicInterval precision := ⟨845067875050819576653150357460419166795603314770, 845067875050819576653150357460419168994626570323⟩
def centerCLog : DyadicInterval precision := ⟨666878718032087192196946209047771812891741438849, 666878718032087192196946209047771815090764694402⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨845067875050819576653150357460419167345359128658, scale precision, 845067875050819576653150357460419168444870756435, scale precision,
    0, 128, 0, 128, ⟨-800614623694273266054379748938506214055524413058, -800614623694273266054379748938506214055522315905⟩, ⟨-800614623694273266054379748938506212153975328419, -800614623694273266054379748938506212153973231266⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨867489492618149463275986544875772565856137474502, 867489492618149463275986544875772565856137474503⟩
def centerBExp : DyadicInterval precision := ⟨445901872104391230194975258010082074992545101282, 445901872104391230194975258010082077191568356835⟩
def centerBLog : DyadicInterval precision := ⟨389166423090467094702464592642613974852400601647, 389166423090467094702464592642613977051423857200⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨445901872104391230194975258010082075542300915170, scale precision, 445901872104391230194975258010082076641812542947, scale precision,
    1, 128, 1, 128, ⟨-1734978985236298926551973089751545133514172496332, -1734978985236298926551973089751545133514170399179⟩, ⟨-1734978985236298926551973089751545129910379498835, -1734978985236298926551973089751545129910377401682⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨390021907983024779256146395473341757167804190697, 407186672849656374487538180028229486749868035096⟩
def wholeDExp : DyadicInterval precision := ⟨837149651842014699656242248506338774132995544843, 857046406820575460675375243512252172179026178685⟩
def wholeDLog : DyadicInterval precision := ⟨661852897083560210399534374966476333027119568239, 674448983099953378325059509857368476506693482805⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨837149651842014699656242248506338774682751358731, scale precision, 857046406820575460675375243512252171629270364797, scale precision,
    0, 128, 0, 128, ⟨-814373345699312748975076360056458974459504611190, -814373345699312748975076360056458974459502514037⟩, ⟨-780043815966049558512292790946683513398123413187, -780043815966049558512292790946683513398121316034⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨391390994830230264090034133324584929749196342428, 409254037795233993269467823541571913821038544817⟩
def wholeCExp : DyadicInterval precision := ⟨834784621304994955524714233082077747148070343691, 855442204069468392391412930235862396780536812154⟩
def wholeCLog : DyadicInterval precision := ⟨660348416871823013646048448585952555973405713802, 673437420530613622463329923875635179170588346809⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨834784621304994955524714233082077747697826157579, scale precision, 855442204069468392391412930235862396230780998266, scale precision,
    0, 128, 0, 128, ⟨-818508075590467986538935647083143828604564750474, -818508075590467986538935647083143828604562653321⟩, ⟨-782781989660460528180068266649169858559149657903, -782781989660460528180068266649169858559147560750⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨845709337934757964588152352207057543087871465214, 889514292724922434205498086129107937680265830374⟩
def wholeBExp : DyadicInterval precision := ⟨432662920644394876300664183322305668219729508862, 459392095176499336902797022465146371391039236540⟩
def wholeBLog : DyadicInterval precision := ⟨378987030212590169329660539401363292648090312652, 399466597538172117851805770482198021300803199721⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨432662920644394876300664183322305668769485322750, scale precision, 459392095176499336902797022465146370841283422652, scale precision,
    1, 128, 1, 128, ⟨-1779028585449844868410996172258215877217565017370, -1779028585449844868410996172258215877217562920217⟩, ⟨-1691418675869515929176304704414115084426760854207, -1691418675869515929176304704414115084426758757054⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0147StableWitnesses

end


