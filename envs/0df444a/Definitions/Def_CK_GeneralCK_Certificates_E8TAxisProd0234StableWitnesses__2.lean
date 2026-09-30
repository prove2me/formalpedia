-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0234StableWitnesses__2
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0234StableWitnesses__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:26:40.132526+00:00
-- url     : https://prove2.me/theorems/4623d5d2-c27f-4e84-9b52-1ecb806b68b9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0234StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisProd0235StableWitnesses)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0234StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisProd0235StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0234StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisProd0235StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0234StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisProd0235StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0234StableWitnesses (+1 modules: GeneralCK/Certificates/E8TAxisProd0235StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0234StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0234StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3957182113162240766624229437560720104187299711, 3957182113162240766624229437560720104187299712⟩
def centerAExp : DyadicInterval precision := ⟨1453608663518239684990297266292415545523124059933, 1453608663518239684990297266292415547722147315486⟩
def centerALog : DyadicInterval precision := ⟨1009083914440550911538268226967653949061006604559, 1009083914440550911538268226967653951260029860112⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453608663518239684990297266292415546072879873821, scale precision, 1453608663518239684990297266292415547172391501598, scale precision,
    0, 128, 0, 128, ⟨-7914364226324481533248458875121440761116590109, -7914364226324481533248458875121440761114492956⟩, ⟨-7914364226324481533248458875121439655634705892, -7914364226324481533248458875121439655632608739⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨845337768071990511126652069424194906034451240659, 845337768071990511126652069424194906034451240660⟩
def centerCExp : DyadicInterval precision := ⟨459625744812329855016542331079191836525372691830, 459625744812329855016542331079191838724395947383⟩
def centerCLog : DyadicInterval precision := ⟨399644357792766708063610199213932442659168580954, 399644357792766708063610199213932444858191836507⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨459625744812329855016542331079191837075128505718, scale precision, 459625744812329855016542331079191838174640133495, scale precision,
    1, 128, 1, 128, ⟨-1690675536143981022253304138848389813816997563353, -1690675536143981022253304138848389813816995466200⟩, ⟨-1690675536143981022253304138848389810320809496436, -1690675536143981022253304138848389810320807399283⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2133233816301691795002150216594788118513446431652, 2133233816301691795002150216594788118513446431653⟩
def centerBExp : DyadicInterval precision := ⟨78884447263064588288070771164605986383210980500, 78884447263064588288070771164605988582234236053⟩
def centerBLog : DyadicInterval precision := ⟨76829187644859338743654201602323576482193177682, 76829187644859338743654201602323578681216433235⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨78884447263064588288070771164605986932966794388, scale precision, 78884447263064588288070771164605988032478422165, scale precision,
    4, 128, 4, 128, ⟨-4266467632603383590004300433189576247212285963260, -4266467632603383590004300433189576247212283866107⟩, ⟨-4266467632603383590004300433189576226841501860513, -4266467632603383590004300433189576226841499763360⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4115470352964345628383522602588716836376905847⟩
def wholeAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨839031879741317077683899283136953497091606880567, 851664090100827451657094731038580694740573064192⟩
def wholeCExp : DyadicInterval precision := ⟨455663805848908084790072734139341494563462778276, 463609168429867024452507024245611694204639985659⟩
def wholeCLog : DyadicInterval precision := ⟨396627192296518628644841411177030445902474954982, 402671618163181342715035916931189810993995206343⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨455663805848908084790072734139341495113218592164, scale precision, 463609168429867024452507024245611693654884171771, scale precision,
    1, 128, 1, 128, ⟨-1703328180201654903314189462077161391244440666187, -1703328180201654903314189462077161391244438569034⟩, ⟨-1678063759482634155367798566273906992450140753279, -1678063759482634155367798566273906992450138656126⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2114892083877939738005514401558662499887125439346, 2151608766465811431903588757123928429060846369021⟩
def wholeBExp : DyadicInterval precision := ⟨76925605049232944729522543746026316614493602460, 80889492576912682327274374943340514552466307084⟩
def wholeBLog : DyadicInterval precision := ⟨74969476655568390889592156616281053501641005397, 78730315892812265623677575389133253017201906914⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨76925605049232944729522543746026317164249416348, scale precision, 80889492576912682327274374943340514002710493196, scale precision,
    4, 128, 4, 128, ⟨-4303217532931622863807177514247856868566447800787, -4303217532931622863807177514247856868566445703634⟩, ⟨-4229784167755879476011028803117324989841329905702, -4229784167755879476011028803117324989841327808549⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0234StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0235StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0235StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3957182113162240766624229437560720104187299711, 3957182113162240766624229437560720104187299712⟩
def centerAExp : DyadicInterval precision := ⟨1453608663518239684990297266292415545523124059933, 1453608663518239684990297266292415547722147315486⟩
def centerALog : DyadicInterval precision := ⟨1009083914440550911538268226967653949061006604559, 1009083914440550911538268226967653951260029860112⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453608663518239684990297266292415546072879873821, scale precision, 1453608663518239684990297266292415547172391501598, scale precision,
    0, 128, 0, 128, ⟨-7914364226324481533248458875121440761116590109, -7914364226324481533248458875121440761114492956⟩, ⟨-7914364226324481533248458875121439655634705892, -7914364226324481533248458875121439655632608739⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨833168237212828995740815911336441386620862089164, 833168237212828995740815911336441386620862089165⟩
def centerCExp : DyadicInterval precision := ⟨467344195684860112735578888446237005916299986340, 467344195684860112735578888446237008115323241893⟩
def centerCLog : DyadicInterval precision := ⟨405504421263631511846772706554827522792912468315, 405504421263631511846772706554827524991935723868⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨467344195684860112735578888446237006466055800228, scale precision, 467344195684860112735578888446237007565567428005, scale precision,
    1, 128, 1, 128, ⟨-1666336474425657991481631822672882774960948509337, -1666336474425657991481631822672882774960946412184⟩, ⟨-1666336474425657991481631822672882771522501944476, -1666336474425657991481631822672882771522499847323⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2097209997257589686738467018321597507387706627070, 2097209997257589686738467018321597507387706627071⟩
def centerBExp : DyadicInterval precision := ⟨82870660343363229596010430572427971019104695551, 82870660343363229596010430572427973218127951104⟩
def centerBLog : DyadicInterval precision := ⟨80606378247453132175934360240293645866174770844, 80606378247453132175934360240293648065198026397⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨82870660343363229596010430572427971568860509439, scale precision, 82870660343363229596010430572427972668372137216, scale precision,
    4, 128, 4, 128, ⟨-4194419994515179373476934036643195024470872487820, -4194419994515179373476934036643195024470870390667⟩, ⟨-4194419994515179373476934036643195005079956117631, -4194419994515179373476934036643195005079954020478⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4115470352964345628383522602588716836376905847⟩
def wholeAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨826901523548668615692832474483103847793618386642, 839455166592395805407217682950670359384428464510⟩
def wholeCExp : DyadicInterval precision := ⟨463340700937036937766412117641448263562136643151, 471369242339977559507271857985971581600991523236⟩
def wholeCLog : DyadicInterval precision := ⟨402467789354726448713087751549657183500373884886, 408551053031161301480232418544383882594984098917⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨463340700937036937766412117641448264111892457039, scale precision, 471369242339977559507271857985971581051235709348, scale precision,
    1, 128, 1, 128, ⟨-1678910333184791610814435365901340720502936206649, -1678910333184791610814435365901340720502934109496⟩, ⟨-1653803047097337231385664948966207693882695077108, -1653803047097337231385664948966207693882692979955⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2078936827575299711790878182428483697450362567558, 2115518591256460508615860472941704621906352270019⟩
def wholeBExp : DyadicInterval precision := ⟨80820171893873056249601671183920388190024308277, 84969052621182127677560925844093412127682541445⟩
def wholeBLog : DyadicInterval precision := ⟨78664629202491672562325196314298821044720614936, 82590823418721628194469291135799962641965736052⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨80820171893873056249601671183920388739780122165, scale precision, 84969052621182127677560925844093411577926727557, scale precision,
    4, 128, 4, 128, ⟨-4231037182512921017231720945883409253754147227524, -4231037182512921017231720945883409253754145130371⟩, ⟨-4157873655150599423581756364856967385444706640757, -4157873655150599423581756364856967385444704543604⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0235StableWitnesses

end


