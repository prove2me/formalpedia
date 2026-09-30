-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0035StableWitnesses__2
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0035StableWitnesses__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:30:10.829806+00:00
-- url     : https://prove2.me/theorems/6d39fdc6-7470-4fc2-bbf1-e36550ac5dea
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0035StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisZero0036StableWitnesses)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0035StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisZero0036StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0035StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisZero0036StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0035StableWitnesses (+1 modules: GeneralCK.Certificates.E8TAxisZero0036StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0035StableWitnesses (+1 modules: GeneralCK/Certificates/E8TAxisZero0036StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0035StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0035StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨521774884976969249658675544420781985592392356176, 521774884976969249658675544420781985592392356177⟩
def centerDExp : DyadicInterval precision := ⟨715651972798857079113875938009045310901254744990, 715651972798857079113875938009045313100278000543⟩
def centerDLog : DyadicInterval precision := ⟨582487198387037182294075308140412786716139382242, 582487198387037182294075308140412788915162637795⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨715651972798857079113875938009045311451010558878, scale precision, 715651972798857079113875938009045312550522186655, scale precision,
    0, 256, 0, 256, ⟨-1043549769953938499317351088841563972307494916592, -1043549769953938499317351088841563972307492819439⟩, ⟨-1043549769953938499317351088841563970062076605264, -1043549769953938499317351088841563970062074508111⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨522136373312650513785350318939404398169807070206, 522136373312650513785350318939404398169807070207⟩
def centerCExp : DyadicInterval precision := ⟨715298041119813052229700366229514119390027757525, 715298041119813052229700366229514121589051013078⟩
def centerCLog : DyadicInterval precision := ⟨582249588245044065875431428742331392430316541517, 582249588245044065875431428742331394629339797070⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨715298041119813052229700366229514119939783571413, scale precision, 715298041119813052229700366229514121039295199190, scale precision,
    0, 256, 0, 256, ⟨-1044272746625301027570700637878808797462879864609, -1044272746625301027570700637878808797462877767456⟩, ⟨-1044272746625301027570700637878808795216350513368, -1044272746625301027570700637878808795216348416215⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1190576161588073355773995377789091840473814674949, 1190576161588073355773995377789091840473814674950⟩
def centerBExp : DyadicInterval precision := ⟨286566084441066036302501202683411324676512946283, 286566084441066036302501202683411326875536201836⟩
def centerBLog : DyadicInterval precision := ⟨261676888883987852531401652127215831040717905475, 261676888883987852531401652127215833239741161028⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨286566084441066036302501202683411325226268760171, scale precision, 286566084441066036302501202683411326325780387948, scale precision,
    0, 256, 0, 256, ⟨-2381152323176146711547990755578183683751413071144, -2381152323176146711547990755578183683751410973991⟩, ⟨-2381152323176146711547990755578183678143847725808, -2381152323176146711547990755578183678143845628655⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨512756788786713314020267203907621024217207656619, 530829944683894805437507571749273968698214433228⟩
def wholeDExp : DyadicInterval precision := ⟨706838726837510462039096914346652691200364343781, 724538456853667540563062557829026726602043072281⟩
def wholeDLog : DyadicInterval precision := ⟨576558946667156773600005109862481905428300877399, 588440465573623044036052405976243775513762722746⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨706838726837510462039096914346652691750120157669, scale precision, 724538456853667540563062557829026726052287258393, scale precision,
    0, 256, 0, 256, ⟨-1061659889367789610875015143498547938533137613158, -1061659889367789610875015143498547938533135516005⟩, ⟨-1025513577573426628040534407815242047325477264753, -1025513577573426628040534407815242047325475167600⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨512756788786713314020267203907621024217207656619, 531555965882942544279009677206999034689002146544⟩
def wholeCExp : DyadicInterval precision := ⟨706136811708486537592693838597541052530539713549, 724538456853667540563062557829026726602043072281⟩
def wholeCLog : DyadicInterval precision := ⟨576085766255771006117633656584879293563876384760, 588440465573623044036052405976243775513762722746⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨706136811708486537592693838597541053080295527437, scale precision, 724538456853667540563062557829026726052287258393, scale precision,
    0, 256, 0, 256, ⟨-1063111931765885088558019354413998070515842951610, -1063111931765885088558019354413998070515840854457⟩, ⟨-1025513577573426628040534407815242047325477264753, -1025513577573426628040534407815242047325475167600⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1165198338510721332197179831323682353412471968230, 1216227503301754778736371332938162533197661849347⟩
def wholeBExp : DyadicInterval precision := ⟨276681340957591818975210961557401193958326086638, 296692898824012362113584347097260388991660251293⟩
def wholeBLog : DyadicInterval precision := ⟨253389127192811686250354731355988593745390099273, 270119153533168252924663037126585932258512134314⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨276681340957591818975210961557401194508081900526, scale precision, 296692898824012362113584347097260388441904437405, scale precision,
    0, 256, 0, 256, ⟨-2432455006603509557472742665876325069299275622123, -2432455006603509557472742665876325069299273524970⟩, ⟨-2330396677021442664394359662647364704116861895370, -2330396677021442664394359662647364704116859798217⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0035StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0036StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0036StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨503775002792062322984841617274484055444075625516, 503775002792062322984841617274484055444075625517⟩
def centerDExp : DyadicInterval precision := ⟨733498839633313504812043629918338881519303578660, 733498839633313504812043629918338883718326834213⟩
def centerDLog : DyadicInterval precision := ⟨594418786089508030264928688350882176985232861495, 594418786089508030264928688350882179184256117048⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨733498839633313504812043629918338882069059392548, scale precision, 733498839633313504812043629918338883168571020325, scale precision,
    0, 256, 0, 256, ⟨-1007550005584124645969683234548968111983544655694, -1007550005584124645969683234548968111983542558541⟩, ⟨-1007550005584124645969683234548968109792759943527, -1007550005584124645969683234548968109792757846374⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨504133585258291579730042822748650359631181373610, 504133585258291579730042822748650359631181373611⟩
def centerCExp : DyadicInterval precision := ⟨733138996997124824424036976485131670896332717878, 733138996997124824424036976485131673095355973431⟩
def centerCLog : DyadicInterval precision := ⟨594179171692879400727128305875189305571109817440, 594179171692879400727128305875189307770133072993⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨733138996997124824424036976485131671446088531766, scale precision, 733138996997124824424036976485131672545600159543, scale precision,
    0, 256, 0, 256, ⟨-1008267170516583159460085645497300720358293797369, -1008267170516583159460085645497300720358291700216⟩, ⟨-1008267170516583159460085645497300718166433794228, -1008267170516583159460085645497300718166431697075⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1141073731955818375584170648779984782482675327698, 1141073731955818375584170648779984782482675327699⟩
def centerBExp : DyadicInterval precision := ⟨306651230394572244390251199040883631471083388948, 306651230394572244390251199040883633670106644501⟩
def centerBLog : DyadicInterval precision := ⟨278373675800960836861233090082668958948070423721, 278373675800960836861233090082668961147093679274⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨306651230394572244390251199040883632020839202836, scale precision, 306651230394572244390251199040883633120350830613, scale precision,
    0, 256, 0, 256, ⟨-2282147463911636751168341297559969567585491271312, -2282147463911636751168341297559969567585489174159⟩, ⟨-2282147463911636751168341297559969562345212136632, -2282147463911636751168341297559969562345210039479⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨494828875109284674194281948410566590218630888609, 512756788786713314020267203907621024217207656620⟩
def wholeDExp : DyadicInterval precision := ⟨724538456853667540563062557829026724403019816728, 742533801492811413004049823802046285637355489138⟩
def wholeDLog : DyadicInterval precision := ⟨588440465573623044036052405976243773314739467193, 600422206098217740957049834384989022236361477122⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨724538456853667540563062557829026724952775630616, scale precision, 742533801492811413004049823802046285087599675250, scale precision,
    0, 256, 0, 256, ⟨-1025513577573426628040534407815242049543355458877, -1025513577573426628040534407815242049543353361724⟩, ⟨-989657750218569348388563896821133179355198924442, -989657750218569348388563896821133179355196827289⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨494828875109284674194281948410566590218630888609, 513476891620287433729744816122965384439477635575⟩
def wholeCExp : DyadicInterval precision := ⟨723824827532911875227338360353220504128867257720, 742533801492811413004049823802046285637355489138⟩
def wholeCLog : DyadicInterval precision := ⟨587963282790660940513969362008894092405499604698, 600422206098217740957049834384989022236361477122⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨723824827532911875227338360353220504678623071608, scale precision, 742533801492811413004049823802046285087599675250, scale precision,
    0, 256, 0, 256, ⟨-1026953783240574867459489632245930769988988735813, -1026953783240574867459489632245930769988986638660⟩, ⟨-989657750218569348388563896821133179355198924442, -989657750218569348388563896821133179355196827289⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1116232934363142447689933532280253085435679534202, 1166188388182342115326847483651789008827456546754⟩
def wholeBExp : DyadicInterval precision := ⟨296291199908713716536122412645638002165892704158, 317254588964962553244948722126718136224963287175⟩
def wholeBLog : DyadicInterval precision := ⟨269785202604095038338480629940283764585141042721, 287111916148150123139703066395969034959392352836⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨296291199908713716536122412645638002715648518046, scale precision, 317254588964962553244948722126718135675207473287, scale precision,
    0, 256, 0, 256, ⟨-2332376776364684230653694967303578020366668734789, -2332376776364684230653694967303578020366666637636⟩, ⟨-2232465868726284895379867064560506168338791479437, -2232465868726284895379867064560506168338789382284⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 256, 0, 256⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0036StableWitnesses

end


