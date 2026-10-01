-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0344CertifiedArithmetic__7
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0344CertifiedArithmetic__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T20:32:16.035054+00:00
-- url     : https://prove2.me/theorems/c2ae7769-cabe-44b5-ab31-f19c2fe5e410
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0344CertifiedArithmetic (+6 modules: GeneralCK.Certificates.E8TAxisProd0345CertifiedArithmetic, GeneralCK.Certificates.E8TAx…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0344CertifiedArithmetic (+6 modules: GeneralCK.Certificates.E8TAxisProd0345CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0346CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0347CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0348CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0349CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0350CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0344CertifiedArithmetic (+6 modules: GeneralCK.Certificates.E8TAxisProd0345CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0346CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0347CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0348CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0349CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0350CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0344CertifiedArithmetic (+6 modules: GeneralCK.Certificates.E8TAxisProd0345CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0346CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0347CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0348CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0349CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0350CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0344CertifiedArithmetic (+6 modules: GeneralCK/Certificates/E8TAxisProd0345CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0346CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0347CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0348CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0349CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0350CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0342GraphCenterA__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0344GraphCenterB__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0336GraphCenterC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0337GraphCenterD__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0344GraphWholeA__6
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0342GraphWholeB__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0340GraphWholeC__6
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0338GraphWholeD__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0321Geometry__24
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0345Geometry__24
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0346GraphWholeC__6
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0346GraphWholeD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0347GraphCenterC__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0347GraphCenterD__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0350GraphWholeA__7

-- ===== source module GeneralCK.Certificates.E8TAxisProd0344CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0344CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0344GraphCenterA.qJetBox,
   E8TAxisProd0344GraphCenterB.qJetBox,
   E8TAxisProd0344GraphCenterC.qJetBox,
   E8TAxisProd0344GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0344GraphWholeA.qJetBox,
   E8TAxisProd0344GraphWholeB.qJetBox,
   E8TAxisProd0344GraphWholeC.qJetBox,
   E8TAxisProd0344GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨93739503467894002778304055272495727815943647433, 93739503467894002778304055272496215612769339718⟩
  | 0, 2 => ⟨255311145377983732659716944082844262722070057442, 255311145377983732659716944082846318256960878334⟩
  | 1, 1 => ⟨256400647201049591103209571472570474756120030159, 256400647201049591103209571472574291664856862488⟩
  | 0, 3 => ⟨481483778536246108292987068878627995459417626563, 481483778536246108292987068878635009795650046621⟩
  | 1, 2 => ⟨641173782841639890186590805618691969691062144317, 641173782841639890186590805618704860115848509707⟩
  | 2, 1 => ⟨643607105332744780654789105637985753630551411884, 643607105332744780654789105638009678254105209080⟩
  | 0, 4 => ⟨762345123450259515694254962254538959676845804087, 762345123450259515694254962254564321666317791173⟩
  | 1, 3 => ⟨1117697326737381350203601008717032888508765376295, 1117697326737381350203601008717079913604442527856⟩
  | 2, 2 => ⟨1474157150315255184040570051413816028774258218255, 1474157150315255184040570051413904065949876807719⟩
  | 3, 1 => ⟨1479199612093234430572864106540056264645310303629, 1479199612093234430572864106540222204525856487572⟩
  | 0, 5 => ⟨-4679528682308053667220139077530049038020565420795248, 4700539585419999992883580596442828191858039043526584⟩
  | 1, 4 => ⟨-9208313188920486886775516709649630326531627806659165, 9239903107101591700456573116073588329302777094249579⟩
  | 2, 3 => ⟨-18136283606973988171531102690148472404054940975434245, 18181703050698300108226909786610361350256911292368156⟩
  | 3, 2 => ⟨-35743495546556384460513025730795251883305087771897468, 35802974037665453934243773333575216849562505928445363⟩
  | 4, 1 => ⟨-70481953122812008883998016317453906849048275175930313, 70542497002273157111256113870314528676533704918194298⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0344Geometry.ds, E8TAxisProd0344Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 88531321495735088594931828688399011031969865742 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0344CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0345CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0345CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0345GraphCenterA.qJetBox,
   E8TAxisProd0345GraphCenterB.qJetBox,
   E8TAxisProd0345GraphCenterC.qJetBox,
   E8TAxisProd0345GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0345GraphWholeA.qJetBox,
   E8TAxisProd0345GraphWholeB.qJetBox,
   E8TAxisProd0345GraphWholeC.qJetBox,
   E8TAxisProd0345GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨84929488665036973744050922289560589013421083957, 84929488665036973744050922289561029323713243979⟩
  | 0, 2 => ⟨233197093904381838914048651990775443919146146095, 233197093904381838914048651990777288801147854168⟩
  | 1, 1 => ⟨234202328247959000769752818933638062786149272313, 234202328247959000769752818933641482278527419960⟩
  | 0, 3 => ⟨442826410131913949070808017930614986450634539633, 442826410131913949070808017930621261161376026255⟩
  | 1, 2 => ⟨590171851978994936280157662977510073176181365408, 590171851978994936280157662977521584250786733209⟩
  | 2, 1 => ⟨592430279329982147334195383715894186824477948240, 592430279329982147334195383715915520010662920250⟩
  | 0, 4 => ⟨704865603952780735895284094921752926765724359017, 704865603952780735895284094921775507025258652202⟩
  | 1, 3 => ⟨1034679814400465856182338770097855728590867800768, 1034679814400465856182338770097897536167257565451⟩
  | 2, 2 => ⟨1365526527002909650813241268317110202981466394113, 1365526527002909650813241268317188379019948913843⟩
  | 3, 1 => ⟨1370221454184737160644267700336488301205790956531, 1370221454184737160644267700336635488936554054621⟩
  | 0, 5 => ⟨-4262044931606502719931056540674490878785692402192873, 4281507913775692369886607074063681285553075546823208⟩
  | 1, 4 => ⟨-8383931347776303309243038692915391281081533937524243, 8413217250369012231437259163471159340350764816472650⟩
  | 2, 3 => ⟨-16506967192236482030883312107114706500070600110477991, 16549101255298431575988491816407560189514743363290873⟩
  | 3, 2 => ⟨-32521152023025659388299611117176070530162573639106872, 32576354080577021273373540608400861272496970962231606⟩
  | 4, 1 => ⟨-64105422302948438610779783385502333899791083361463928, 64161638171533322443153472562538165812564593825711415⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0345Geometry.ds, E8TAxisProd0345Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 80172681485471749282736728662430423938945069813 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0345CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0346CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0346CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0346GraphCenterA.qJetBox,
   E8TAxisProd0346GraphCenterB.qJetBox,
   E8TAxisProd0346GraphCenterC.qJetBox,
   E8TAxisProd0346GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0346GraphWholeA.qJetBox,
   E8TAxisProd0346GraphWholeB.qJetBox,
   E8TAxisProd0346GraphWholeC.qJetBox,
   E8TAxisProd0346GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨93420740447324622580604598638401772995133016348, 93420740447324622580604598638402259769701220581⟩
  | 0, 2 => ⟨254709885883888858067876859751095416547878005477, 254709885883888858067876859751097467601089223468⟩
  | 1, 1 => ⟨255600052633684108697633828713680506985015616058, 255600052633684108697633828713684315525063557857⟩
  | 0, 3 => ⟨480531694341317842496922250281056491286172852932, 480531694341317842496922250281063490036934067666⟩
  | 1, 2 => ⟨639777956639615627912234448609192316433471842467, 639777956639615627912234448609205178078522433033⟩
  | 2, 1 => ⟨641766279207513257894227584923084573349522651499, 641766279207513257894227584923108444318355783772⟩
  | 0, 4 => ⟨760989959723812732695271905246943291277655443176, 760989959723812732695271905246968594621453605473⟩
  | 1, 3 => ⟨1115625183522754486164518854626474275426337063431, 1115625183522754486164518854626521191612571908262⟩
  | 2, 2 => ⟨1471165535077327118785204500540592877675015124622, 1471165535077327118785204500540680710559529381046⟩
  | 3, 1 => ⟨1475286065470935936296905734861665148591122928444, 1475286065470935936296905734861830702528989789990⟩
  | 0, 5 => ⟨-4670699698415352017369137399533947811920391202245717, 4691670074930550495789046370016145940968663483094524⟩
  | 1, 4 => ⟨-9190909895524565917317459974822494384308357713909817, 9222437166634059216552158999925335859980549900786078⟩
  | 2, 3 => ⟨-18101941447333817553875595592460872297264741610120683, 18147265583095944674830772440584930980250489748694909⟩
  | 3, 2 => ⟨-35675675608741473839254311081118975097495221753888571, 35735012938987927327942887313755160541759804510529742⟩
  | 4, 1 => ⟨-70347939733965391363706608407108576203532602234266905, 70408285348754102596720386942422421193606447472754604⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0346Geometry.ds, E8TAxisProd0346Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 88228262226426200607280497723009902805361060604 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0346CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0347CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0347CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0347GraphCenterA.qJetBox,
   E8TAxisProd0347GraphCenterB.qJetBox,
   E8TAxisProd0347GraphCenterC.qJetBox,
   E8TAxisProd0347GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0347GraphWholeA.qJetBox,
   E8TAxisProd0347GraphWholeB.qJetBox,
   E8TAxisProd0347GraphWholeC.qJetBox,
   E8TAxisProd0347GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨84638338026443354094780668527331648159917189301, 84638338026443354094780668527332087548145774205⟩
  | 0, 2 => ⟨232644111240378218668835182493408545780707065832, 232644111240378218668835182493410386635538321588⟩
  | 1, 1 => ⟨233465421275132154009960517753788073190867854488, 233465421275132154009960517753791485173264950600⟩
  | 0, 3 => ⟨441946114239363410189822038267654386229055279405, 441946114239363410189822038267660646976655202772⟩
  | 1, 2 => ⟨588879705539623667362107711356806852249726805758, 588879705539623667362107711356818337573835750635⟩
  | 2, 1 => ⟨590725109738114209157889816727666939383430091839, 590725109738114209157889816727688224613223638160⟩
  | 0, 4 => ⟨703608169572379370424823444692309638629629035712, 703608169572379370424823444692332166560540757092⟩
  | 1, 3 => ⟨1032755035127440754036973363803567985084877397546, 1032755035127440754036973363803609695593252281252⟩
  | 2, 2 => ⟨1362745644224253809627810335388205579558611374995, 1362745644224253809627810335388283573681316046499⟩
  | 3, 1 => ⟨1366582177570005583911682575085501392023867029427, 1366582177570005583911682575085648236362343436999⟩
  | 0, 5 => ⟨-4253772386560297577382329535829488294176968308186653, 4273197367390037805420608508748499124627331218848732⟩
  | 1, 4 => ⟨-8367626895300945078180756794844208355547508238848888, 8396853872125064954057155335517288234317061238463376⟩
  | 2, 3 => ⟨-16474798026374681206749360955070288462231946277003592, 16516842230185536328686283987885044394695362273667040⟩
  | 3, 2 => ⟨-32457633412205209270788240088551649442115350285072646, 32512702202264421111751412772571624297379141337434003⟩
  | 4, 1 => ⟨-63979929522771309521683867763391509323270579541575807, 64035958278542281500549949936138672387871702634136751⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0347Geometry.ds, E8TAxisProd0347Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 79895996939975303327296381023976393532738746321 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0347CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0348CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0348CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0348GraphCenterA.qJetBox,
   E8TAxisProd0348GraphCenterB.qJetBox,
   E8TAxisProd0348GraphCenterC.qJetBox,
   E8TAxisProd0348GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0348GraphWholeA.qJetBox,
   E8TAxisProd0348GraphWholeB.qJetBox,
   E8TAxisProd0348GraphWholeC.qJetBox,
   E8TAxisProd0348GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨76885006325903377816750096087870244063450294986, 76885006325903377816750096087870641658294471696⟩
  | 0, 2 => ⟨212847445085387457935383490223348537921221683195, 212847445085387457935383490223350193891597502348⟩
  | 1, 1 => ⟨213774478020559406124483497877965990613929888624, 213774478020559406124483497877969054136496524213⟩
  | 0, 3 => ⟨407046059974358178394238674722768109592825911251, 407046059974358178394238674722773722564016361159⟩
  | 1, 2 => ⟨542935307771389376349772914233669606693189406749, 542935307771389376349772914233679885225381778412⟩
  | 2, 1 => ⟨545030898046367750879992636378566182177123231841, 545030898046367750879992636378585202438115165889⟩
  | 0, 4 => ⟨651478831460457012556424379147412498926342532416, 651478831460457012556424379147432600143565170513⟩
  | 1, 3 => ⟨957515656648487763425815174961727225248783914077, 957515656648487763425815174961764387930305119316⟩
  | 2, 2 => ⟨1264515030716346776080658359681240665601486572510, 1264515030716346776080658359681310071154704638703⟩
  | 3, 1 => ⟨1268886161843796696455052051045158452292005641759, 1268886161843796696455052051045288977399352657589⟩
  | 0, 5 => ⟨-3870300043101906341464036264398354677615945403470972, 3888300795689583235263522318079114816559026071305030⟩
  | 1, 4 => ⟨-7610552862400224730018710871169572839393884210827067, 7637656396852799970693997265030120291445818903760418⟩
  | 2, 3 => ⟨-14978838988144912828287434252049760565991192485162286, 15017854607053741625285378823874130689772034537270517⟩
  | 3, 2 => ⟨-29499739810027754310737000503658171513898676670067273, 29550877097454907254010576981956490717703914933243028⟩
  | 4, 1 => ⟨-58128184368167033318749457461604579658313914220565254, 58180283030186078546825890639977485656952672051815541⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0348Geometry.ds, E8TAxisProd0348Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 72544137107428488848413162827539716951642269662 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0348CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0349CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0349CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0349GraphCenterA.qJetBox,
   E8TAxisProd0349GraphCenterB.qJetBox,
   E8TAxisProd0349GraphCenterC.qJetBox,
   E8TAxisProd0349GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0349GraphWholeA.qJetBox,
   E8TAxisProd0349GraphWholeB.qJetBox,
   E8TAxisProd0349GraphWholeC.qJetBox,
   E8TAxisProd0349GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨69544811436257934093035077958790276655437429308, 69544811436257934093035077958790635817511167787⟩
  | 0, 2 => ⟨194131685920474325113860333434754665425825677213, 194131685920474325113860333434756151967840639471⟩
  | 1, 1 => ⟨194986165163746993383927733402623703546490277888, 194986165163746993383927733402626448207982363968⟩
  | 0, 3 => ⟨373939682157010517863743686400456965417338560359, 373939682157010517863743686400461986356542267806⟩
  | 1, 2 => ⟨499199840492468101751411639821270073510770669050, 499199840492468101751411639821279250767252729310⟩
  | 2, 1 => ⟨501143827470780466599115212677771234429908983670, 501143827470780466599115212677788190566464230107⟩
  | 0, 4 => ⟨601902988950794071251491364984427161233603908820, 601902988950794071251491364984445053592250563806⟩
  | 1, 3 => ⟨885802698979880649949851440307293910519093560165, 885802698979880649949851440307326939026678843469⟩
  | 2, 2 => ⟨1170599817572068196124606831371886136083798974536, 1170599817572068196124606831371947743156141774553⟩
  | 3, 1 => ⟨1174669304687979902057345830321353255649939271327, 1174669304687979902057345830321468978934382465237⟩
  | 0, 5 => ⟨-3504190553976897916508859401097138521633233629269135, 3520801874709048069865476218645711643143533116875579⟩
  | 1, 4 => ⟨-6887971525265207121039534292351167340628287816022905, 6912996603016795250394907981869473949498969421322717⟩
  | 2, 3 => ⟨-13551477244168541570854507140136248375891064323407115, 13587517383734431204448215696511392896368849563401044⟩
  | 3, 2 => ⟨-26678382016841358040247407516308573868463240111573532, 26725635583647785638805534195242157427797843539086388⟩
  | 4, 1 => ⟨-52548395551758016155729991306405617701081445412844794, 52596555054166822186533558088534154838244177283918496⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0349Geometry.ds, E8TAxisProd0349Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 65586932676462660946923990926983100163785903780 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0349CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0350CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0350CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0350GraphCenterA.qJetBox,
   E8TAxisProd0350GraphCenterB.qJetBox,
   E8TAxisProd0350GraphCenterC.qJetBox,
   E8TAxisProd0350GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0350GraphWholeA.qJetBox,
   E8TAxisProd0350GraphWholeB.qJetBox,
   E8TAxisProd0350GraphWholeC.qJetBox,
   E8TAxisProd0350GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨76619264812306039813222757437869775248531960263, 76619264812306039813222757437870172011442270332⟩
  | 0, 2 => ⟨212339146174366601551644465292075499026047534576, 212339146174366601551644465292077151377246173254⟩
  | 1, 1 => ⟨213096556479245505220401713648754374594856174881, 213096556479245505220401713648757431377589648272⟩
  | 0, 3 => ⟨406232440670575265704584072746183172293972305818, 406232440670575265704584072746188772755151275076⟩
  | 1, 2 => ⟨541739530736986897538808549590042449616718670387, 541739530736986897538808549590052705109214506554⟩
  | 2, 1 => ⟨543451870120418612161668454878214082797285784282, 543451870120418612161668454878233060197048208594⟩
  | 0, 4 => ⟨650312375907927454231059189292553518883226520023, 650312375907927454231059189292573573411325500474⟩
  | 1, 3 => ⟨955728107120243813344026484039241383921995017089, 955728107120243813344026484039278460098030916053⟩
  | 2, 2 => ⟨1261930418282120154274802540446447317037190695451, 1261930418282120154274802540446516560619218894911⟩
  | 3, 1 => ⟨1265502353708397070775212191363724653464650413023, 1265502353708397070775212191363854873082623166658⟩
  | 0, 5 => ⟨-3862567842694222500711859655360117195910153112468180, 3880532867428029960108410718128839195857804690533687⟩
  | 1, 4 => ⟨-7595315712237330457536424028768975660218139180370948, 7622363767324399095633528698916351244875984181139138⟩
  | 2, 3 => ⟨-14948780721237111284675924999523675315093666666664258, 14987711673533363189440716827945903537093437916001328⟩
  | 3, 2 => ⟨-29440399897291210759439132655253670395418492510915381, 29491411675191942369681848890547993109115870018980786⟩
  | 4, 1 => ⟨-58010969494883673491409598709427642948891060040822659, 58062892408121553037854795367427676388256835747405459⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0350Geometry.ds, E8TAxisProd0350Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 72291713534747326326265313491743643034813735041 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0350CertifiedArithmetic

end


