-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0506CertifiedArithmetic__10
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0506CertifiedArithmetic__10
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T16:18:47.531189+00:00
-- url     : https://prove2.me/theorems/eda69724-da3a-4965-95e0-20ff12ea6c5f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0506CertifiedArithmetic (+9 modules: GeneralCK.Certificates.E8TAxisProd0507CertifiedArithmetic, GeneralCK.Certificates.E8TAx…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0506CertifiedArithmetic (+9 modules: GeneralCK.Certificates.E8TAxisProd0507CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0508CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0509CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0510CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0511CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0512CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0513CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0514CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0515CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0506CertifiedArithmetic (+9 modules: GeneralCK.Certificates.E8TAxisProd0507CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0508CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0509CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0510CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0511CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0512CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0513CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0514CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0515CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0506CertifiedArithmetic (+9 modules: GeneralCK.Certificates.E8TAxisProd0507CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0508CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0509CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0510CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0511CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0512CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0513CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0514CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0515CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0506CertifiedArithmetic (+9 modules: GeneralCK/Certificates/E8TAxisProd0507CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0508CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0509CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0510CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0511CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0512CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0513CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0514CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0515CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0504GraphCenterA__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0506GraphCenterB__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0502GraphCenterC__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0502GraphCenterD__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0500GraphWholeA__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0500GraphWholeB__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0504GraphWholeC__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0505GraphWholeD__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0494Geometry__23
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0508GraphWholeA__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0509GraphWholeB__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0511GraphCenterD__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0514GraphCenterA__14

-- ===== source module GeneralCK.Certificates.E8TAxisProd0506CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0506CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0506GraphCenterA.qJetBox,
   E8TAxisProd0506GraphCenterB.qJetBox,
   E8TAxisProd0506GraphCenterC.qJetBox,
   E8TAxisProd0506GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0506GraphWholeA.qJetBox,
   E8TAxisProd0506GraphWholeB.qJetBox,
   E8TAxisProd0506GraphWholeC.qJetBox,
   E8TAxisProd0506GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨11093794010078916018888558509428166152719914432, 11093794010078916018888558509428235455218000453⟩
  | 0, 2 => ⟨35873127700764363107898452535702433568205696672, 35873127700764363107898452535702679379938348965⟩
  | 1, 1 => ⟨36172603296549882798200539806854716400590043951, 36172603296549882798200539806855148547128413686⟩
  | 0, 3 => ⟨79282529644314827170381090863093453249512686377, 79282529644314827170381090863094231349629062299⟩
  | 1, 2 => ⟨107862750323820381408038806252131601692887749400, 107862750323820381408038806252132964271402600430⟩
  | 2, 1 => ⟨108651059437416723792156890642910427400071424295, 108651059437416723792156890642912866048800638325⟩
  | 0, 4 => ⟨144896723189248036963892872251808739677548863013, 144896723189248036963892872251811311341130379855⟩
  | 1, 3 => ⟨219589922790154743301431371622524087035669174555, 219589922790154743301431371622528674377069152799⟩
  | 2, 2 => ⟨294709998300507480768817500025508931507109473143, 294709998300507480768817500025517272356291018159⟩
  | 3, 1 => ⟨296561722555506645238166777383739095462621151709, 296561722555506645238166777383754406806242595400⟩
  | 0, 5 => ⟨-447654301980959037389455396991765218168863961229331, 450469633194095519590738624840546146215986312764251⟩
  | 1, 4 => ⟨-870849169609220636965481569636465996385905044700360, 875040971268852454318840601207604706399154859060518⟩
  | 2, 3 => ⟨-1696348920692127049564567423260478246278917923969134, 1702342957578440290570162611866443065343877726403116⟩
  | 3, 2 => ⟨-3306958531357686328074310719709056123031472939840426, 3314794714079950419082815212619823273796703959359829⟩
  | 4, 1 => ⟨-6450251036285090030720582013147582545791029475105864, 6458259947486097762867503242164707495348704606438743⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0506Geometry.ds, E8TAxisProd0506Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 10372201969145533583338242005572842864428357801 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0506CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0507CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0507CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0507GraphCenterA.qJetBox,
   E8TAxisProd0507GraphCenterB.qJetBox,
   E8TAxisProd0507GraphCenterC.qJetBox,
   E8TAxisProd0507GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0507GraphWholeA.qJetBox,
   E8TAxisProd0507GraphWholeB.qJetBox,
   E8TAxisProd0507GraphWholeC.qJetBox,
   E8TAxisProd0507GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨9861757975064794047922572637817526209139761646, 9861757975064794047922572637817589465470853664⟩
  | 0, 2 => ⟨32181678173530413208477596860520628286204703510, 32181678173530413208477596860520849978578462946⟩
  | 1, 1 => ⟨32453990691852761276905584744834474130563330948, 32453990691852761276905584744834862286047048173⟩
  | 0, 3 => ⟨71731369666209677127108477860523741232066721676, 71731369666209677127108477860524440634535353185⟩
  | 1, 2 => ⟨97722980589658888305126623576668386809035213835, 97722980589658888305126623576669607553742292389⟩
  | 2, 1 => ⟨98447148590508352150649796860957174499880498295, 98447148590508352150649796860959354615676776366⟩
  | 0, 4 => ⟨132271818282329085530307034417551140312263932898, 132271818282329085530307034417553447109002797267⟩
  | 1, 3 => ⟨200891051881897322662937036738223165650905815073, 200891051881897322662937036738227270354890687397⟩
  | 2, 2 => ⟨269908094629435669942682528132067343365332907302, 269908094629435669942682528132074794451499722191⟩
  | 3, 1 => ⟨271627444194938726404628436549232545561695311165, 271627444194938726404628436549246204316102568358⟩
  | 0, 5 => ⟨-386509959860928805492353271631097759039798755946960, 389002580159592967971005502922178098578211457684527⟩
  | 1, 4 => ⟨-751183876950806189017493811944453134985589911254358, 754888627747609030646595094920231233923800290582384⟩
  | 2, 3 => ⟨-1461952089002952410668784702941717813016463580161878, 1467243735422673284634089126761446778350745926884147⟩
  | 3, 2 => ⟨-2847565748166758536859343296245800586822960529209247, 2854479995700994942949779757260142704458631028760670⟩
  | 4, 1 => ⟨-5549488489746706682948151015770402425969368029521595, 5556557046819791710098162863875823127214130184803152⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0507Geometry.ds, E8TAxisProd0507Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 9215283655975563955932376008973971852748157975 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0507CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0508CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0508CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0508GraphCenterA.qJetBox,
   E8TAxisProd0508GraphCenterB.qJetBox,
   E8TAxisProd0508GraphCenterC.qJetBox,
   E8TAxisProd0508GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0508GraphWholeA.qJetBox,
   E8TAxisProd0508GraphWholeB.qJetBox,
   E8TAxisProd0508GraphWholeC.qJetBox,
   E8TAxisProd0508GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨8793059064093879098109585350632047311644577180, 8793059064093879098109585350632105212672285223⟩
  | 0, 2 => ⟨28920141882796837299576184261410108790851038937, 28920141882796837299576184261410309236684715560⟩
  | 1, 1 => ⟨29197080011913634358738811095264875125932316848, 29197080011913634358738811095265224600237838864⟩
  | 0, 3 => ⟨64977577639555301254004362069776374103583262964, 64977577639555301254004362069777004163285233338⟩
  | 1, 2 => ⟨88670776690170268043295722149312690495951300066, 88670776690170268043295722149313786437126175199⟩
  | 2, 1 => ⟨89414712251389799147598161999581870232471998954, 89414712251389799147598161999583823145352788886⟩
  | 0, 4 => ⟨120861371450827909351411193868734138805304782794, 120861371450827909351411193868736212048904158310⟩
  | 1, 3 => ⟨183987152834102465831359036893414533518313344819, 183987152834102465831359036893418212781163258897⟩
  | 2, 2 => ⟨247527585058358460257983808080524397782599017506, 247527585058358460257983808080531064948620071506⟩
  | 3, 1 => ⟨249313170538425509688985967479758284826662944675, 249313170538425509688985967479770488592834875795⟩
  | 0, 5 => ⟨-333634512772780385276094784308203585697175337026778, 335843603336067253287092037667118846481187124922090⟩
  | 1, 4 => ⟨-647773387896813337040419164749947972801251522462649, 651050573499864275105805689483836873706542179189027⟩
  | 2, 3 => ⟨-1259533621940274434282500828439158911504258898082428, 1264208971305920213968012569875656049573979540239278⟩
  | 3, 2 => ⟨-2451120101967225595274358162265747840339695251170368, 2457225625115147347774718416881514718319502040549799⟩
  | 4, 1 => ⟨-4772690750142180592687822346039149230183283601203784, 4778934728736494400651994575911435865592337095721480⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0508Geometry.ds, E8TAxisProd0508Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 8212355188143642596103486287201695083984641406 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0508CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0509CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0509CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0509GraphCenterA.qJetBox,
   E8TAxisProd0509GraphCenterB.qJetBox,
   E8TAxisProd0509GraphCenterC.qJetBox,
   E8TAxisProd0509GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0509GraphWholeA.qJetBox,
   E8TAxisProd0509GraphWholeB.qJetBox,
   E8TAxisProd0509GraphWholeC.qJetBox,
   E8TAxisProd0509GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨7799642532011104729723869978090212548431682939, 7799642532011104729723869978090265486989136559⟩
  | 0, 2 => ⟨25888706165326702795090194879014331188513279787, 25888706165326702795090194879014512091895907099⟩
  | 1, 1 => ⟨26140033791896485808881807194825494858456437114, 26140033791896485808881807194825808851795355383⟩
  | 0, 3 => ⟨58657078296255429323944155130789971456334348488, 58657078296255429323944155130790537781489345070⟩
  | 1, 2 => ⟨80162681179876100104672439481902173114478829582, 80162681179876100104672439481903154597846448099⟩
  | 2, 1 => ⟨80844802044253006746195652083370473688474039579, 80844802044253006746195652083372218577708287708⟩
  | 0, 4 => ⟨110089445617430566582957589675123673817959184764, 110089445617430566582957589675125532137027739244⟩
  | 1, 3 => ⟨167973567749462775097097728747411422535427602069, 167973567749462775097097728747414710883115990495⟩
  | 2, 2 => ⟨226243705979442261989077312867090600540774239080, 226243705979442261989077312867096548211156144331⟩
  | 3, 1 => ⟨227899675557460281883874040834474785217736938975, 227899675557460281883874040834485654970870722598⟩
  | 0, 5 => ⟨-286164449814639331564160314098852906438668331945488, 288115349457336510902279945532473667655218177530838⟩
  | 1, 4 => ⟨-555004347187568009540139247594028293635175309281775, 557892632541752862491895131740473465103787521386137⟩
  | 2, 3 => ⟨-1078076910511428673793015106005456871271820909404521, 1082192219458538655325568161969378658426666148508118⟩
  | 3, 2 => ⟨-2095983833194828052259343879347099245427144545136281, 2101354892000934714532833716325484367456110280942044⟩
  | 4, 1 => ⟨-4077333817533996303632587004608425716370666567226231, 4082828876034808458072302105125071943404915235397165⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0509Geometry.ds, E8TAxisProd0509Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 7280512358712203338548616818160816123198259644 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0509CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0510CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0510CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0510GraphCenterA.qJetBox,
   E8TAxisProd0510GraphCenterB.qJetBox,
   E8TAxisProd0510GraphCenterC.qJetBox,
   E8TAxisProd0510GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0510GraphWholeA.qJetBox,
   E8TAxisProd0510GraphWholeB.qJetBox,
   E8TAxisProd0510GraphWholeC.qJetBox,
   E8TAxisProd0510GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨8756959611149945152742253584523006841920117308, 8756959611149945152742253584523064627528760013⟩
  | 0, 2 => ⟨28839014269937722916781530243571583683790623576, 28839014269937722916781530243571783689450159991⟩
  | 1, 1 => ⟨29086385179489937372370026037588885600243022254, 29086385179489937372370026037589234290350398553⟩
  | 0, 3 => ⟨64826653917333061600070469854157833447393653296, 64826653917333061600070469854158462107312207783⟩
  | 1, 2 => ⟨88441036370131330077851831015937487634477886270, 88441036370131330077851831015938581098707740322⟩
  | 2, 1 => ⟨89105664598422681885194642241626209256792938417, 89105664598422681885194642241628157695522151627⟩
  | 0, 4 => ⟨120616656373734690308044635676583559605190602420, 120616656373734690308044635676585628140078205518⟩
  | 1, 3 => ⟨183597477360103519313832098340285857841226401953, 183597477360103519313832098340289528668593509354⟩
  | 2, 2 => ⟨246948841816535360402190165940630369335711447802, 246948841816535360402190165940637021078317914979⟩
  | 3, 1 => ⟨248544386382570516327548292246215607219954022311, 248544386382570516327548292246227782492393512932⟩
  | 0, 5 => ⟨-332625481469455300056071262674281868442443579548878, 334829409902034935577613446041429232824993036704375⟩
  | 1, 4 => ⟨-645801701241812700230943878378986663378491278679014, 649071165463423172853497791002820028324100316303912⟩
  | 2, 3 => ⟨-1255675850983898272914257692857404101133466418635909, 1260340195482746762893502158316039883864359544667376⟩
  | 3, 2 => ⟨-2443565666781365478614667013357094478558009946737853, 2449656888996951736509385358589830560115788310083262⟩
  | 4, 1 => ⟨-4757888316713442045390630257780827645802584877305797, 4764117588870194420724615534075493655866223155167802⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0510Geometry.ds, E8TAxisProd0510Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 8178417851283146395748905423932974525197577150 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0510CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0511CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0511CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0511GraphCenterA.qJetBox,
   E8TAxisProd0511GraphCenterB.qJetBox,
   E8TAxisProd0511GraphCenterC.qJetBox,
   E8TAxisProd0511GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0511GraphWholeA.qJetBox,
   E8TAxisProd0511GraphWholeB.qJetBox,
   E8TAxisProd0511GraphWholeC.qJetBox,
   E8TAxisProd0511GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨7767327439328783117558641129096142992401015199, 7767327439328783117558641129096195825941992853⟩
  | 0, 2 => ⟨25815470766198139140899265548286918600222306625, 25815470766198139140899265548287099106449186273⟩
  | 1, 1 => ⟨26039961576147148791863667354259406690011541395, 26039961576147148791863667354259719978147419919⟩
  | 0, 3 => ⟨58519607198626275402610211831966730048131289326, 58519607198626275402610211831967295112101167553⟩
  | 1, 2 => ⟨79952938884193948313395597460253767056748136863, 79952938884193948313395597460254746314089403369⟩
  | 2, 1 => ⟨80562331706717710405244211023964877195071154703, 80562331706717710405244211023966618069841803888⟩
  | 0, 4 => ⟨109864377543537844966040263969623254969475536079, 109864377543537844966040263969625109044103043365⟩
  | 1, 3 => ⟨167614215103713985259244532838464793301746007482, 167614215103713985259244532838468074059792949510⟩
  | 2, 2 => ⟨225709003670478845744938622557920464141876219971, 225709003670478845744938622557926397950241719651⟩
  | 3, 1 => ⟨227188709895938097293662186756095254744416650371, 227188709895938097293662186756106098910916170657⟩
  | 0, 5 => ⟨-285281327415587989938179627459356184657371627165680, 287227631153408276914510411567116436667234303367350⟩
  | 1, 4 => ⟨-553279981643438422332007452416487623464876101917434, 556161395196681883452916047412666775139892270109964⟩
  | 2, 3 => ⟨-1074705408465631991232570945578574483069945320631023, 1078810920154912616030326979346085434038919498174667⟩
  | 3, 2 => ⟨-2089386104799905870229237119984618565131789749346410, 2094744414281199662465895106071655160737878922414556⟩
  | 4, 1 => ⟨-4064414623991811985444675945804668264849493006990065, 4069896518279319713820240362233291066318529480331448⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0511Geometry.ds, E8TAxisProd0511Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 7250150214471440971502285803888996598756197357 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0511CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0512CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0512CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0512GraphCenterA.qJetBox,
   E8TAxisProd0512GraphCenterB.qJetBox,
   E8TAxisProd0512GraphCenterC.qJetBox,
   E8TAxisProd0512GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0512GraphWholeA.qJetBox,
   E8TAxisProd0512GraphWholeB.qJetBox,
   E8TAxisProd0512GraphWholeC.qJetBox,
   E8TAxisProd0512GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨7085833893614457921799915553519428722417161005, 7085833893614457921799915553519477744745611828⟩
  | 0, 2 => ⟨23549140362661225800875443970608779974816095026, 23549140362661225800875443970608945477162716719⟩
  | 1, 1 => ⟨23924748680230968367967933095674733504137264677, 23924748680230968367967933095675019514458997902⟩
  | 0, 3 => ⟨53645687947483701247921398054408759501070973235, 53645687947483701247921398054409275436158278171⟩
  | 1, 2 => ⟨73546618578250581116565828174300366823571826002, 73546618578250581116565828174301257777663471852⟩
  | 2, 1 => ⟨74575483957829389472249192611308782005006811726, 74575483957829389472249192611310362453988212053⟩
  | 0, 4 => ⟨101408376313335711373822890910284730966064284709, 101408376313335711373822890910286419151255565948⟩
  | 1, 3 => ⟨155183666803956550722887086439767539022439462694, 155183666803956550722887086439770517626584060999⟩
  | 2, 2 => ⟨209549353317427376435215657486785678394573808635, 209549353317427376435215657486791056021066348362⟩
  | 3, 1 => ⟨212073325978262551571867075150051199599811338253, 212073325978262551571867075150061012953522082883⟩
  | 0, 5 => ⟨-249318270313699471770994956728776395080990351899697, 251064612265356897380923014124313092382884858105161⟩
  | 1, 4 => ⟨-483046980407439779116574607101038990948516851619382, 485626845151832350934549939571265370601783997568334⟩
  | 2, 3 => ⟨-937430826230318166838166583824839187673594115118844, 941101494553489914089781307369237441673935093324387⟩
  | 3, 2 => ⟨-1820930025402563125086092606670388906825219447290907, 1825717504637108447386328364675515768002475542812769⟩
  | 4, 1 => ⟨-3539204655601129123663761687720808852524849300456143, 3544105816469394723469106199060849826125770508236425⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0512Geometry.ds, E8TAxisProd0512Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 6611587406962962825285039615610555781122598231 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0512CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0513CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0513CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0513GraphCenterA.qJetBox,
   E8TAxisProd0513GraphCenterB.qJetBox,
   E8TAxisProd0513GraphCenterC.qJetBox,
   E8TAxisProd0513GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0513GraphWholeA.qJetBox,
   E8TAxisProd0513GraphWholeB.qJetBox,
   E8TAxisProd0513GraphWholeC.qJetBox,
   E8TAxisProd0513GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6272591811981252508795892421401866487170803169, 6272591811981252508795892421401911386599244686⟩
  | 0, 2 => ⟨21037334602724079563822813209561409811279381351, 21037334602724079563822813209561559313707506817⟩
  | 1, 1 => ⟨21377557105368734164802646940032495841041125094, 21377557105368734164802646940032752943771597853⟩
  | 0, 3 => ⟨48320194275258663988688543938254076669323997601, 48320194275258663988688543938254540521427778402⟩
  | 1, 2 => ⟨66351069103425502597232384801031558050228900079, 66351069103425502597232384801032355846986417352⟩
  | 2, 1 => ⟨67292618743757662729109158980556270517816067215, 67292618743757662729109158980557682191217950528⟩
  | 0, 4 => ⟨92160471739769251781594458754309928290629365012, 92160471739769251781594458754311440657916615836⟩
  | 1, 3 => ⟨141377253899268630816493053449884150433770373986, 141377253899268630816493053449886810178163961716⟩
  | 2, 2 => ⟨191142940227402060170408932000512109612289571913, 191142940227402060170408932000516901683669084044⟩
  | 3, 1 => ⟨193480326115144080092031531836723110753403952712, 193480326115144080092031531836731840717454633622⟩
  | 0, 5 => ⟨-212715023707116386455002895673926119710218319734333, 214259373264729467838398224591271331163516175020011⟩
  | 1, 4 => ⟨-411626804900332447846157287302353636222360821942456, 413902834608988353968320826530556160840048537007880⟩
  | 2, 3 => ⟨-797944881012539023551171935868290708614982766737896, 801178712035045766507586798310054252299848573258599⟩
  | 3, 2 => ⟨-1548347103629979407331787965103610181011346287337323, 1552562577244620231275228889054105017058364249544700⟩
  | 4, 1 => ⟨-3006291203810051414864611522102038931223669783428805, 3010610497743475582621867653817535557653743202924198⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0513Geometry.ds, E8TAxisProd0513Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5849449406779200548615677540791454830746085685 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0513CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0514CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0514CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0514GraphCenterA.qJetBox,
   E8TAxisProd0514GraphCenterB.qJetBox,
   E8TAxisProd0514GraphCenterC.qJetBox,
   E8TAxisProd0514GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0514GraphWholeA.qJetBox,
   E8TAxisProd0514GraphWholeB.qJetBox,
   E8TAxisProd0514GraphWholeC.qJetBox,
   E8TAxisProd0514GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨7056439345861323451465957894949073877105073650, 7056439345861323451465957894949122802668067653⟩
  | 0, 2 => ⟨23482162423554543398260302562666850887561429641, 23482162423554543398260302562667016027054633128⟩
  | 1, 1 => ⟨23832936557018881745444227554937166255354777590, 23832936557018881745444227554937451623559627582⟩
  | 0, 3 => ⟨53519058176697444843517078916983068538087067554, 53519058176697444843517078916983583323600075818⟩
  | 1, 2 => ⟨73352848312073618761628162484163361749152315370, 73352848312073618761628162484164250679639282612⟩
  | 2, 1 => ⟨74313859453172933847644809969861137556323737764, 74313859453172933847644809969862714361969629447⟩
  | 0, 4 => ⟨101199319554798339291519649832826169605568123725, 101199319554798339291519649832827853924299374677⟩
  | 1, 3 => ⟨154848862056362414689854219106430246147163156071, 154848862056362414689854219106433217851910126149⟩
  | 2, 2 => ⟨209050013638928184062620083193702981439658645211, 209050013638928184062620083193708346479910746988⟩
  | 3, 1 => ⟨211408011554018215843813349170751976809033799941, 211408011554018215843813349170761766953014037428⟩
  | 0, 5 => ⟨-248535454782700081163103985469374627271058510047203, 250277739683106535585184374364240203766730949287262⟩
  | 1, 4 => ⟨-481519586875350089728308845657535692699388110657239, 484093339617367123442618663013619938849868772328706⟩
  | 2, 3 => ⟨-934446449594083936988569812813979527657233890839372, 938108360714644603920551392832821388967134961405641⟩
  | 3, 2 => ⟨-1815093616250272850358466219491533887264035779973755, 1819869658767353307922792841635555591148381290365118⟩
  | 4, 1 => ⟨-3527783415173514946830590226270193592428095754347449, 3532672721004224439664934478038478820755908173886289⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0514Geometry.ds, E8TAxisProd0514Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 6583982892977758178732567231611662757973934706 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0514CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0515CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0515CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0515GraphCenterA.qJetBox,
   E8TAxisProd0515GraphCenterB.qJetBox,
   E8TAxisProd0515GraphCenterC.qJetBox,
   E8TAxisProd0515GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0515GraphWholeA.qJetBox,
   E8TAxisProd0515GraphWholeB.qJetBox,
   E8TAxisProd0515GraphWholeC.qJetBox,
   E8TAxisProd0515GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6246332863895099302105791681503518553803019038, 6246332863895099302105791681503563365084523531⟩
  | 0, 2 => ⟨20977006310243778155846930339362218920459131109, 20977006310243778155846930339362368095380903761⟩
  | 1, 1 => ⟨21294728639658957201549264211898367196926755815, 21294728639658957201549264211898623722220549768⟩
  | 0, 3 => ⟨48205113678921288831118220860807197999607658809, 48205113678921288831118220860807660816075239583⟩
  | 1, 2 => ⟨66174540250400496234563322799620927153003379850, 66174540250400496234563322799621723131840869914⟩
  | 2, 1 => ⟨67053978055829889966183652756999837361613829983, 67053978055829889966183652757001245767671855331⟩
  | 0, 4 => ⟨91968540381637672499662687911439133011392060217, 91968540381637672499662687911440641896147702707⟩
  | 1, 3 => ⟨141069006606032685579513077951115047014900379876, 141069006606032685579513077951117700558151831198⟩
  | 2, 2 => ⟨190682308992303660366212945419032341388321243092, 190682308992303660366212945419037122160907890831⟩
  | 3, 1 => ⟨192865957999563003527256098409486368711039618376, 192865957999563003527256098409495077859874667720⟩
  | 0, 5 => ⟨-212038297581833705212269925295936899156752593749833, 213579044317109166075277162737857209375544074620867⟩
  | 1, 4 => ⟨-410307520457905021479938921465002297798519395303885, 412578155810928021863726411955735149775953685593331⟩
  | 2, 3 => ⟨-795369172731349414625281606533465769556176614482342, 798595293764259340839940695720367567355299766999046⟩
  | 3, 2 => ⟨-1543313779493456655078698984630314753351226229373108, 1547519159989168940292157775010489801348441277814353⟩
  | 4, 1 => ⟨-2996448974004431601421644330876425111484281649837383, 3000757654452206037706563745911179967354221669201498⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0515Geometry.ds, E8TAxisProd0515Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5824803588358941816772158824994010328494175054 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0515CertifiedArithmetic

end


