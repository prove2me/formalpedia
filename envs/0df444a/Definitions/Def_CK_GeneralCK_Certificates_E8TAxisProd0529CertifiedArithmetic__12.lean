-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0529CertifiedArithmetic__12
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0529CertifiedArithmetic__12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T14:44:02.631552+00:00
-- url     : https://prove2.me/theorems/6c5573d3-5f75-464f-ba93-7787414a8dcb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0529CertifiedArithmetic (+11 modules: GeneralCK.Certificates.E8TAxisProd0530CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0529CertifiedArithmetic (+11 modules: GeneralCK.Certificates.E8TAxisProd0530CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0531CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0532CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0533CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0534CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0535CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0536CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0537CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0538CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0539CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0540CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0529CertifiedArithmetic (+11 modules: GeneralCK.Certificates.E8TAxisProd0530CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0531CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0532CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0533CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0534CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0535CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0536CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0537CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0538CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0539CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0540CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0529CertifiedArithmetic (+11 modules: GeneralCK.Certificates.E8TAxisProd0530CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0531CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0532CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0533CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0534CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0535CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0536CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0537CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0538CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0539CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0540CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0529CertifiedArithmetic (+11 modules: GeneralCK/Certificates/E8TAxisProd0530CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0531CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0532CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0533CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0534CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0535CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0536CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0537CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0538CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0539CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0540CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0528GraphCenterA__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0527GraphCenterB__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0518GraphCenterC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0527GraphCenterD__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0523GraphWholeA__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0525GraphWholeB__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0520GraphWholeC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0520GraphWholeD__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0517Geometry__21
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0531GraphCenterC__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0532GraphWholeD__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0535GraphCenterD__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0536GraphCenterA__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0537GraphWholeB__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0537GraphWholeC__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0538Geometry__19
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0539GraphWholeA__17

-- ===== source module GeneralCK.Certificates.E8TAxisProd0529CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0529CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0529GraphCenterA.qJetBox,
   E8TAxisProd0529GraphCenterB.qJetBox,
   E8TAxisProd0529GraphCenterC.qJetBox,
   E8TAxisProd0529GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0529GraphWholeA.qJetBox,
   E8TAxisProd0529GraphWholeB.qJetBox,
   E8TAxisProd0529GraphWholeC.qJetBox,
   E8TAxisProd0529GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3807352332623868787207955093075732429544810093, 3807352332623868787207955093075764336286686964⟩
  | 0, 2 => ⟨13249163795186428511937935035189954228924932699, 13249163795186428511937935035190054305093945766⟩
  | 1, 1 => ⟨13475857159907855938160068251355944046534993020, 13475857159907855938160068251356112429705681668⟩
  | 0, 3 => ⟨31423216232050686714475763989928044015868714711, 31423216232050686714475763989928347375671478398⟩
  | 1, 2 => ⟨43450231166958844579344355498612152383713114839, 43450231166958844579344355498612664638311688829⟩
  | 2, 1 => ⟨44103407486984100783634988916745026689204587095, 44103407486984100783634988916745923148734473782⟩
  | 0, 4 => ⟨62052762064486601100775032692715724079206697511, 62052762064486601100775032692716694702671451380⟩
  | 1, 3 => ⟨96210557137566589610591269219553630059462070629, 96210557137566589610591269219555311138118842620⟩
  | 2, 2 => ⟨130774807542329142927598216867017934914571404500, 130774807542329142927598216867020935173630235444⟩
  | 3, 1 => ⟨132477474825618238242545323808480308895946835078, 132477474825618238242545323808485733017151691763⟩
  | 0, 5 => ⟨-109963677272212769134219876172936420555577082569039, 110911664077167496333340872171152569121671895873641⟩
  | 1, 4 => ⟨-211571303734045228046419700393788602370222180006759, 212951561879137131529295186424144579656120525920093⟩
  | 2, 3 => ⟨-408039242119113821766819859894334335470924627958478, 409986144315333653749897406966888184242518185790010⟩
  | 3, 2 => ⟨-787950108939373608137597220624040514892316457592441, 790481160662792990305087090467372662234031425303030⟩
  | 4, 1 => ⟨-1522707910021383664832119646273934842739788806341622, 1525313628920652964924292890633068985283845973146356⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0529Geometry.ds, E8TAxisProd0529Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3542055278866074114526606609848538854108467295 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0529CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0530CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0530CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0530GraphCenterA.qJetBox,
   E8TAxisProd0530GraphCenterB.qJetBox,
   E8TAxisProd0530GraphCenterC.qJetBox,
   E8TAxisProd0530GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0530GraphWholeA.qJetBox,
   E8TAxisProd0530GraphWholeB.qJetBox,
   E8TAxisProd0530GraphWholeC.qJetBox,
   E8TAxisProd0530GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4302575896206592422894540011578894759711738716, 4302575896206592422894540011578929391240506330⟩
  | 0, 2 => ⟨14854136281612569793276244910103953782922438785, 14854136281612569793276244910104064082672514288⟩
  | 1, 1 => ⟨15088801323836357720700418556691317268758955998, 15088801323836357720700418556691503926474300110⟩
  | 0, 3 => ⟨34970771863106694446178362699952521874628417139, 34970771863106694446178362699952858375812705673⟩
  | 1, 2 => ⟨48252726859424904991297871503435691431633009421, 48252726859424904991297871503436262445600612600⟩
  | 2, 1 => ⟨48922307613730495257181825903471178539151171214, 48922307613730495257181825903472180721302221671⟩
  | 0, 4 => ⟨68494663108672392614378958489153855034087193722, 68494663108672392614378958489154937404942005735⟩
  | 1, 3 => ⟨105889893157186955458269103447781681666621736179, 105889893157186955458269103447783564106399408745⟩
  | 2, 2 => ⟨143695087245646875734344508615221745084277124644, 143695087245646875734344508615225113228895631846⟩
  | 3, 1 => ⟨145419557571324257942616763191092542296704051022, 145419557571324257942616763191098643765221151022⟩
  | 0, 5 => ⟨-129693268757887763918849436439275061725520468162893, 130761395250133318839607950536870297182203956275105⟩
  | 1, 4 => ⟨-249919116206147215204163519723344857572438869696467, 251479790851341189431092914198703511630537087499295⟩
  | 2, 3 => ⟨-482656252334084024686137835497356050218899377846634, 484862345097139021423140476385189776936222751067809⟩
  | 3, 2 => ⟨-933233394796853790909178663432813799833275035137965, 936103616778522317588610771193505635164033277880774⟩
  | 4, 1 => ⟨-1805705601244317965286740932455413488657652708942191, 1808655927834297557126878980231625321149350920588605⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0530Geometry.ds, E8TAxisProd0530Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4005125561356566766201793292866018343575830796 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0530CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0531CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0531CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0531GraphCenterA.qJetBox,
   E8TAxisProd0531GraphCenterB.qJetBox,
   E8TAxisProd0531GraphCenterC.qJetBox,
   E8TAxisProd0531GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0531GraphWholeA.qJetBox,
   E8TAxisProd0531GraphWholeB.qJetBox,
   E8TAxisProd0531GraphWholeC.qJetBox,
   E8TAxisProd0531GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3790815407079077534155992797850745140988926917, 3790815407079077534155992797850776986622268849⟩
  | 0, 2 => ⟨13209933218492650910866676463771930216646590329, 13209933218492650910866676463772030075019094812⟩
  | 1, 1 => ⟨13421619478354333770527608219614349961565278349, 13421619478354333770527608219614517967133000220⟩
  | 0, 3 => ⟨31345734563986136227330862066125499717136715287, 31345734563986136227330862066125802395625316196⟩
  | 1, 2 => ⟨43330104970549832771205505396369902188449574936, 43330104970549832771205505396370413262520241760⟩
  | 2, 1 => ⟨43940145408969240550731092417201247851500527486, 43940145408969240550731092417202142205789926178⟩
  | 0, 4 => ⟨61917949292875612817744539529945083564067028199, 61917949292875612817744539529946051909781798232⟩
  | 1, 3 => ⟨95991428134461154521584100161916603537429839478, 95991428134461154521584100161918280601788802043⟩
  | 2, 2 => ⟨130444628706915697096260073305943176985244222151, 130444628706915697096260073305946169972446461823⟩
  | 3, 1 => ⟨132035191097137753079827374160492486338823280449, 132035191097137753079827374160497897125644760314⟩
  | 0, 5 => ⟨-109594166382597267787142484169450941611990562590994, 110539907488559812368784425521883799509732244448520⟩
  | 1, 4 => ⟨-210853810657598324802905339934173807391785114109081, 212230660893464957451745544636438832589061303222718⟩
  | 2, 3 => ⟨-406643521680008533862656441610771871179124528384157, 408585451394699336742955520412807929559771867051383⟩
  | 3, 2 => ⟨-785232050605569941105448163702520337552146109459854, 787756358254066390806096295650219735582337711681184⟩
  | 4, 1 => ⟨-1517410810965362849714210929106266446325602591753098, 1520008819535448843197901410834160718176602330357649⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0531Geometry.ds, E8TAxisProd0531Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3526570372361237549453041221533440630088186152 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0531CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0532CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0532CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0532GraphCenterA.qJetBox,
   E8TAxisProd0532GraphCenterB.qJetBox,
   E8TAxisProd0532GraphCenterC.qJetBox,
   E8TAxisProd0532GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0532GraphWholeA.qJetBox,
   E8TAxisProd0532GraphWholeB.qJetBox,
   E8TAxisProd0532GraphWholeC.qJetBox,
   E8TAxisProd0532GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3350543260362152737180844395838483746171354496, 3350543260362152737180844395838513116908371431⟩
  | 0, 2 => ⟨11769436126902266212999419606794188287645394932, 11769436126902266212999419606794278951339301085⟩
  | 1, 1 => ⟨11973726129435195654876842350717395308920692075, 11973726129435195654876842350717546930206049049⟩
  | 0, 3 => ⟨28131609903991148457051240662625824416376938607, 28131609903991148457051240662626097344995137452⟩
  | 1, 2 => ⟨38972925142558310273914987833179680898668416425, 38972925142558310273914987833180139360603755219⟩
  | 2, 1 => ⟨39567347470449051520831654411829875853006104104, 39567347470449051520831654411830675725503168876⟩
  | 0, 4 => ⟨56016601293784785682901357938211152973640597698, 56016601293784785682901357938212021115551661782⟩
  | 1, 3 => ⟨87105242816477126101805641988849953104742341361, 87105242816477126101805641988851449959649412709⟩
  | 2, 2 => ⟨118569945508964590778069118110728193806913466937, 118569945508964590778069118110730858038258003236⟩
  | 3, 1 => ⟨120138565035681668097966592498342063339315442810, 120138565035681668097966592498346869647580204494⟩
  | 0, 5 => ⟨-92753441397898166225142500792562167678779332970239, 93592792816508784251561593456273423066786956796059⟩
  | 1, 4 => ⟨-178157561311086109120274361268491953687836095502697, 179374872970299898680692372340548654442870229551424⟩
  | 2, 3 => ⟨-343090509359376764815784082280068441413761688809030, 344803465533874814066577702281620883238762311325990⟩
  | 3, 2 => ⟨-661618785620622644601689460008939265662884626858478, 663843628585145530242673019225887793003786584005102⟩
  | 4, 1 => ⟨-1276871839077796781281232959314022376077374025788304, 1279165616207511861828833994480682079392664405009737⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0532Geometry.ds, E8TAxisProd0532Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3115106671953240354216550443072953633090028116 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0532CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0533CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0533CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0533GraphCenterA.qJetBox,
   E8TAxisProd0533GraphCenterB.qJetBox,
   E8TAxisProd0533GraphCenterC.qJetBox,
   E8TAxisProd0533GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0533GraphWholeA.qJetBox,
   E8TAxisProd0533GraphWholeB.qJetBox,
   E8TAxisProd0533GraphWholeC.qJetBox,
   E8TAxisProd0533GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2944881304756036068177206129224398582011542489, 2944881304756036068177206129224425647530947519⟩
  | 0, 2 => ⟨10442949826282694633047751872192986175661838082, 10442949826282694633047751872193068372284140632⟩
  | 1, 1 => ⟨10626863286256352454264132585997374664238283121, 10626863286256352454264132585997511256790385823⟩
  | 0, 3 => ⟨25153457693066456795981853979610549543365301587, 25153457693066456795981853979610795159190323540⟩
  | 1, 2 => ⟨34916014674220368872791574601155657498870674969, 34916014674220368872791574601156067810369236718⟩
  | 2, 1 => ⟨35456341677172848769576639833299331359448924457, 35456341677172848769576639833300044946992521182⟩
  | 0, 4 => ⟨50494673241084599175293630378518586075706707331, 50494673241084599175293630378519362384273547851⟩
  | 1, 3 => ⟨78757119523496364411268417384390821096720224006, 78757119523496364411268417384392153215141944038⟩
  | 2, 2 => ⟨107367101102423979230489610860789544162696438832, 107367101102423979230489610860791908381217261754⟩
  | 3, 1 => ⟨108810421871694707841585228674767107123769865627, 108810421871694707841585228674771362622910134511⟩
  | 0, 5 => ⟨-78373132672861156647244221367009967824190030616322, 79108246681364926706501528310043652626992711911644⟩
  | 1, 4 => ⟨-150268718341736122228236533959933000862438797420046, 151329040638411943582755463384384647453579302234898⟩
  | 2, 3 => ⟨-288934754862525377031122463457727518529425101473071, 290421506275198780434959429517116936140911855759932⟩
  | 3, 2 => ⟨-556380012804359402929717575493831850703732219113069, 558307858838620199542778717640687103810542498669871⟩
  | 4, 1 => ⟨-1072268641316287095306624780589304271759340539593718, 1074258500069239348109412730769604092867194773505265⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0533Geometry.ds, E8TAxisProd0533Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2736152711568898953948933625764997789236624029 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0533CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0534CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0534CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0534GraphCenterA.qJetBox,
   E8TAxisProd0534GraphCenterB.qJetBox,
   E8TAxisProd0534GraphCenterC.qJetBox,
   E8TAxisProd0534GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0534GraphWholeA.qJetBox,
   E8TAxisProd0534GraphWholeB.qJetBox,
   E8TAxisProd0534GraphWholeC.qJetBox,
   E8TAxisProd0534GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3335853424799208415310748577191979413454929078, 3335853424799208415310748577192008728327228509⟩
  | 0, 2 => ⟨11734315345441496853078665615257992552855499233, 11734315345441496853078665615258083019742079511⟩
  | 1, 1 => ⟨11925077971714363846490416516626151207277334724, 11925077971714363846490416516626302488977374082⟩
  | 0, 3 => ⟨28061666061420127239721880485681951346867312218, 28061666061420127239721880485682223661981571197⟩
  | 1, 2 => ⟨38864169001067412947469165958832155400899630199, 38864169001067412947469165958832612803758960206⟩
  | 2, 1 => ⟨39419324423946864069617957479358979549975899891, 39419324423946864069617957479359777537949040609⟩
  | 0, 4 => ⟨55893586021980807841311422735571261672965512435, 55893586021980807841311422735572127768708537870⟩
  | 1, 3 => ⟨86904649390363006050611720392107479853861178190, 86904649390363006050611720392108973113564705624⟩
  | 2, 2 => ⟨118267032456564666415693554724838743908010160540, 118267032456564666415693554724841401637654108459⟩
  | 3, 1 => ⟨119732341794133351811457792902242099759079651137, 119732341794133351811457792902246894161038063491⟩
  | 0, 5 => ⟨-92438445763337549561827058362740813925853669648794, 93275789301985103581981079744104220091484190708135⟩
  | 1, 4 => ⟨-177546631477534304963957912265709281684651987484126, 178760888332379515051999223607364677292592806117829⟩
  | 2, 3 => ⟨-341903312502879443221741234476301550022766127212681, 343611789287712109971068427439219592346262036392531⟩
  | 3, 2 => ⟨-659309053550469368214239492573350498914162532170884, 661527764381478840906572721487870086503982898810696⟩
  | 4, 1 => ⟨-1272374730910143238901618971213432663886089705130644, 1274661344972715418940863737674415807720652780856183⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0534Geometry.ds, E8TAxisProd0534Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3101359491936756935346582765404289863555572324 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0534CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0535CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0535CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0535GraphCenterA.qJetBox,
   E8TAxisProd0535GraphCenterB.qJetBox,
   E8TAxisProd0535GraphCenterC.qJetBox,
   E8TAxisProd0535GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0535GraphWholeA.qJetBox,
   E8TAxisProd0535GraphWholeB.qJetBox,
   E8TAxisProd0535GraphWholeC.qJetBox,
   E8TAxisProd0535GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2931847252184064150760556371877857386491726940, 2931847252184064150760556371877884400898272112⟩
  | 0, 2 => ⟨10411547423926721053404718673898338618759653354, 10411547423926721053404718673898420637482097572⟩
  | 1, 1 => ⟨10583279749136043097059315786427219144002927190, 10583279749136043097059315786427355431136424047⟩
  | 0, 3 => ⟨25090409427676534413742690069615983985948084289, 25090409427676534413742690069616229049355052272⟩
  | 1, 2 => ⟨34817682920953719390022291233805366216704626885, 34817682920953719390022291233805775578339434979⟩
  | 2, 1 => ⟨35322306318079481262910118709894010798121931995, 35322306318079481262910118709894722699357676684⟩
  | 0, 4 => ⟨50382587545890028221508709813457836888680516756, 50382587545890028221508709813458611360167892010⟩
  | 1, 3 => ⟨78573746653516818061842076017273049016086119249, 78573746653516818061842076017274377917239131202⟩
  | 2, 2 => ⟨107089569619325683860214666156422405180588161011, 107089569619325683860214666156424763591376072291⟩
  | 3, 1 => ⟨108437802485866939350814968295766783085044692850, 108437802485866939350814968295771027963772711151⟩
  | 0, 5 => ⟨-78109714952127911303011097209779121436258598892607, 78842909494876260946632345479358862627190882393471⟩
  | 1, 4 => ⟨-149758413530667558109114802821395360770222166531944, 150815805550224912151156275135601206875644009765557⟩
  | 2, 3 => ⟨-287944061004355057224586431963873071892621188220117, 289426505046701280400780400303041775008319009153944⟩
  | 3, 2 => ⟨-554454255401381257641856645073067997287690162877600, 556376204518085598823744847824673461791777998529803⟩
  | 4, 1 => ⟨-1068522166674905341973240010086507266417318616761095, 1070505178340899533681089290572339580436780102783356⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0535Geometry.ds, E8TAxisProd0535Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2723962073606729534943548103380116744074710937 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0535CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0536CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0536CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0536GraphCenterA.qJetBox,
   E8TAxisProd0536GraphCenterB.qJetBox,
   E8TAxisProd0536GraphCenterC.qJetBox,
   E8TAxisProd0536GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0536GraphWholeA.qJetBox,
   E8TAxisProd0536GraphWholeB.qJetBox,
   E8TAxisProd0536GraphWholeC.qJetBox,
   E8TAxisProd0536GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4284035524485645818055422486207151829777611810, 4284035524485645818055422486207186394541528036⟩
  | 0, 2 => ⟨14810476289872042291389122899707095279775434125, 14810476289872042291389122899707205338950754055⟩
  | 1, 1 => ⟨15028568079574312620454269394573427199906980228, 15028568079574312620454269394573613438648959400⟩
  | 0, 3 => ⟨34885245601160926035465464922400486784641266099, 34885245601160926035465464922400822530916654745⟩
  | 1, 2 => ⟨48120513669389767391628130105540406561885665055, 48120513669389767391628130105540976263229942441⟩
  | 2, 1 => ⟨48742913035240118780543444569919166955637367204, 48742913035240118780543444569920166792139222062⟩
  | 0, 4 => ⟨68347401867969309170458514547678659276846554943, 68347401867969309170458514547679739119267936267⟩
  | 1, 3 => ⟨105651287340609915993523555061761201470568994669, 105651287340609915993523555061763079441699999324⟩
  | 2, 2 => ⟨143336357943951422193333972222516794195944488915, 143336357943951422193333972222520154232979182093⟩
  | 3, 1 => ⟨144939657675042716180216263050190492310823905205, 144939657675042716180216263050196578894071297488⟩
  | 0, 5 => ⟨-129262245580587835345698338624469260825406598993375, 130327860264246822186479580385787069122055919983412⟩
  | 1, 4 => ⟨-249081263825394790909675821398894753225882953190958, 250638134599298899858922076703522396991986048088181⟩
  | 2, 3 => ⟨-481024790418963601292130038995974240761418556823072, 483225356110793593253218083639128848600004154938137⟩
  | 3, 2 => ⟨-930053288257622001072303886730481102046044266288661, 932916074463997278011043190503391060519595621005738⟩
  | 4, 1 => ⟨-1799502435075094429053966086218532244317434557141691, 1802444423847025820466735847616205912046608680573372⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0536Geometry.ds, E8TAxisProd0536Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3987754716467189764050312784590626234543223772 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0536CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0537CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0537CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0537GraphCenterA.qJetBox,
   E8TAxisProd0537GraphCenterB.qJetBox,
   E8TAxisProd0537GraphCenterC.qJetBox,
   E8TAxisProd0537GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0537GraphWholeA.qJetBox,
   E8TAxisProd0537GraphWholeB.qJetBox,
   E8TAxisProd0537GraphWholeC.qJetBox,
   E8TAxisProd0537GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3774327459266463970576693930668642577237506445, 3774327459266463970576693930668674361882496996⟩
  | 0, 2 => ⟨13170799388627783981441769052047442967013648051, 13170799388627783981441769052047542608059508048⟩
  | 1, 1 => ⟨13367531783462708513912813651319237622066956193, 13367531783462708513912813651319405250864161494⟩
  | 0, 3 => ⟨31268421252768722566682300489034207653278516060, 31268421252768722566682300489034509651949906210⟩
  | 1, 2 => ⟨43210252419224875090083802968199777294757893071, 43210252419224875090083802968200287190927957338⟩
  | 2, 1 => ⟨43777295636886418040551940841263251294520056068, 43777295636886418040551940841264143548298280022⟩
  | 0, 4 => ⟨61783391040743677600718271295468575590847172393, 61783391040743677600718271295469541663911682236⟩
  | 1, 3 => ⟨95772724886149737897687211577814358556835388095, 95772724886149737897687211577816031615951913021⟩
  | 2, 2 => ⟨130115117864502412010847598763455278446141712274, 130115117864502412010847598763458264177967726818⟩
  | 3, 1 => ⟨131593889012528543581113766257985341393209577632, 131593889012528543581113766257990738876019334653⟩
  | 0, 5 => ⟨-109225806672457659231985854315426528170869737665657, 110169306557943924458368259703465436542835982088466⟩
  | 1, 4 => ⟨-210138566054241515006091024784506178930186399654754, 211512014903375177649326787286280644539199217955593⟩
  | 2, 3 => ⟨-405252199539711431737814342481654038834996655785549, 407189165550907328635820769749585048638951691855983⟩
  | 3, 2 => ⟨-782522604292337068388033615802629947193923898426456, 785040177977304250957511691414027008260768245097866⟩
  | 4, 1 => ⟨-1512130586217524581168251020948552135598558158199623, 1514720891592857196119341538567409885499661548592507⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0537Geometry.ds, E8TAxisProd0537Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3511131538683677049958820982344819245250401789 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0537CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0538CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0538CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0538GraphCenterA.qJetBox,
   E8TAxisProd0538GraphCenterB.qJetBox,
   E8TAxisProd0538GraphCenterC.qJetBox,
   E8TAxisProd0538GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0538GraphWholeA.qJetBox,
   E8TAxisProd0538GraphWholeB.qJetBox,
   E8TAxisProd0538GraphWholeC.qJetBox,
   E8TAxisProd0538GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4265549660984896942173963174322382620544662406, 4265549660984896942173963174322417118675605576⟩
  | 0, 2 => ⟨14766923090982735623979205311031157801365710617, 14766923090982735623979205311031267620485228201⟩
  | 1, 1 => ⟨14968499915508408320048741525249345032979506653, 14968499915508408320048741525249530853670384546⟩
  | 0, 3 => ⟨34799903243869943146483360695603829974461029741, 34799903243869943146483360695604164967481823388⟩
  | 1, 2 => ⟨47988598450125862572571233136634647841731220869, 47988598450125862572571233136635216233362586827⟩
  | 2, 1 => ⟨48563966420107023928613289369011354033692960406, 48563966420107023928613289369012351529791437348⟩
  | 0, 4 => ⟨68200415587673868693804166004774090437504276247, 68200415587673868693804166004775167757117185171⟩
  | 1, 3 => ⟨105413139798112235379831614041843959605077138603, 105413139798112235379831614041845833117565855163⟩
  | 2, 2 => ⟨142978345674939121730563931610620086148353502824, 142978345674939121730563931610623438096026000918⟩
  | 3, 1 => ⟨144460809417369170331532690343584275085097024771, 144460809417369170331532690343590346816673368242⟩
  | 0, 5 => ⟨-128832538692940247745004413684004170363187012122477, 129895646704254928028878028289988876966255910796169⟩
  | 1, 4 => ⟨-248245984509540586846295917956717843281471137639311, 249799058942492673797946032523805897183516296918875⟩
  | 2, 3 => ⟨-479398365536567010622524224143298085099029403066736, 481593414408442987021231594214421632084084559698150⟩
  | 3, 2 => ⟨-926883051502119961768655903688951185594034584936130, 929738414054249348497589631202934054356287742905000⟩
  | 4, 1 => ⟨-1793318621245868509767616108190292412683461203597120, 1796252281721762143756417909519330457192403893386016⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0538Geometry.ds, E8TAxisProd0538Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3970435179741002805351808247094878295202220293 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0538CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0539CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0539CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0539GraphCenterA.qJetBox,
   E8TAxisProd0539GraphCenterB.qJetBox,
   E8TAxisProd0539GraphCenterC.qJetBox,
   E8TAxisProd0539GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0539GraphWholeA.qJetBox,
   E8TAxisProd0539GraphWholeB.qJetBox,
   E8TAxisProd0539GraphWholeC.qJetBox,
   E8TAxisProd0539GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3757888368383937926915389427453963982472651708, 3757888368383937926915389427453995706249231363⟩
  | 0, 2 => ⟨13131762095344505426046043519865374934550788362, 13131762095344505426046043519865474358738862981⟩
  | 1, 1 => ⟨13313593733509063396683500343987211065988777554, 13313593733509063396683500343987378318846123012⟩
  | 0, 3 => ⟨31191275980505194621624510421217527098657564241, 31191275980505194621624510421217828419005480198⟩
  | 1, 2 => ⟨43090672981228753974584118278570234890286948820, 43090672981228753974584118278570743611178064070⟩
  | 2, 1 => ⟨43614857336443658638820496680315518719851614321, 43614857336443658638820496680316408877837803923⟩
  | 0, 4 => ⟨61649086898428280840476553135432820948450608394, 61649086898428280840476553135433784753953759837⟩
  | 1, 3 => ⟨95554446691563123342878055458833164559919478785, 95554446691563123342878055458834833622829810907⟩
  | 2, 2 => ⟨129786273896526906563361639592648479798350786369, 129786273896526906563361639592651458291246283318⟩
  | 3, 1 => ⟨131153566881042973661623229213204200037927167466, 131153566881042973661623229213209584247033211832⟩
  | 0, 5 => ⟨-108858594991338203577106216628532734157589780643124, 109799858128719220694272810094442349800127995792626⟩
  | 1, 4 => ⟨-209425563752180094161552144957117156869393836783688, 210795617731922005637919817549043358524568055742340⟩
  | 2, 3 => ⟨-403865263580550185676736122675065750000104188892433, 405797274664076727838342640910253645094795810349337⟩
  | 3, 2 => ⟨-779821746182498146742341650839058631800099409958990, 782332596027602394743101298166882897869532029180000⟩
  | 4, 1 => ⟨-1506867188934153316255970668388743219727512148199422, 1509449798302250779144545214708424140442629818107684⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0539Geometry.ds, E8TAxisProd0539Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3495738663663546831627249752326863230677462054 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0539CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0540CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0540CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0540GraphCenterA.qJetBox,
   E8TAxisProd0540GraphCenterB.qJetBox,
   E8TAxisProd0540GraphCenterC.qJetBox,
   E8TAxisProd0540GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0540GraphWholeA.qJetBox,
   E8TAxisProd0540GraphWholeB.qJetBox,
   E8TAxisProd0540GraphWholeC.qJetBox,
   E8TAxisProd0540GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3321207435609487944868277875887145956070884454, 3321207435609487944868277875887175215187819201⟩
  | 0, 2 => ⟨11699281897739488649939730294372638288122832537, 11699281897739488649939730294372728558626618864⟩
  | 1, 1 => ⟨11876565602559584769453947312265941314791717893, 11876565602559584769453947312266092257656114279⟩
  | 0, 3 => ⟨27991875841010395169014968100028229538454367805, 27991875841010395169014968100028501241416110940⟩
  | 1, 2 => ⟨38755663354665470899618697423332566270435114436, 38755663354665470899618697423333022616584325353⟩
  | 2, 1 => ⟨39271679630621133526062560162233961201995933815, 39271679630621133526062560162234757309698021764⟩
  | 0, 4 => ⟨55770805772117182174366872389156158562989241953, 55770805772117182174366872389157022617175376717⟩
  | 1, 3 => ⟨86704450564916881903641852316693370814689534691, 86704450564916881903641852316694860487362829459⟩
  | 2, 2 => ⟨117964740251831364885502210903803185249738810871, 117964740251831364885502210903805836492544640714⟩
  | 3, 1 => ⟨119327032705145036117048762029634965519904654381, 119327032705145036117048762029639748042930553441⟩
  | 0, 5 => ⟨-92124450423101918917684207760454871537806433635290, 92959790208587403870970922941699510882986684016800⟩
  | 1, 4 => ⟨-176937653760444765719609096163274193749715114773994, 178148861910296570563092879671170405759630742939195⟩
  | 2, 3 => ⟨-340719931280760322003182735524525563534887951050591, 342423937097316400352367922665337165210225900884209⟩
  | 3, 2 => ⟨-657006787130595320703356570089185607104654189436208, 659219376072827572353661614569737456886443063503930⟩
  | 4, 1 => ⟨-1267892240408874039165784726752372775599832063396179, 1270171700276999138250415971713702883705981128222254⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0540Geometry.ds, E8TAxisProd0540Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3087653530730151411700626283490255594630589131 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0540CertifiedArithmetic

end


