-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0464CertifiedArithmetic__14
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0464CertifiedArithmetic__14
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T19:40:55.990636+00:00
-- url     : https://prove2.me/theorems/d2a2606e-3ee1-4990-854a-03ff8ded235b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0464CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0465CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0464CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0465CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0466CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0467CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0468CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0469CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0470CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0471CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0472CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0473CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0474CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0475CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0476CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0477CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0464CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0465CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0466CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0467CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0468CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0469CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0470CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0471CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0472CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0473CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0474CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0475CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0476CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0477CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0464CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0465CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0466CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0467CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0468CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0469CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0470CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0471CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0472CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0473CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0474CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0475CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0476CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0477CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0464CertifiedArithmetic (+13 modules: GeneralCK/Certificates/E8TAxisProd0465CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0466CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0467CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0468CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0469CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0470CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0471CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0472CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0473CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0474CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0475CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0476CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0477CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0456GraphCenterA__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0457GraphCenterB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0458GraphCenterC__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0461GraphCenterD__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0456GraphWholeA__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0456GraphWholeB__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0462GraphWholeC__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0456GraphWholeD__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0445Geometry__26
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0465GraphWholeB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0466GraphWholeA__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0466GraphWholeD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0468GraphCenterB__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0468GraphCenterC__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0469GraphCenterD__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0470GraphCenterA__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0471GraphWholeC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0471Geometry__23
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0476GraphCenterB__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0476GraphCenterC__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0476GraphWholeB__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0477GraphWholeD__13

-- ===== source module GeneralCK.Certificates.E8TAxisProd0464CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0464CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0464GraphCenterA.qJetBox,
   E8TAxisProd0464GraphCenterB.qJetBox,
   E8TAxisProd0464GraphCenterC.qJetBox,
   E8TAxisProd0464GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0464GraphWholeA.qJetBox,
   E8TAxisProd0464GraphWholeB.qJetBox,
   E8TAxisProd0464GraphWholeC.qJetBox,
   E8TAxisProd0464GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨11410735146529347262616108291793726876142931621, 11410735146529347262616108291793797162157307128⟩
  | 0, 2 => ⟨36572422499646047612729448580435978163847018964, 36572422499646047612729448580436227786302138444⟩
  | 1, 1 => ⟨37124849470870024315373359391839732777724713420, 37124849470870024315373359391840171755853791471⟩
  | 0, 3 => ⟨80559243361607500366673607884697146863354517655, 80559243361607500366673607884697937116043021463⟩
  | 1, 2 => ⟨109798210787665925883156905340121127274980643861, 109798210787665925883156905340122511453660474995⟩
  | 2, 1 => ⟨111250564674531004449367242340919398177638745589, 111250564674531004449367242340921875955587818171⟩
  | 0, 4 => ⟨146927698947313273956236669982429021744982033795, 146927698947313273956236669982431634294286391725⟩
  | 1, 3 => ⟨222807778783743762879771272959597091932677816259, 222807778783743762879771272959601752679195379369⟩
  | 2, 2 => ⟨299472975630507708107359648699761595882343334034, 299472975630507708107359648699770071113200127557⟩
  | 3, 1 => ⟨302880182477247724540224441296542397607247359831, 302880182477247724540224441296557957514165962361⟩
  | 0, 5 => ⟨-456821748187680355269253591652041947999193991603625, 459682585742947122537599855026738017911244778957221⟩
  | 1, 4 => ⟨-888787266434150627071496256328296279306478236087215, 893047170757396473441627954365308355570196984844428⟩
  | 2, 3 => ⟨-1731491881667312100945501530732898929533530708377030, 1737582907514805382834698729683899040277516954948084⟩
  | 3, 2 => ⟨-3375863830716683511437069038506270152973464998891901, 3383825709727610919134502642609065515950870117239975⟩
  | 4, 1 => ⟨-6585435342199460319839177161502783682431206206560014, 6593572552760644115020319580131690696890167991407484⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0464Geometry.ds, E8TAxisProd0464Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 10670516526387667725118391242035125962690548836 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0464CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0465CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0465CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0465GraphCenterA.qJetBox,
   E8TAxisProd0465GraphCenterB.qJetBox,
   E8TAxisProd0465GraphCenterC.qJetBox,
   E8TAxisProd0465GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0465GraphWholeA.qJetBox,
   E8TAxisProd0465GraphWholeB.qJetBox,
   E8TAxisProd0465GraphWholeC.qJetBox,
   E8TAxisProd0465GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨10146108446238908327221707694736486229679442817, 10146108446238908327221707694736550379889013846⟩
  | 0, 2 => ⟨32814414988439886806134698285831758951554316174, 32814414988439886806134698285831984081437225757⟩
  | 1, 1 => ⟨33316794933782771831368407097003337264285918559, 33316794933782771831368407097003731563814524906⟩
  | 0, 3 => ⟨72896916393604580948560986292179510663373087111, 72896916393604580948560986292180221017524867762⟩
  | 1, 2 => ⟨99493751381015295584749917482599872557373852492, 99493751381015295584749917482601112723411167756⟩
  | 2, 1 => ⟨100828080864219438762896620533109744569989434647, 100828080864219438762896620533111959816251563227⟩
  | 0, 4 => ⟨134142702220025529634871116077301162099461507721, 134142702220025529634871116077303505779935051452⟩
  | 1, 3 => ⟨203862818031421167052099929128610527921373893260, 203862818031421167052099929128614698741195871841⟩
  | 2, 2 => ⟨274314629524591109020054530256499252577841983090, 274314629524591109020054530256506824590413327909⟩
  | 3, 1 => ⟨277478463325198821710743909629605387894038080588, 277478463325198821710743909629619270152429286199⟩
  | 0, 5 => ⟨-394604492435690240594171499530703555544614269206943, 397137770492331599683704804727391111473154607784621⟩
  | 1, 4 => ⟨-767012290421182517669413904540129306856553402470774, 770777874720388534021809749048563124743085448194203⟩
  | 2, 3 => ⟨-1492942834610477866457070922365069543250687623374031, 1498321145210598469052411889700771090178188691398722⟩
  | 3, 2 => ⟨-2908293326911160446943582638510818314517378478193816, 2915320023418380910127037007594611436298646899546077⟩
  | 4, 1 => ⟨-5668558419828066617986607010183445151506081889299627, 5675742158602764694102939930233131606727220826851531⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0465Geometry.ds, E8TAxisProd0465Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 9482769088465452138228685679343498025828074193 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0465CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0466CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0466CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0466GraphCenterA.qJetBox,
   E8TAxisProd0466GraphCenterB.qJetBox,
   E8TAxisProd0466GraphCenterC.qJetBox,
   E8TAxisProd0466GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0466GraphWholeA.qJetBox,
   E8TAxisProd0466GraphWholeB.qJetBox,
   E8TAxisProd0466GraphWholeC.qJetBox,
   E8TAxisProd0466GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨11365082507509387054212208012513296367279610012, 11365082507509387054212208012513366511935567513⟩
  | 0, 2 => ⟨36471838156721572650686620405512789672265786840, 36471838156721572650686620405513038746819757969⟩
  | 1, 1 => ⟨36987775655551234487306058662397560795989764641, 36987775655551234487306058662397998791810771204⟩
  | 0, 3 => ⟨80375766080809439189220124762512462477604500808, 80375766080809439189220124762513250982988042514⟩
  | 1, 2 => ⟨109519990008311651810715318934378726151016036743, 109519990008311651810715318934380107223916712209⟩
  | 2, 1 => ⟨110876651232670165678674845904954841740193005150, 110876651232670165678674845904957313891819651848⟩
  | 0, 4 => ⟨146636035300295892379468697777901898532311378231, 146636035300295892379468697777904505203239663154⟩
  | 1, 3 => ⟨222345606374746114061322826398736790715986985468, 222345606374746114061322826398741440908750127315⟩
  | 2, 2 => ⟨298788743594920163329816908271145596485641051843, 298788743594920163329816908271154052396126779824⟩
  | 3, 1 => ⟨301972035031710184419347076423913927367514201370, 301972035031710184419347076423929451538082054323⟩
  | 0, 5 => ⟨-455502548858854310446125529222938276646655827056646, 458356843049130741479430232201071149767675342666669⟩
  | 1, 4 => ⟨-886205902526000404950888426713384639051998681877779, 890456016212786970553081330071262960426538450606657⟩
  | 2, 3 => ⟨-1726434538953802170361321548617757719227793591560173, 1732511623448427360108028305104468935479432590318089⟩
  | 3, 2 => ⟨-3365947566670753167804955286674689286164419022529794, 3373891381110973374955493833590399725417659552999164⟩
  | 4, 1 => ⟨-6565980248125737709749984574389154535656056596379987, 6574099025276205177363930613294207030909340167780986⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0466Geometry.ds, E8TAxisProd0466Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 10627545023492533056206570283236261023792535941 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0466CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0467CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0467CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0467GraphCenterA.qJetBox,
   E8TAxisProd0467GraphCenterB.qJetBox,
   E8TAxisProd0467GraphCenterC.qJetBox,
   E8TAxisProd0467GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0467GraphWholeA.qJetBox,
   E8TAxisProd0467GraphWholeB.qJetBox,
   E8TAxisProd0467GraphWholeC.qJetBox,
   E8TAxisProd0467GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨10105147334574923658463190082510352769316887698, 10105147334574923658463190082510416791053303542⟩
  | 0, 2 => ⟨32723398571934068577068809143937830225135902648, 32723398571934068577068809143938054860774444276⟩
  | 1, 1 => ⟨33192586901176450688481829055088519426572850142, 33192586901176450688481829055088912842643347821⟩
  | 0, 3 => ⟨72729405991032531689538494182452382167408284249, 72729405991032531689538494182453090946895782068⟩
  | 1, 2 => ⟨99239189714281761378526661185194297318462405757, 99239189714281761378526661185195534691949096737⟩
  | 2, 1 => ⟨100485583356141741284482365701786719547347458509, 100485583356141741284482365701788929742143501586⟩
  | 0, 4 => ⟨133874020633456967006781505600553656267002245096, 133874020633456967006781505600555994644331967491⟩
  | 1, 3 => ⟨203435977131051720232133599140687323949453475146, 203435977131051720232133599140691485263208522687⟩
  | 2, 2 => ⟨273681580974143714866118038333065326099785113050, 273681580974143714866118038333072880725832887302⟩
  | 3, 1 => ⟨276637467059938967246737483749069199105358508111, 276637467059938967246737483749083049228911250456⟩
  | 0, 5 => ⟨-393438463297104908164721614430471414937800751631441, 395965899993953356211336416489623385417909374280612⟩
  | 1, 4 => ⟨-764732120521350112627100585255511827766710225224436, 768488966963311165904816711299826166848524818215166⟩
  | 2, 3 => ⟨-1488478323697381438585744815863717664514776610258078, 1493844188904543509850221873589739842496415375644518⟩
  | 3, 2 => ⟨-2899544701981641439860501497455855237862448035639513, 2906555254374926013399767368764586025781525757820848⟩
  | 4, 1 => ⟨-5651404324234940647545940809592011894312623512954119, 5658571533197055318427598868325121612610131710523655⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0467Geometry.ds, E8TAxisProd0467Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 9444235811271769631092354068601237856851297355 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0467CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0468CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0468CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0468GraphCenterA.qJetBox,
   E8TAxisProd0468GraphCenterB.qJetBox,
   E8TAxisProd0468GraphCenterC.qJetBox,
   E8TAxisProd0468GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0468GraphWholeA.qJetBox,
   E8TAxisProd0468GraphWholeB.qJetBox,
   E8TAxisProd0468GraphWholeC.qJetBox,
   E8TAxisProd0468GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨9011796146538823093556949406097976447018868473, 9011796146538823093556949406098035045472640790⟩
  | 0, 2 => ⟨29410886755271784187879083293444671764208798865, 29410886755271784187879083293444874871066870017⟩
  | 1, 1 => ⟨29867307474918603133073624318875152372428784498, 29867307474918603133073624318875506587987896761⟩
  | 0, 3 => ⟨65889568468476821338616149566085841144327601404, 65889568468476821338616149566086479666539224751⟩
  | 1, 2 => ⟨90059488010074390591615699380535670955509246455, 90059488010074390591615699380536781871986715043⟩
  | 2, 1 => ⟨91284252497116775142176351747945734504126613301, 91284252497116775142176351747947714468160344692⟩
  | 0, 4 => ⟨122338799032055493525366119817406016731857253830, 122338799032055493525366119817408118441819552407⟩
  | 1, 3 => ⟨186340142803058175360823811229378115491003784183, 186340142803058175360823811229381845750582314082⟩
  | 2, 2 => ⟨251023075232314724651114251649892278009393591903, 251023075232314724651114251649899038417637182914⟩
  | 3, 1 => ⟨253959303912465077067825279201638970749929027359, 253959303912465077067825279201651346775791583848⟩
  | 0, 5 => ⟨-339744277970288723839072168453844704108809355234357, 341984548670357896175439634293520163893313057657947⟩
  | 1, 4 => ⟨-659712484696293914093094980690761565171128532102855, 663036323020180751830047317362757498629391972100561⟩
  | 2, 3 => ⟨-1282894287563209842872534898002377870054997782692406, 1287636132535316072711962118228546414995688424157111⟩
  | 3, 2 => ⟨-2496867531302366097279631374238763044785057633039898, 2503059449498938453865080118208535644412896180972695⟩
  | 4, 1 => ⟨-4862333237893475710127514365669400934554619816250217, 4868666037185661061501984908982363625764619396906238⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0468Geometry.ds, E8TAxisProd0468Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 8418001749924805443851041435215160020122600420 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0468CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0469CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0469CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0469GraphCenterA.qJetBox,
   E8TAxisProd0469GraphCenterB.qJetBox,
   E8TAxisProd0469GraphCenterC.qJetBox,
   E8TAxisProd0469GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0469GraphWholeA.qJetBox,
   E8TAxisProd0469GraphWholeB.qJetBox,
   E8TAxisProd0469GraphWholeC.qJetBox,
   E8TAxisProd0469GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨7995465323052084977830465333852021044679173524, 7995465323052084977830465333852074617792113839⟩
  | 0, 2 => ⟨26331743223574059997889760159843789738974943684, 26331743223574059997889760159843973043337160181⟩
  | 1, 1 => ⟨26745998445172534456740522993930239901464431688, 26745998445172534456740522993930558158520966610⟩
  | 0, 3 => ⟨59487835825533531895681498189931664759277419751, 59487835825533531895681498189932238709186696510⟩
  | 1, 2 => ⟨81430605515473816874703494190181285024965710590, 81430605515473816874703494190182279966965592538⟩
  | 2, 1 => ⟨82553718033854795096505862386842655186791724191, 82553718033854795096505862386844424348610819953⟩
  | 0, 4 => ⟨111448319241450100695426454166230288202237452938, 111448319241450100695426454166232172181979420135⟩
  | 1, 3 => ⟨170143562339878686206533068809976601077069635382, 170143562339878686206533068809979935310108923920⟩
  | 2, 2 => ⟨229473365417996229146260769894676475374094863560, 229473365417996229146260769894682506851610630359⟩
  | 3, 1 => ⟨232196645050110676644624202474899347728581816291, 232196645050110676644624202474910372175172122979⟩
  | 0, 5 => ⟨-291513421065276477987117589501886228202781047210230, 293492071740460989360388978100590281429321313133257⟩
  | 1, 4 => ⟨-565448982321361521876903848337178365883353095221881, 568378782341874475462547379529137971707895708601818⟩
  | 2, 3 => ⟨-1098499169011282082836753918756914710020503514010659, 1102673674925716879117875160576543509803318990489740⟩
  | 3, 2 => ⟨-2135949956267323114957748726690564796602048622717528, 2141398034862404161483120310531167126209478184508335⟩
  | 4, 1 => ⟨-4155595719794368056641756055148227408035218286274436, 4161170282613328708419072635241042154340642583690362⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0469Geometry.ds, E8TAxisProd0469Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 7464509905037561408829537493878199547341512619 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0469CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0470CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0470CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0470GraphCenterA.qJetBox,
   E8TAxisProd0470GraphCenterB.qJetBox,
   E8TAxisProd0470GraphCenterC.qJetBox,
   E8TAxisProd0470GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0470GraphWholeA.qJetBox,
   E8TAxisProd0470GraphWholeB.qJetBox,
   E8TAxisProd0470GraphWholeC.qJetBox,
   E8TAxisProd0470GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨8975083974516409934263357928958997265856239758, 8975083974516409934263357928959055747485215909⟩
  | 0, 2 => ⟨29328620307435806511066872790560339202678759491, 29328620307435806511066872790560541863644135396⟩
  | 1, 1 => ⟨29754878590505088428273370671868296225989666270, 29754878590505088428273370671868649647028131739⟩
  | 0, 3 => ⟨65736799595985256337416644513992724887124176564, 65736799595985256337416644513993361991288941209⟩
  | 1, 2 => ⟨89826809124254753026376451923082654461287876556, 89826809124254753026376451923083762868296589043⟩
  | 2, 1 => ⟨90970839600889241498884268508107330024127765107, 90970839600889241498884268508109305454979460438⟩
  | 0, 4 => ⟨122091469911128457464713567993302456359002789875, 122091469911128457464713567993304553298978429731⟩
  | 1, 3 => ⟨185946193796735721102474020960657447650615951843, 185946193796735721102474020960661169364857578118⟩
  | 2, 2 => ⟨250437742680026146637415104819739745019259401625, 250437742680026146637415104819746489803251822744⟩
  | 3, 1 => ⟨253180955142550259606789982943923562969734837963, 253180955142550259606789982943935910130583113745⟩
  | 0, 5 => ⟨-338719346230262834866867354498902343655780070531555, 340954391448071326084663982339010296325692072875761⟩
  | 1, 4 => ⟨-657709613135082402411458136106261363584993711225749, 661025634624130818394037365449703397845773729758524⟩
  | 2, 3 => ⟨-1278975262086497986514114619943501678346439085399771, 1283705967243732536785541979091964641410536363540965⟩
  | 3, 2 => ⟨-2489192663245366291477270301549283521857738762038997, 2495370110427297444638714966088009570981893592960780⟩
  | 4, 1 => ⟨-4847293869780093169248653762869039234582922810098350, 4853611796175670551900354936184136772719090775985036⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0470Geometry.ds, E8TAxisProd0470Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 8383485417251934965868669136675028363093464101 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0470CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0471CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0471CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0471GraphCenterA.qJetBox,
   E8TAxisProd0471GraphCenterB.qJetBox,
   E8TAxisProd0471GraphCenterC.qJetBox,
   E8TAxisProd0471GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0471GraphWholeA.qJetBox,
   E8TAxisProd0471GraphWholeB.qJetBox,
   E8TAxisProd0471GraphWholeC.qJetBox,
   E8TAxisProd0471GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨7962597082634129423885940957808658521498834932, 7962597082634129423885940957808711988319805069⟩
  | 0, 2 => ⟨26257470438522989062244468335020841230047953528, 26257470438522989062244468335021024132089537405⟩
  | 1, 1 => ⟨26644343018277514406604915982381320148670453603, 26644343018277514406604915982381637691221899113⟩
  | 0, 3 => ⟨59348667649903392499293661819390486656414501091, 59348667649903392499293661819391059328639895102⟩
  | 1, 2 => ⟨81218153208921291372226088235141030294964446294, 81218153208921291372226088235142022981607878299⟩
  | 2, 1 => ⟨82267214457934835730362606116860679626849878077, 82267214457934835730362606116862444721025086655⟩
  | 0, 4 => ⟨111220829358331638330567511991488160268627271490, 111220829358331638330567511991490039948395929785⟩
  | 1, 3 => ⟨169780238979368543568063308696448145554806906045, 169780238979368543568063308696451472098747929070⟩
  | 2, 2 => ⟨228932527339340078856994332613575521546743051999, 228932527339340078856994332613581538980494467648⟩
  | 3, 1 => ⟨231476759421684646922640911750992616587552470783, 231476759421684646922640911751003615111611831592⟩
  | 0, 5 => ⟨-290615926021876259562080219518930291341426777260028, 292589925705478132055922462323720702626762769657878⟩
  | 1, 4 => ⟨-563696444613728617794898372330131016288679861042395, 566619288515432367408452524318341575163363591937120⟩
  | 2, 3 => ⟨-1095072358225172975478863865461554716448756308981607, 1099236946884104678369201987688038486465379456244172⟩
  | 3, 2 => ⟨-2129243537056657870392802610415026472912853845101708, 2134678714923190853300458842265415502405451005843671⟩
  | 4, 1 => ⟨-4142462793848986232760180592958944920933730060335769, 4148024044114589073692263597455806149857658476937375⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0471Geometry.ds, E8TAxisProd0471Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 7433625397475910328822518173158102197745001742 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0471CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0472CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0472CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0472GraphCenterA.qJetBox,
   E8TAxisProd0472GraphCenterB.qJetBox,
   E8TAxisProd0472GraphCenterC.qJetBox,
   E8TAxisProd0472GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0472GraphWholeA.qJetBox,
   E8TAxisProd0472GraphWholeB.qJetBox,
   E8TAxisProd0472GraphWholeC.qJetBox,
   E8TAxisProd0472GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨11319555455671357932947343081466752457461671362, 11319555455671357932947343081466822461045550110⟩
  | 0, 2 => ⟨36371482932668585383414907989276316776247415905, 36371482932668585383414907989276565304075115641⟩
  | 1, 1 => ⟨36851049255350279557543983223924555829384234662, 36851049255350279557543983223924992845026857484⟩
  | 0, 3 => ⟨80192653061097608629558608684157334134243670552, 80192653061097608629558608684158120896076531999⟩
  | 1, 2 => ⟨109242346426531101717447691282086596771958293937, 109242346426531101717447691282087974745783758000⟩
  | 2, 1 => ⟨110503592285365577781080756867770166851586338261, 110503592285365577781080756867772633389077783093⟩
  | 0, 4 => ⟨146344881075282687969760485167426567220723194278, 146344881075282687969760485167429168025838144992⟩
  | 1, 3 => ⟨221884262440921174457710388148426347293199471846, 221884262440921174457710388148430986954721266581⟩
  | 2, 2 => ⟨298105783986953439080508429155650687046157881736, 298105783986953439080508429155659123677407808006⟩
  | 3, 1 => ⟨301065729635324536358069283070364973122586179588, 301065729635324536358069283070380461632827565696⟩
  | 0, 5 => ⟨-454186546562801038185596255557018120855411472638215, 457034311226550241951344020454286513753781966822534⟩
  | 1, 4 => ⟨-883630816270981580754877192647333394194539062248472, 887871159877445062855438311540900195223972711269878⟩
  | 2, 3 => ⟨-1721389538705737153690734044885441510579529528649903, 1727452710623378222633659575862610396280415003306546⟩
  | 3, 2 => ⟨-3356055590045601965495181374394629516606974767654260, 3363981376131459407852159063705685826661528412109707⟩
  | 4, 1 => ⟨-6546572977331199354694162220620743914847936879764990, 6554673356229234713636693990732917102649387589840085⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0472Geometry.ds, E8TAxisProd0472Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 10584692352573563251875399188842325288498460987 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0472CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0473CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0473CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0473GraphCenterA.qJetBox,
   E8TAxisProd0473GraphCenterB.qJetBox,
   E8TAxisProd0473GraphCenterC.qJetBox,
   E8TAxisProd0473GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0473GraphWholeA.qJetBox,
   E8TAxisProd0473GraphWholeB.qJetBox,
   E8TAxisProd0473GraphWholeC.qJetBox,
   E8TAxisProd0473GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨10064299862651492272781538964231908178075787666, 10064299862651492272781538964231972071598674985⟩
  | 0, 2 => ⟨32632591333646955821671812582011799745377604699, 32632591333646955821671812582012023887832725962⟩
  | 1, 1 => ⟨33068696737384619075862934812798431324422432945, 33068696737384619075862934812798823858954064948⟩
  | 0, 3 => ⟨72562231145330700031868211503590814045607679701, 72562231145330700031868211503591521253822202765⟩
  | 1, 2 => ⟨98985161117476414251837936089714570630494327653, 98985161117476414251837936089715805217476574807⟩
  | 2, 1 => ⟨100143876418258358861636630520779683176869444891, 100143876418258358861636630520781888331180530436⟩
  | 0, 4 => ⟨133605811103497252417629267522524341347309027420, 133605811103497252417629267522526674432880417755⟩
  | 1, 3 => ⟨203009905937753280149088251483594844779330834095, 203009905937753280149088251483598996607404252061⟩
  | 2, 2 => ⟨273049716885534791720851718964779078785222876270, 273049716885534791720851718964786616061980619443⟩
  | 3, 1 => ⟨275798187824256270699127665728281782653728483201, 275798187824256270699127665728295600711239610325⟩
  | 0, 5 => ⟨-392275363156312246419352065233734329167525671366243, 394796970813309585707105096449041580558410059166522⟩
  | 1, 4 => ⟨-762457699708300500655003623352701689877230725142609, 766205826531722818326153087565299332452928250613342⟩
  | 2, 3 => ⟨-1484025111598084870664359516340372803824468197607517, 1489378556819978039126748989813718073574664188420329⟩
  | 3, 2 => ⟨-2890818301991454406415057512238654064600261015202901, 2897812741970303930893468229806356470462966160815002⟩
  | 4, 1 => ⟨-5634293973321330964770888666332707152500233017176245, 5641444682509257905174612304585558657128509697574432⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0473Geometry.ds, E8TAxisProd0473Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 9405809991957936872019051044966547390987913865 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0473CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0474CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0474CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0474GraphCenterA.qJetBox,
   E8TAxisProd0474GraphCenterB.qJetBox,
   E8TAxisProd0474GraphCenterC.qJetBox,
   E8TAxisProd0474GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0474GraphWholeA.qJetBox,
   E8TAxisProd0474GraphWholeB.qJetBox,
   E8TAxisProd0474GraphWholeC.qJetBox,
   E8TAxisProd0474GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨11274153704901083750785952143010400465155514809, 11274153704901083750785952143010470327953067476⟩
  | 0, 2 => ⟨36271356372558504569013513203107499983819232323, 36271356372558504569013513203107747966093051086⟩
  | 1, 1 => ⟨36714669549417087388836762327758263296314726684, 36714669549417087388836762327758699333904139703⟩
  | 0, 3 => ⟨80009903666196988533821868044668869161532123891, 80009903666196988533821868044669654183560646563⟩
  | 1, 2 => ⟨108965279007573104518812029551841247787878595067, 108965279007573104518812029551842622669318655760⟩
  | 2, 1 => ⟨110131386243407802124206400918083012031215786770, 110131386243407802124206400918085472966733640409⟩
  | 0, 4 => ⟨146054235468494242167572163462377819191766413646, 146054235468494242167572163462380414143604775488⟩
  | 1, 3 => ⟨221423745634153980739300513007302436928364765048, 221423745634153980739300513007307066081112156762⟩
  | 2, 2 => ⟨297424094687056220053871351618983568789547258204, 297424094687056220053871351618991986182613094475⟩
  | 3, 1 => ⟨300161263115873780655069067039075726700899257092, 300161263115873780655069067039091179626685238758⟩
  | 0, 5 => ⟨-452873735716807592353113429817094326335036151164046, 455714984660960426106740663919369314547879329291380⟩
  | 1, 4 => ⟨-881061996704039858345084634487917765808621485491266, 885292590740044469610007143810982699300821946551933⟩
  | 2, 3 => ⟨-1716356859336393413537556284150822703702355088126053, 1722406147383644685156656733795394682556701513322269⟩
  | 3, 2 => ⟨-3346187858291338565897124363636800671334456888058510, 3354095652145386500857088129871043333751882150044561⟩
  | 4, 1 => ⟨-6527213445878301386915777612722153452656973961405020, 6535295461572163444770808560652023484352879299458518⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0474Geometry.ds, E8TAxisProd0474Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 10541958241416817063381653270112027920577025805 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0474CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0475CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0475CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0475GraphCenterA.qJetBox,
   E8TAxisProd0475GraphCenterB.qJetBox,
   E8TAxisProd0475GraphCenterC.qJetBox,
   E8TAxisProd0475GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0475GraphWholeA.qJetBox,
   E8TAxisProd0475GraphWholeB.qJetBox,
   E8TAxisProd0475GraphWholeC.qJetBox,
   E8TAxisProd0475GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨10023565769257840989548506172683557679122271707, 10023565769257840989548506172683621444690725982⟩
  | 0, 2 => ⟨32541992854501061033342027641028306744009635540, 32541992854501061033342027641028530394340037167⟩
  | 1, 1 => ⟨32945123776670874649618933287058726398697001173, 32945123776670874649618933287059118053604938167⟩
  | 0, 3 => ⟨72395391266893772621426285117407020526064982011, 72395391266893772621426285117407726166390661910⟩
  | 1, 2 => ⟨98731664629247134422900232714507283609045577207, 98731664629247134422900232714508515415556801139⟩
  | 2, 1 => ⟨99802958571221883364529948674459323045333952204, 99802958571221883364529948674461523170118104526⟩
  | 0, 4 => ⟨133338072885612190371958484154108542353236735477, 133338072885612190371958484154110870158411714901⟩
  | 1, 3 => ⟨202584603201105883119746783714466534347508227428, 202584603201105883119746783714470676710243520832⟩
  | 2, 2 => ⟨272419035291484944766971630429506575280908285830, 272419035291484944766971630429514095245533846829⟩
  | 3, 1 => ⟨274960622673228003686384479205672840959529465000, 274960622673228003686384479205686627019657020367⟩
  | 0, 5 => ⟨-391115186554251550292944386091298173749176037466816, 393630977465313200039117819957184064334578728014209⟩
  | 1, 4 => ⟨-760189017258818628412364229461423702176610827182509, 763928442665652453288075131301046815430785580524948⟩
  | 2, 3 => ⟨-1479583177201835371629100991094796349066327975809926, 1484924227793417680979055566752056594101525804728956⟩
  | 3, 2 => ⟨-2882114085330895664986040310548002315757117343856592, 2889092444529454962409038896252889872481799153960431⟩
  | 4, 1 => ⟨-5617227285011135193273410450706772815856095859122747, 5624361524401705706127709259211263514249331425902042⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0475Geometry.ds, E8TAxisProd0475Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 9367491382172982930561177242855552904989587755 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0475CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0476CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0476CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0476GraphCenterA.qJetBox,
   E8TAxisProd0476GraphCenterB.qJetBox,
   E8TAxisProd0476GraphCenterC.qJetBox,
   E8TAxisProd0476GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0476GraphWholeA.qJetBox,
   E8TAxisProd0476GraphWholeB.qJetBox,
   E8TAxisProd0476GraphWholeC.qJetBox,
   E8TAxisProd0476GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨8938474516283585282441692883819635303559769327, 8938474516283585282441692883819693668599437395⟩
  | 0, 2 => ⟨29246544627578517427055338878775520027616756913, 29246544627578517427055338878775722243647592845⟩
  | 1, 1 => ⟨29642740247112499548655438049329039656814384084, 29642740247112499548655438049329392285061780753⟩
  | 0, 3 => ⟨65584339611451138502335823750492383323942139284, 65584339611451138502335823750493019013120102736⟩
  | 1, 2 => ⟨89594622227603576576419508944000007695655634705, 89594622227603576576419508944001113598644911821⟩
  | 2, 1 => ⟨90658157680927014848688683681355770830690670648, 90658157680927014848688683681357741738250687449⟩
  | 0, 4 => ⟨121844578185103169018554091999272929374739955485, 121844578185103169018554091999275021554994321921⟩
  | 1, 3 => ⟨185552959940013702421632171222008140849442901936, 185552959940013702421632171222011854036750707177⟩
  | 2, 2 => ⟨249853512903106026131329725433098802825455501642, 249853512903106026131329725433105532018840178916⟩
  | 3, 1 => ⟨252404207298525628771040621646900181716324573671, 252404207298525628771040621646912500074352215091⟩
  | 0, 5 => ⟨-337697076443476112169035914070493646218858278987651, 339926907262502308249094232530267048810877579265662⟩
  | 1, 4 => ⟨-655711964184775660193379163310189637524905524705738, 659020185264223507275542150123452226037805067435917⟩
  | 2, 3 => ⟨-1275066496257152169863854513247109804270216410899508, 1279786084540055200617062843926377333015454869836900⟩
  | 3, 2 => ⟨-2481537967325405414805405870971802579670998967104107, 2487700972289855829086228173228161049918097273490269⟩
  | 4, 1 => ⟨-4832294188646540464201127772258589987189593257374687, 4838597269965702898781808558624454432712585097487458⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0476Geometry.ds, E8TAxisProd0476Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 8349066148179290665991468345377144259220976497 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0476CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0477CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0477CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0477GraphCenterA.qJetBox,
   E8TAxisProd0477GraphCenterB.qJetBox,
   E8TAxisProd0477GraphCenterC.qJetBox,
   E8TAxisProd0477GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0477GraphWholeA.qJetBox,
   E8TAxisProd0477GraphWholeB.qJetBox,
   E8TAxisProd0477GraphWholeC.qJetBox,
   E8TAxisProd0477GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨7929821574546370200614737659240706188134330498, 7929821574546370200614737659240759548876999876⟩
  | 0, 2 => ⟨26183371436070554772764505855371198666628027288, 26183371436070554772764505855371381167214369749⟩
  | 1, 1 => ⟨26542952873092419437040032846400660323855834923, 26542952873092419437040032846400977153460800785⟩
  | 0, 3 => ⟨59209783583292086789365856371856170892479435512, 59209783583292086789365856371856742289785348018⟩
  | 1, 2 => ⟨81006154641161968658884208750917454244163933862, 81006154641161968658884208750918444680365186420⟩
  | 2, 1 => ⟨81981386287646992161845480486767943973620242830, 81981386287646992161845480486769705009061833040⟩
  | 0, 4 => ⟨110993744704722671963315928773472237800997837029, 110993744704722671963315928773474113190096600011⟩
  | 1, 3 => ⟨169417580091139249919157919456693086481081327440, 169417580091139249919157919456696405352585573438⟩
  | 2, 2 => ⟨228392716123463218458071197856848146127350195202, 228392716123463218458071197856854149547783418573⟩
  | 3, 1 => ⟨230758366798805429623956072368039925569294654889, 230758366798805429623956072368050898227090149092⟩
  | 0, 5 => ⟨-289720837543678980604631399801654992999036872504281, 291690196148253866327336321937813310713274300982651⟩
  | 1, 4 => ⟨-561948626148415117829460966956247871382629361946577, 564864528608154893737004848636467534089785795051119⟩
  | 2, 3 => ⟨-1091654813822423822315907126863594267193755048848601, 1095809505706611870057632980370501809287037927560613⟩
  | 3, 2 => ⟨-2122555328494520015769040820396774730570869901512862, 2127977631313491832975655107786886969760461695689085⟩
  | 4, 1 => ⟨-4129365679023728633558136389716975523947934394324272, 4134913641481322425423923352089697131533795454753025⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0477Geometry.ds, E8TAxisProd0477Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 7402828464135015190171650183033533631342095527 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0477CertifiedArithmetic

end


