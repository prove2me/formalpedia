-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0016CertifiedArithmetic__15
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0016CertifiedArithmetic__15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T16:56:21.743004+00:00
-- url     : https://prove2.me/theorems/170fb124-6654-409c-9cd3-c394e0351031
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0016CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisZero0017CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0016CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisZero0017CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0018CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0019CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0020CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0021CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0022CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0023CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0024CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0025CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0026CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0027CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0028CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0029CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0030CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0016CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisZero0017CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0018CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0019CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0020CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0021CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0022CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0023CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0024CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0025CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0026CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0027CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0028CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0029CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0030CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0016CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisZero0017CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0018CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0019CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0020CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0021CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0022CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0023CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0024CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0025CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0026CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0027CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0028CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0029CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0030CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0016CertifiedArithmetic (+14 modules: GeneralCK/Certificates/E8TAxisZero0017CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0018CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0019CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0020CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0021CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0022CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0023CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0024CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0025CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0026CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0027CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0028CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0029CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0030CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000GraphCenterA__21
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000GraphCenterB__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0012GraphCenterC__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000GraphCenterD__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000GraphWholeA__20
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000GraphWholeB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000GraphWholeC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000GraphWholeD__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularInverseBoxes
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000Geometry__22
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0017GraphCenterB__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0018GraphCenterD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0018GraphWholeB__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0018GraphWholeC__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0018GraphWholeD__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0021GraphWholeA__22
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0022GraphCenterA__22
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0023Geometry__20
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0025GraphCenterC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0029GraphCenterB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0030GraphWholeC__15

-- ===== source module GeneralCK.Certificates.E8TAxisZero0016CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0016CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0016GraphCenterA.qJetBox,
   E8TAxisZero0016GraphCenterB.qJetBox,
   E8TAxisZero0016GraphCenterC.qJetBox,
   E8TAxisZero0016GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0016GraphWholeA.qJetBox,
   E8TAxisZero0016GraphWholeB.qJetBox,
   E8TAxisZero0016GraphWholeC.qJetBox,
   E8TAxisZero0016GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨300211243351065784939054017541972008733, 300211243351065784939054018018610167831⟩
  | 0, 2 => ⟨13930716343527186419215537550871432924776, 13930716343527186419215537552680108574519⟩
  | 1, 1 => ⟨14194135385519898071714888583150458862218, 14194135385519898071714888585689737658789⟩
  | 0, 3 => ⟨315453262378812939524122454878984702151936, 315453262378812939524122454881485326091593⟩
  | 1, 2 => ⟨529940028106571636371503226302737093839934, 529940028106571636371503226306093515372101⟩
  | 2, 1 => ⟨537472613794029968642349915067619160551886, 537472613794029968642349915072424268577136⟩
  | 0, 4 => ⟨3034719028776701840725737447511520505007416, 3034719028776701840725737447655309377117090⟩
  | 1, 3 => ⟨9061323981111061357272033539568295169281242, 9061323981111061357272033539579372567797628⟩
  | 2, 2 => ⟨15159456921463412444003754714845871489160470, 15159456921463412444003754714861632943895042⟩
  | 3, 1 => ⟨15303866018257931749933479180944730628408498, 15303866018257931749933479180968132172896416⟩
  | 0, 5 => ⟨-45826869311247635270443069268566888462996887776, 45847827670715625173808936227800697197123428283⟩
  | 1, 4 => ⟨-70434495344645792575773724658276369647045894077, 70123147572625478084292175138328152005365814528⟩
  | 2, 3 => ⟨-111296288456144469130332092078583965045644177383, 110631185627477486620586754933100120263831004147⟩
  | 3, 2 => ⟨-176614329430226522579609619558792088846310263113, 175612525783784999011896774659066317401056335067⟩
  | 4, 1 => ⟨-276521317807254579454998258580226230092729362972, 275597617826786105640604163868482090294524912050⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0016Geometry.ds, E8TAxisZero0016Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 196081565182804985449297790269418151509 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0016CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0017CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0017CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0017GraphCenterA.qJetBox,
   E8TAxisZero0017GraphCenterB.qJetBox,
   E8TAxisZero0017GraphCenterC.qJetBox,
   E8TAxisZero0017GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0017GraphWholeA.qJetBox,
   E8TAxisZero0017GraphWholeB.qJetBox,
   E8TAxisZero0017GraphWholeC.qJetBox,
   E8TAxisZero0017GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨665194682077750464088621681013999224106361, 665194682077750464088621681015158528502116⟩
  | 0, 2 => ⟨6994260986210369347547043170000221007149640, 6994260986210369347547043170003370247574080⟩
  | 1, 1 => ⟨7052220000990698725049661610884667914396992, 7052220000990698725049661610888984227802762⟩
  | 0, 3 => ⟨37418245738923187261699140411462827179097217, 37418245738923187261699140412398966489890350⟩
  | 1, 2 => ⟨60794969505651713407143107451178317967403750, 60794969505651713407143107451186941797695683⟩
  | 2, 1 => ⟨61181748319218245567141054050258947254894134, 61181748319218245567141054050271420440654165⟩
  | 0, 4 => ⟨105799189837612975048405790313287360277453736, 105799189837612975048405795524439856849983934⟩
  | 1, 3 => ⟨260659826425944331879640227860436099179737029, 260659826425944331879640227862438933393995632⟩
  | 2, 2 => ⟨416321853237603177016411556426676009542976476, 416321853237603177016411556426711478067948521⟩
  | 3, 1 => ⟨418223962209544410408577279611854721109411459, 418223962209544410408577279611910026444245269⟩
  | 0, 5 => ⟨-505101222181729382699617934364267525848396520402, 513573072755302435706988635145482166184783829645⟩
  | 1, 4 => ⟨-847406968435458682694920823654982146777382188238, 850969534201294489397487991136312390841884771816⟩
  | 2, 3 => ⟨-1445828802150616807353701522423227473589230637950, 1443377681263783675174841740700869057286488252594⟩
  | 3, 2 => ⟨-2475396994484463130232038690194479792316702462395, 2467585744408526187048090261398978374938134902035⟩
  | 4, 1 => ⟨-4216347798155317834952133798538558632868754335515, 4211646090078595640536940953367582049750369162420⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0017Geometry.ds, E8TAxisZero0017Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 512158974972576060314190279180699394898278 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0017CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0018CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0018CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0018GraphCenterA.qJetBox,
   E8TAxisZero0018GraphCenterB.qJetBox,
   E8TAxisZero0018GraphCenterC.qJetBox,
   E8TAxisZero0018GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0018GraphWholeA.qJetBox,
   E8TAxisZero0018GraphWholeB.qJetBox,
   E8TAxisZero0018GraphWholeC.qJetBox,
   E8TAxisZero0018GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨472643404391835590557382779259175788545382, 472643404391835590557382779260265805854565⟩
  | 0, 2 => ⟨5287059626056185531439693090967990312359826, 5287059626056185531439693090970994338157866⟩
  | 1, 1 => ⟨5333827442486660073647786620722652629913031, 5333827442486660073647786620726762491281352⟩
  | 0, 3 => ⟨29924065224944192313381892376595682045494853, 29924065224944192313381892377469789556475041⟩
  | 1, 2 => ⟨48796184626043372583707157900362043124591729, 48796184626043372583707157900370105322551243⟩
  | 2, 1 => ⟨49126678760011745651299277044053695315683437, 49126678760011745651299277044065284523881541⟩
  | 0, 4 => ⟨87530435075142653083380277382427030299169596, 87530435075142653083380282248247513615590190⟩
  | 1, 3 => ⟨219848226550131091931314771219770198826645992, 219848226550131091931314771221759193488329924⟩
  | 2, 2 => ⟨352896882893585605160861122129565641623411973, 352896882893585605160861122129598728141099880⟩
  | 3, 1 => ⟨354599998277132254688445947065304830439058179, 354599998277132254688445947065356216305895927⟩
  | 0, 5 => ⟨-473964557351441330076213088348072286531584531423, 481312365576129822917880211169789745971109360458⟩
  | 1, 4 => ⟨-792010469069956708339236756973250994822214087593, 794541312359710206750346756933960257383596482068⟩
  | 2, 3 => ⟨-1346231014072743801507748955975555371580765692437, 1342848501352022529904209010358139863585788152498⟩
  | 3, 2 => ⟨-2295696226651881103979882353682378873628542257442, 2287002605583346862141627791265223204470896748459⟩
  | 4, 1 => ⟨-3892337924533255239832329402920589274865141200282, 3886498040084464251904876205886700933570075169548⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0018Geometry.ds, E8TAxisZero0018Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 353881775513915631168467927774028873487514 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0018CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0019CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0019CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0019GraphCenterA.qJetBox,
   E8TAxisZero0019GraphCenterB.qJetBox,
   E8TAxisZero0019GraphCenterC.qJetBox,
   E8TAxisZero0019GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0019GraphWholeA.qJetBox,
   E8TAxisZero0019GraphWholeB.qJetBox,
   E8TAxisZero0019GraphWholeC.qJetBox,
   E8TAxisZero0019GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨328219527029119112238959747153201639836162, 328219527029119112238959747154225265510554⟩
  | 0, 2 => ⟨3925084757099624094692117829031727609612883, 3925084757099624094692117829034594718659310⟩
  | 1, 1 => ⟨3962325962338886438968561865043099010308974, 3962325962338886438968561865047015795230688⟩
  | 0, 3 => ⟨23625694919913523003457204980568481547517245, 23625694919913523003457204981380951230869760⟩
  | 1, 2 => ⟨38662018313049210989755480832488488573795097, 38662018313049210989755480832496024628621070⟩
  | 2, 1 => ⟨38942174652992855586007623921542335063744524, 38942174652992855586007623921553098974251234⟩
  | 0, 4 => ⟨71876299899804698914338524190219795189765267, 71876299899804698914338528712793292198388890⟩
  | 1, 3 => ⟨184034330239042935845482028587109152820596833, 184034330239042935845482028589085328297782008⟩
  | 2, 2 => ⟨296856906059140566538820577948522528968943588, 296856906059140566538820577948553409645717347⟩
  | 3, 1 => ⟨298378098548661066105927980137007914792390725, 298378098548661066105927980137055682245896757⟩
  | 0, 5 => ⟨-444980187817227771477295874634126007939676022035, 451285926939770239737627469014194077503155508680⟩
  | 1, 4 => ⟨-740566534626311807796249097981376371250573899711, 742166744949615099605177002065730287945173766204⟩
  | 2, 3 => ⟨-1253950727194827151723546558771412413375483206436, 1249759814068583871154302337211287301654177867970⟩
  | 3, 2 => ⟨-2129583531175634709791975700482301535693667157302, 2120155101777142769243353159081103533855685405212⟩
  | 4, 1 => ⟨-3593609659738441659546139270614734029755567974385, 3586803441376651892284912934881892474102202340250⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0019Geometry.ds, E8TAxisZero0019Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 237049267108541827514955987640653023808377 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0019CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0020CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0020CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0020GraphCenterA.qJetBox,
   E8TAxisZero0020GraphCenterB.qJetBox,
   E8TAxisZero0020GraphCenterC.qJetBox,
   E8TAxisZero0020GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0020GraphWholeA.qJetBox,
   E8TAxisZero0020GraphWholeB.qJetBox,
   E8TAxisZero0020GraphWholeC.qJetBox,
   E8TAxisZero0020GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨221959384088693371803774574470232931147396, 221959384088693371803774574471192882546436⟩
  | 0, 2 => ⟨2853550221435763738154251997500927156213448, 2853550221435763738154251997503665113916481⟩
  | 1, 1 => ⟨2882751595927177573610994584974228670090501, 2882751595927177573610994584977964859634832⟩
  | 0, 3 => ⟨18375403760285951007093231831949916583596529, 18375403760285951007093231832701112488008708⟩
  | 1, 2 => ⟨30173364461641194787404145329948964602773339, 30173364461641194787404145329956007284157212⟩
  | 2, 1 => ⟨30408625203573795817380264309386884426826501, 30408625203573795817380264309396877083768818⟩
  | 0, 4 => ⟨58508929571603649523971658656317013371881203, 58508929571603649523971662837570007833847603⟩
  | 1, 3 => ⟨152687940404948141863228650142611418522775019, 152687940404948141863228650144575767157965755⟩
  | 2, 2 => ⟨247468942251766520344525800071288325779530336, 247468942251766520344525800071317162793405427⟩
  | 3, 1 => ⟨248823467515043004044309787652651092173306152, 248823467515043004044309787652695517795916439⟩
  | 0, 5 => ⟨-417998077227911384901177348738112052691285926258, 423329206989904679281735465048334383107799051139⟩
  | 1, 4 => ⟨-692798802996708329621908145709068584269602307211, 693540914457980190126477115515597128765752875048⟩
  | 2, 3 => ⟨-1168463290535314775802292796342802536578680371076, 1163542558424388239286569309669218734193921592489⟩
  | 3, 2 => ⟨-1976052975426346461615313197282628837425357965934, 1965977788146867432644843764340760356970469479900⟩
  | 4, 1 => ⟨-3318191112885395921226593660875072903871893449101, 3310522806124247641615838061101914379512807070272⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0020Geometry.ds, E8TAxisZero0020Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 152736816192496062903983532904375165211759 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0020CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0021CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0021CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0021GraphCenterA.qJetBox,
   E8TAxisZero0021GraphCenterB.qJetBox,
   E8TAxisZero0021GraphCenterC.qJetBox,
   E8TAxisZero0021GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0021GraphWholeA.qJetBox,
   E8TAxisZero0021GraphWholeB.qJetBox,
   E8TAxisZero0021GraphWholeC.qJetBox,
   E8TAxisZero0021GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨145513332391570373927371332162036084494889, 145513332391570373927371332162934912591199⟩
  | 0, 2 => ⟨2024172597244583681297691048563338425727854, 2024172597244583681297691048565954506497380⟩
  | 1, 1 => ⟨2046658024968352908311890610686375299816754, 2046658024968352908311890610689942552797288⟩
  | 0, 3 => ⟨14041082069792831976475779634089307995049199, 14041082069792831976475779634779564968929205⟩
  | 1, 2 => ⟨23132729629550929151207642922008473491992739, 23132729629550929151207642922015053066929147⟩
  | 2, 1 => ⟨23328086625808595490537584166825474754302716, 23328086625808595490537584166834745945286624⟩
  | 0, 4 => ⟨47138384444445929785353254514053389606030292, 47138384444445929785353258355757173333106743⟩
  | 1, 3 => ⟨125338552752405820970352095315050221912543331, 125338552752405820970352095317003710338896012⟩
  | 2, 2 => ⟨204081516752214042481025429973135012391901169, 204081516752214042481025429973161955136968267⟩
  | 3, 1 => ⟨205282964653402589726318178141427836896336319, 205282964653402589726318178141469174947710840⟩
  | 0, 5 => ⟨-393230726870137985235963955909038998903835149899, 397434608240552443797336861249249320867115064905⟩
  | 1, 4 => ⟨-648968783620961022864700771481196429817521233994, 648636776629655747821100833413244261813143292946⟩
  | 2, 3 => ⟨-1090079175361624246513544095587173504985646371319, 1084125500664554143264412410648084081778510940224⟩
  | 3, 2 => ⟨-1835412848758873517150803957404909911203178893023, 1824305202738158939305023643555976907122474527445⟩
  | 4, 1 => ⟨-3066194486715372179298511722274334714921252733525, 3057292218415393414857063687341853998954527459683⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0021Geometry.ds, E8TAxisZero0021Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 93504490650166628164562669744179023782604 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0021CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0022CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0022CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0022GraphCenterA.qJetBox,
   E8TAxisZero0022GraphCenterB.qJetBox,
   E8TAxisZero0022GraphCenterC.qJetBox,
   E8TAxisZero0022GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0022GraphWholeA.qJetBox,
   E8TAxisZero0022GraphWholeB.qJetBox,
   E8TAxisZero0022GraphWholeC.qJetBox,
   E8TAxisZero0022GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨91952248620111755915352790300529404962417, 91952248620111755915352790301369505129788⟩
  | 0, 2 => ⟨1394534417978470148796384661219307731892934, 1394534417978470148796384661221808757312403⟩
  | 1, 1 => ⟨1411478168673555636079291797566150368541418, 1411478168673555636079291797569559587900687⟩
  | 0, 3 => ⟨10504460438838332516441436842432700330624893, 10504460438838332516441436843062324684265362⟩
  | 1, 2 => ⟨17361798496083401927119180559254436147673745, 17361798496083401927119180559260580578415583⟩
  | 2, 1 => ⟨17521843184597647616372648388368574773310351, 17521843184597647616372648388377170375143430⟩
  | 0, 4 => ⟨37509116232609346583492881740240497163028409, 37509116232609346583492885244014239176793642⟩
  | 1, 3 => ⟨101570061265088678088987482376900673619480676, 101570061265088678088987482378844244970689114⟩
  | 2, 2 => ⟨166117591648929309529638570707642605405087790, 166117591648929309529638570707667791591760394⟩
  | 3, 1 => ⟨167178019875335120913390017698447212305811841, 167178019875335120913390017698485696684003495⟩
  | 0, 5 => ⟨-370171730964512377505385185496381176130621344735, 373243112822952065939767569743450375886632780767⟩
  | 1, 4 => ⟨-608207025856369706005171488337354574908943883150, 606806925294450539760749369542433346415738725168⟩
  | 2, 3 => ⟨-1017295357381519493820399829696473780090556318589, 1010329617442738269762987758336201826711811915797⟩
  | 3, 2 => ⟨-1705077824836784961859085821808544984302276716017, 1692976176446369070476618156969608358060792232542⟩
  | 4, 1 => ⟨-2833226647951927400213708445211515782306103227172, 2823141793001547945500089598974985566049944500744⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0022Geometry.ds, E8TAxisZero0022Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 53239640887129496218613099122613491181789 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0022CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0023CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0023CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0023GraphCenterA.qJetBox,
   E8TAxisZero0023GraphCenterB.qJetBox,
   E8TAxisZero0023GraphCenterC.qJetBox,
   E8TAxisZero0023GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0023GraphWholeA.qJetBox,
   E8TAxisZero0023GraphWholeB.qJetBox,
   E8TAxisZero0023GraphWholeC.qJetBox,
   E8TAxisZero0023GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨55592820877091482647011232096299575526781, 55592820877091482647011232097083197483980⟩
  | 0, 2 => ⟨927520145809227029700036679248829235237580, 927520145809227029700036679251221609233470⟩
  | 1, 1 => ⟨939958659747413564513004960774855413108286, 939958659747413564513004960778116806954848⟩
  | 0, 3 => ⟨7659484972532807374797406381924139248831360, 7659484972532807374797406382493409357887040⟩
  | 1, 2 => ⟨12699208157702352186721519226008528119682104, 12699208157702352186721519226014263244491107⟩
  | 2, 1 => ⟨12828177545014712520079134170776382208284146, 12828177545014712520079134170784344502176656⟩
  | 0, 4 => ⟨29396830066466550145941321221952486116441801, 29396830066466550145941324389266027840275473⟩
  | 1, 3 => ⟨81016037912539232292738044601260669635636869, 81016037912539232292738044603195245658556800⟩
  | 2, 2 => ⟨133068259780133079293199248801933018594824927, 133068259780133079293199248801956575255195508⟩
  | 3, 1 => ⟨133998312947409573012248287763215040999177011, 133998312947409573012248287763250887030529462⟩
  | 0, 5 => ⟨-348608968753920029299993169255231298277593285037, 350610784684243268755463363443110697596363739772⟩
  | 1, 4 => ⟨-570181115145106954372661690352374647094675942879, 567787225542316583474021311423408145167735653167⟩
  | 2, 3 => ⟨-949555445883405319411106774121271780200103205488, 941666675236766851267798287940320446433399968792⟩
  | 3, 2 => ⟨-1584074141836222920364022722067890282677444636956, 1571085150259173108886518152942031148984865443016⟩
  | 4, 1 => ⟨-2617547829796558910420857708094131098835483280037, 2606401762603713885785551484253879660866377799597⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0023Geometry.ds, E8TAxisZero0023Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 26966826205652825235479530137571934175308 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0023CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0024CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0024CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0024GraphCenterA.qJetBox,
   E8TAxisZero0024GraphCenterB.qJetBox,
   E8TAxisZero0024GraphCenterC.qJetBox,
   E8TAxisZero0024GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0024GraphWholeA.qJetBox,
   E8TAxisZero0024GraphWholeB.qJetBox,
   E8TAxisZero0024GraphWholeC.qJetBox,
   E8TAxisZero0024GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨31839455399087884877608766208231215851471, 31839455399087884877608766208960472828608⟩
  | 0, 2 => ⟨590818736658365871568730110319718539550155, 590818736658365871568730110322008280827380⟩
  | 1, 1 => ⟨599661028364110301589944178663874292316479, 599661028364110301589944178666997430101149⟩
  | 0, 3 => ⟨5410831619323436732955989405623674621576369, 5410831619323436732955989406132841474020205⟩
  | 1, 2 => ⟨8998508280784715226466655290145072450179305, 8998508280784715226466655290150422148375762⟩
  | 2, 1 => ⟨9100327417009876711199586902581334568455076, 9100327417009876711199586902588702527409486⟩
  | 0, 4 => ⟨22605703852583571055802450911452303417581883, 22605703852583571055802453743628687323412233⟩
  | 1, 3 => ⟨63355545208927627996681072088033022677585079, 63355545208927627996681072089959505756200351⟩
  | 2, 2 => ⟨104487147301993884142099356287216824433175026, 104487147301993884142099356287238868839998377⟩
  | 3, 1 => ⟨105296162520321930935590726684237428241395118, 105296162520321930935590726684270834314757161⟩
  | 0, 5 => ⟨-328407557142579434562794852380102841290674280519, 329411615382880393995601500463873860564180364566⟩
  | 1, 4 => ⟨-534653506225700624562744289628507038544370118108, 531346854117177229708442078096378413403148245067⟩
  | 2, 3 => ⟨-886429280479920817356995397539805530135086954011, 877710603814647240917185016662709922660918301306⟩
  | 3, 2 => ⟨-1471611542172693843741015268058982278329613714963, 1457842895840348528924694865811236818194175357238⟩
  | 4, 1 => ⟨-2417683408648872090986644307997299210474364595517, 2405595956853910111820047864347343727958594643799⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0024Geometry.ds, E8TAxisZero0024Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 10707544809249210940039230385026410353308 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0024CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0025CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0025CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0025GraphCenterA.qJetBox,
   E8TAxisZero0025GraphCenterB.qJetBox,
   E8TAxisZero0025GraphCenterC.qJetBox,
   E8TAxisZero0025GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0025GraphWholeA.qJetBox,
   E8TAxisZero0025GraphWholeB.qJetBox,
   E8TAxisZero0025GraphWholeC.qJetBox,
   E8TAxisZero0025GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨26678359637762354485849537582164580756384353, 26678359637762354485849537582167374430629944⟩
  | 0, 2 => ⟨154022479912378979860113137270423644320069582, 154022479912378979860113137270430708518233926⟩
  | 1, 1 => ⟨154681215480713319995136163232649415345410509, 154681215480713319995136163232659671429196312⟩
  | 0, 3 => ⟨504788418628118235114516851179763473564546132, 504788418628118235114516851181737265139159510⟩
  | 1, 2 => ⟨769617258359029412843137655109890061808461744, 769617258359029412843137655109915063691695824⟩
  | 2, 1 => ⟨772287514661595147155435106444457965623086464, 772287514661595147155435106444497049766578059⟩
  | 0, 4 => ⟨1168877567493116406983612321751513683913595286, 1168877567493116406983612332716028869073144172⟩
  | 1, 3 => ⟨2238688028713191084830274786852996221890603813, 2238688028713191084830274786855374886318980751⟩
  | 2, 2 => ⟨3311444640999054014236990274522719622836921221, 3311444640999054014236990274522831119366507986⟩
  | 3, 1 => ⟨3320753622531712169591492432166663413518264394, 3320753622531712169591492432166847252530741748⟩
  | 0, 5 => ⟨-10735769146881271823455014711255658407132125292520, 10812480470359655967265665874869999215251857068576⟩
  | 1, 4 => ⟨-19702584108521468592005660372458969585884918644366, 19763718083805187983140300262996567327001356998078⟩
  | 2, 3 => ⟨-36396185550062301628799750450115818653587807775195, 36437116949617139583327205695236627167274218153037⟩
  | 3, 2 => ⟨-67379351863545062896737534651054997869880318932465, 67405064303525039868638585169695681697546585348377⟩
  | 4, 1 => ⟨-124712900699833919295924172917930605356635740969596, 124761104344718475704327448065533679561805112623108⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0025Geometry.ds, E8TAxisZero0025Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 15127678758184271895392708819689485833406284 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0025CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0026CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0026CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0026GraphCenterA.qJetBox,
   E8TAxisZero0026GraphCenterB.qJetBox,
   E8TAxisZero0026GraphCenterC.qJetBox,
   E8TAxisZero0026GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0026GraphWholeA.qJetBox,
   E8TAxisZero0026GraphWholeB.qJetBox,
   E8TAxisZero0026GraphWholeC.qJetBox,
   E8TAxisZero0026GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨18391669026388033538161323980504494308768952, 18391669026388033538161323980506995733683812⟩
  | 0, 2 => ⟨111906823691134322222211237714757865314501496, 111906823691134322222211237714764175636228594⟩
  | 1, 1 => ⟨112415705069660621332919023452444259582592709, 112415705069660621332919023452453334030611237⟩
  | 0, 3 => ⟨380772115262400835667311473778140003431458725, 380772115262400835667311473779969286064859996⟩
  | 1, 2 => ⟨585395446488862877174593002863702525379799646, 585395446488862877174593002863724218673229416⟩
  | 2, 1 => ⟨587537984853930648919430447817567447900321493, 587537984853930648919430447817601066165032387⟩
  | 0, 4 => ⟨889834728526608286694825144136639997440001524, 889834728526608286694825154303297113153513065⟩
  | 1, 3 => ⟨1748170333214115719892366263427673188022143440, 1748170333214115719892366263429982748268011540⟩
  | 2, 2 => ⟨2609001120745376595353972426980513266558783437, 2609001120745376595353972426980608757838654032⟩
  | 3, 1 => ⟨2616632889687138445603446437220312813497714214, 2616632889687138445603446437220469240267013665⟩
  | 0, 5 => ⟨-8916278826632156152027203778931842509867583249178, 8975529992745740088790160635401970709220562521453⟩
  | 1, 4 => ⟨-16278425562796030375549571934354121514196723074146, 16317707584499642099757144218863205456477735523634⟩
  | 2, 3 => ⟨-29925302538307984416437155901700974799127286770346, 29938568362975022054990810174167087782496216734614⟩
  | 3, 2 => ⟨-55129539844839016313755730242597491060042878512130, 55121012535451585758086253121950621802731861869627⟩
  | 4, 1 => ⟨-101512392638513717278964311640150434347462811490060, 101522940715764974071662604012689109154842960792311⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0026Geometry.ds, E8TAxisZero0026Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 9466243995368832791441225479901179973406947 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0026CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0027CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0027CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0027GraphCenterA.qJetBox,
   E8TAxisZero0027GraphCenterB.qJetBox,
   E8TAxisZero0027GraphCenterC.qJetBox,
   E8TAxisZero0027GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0027GraphWholeA.qJetBox,
   E8TAxisZero0027GraphWholeB.qJetBox,
   E8TAxisZero0027GraphWholeC.qJetBox,
   E8TAxisZero0027GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨12412894863566379130638699429038911948837853, 12412894863566379130638699429041151763521902⟩
  | 0, 2 => ⟨80027260312646603412330335488934668912638462, 80027260312646603412330335488940321097798514⟩
  | 1, 1 => ⟨80416194821700679825829079146168129036653996, 80416194821700679825829079146176183174393930⟩
  | 0, 3 => ⟨284202126138560269726605849966240179703822612, 284202126138560269726605849967928779042768715⟩
  | 1, 2 => ⟨440630547028074712800212457232196211738296524, 440630547028074712800212457232215068476355189⟩
  | 2, 1 => ⟨442340702760400121104154102632292321504453697, 442340702760400121104154102632321281820050097⟩
  | 0, 4 => ⟨671838660218457209666203409718466850963764284, 671838660218457209666203419107130863289044048⟩
  | 1, 3 => ⟨1356910027475396123280352314371829322870854068, 1356910027475396123280352314374076924566891899⟩
  | 2, 2 => ⟨2044096382308115293975050126268973633166013125, 2044096382308115293975050126269055592896905745⟩
  | 3, 1 => ⟨2050345458293221502613721483596127070282668460, 2050345458293221502613721483596260430442413253⟩
  | 0, 5 => ⟨-7428292802558852074991964899501201770785051568531, 7475381671830414576972435925158598310327461709817⟩
  | 1, 4 => ⟨-13488247998589772302009427849590302183709212648993, 13513472806764683660058535351138694634880548409201⟩
  | 2, 3 => ⟨-24670015693188280348024725124403479486722869218812, 24666695081570351426713629439087766216893119427555⟩
  | 3, 2 => ⟨-45213403318515842780939135946113452777653677132391, 45185087192118097958532541175886102444356987159088⟩
  | 4, 1 => ⟨-82794499021521921968526566609471987438762598979995, 82782243147612390186104714524067282136538811681018⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0027Geometry.ds, E8TAxisZero0027Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5531832160278881868373820864777301920661859 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0027CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0028CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0028CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0028GraphCenterA.qJetBox,
   E8TAxisZero0028GraphCenterB.qJetBox,
   E8TAxisZero0028GraphCenterC.qJetBox,
   E8TAxisZero0028GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0028GraphWholeA.qJetBox,
   E8TAxisZero0028GraphWholeB.qJetBox,
   E8TAxisZero0028GraphWholeC.qJetBox,
   E8TAxisZero0028GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨8172332506696137742810096372051203065805198, 8172332506696137742810096372053207885558419⟩
  | 0, 2 => ⟨56168753621094158203514715987450612344367245, 56168753621094158203514715987455688292174551⟩
  | 1, 1 => ⟨56462230957133881953542236535655800562889971, 56462230957133881953542236535662971546129846⟩
  | 0, 3 => ⟨209489595463137055211027127911844137622775687, 209489595463137055211027127913395491147915135⟩
  | 1, 2 => ⟨327558264610292645331090540919561612189314673, 327558264610292645331090540919578029401866438⟩
  | 2, 1 => ⟨328914594123644526852517823237128654612338056, 328914594123644526852517823237153633544533514⟩
  | 0, 4 => ⟨502572651006916943171847296845286348978376362, 502572651006916943171847305473890161392712680⟩
  | 1, 3 => ⟨1045865478870951170568824587796694172159743713, 1045865478870951170568824587798886327773406280⟩
  | 2, 2 => ⟨1590951892463365718964301864903254748488772845, 1590951892463365718964301864903325240887486516⟩
  | 3, 1 => ⟨1596062111039864862463241225018772404017461879, 1596062111039864862463241225018886311748648482⟩
  | 0, 5 => ⟨-6203656786555237167201954749175172106961492838106, 6241391789980063952977176700685969231340481231921⟩
  | 1, 4 => ⟨-11200170919477301111770646768980675649555892406200, 11215256540173592829210930182282872285760956546004⟩
  | 2, 3 => ⟨-20374718470403295221642667375042686767324414598501, 20360186942639790936785108901031192649833019102332⟩
  | 3, 2 => ⟨-37135108735088054864827064432034196494924294281752, 37094052700444106313078483100351236809088800935569⟩
  | 4, 1 => ⟨-67596917685733074086997090271741028052218918121549, 67570171817760252505059979794715596671665386737293⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0028Geometry.ds, E8TAxisZero0028Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2880184700826201926579190066130352313844678 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0028CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0029CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0029CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0029GraphCenterA.qJetBox,
   E8TAxisZero0029GraphCenterB.qJetBox,
   E8TAxisZero0029GraphCenterC.qJetBox,
   E8TAxisZero0029GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0029GraphWholeA.qJetBox,
   E8TAxisZero0029GraphWholeB.qJetBox,
   E8TAxisZero0029GraphWholeC.qJetBox,
   E8TAxisZero0029GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5224859546545922839988170482740408425200424, 5224859546545922839988170482742201424239067⟩
  | 0, 2 => ⟨38554335763943532739089321064947392717705128, 38554335763943532739089321064951962753065105⟩
  | 1, 1 => ⟨38772383086984950599904722971369174534853056, 38772383086984950599904722971375579424496436⟩
  | 0, 3 => ⟨152124384355438402106146095980578819905169232, 152124384355438402106146095981996008363344095⟩
  | 1, 2 => ⟨239876511681341524988978021565946876520824707, 239876511681341524988978021565961189768536852⟩
  | 2, 1 => ⟨240943704104479715847383623481855676221446962, 240943704104479715847383623481877243027176383⟩
  | 0, 4 => ⟨372013528913930564997750778172100301401188060, 372013528913930564997750786056777958849665922⟩
  | 1, 3 => ⟨799455384897647902669320663601369540286422159, 799455384897647902669320663603512215980163551⟩
  | 2, 2 => ⟨1228418093614101344247029452038287924877541203, 1228418093614101344247029452038348683156205437⟩
  | 3, 1 => ⟨1232590611661958349444886710431115648630441826, 1232590611661958349444886710431213127865758453⟩
  | 0, 5 => ⟨-5193964745044400696840027397429734456255431900851, 5225852414825053891519608652995179853008960624151⟩
  | 1, 4 => ⟨-9320960678223628766275586196494498135157484499351, 9330803216907110778285828876781586416558074129628⟩
  | 2, 3 => ⟨-16859526302425129193324926257266182395254006701833, 16840508567549570534936159553381175470746642587617⟩
  | 3, 2 => ⟨-30547281316151815448890080357504728551710856074437, 30502151006143906794090142701324707216614419293581⟩
  | 4, 1 => ⟨-55248557762848432420081044930230934866386137556858, 55216569890085644162801545380367805928693118227145⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0029Geometry.ds, E8TAxisZero0029Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1161822194900097662512107693524843187937015 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0029CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0030CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0030CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0030GraphCenterA.qJetBox,
   E8TAxisZero0030GraphCenterB.qJetBox,
   E8TAxisZero0030GraphCenterC.qJetBox,
   E8TAxisZero0030GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0030GraphWholeA.qJetBox,
   E8TAxisZero0030GraphWholeB.qJetBox,
   E8TAxisZero0030GraphWholeC.qJetBox,
   E8TAxisZero0030GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3225177882927098392738019464242549080626407, 3225177882927098392738019464244150482895309⟩
  | 0, 2 => ⟨25762242848937623075429662248299945392165334, 25762242848937623075429662248304070073087037⟩
  | 1, 1 => ⟨25921212794870504117781302907602930803646000, 25921212794870504117781302907608669786648804⟩
  | 0, 3 => ⟨108477344551567999681884629116434018788109079, 108477344551567999681884629117719793012049527⟩
  | 1, 2 => ⟨172480619509125421440224816619490851048724266, 172480619509125421440224816619503344353769100⟩
  | 2, 1 => ⟨173311943045948846440675845664633302033437894, 173311943045948846440675845664651936313935900⟩
  | 0, 4 => ⟨272039661216891460103714109914105205782794009, 272039661216891460103714117069310587630534789⟩
  | 1, 3 => ⟨604980369447126982885412355463712750126895907, 604980369447126982885412355465811435622172183⟩
  | 2, 2 => ⟨939209346866214943153791186234301521125201009, 939209346866214943153791186234354001313832254⟩
  | 3, 1 => ⟨942609538426903659710720681675327301445186388, 942609538426903659710720681675410883079583528⟩
  | 0, 5 => ⟨-4359889104290750716299116416022718064780859626099, 4385921907742622564174521384178524168156799905165⟩
  | 1, 4 => ⟨-7774160698237228002616209962621784679108085977896, 7778707511153473081581799172927862146025839482665⟩
  | 2, 3 => ⟨-13975839778244297487477171472657966179593564738864, 13952268894296880190161102530898189073148484305365⟩
  | 3, 2 => ⟨-25161430505357870327585346523580264035774747255752, 25112036998515391724530940379010186822808436597774⟩
  | 4, 1 => ⟨-45190052757866954482408280625908812748925518939951, 45151676796106184833467461150985222036023607159872⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0030Geometry.ds, E8TAxisZero0030Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 108693613633249006118815488334441885781438 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0030CertifiedArithmetic

end


