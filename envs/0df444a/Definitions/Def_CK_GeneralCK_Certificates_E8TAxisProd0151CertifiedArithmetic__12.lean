-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0151CertifiedArithmetic__12
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0151CertifiedArithmetic__12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T15:18:16.156491+00:00
-- url     : https://prove2.me/theorems/a848da12-5f18-4648-8d84-8863eed57bec
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0151CertifiedArithmetic (+11 modules: GeneralCK.Certificates.E8TAxisProd0152CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0151CertifiedArithmetic (+11 modules: GeneralCK.Certificates.E8TAxisProd0152CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0153CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0154CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0155CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0156CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0157CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0158CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0159CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0160CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0161CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0162CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0151CertifiedArithmetic (+11 modules: GeneralCK.Certificates.E8TAxisProd0152CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0153CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0154CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0155CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0156CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0157CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0158CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0159CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0160CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0161CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0162CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0151CertifiedArithmetic (+11 modules: GeneralCK.Certificates.E8TAxisProd0152CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0153CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0154CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0155CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0156CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0157CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0158CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0159CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0160CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0161CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0162CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0151CertifiedArithmetic (+11 modules: GeneralCK/Certificates/E8TAxisProd0152CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0153CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0154CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0155CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0156CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0157CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0158CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0159CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0160CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0161CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0162CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0139GraphCenterA__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0150GraphCenterB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0139GraphCenterC__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0151GraphCenterD__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0143GraphWholeA__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0137GraphWholeB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0136GraphWholeC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0140GraphWholeD__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0142Geometry__20
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0152GraphCenterA__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0153GraphWholeC__18
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0154GraphCenterC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0154GraphWholeB__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0155GraphWholeD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0160GraphWholeA__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0162Geometry__19

-- ===== source module GeneralCK.Certificates.E8TAxisProd0151CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0151CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0151GraphCenterA.qJetBox,
   E8TAxisProd0151GraphCenterB.qJetBox,
   E8TAxisProd0151GraphCenterC.qJetBox,
   E8TAxisProd0151GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0151GraphWholeA.qJetBox,
   E8TAxisProd0151GraphWholeB.qJetBox,
   E8TAxisProd0151GraphWholeC.qJetBox,
   E8TAxisProd0151GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨417095539060614983914623238314057096054602640, 417095539060614983914623238314067104929035663⟩
  | 0, 2 => ⟨1756370837438824111377375381979494539308821595, 1756370837438824111377375381979519455320430868⟩
  | 1, 1 => ⟨1763953194791595763191415986185178436773212832, 1763953194791595763191415986185215909066357211⟩
  | 0, 3 => ⟨4717673330765469630587706167487465208674715165, 4717673330765469630587706167487532185238350135⟩
  | 1, 2 => ⟨6752207795405572978262980968011453876078566380, 6752207795405572978262980968011555966911543411⟩
  | 2, 1 => ⟨6777354799954720145707650870086228271400956766, 6777354799954720145707650870086397102775093041⟩
  | 0, 4 => ⟨10327739404173899948368569130526047725567564397, 10327739404173899948368569130526242522052358856⟩
  | 1, 3 => ⟨17052129853331410768946758796449291559902610840, 17052129853331410768946758796449599339816197887⟩
  | 2, 2 => ⟨23796637712154315712177762916242275553878771054, 23796637712154315712177762916242796589354398696⟩
  | 3, 1 => ⟨23873912537838097042653776384409559149065431819, 23873912537838097042653776384410463858811309913⟩
  | 0, 5 => ⟨-78029154458673673810094070612510224836796851622354, 78628112846112066958583650474383917776007493680964⟩
  | 1, 4 => ⟨-148915636951788517846590088716590781204959196081056, 149723636160855153032335622265432143258532202792271⟩
  | 2, 3 => ⟨-285018898705061078690247126439281552620005332059822, 286101898239113679576617226091332781312784514677870⟩
  | 3, 2 => ⟨-546205459975358182486293693795838846658962873897580, 547577357676777602120197183615715289137357521960217⟩
  | 4, 1 => ⟨-1047256604627841107949480418919101063033273292220070, 1048688308835282147093820666865791827409257037989752⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0151Geometry.ds, E8TAxisProd0151Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 310800263337182856527018515391921464808137964 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0151CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0152CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0152CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0152GraphCenterA.qJetBox,
   E8TAxisProd0152GraphCenterB.qJetBox,
   E8TAxisProd0152GraphCenterC.qJetBox,
   E8TAxisProd0152GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0152GraphWholeA.qJetBox,
   E8TAxisProd0152GraphWholeB.qJetBox,
   E8TAxisProd0152GraphWholeC.qJetBox,
   E8TAxisProd0152GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨340256290553394899759654917727086537126113239, 340256290553394899759654917727095682629232751⟩
  | 0, 2 => ⟨1435107320647801674144016744578332435542621127, 1435107320647801674144016744578354784436423463⟩
  | 1, 1 => ⟨1466658314279559104967480169947335208302558465, 1466658314279559104967480169947368369968650481⟩
  | 0, 3 => ⟨3882183545811044698842678873788024191540251040, 3882183545811044698842678873788083400401224362⟩
  | 1, 2 => ⟨5617913067869503410473733135599293143438008686, 5617913067869503410473733135599382205138652284⟩
  | 2, 1 => ⟨5723988784240754181274159762400014625856403837, 5723988784240754181274159762400160895527345819⟩
  | 0, 4 => ⟨8537982888781032239138547304082478632964681558, 8537982888781032239138547304082649079940004026⟩
  | 1, 3 => ⟨14273386635410043613078333027617361061736617238, 14273386635410043613078333027617626906136017851⟩
  | 2, 2 => ⟨20095735883662088458824529221805977959312526976, 20095735883662088458824529221806424928107409685⟩
  | 3, 1 => ⟨20425598041510381426504470671715813519757336238, 20425598041510381426504470671716585911484838712⟩
  | 0, 5 => ⟨-62792338371265109370675278838494942147474862890014, 63280726077126095986733312317194634379746084059944⟩
  | 1, 4 => ⟨-119489318896237287598539512261055711735506622365956, 120136534202192034540033045694942322337704946974648⟩
  | 2, 3 => ⟨-228112236588903187491199715559582376628027958916576, 228971612750303029572522521582264104328897585689859⟩
  | 3, 2 => ⟨-436085414659710161962543543947662816425682794941802, 437177908589147955295580525005857556935414173674422⟩
  | 4, 1 => ⟨-834100324015733832397408765904003570640136002609069, 835278880754737221936980091628478362155473062553550⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0152Geometry.ds, E8TAxisProd0152Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 253436351113477274480081489028986516488604303 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0152CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0153CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0153CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0153GraphCenterA.qJetBox,
   E8TAxisProd0153GraphCenterB.qJetBox,
   E8TAxisProd0153GraphCenterC.qJetBox,
   E8TAxisProd0153GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0153GraphWholeA.qJetBox,
   E8TAxisProd0153GraphWholeB.qJetBox,
   E8TAxisProd0153GraphWholeC.qJetBox,
   E8TAxisProd0153GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨258979913362436863916870959639744842059945692, 258979913362436863916870959639753053338167114⟩
  | 0, 2 => ⟨1120660987933360615954337872779525005488597653, 1120660987933360615954337872779544669889336516⟩
  | 1, 1 => ⟨1146189155005464924592030068199923401788769657, 1146189155005464924592030068199952154539789538⟩
  | 0, 3 => ⟨3078583843581314570393547041928027003497374081, 3078583843581314570393547041928078230166540198⟩
  | 1, 2 => ⟨4483669868115942181528073647069151358855646080, 4483669868115942181528073647069227263025411519⟩
  | 2, 1 => ⟨4570898188653553214348507158652662612391021590, 4570898188653553214348507158652786264173840963⟩
  | 0, 4 => ⟨6815192632991841046801452615759283401185235622, 6815192632991841046801452615759429110179855866⟩
  | 1, 3 => ⟨11531232984754202534564540924179696776641087112, 11531232984754202534564540924179920695004345738⟩
  | 2, 2 => ⟨16320828855547623694250868246567659030934141007, 16320828855547623694250868246568032426092548780⟩
  | 3, 1 => ⟨16595606011259734834668319042633153748529104721, 16595606011259734834668319042633795224833207146⟩
  | 0, 5 => ⟨-48808966715038735326159231646408480234235839831272, 49192320776823342957526985790521145856298624676759⟩
  | 1, 4 => ⟨-92535410232585809417711657712356095274814119930771, 93028511714478926520761365425655310675109938237562⟩
  | 2, 3 => ⟨-176069095900002542928168985601057270261893482041163, 176708647776382288032527411206379199053448712700529⟩
  | 3, 2 => ⟨-335517829637882346010292797571563059141194537774908, 336319673207385903013815094067141237704835612237030⟩
  | 4, 1 => ⟨-639689447905420341418536120361910194135608955473008, 640556235173615452908727748762839569887649383694844⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0153Geometry.ds, E8TAxisProd0153Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 191596547712284876775010040864685394253591454 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0153CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0154CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0154CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0154GraphCenterA.qJetBox,
   E8TAxisProd0154GraphCenterB.qJetBox,
   E8TAxisProd0154GraphCenterC.qJetBox,
   E8TAxisProd0154GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0154GraphWholeA.qJetBox,
   E8TAxisProd0154GraphWholeB.qJetBox,
   E8TAxisProd0154GraphWholeC.qJetBox,
   E8TAxisProd0154GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨336680631869267405419039832608208018226858275, 336680631869267405419039832608217133601472341⟩
  | 0, 2 => ⟨1425428497803507213936972413687436621168318197, 1425428497803507213936972413687458886591546977⟩
  | 1, 1 => ⟨1452658056730908716529097736196632978950167697, 1452658056730908716529097736196666011968684404⟩
  | 0, 3 => ⟨3860892779009140805849181038056593647247971974, 3860892779009140805849181038056652620466296807⟩
  | 1, 2 => ⟨5582324617583167454943329166993511107322904059, 5582324617583167454943329166993599798939466832⟩
  | 2, 1 => ⟨5673900107534130217761426370103940509997617691, 5673900107534130217761426370104086152381959177⟩
  | 0, 4 => ⟨8494664351571547588731675204718646479113326012, 8494664351571547588731675204718816208813010296⟩
  | 1, 3 => ⟨14197434931404554380188061678496098743191434043, 14197434931404554380188061678496363430515992295⟩
  | 2, 2 => ⟨19975307376824862518001392361066347496580423472, 19975307376824862518001392361066792458135742656⟩
  | 3, 1 => ⟨20260153231141521166731151572417614952148322127, 20260153231141521166731151572418383773726969452⟩
  | 0, 5 => ⟨-62405268675128920514337931138387246470585960913504, 62890326724605603501044936594101062844957770766601⟩
  | 1, 4 => ⟨-118741533876944932145398155561189717672483121564752, 119383557065100598696255739688532059907579888338300⟩
  | 2, 3 => ⟨-226663595969225510453086706020374821797605670329835, 227514836347239798278965879281068630468897618665672⟩
  | 3, 2 => ⟨-433274709255820929473108235681543546510760864850037, 434354610980974081381573446790395092665605754791250⟩
  | 4, 1 => ⟨-828641866782957230244125718470681796844650868387629, 829801697810806499519319057158123927711398386776895⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0154Geometry.ds, E8TAxisProd0154Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 250573237197257797861108513529843267451954316 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0154CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0155CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0155CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0155GraphCenterA.qJetBox,
   E8TAxisProd0155GraphCenterB.qJetBox,
   E8TAxisProd0155GraphCenterC.qJetBox,
   E8TAxisProd0155GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0155GraphWholeA.qJetBox,
   E8TAxisProd0155GraphWholeB.qJetBox,
   E8TAxisProd0155GraphWholeC.qJetBox,
   E8TAxisProd0155GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨256187863741985726930726052607722368624522966, 256187863741985726930726052607730553075552334⟩
  | 0, 2 => ⟨1112985789380364436380086800198469437014963389, 1112985789380364436380086800198489028910972728⟩
  | 1, 1 => ⟨1135015950823388639969803276266510020733197103, 1135015950823388639969803276266538663360913018⟩
  | 0, 3 => ⟨3061589549895935591251234755448544595656725676, 3061589549895935591251234755448595619565986445⟩
  | 1, 2 => ⟨4454919291680359840766050778335865563670837507, 4454919291680359840766050778335941153492152609⟩
  | 2, 1 => ⟨4530219981519595963360106508751082107163628763, 4530219981519595963360106508751205229558282966⟩
  | 0, 4 => ⟨6780270028381564637079251792095720529671520141, 6780270028381564637079251792095865628098581615⟩
  | 1, 3 => ⟨11469279037680311129882177620654977059431356276, 11469279037680311129882177620655200004744913401⟩
  | 2, 2 => ⟨16221822002576913524788481575988138772478971560, 16221822002576913524788481575988510489102641245⟩
  | 3, 1 => ⟨16459085799428005285219345943328870751592521210, 16459085799428005285219345943329509254119542726⟩
  | 0, 5 => ⟨-48510685890675639000784564766608837249311666970919, 48891513017447585837974015758931840677723799075042⟩
  | 1, 4 => ⟨-91960461319139739621285157586734101051408306614452, 92449705254519319919476604895548178272291260248417⟩
  | 2, 3 => ⟨-174957417931946667608312631823528099377407150108508, 175591038644912195255684851753513296133749682436327⟩
  | 3, 2 => ⟨-333364674678043210954758976140181455913724429157966, 334157515437387273745145472247165339692193928813452⟩
  | 4, 1 => ⟨-635514901267379940058116093571222786925442504636660, 636368639236910035674632876913529133226824451382248⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0155Geometry.ds, E8TAxisProd0155Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 189365588796975859455482427806599160944369440 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0155CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0156CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0156CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0156GraphCenterA.qJetBox,
   E8TAxisProd0156GraphCenterB.qJetBox,
   E8TAxisProd0156GraphCenterC.qJetBox,
   E8TAxisProd0156GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0156GraphWholeA.qJetBox,
   E8TAxisProd0156GraphWholeB.qJetBox,
   E8TAxisProd0156GraphWholeC.qJetBox,
   E8TAxisProd0156GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨195629353927961784601058677455802234734915353, 195629353927961784601058677455809623733905794⟩
  | 0, 2 => ⟨870184238963352799799362324039448813747819143, 870184238963352799799362324039466177601395234⟩
  | 1, 1 => ⟨890765704156792596194214450842884080244951594, 890765704156792596194214450842909092200180108⟩
  | 0, 3 => ⟨2430535745948662831158822720731791927194359900, 2430535745948662831158822720731836364947566831⟩
  | 1, 2 => ⟨3563957477016398640144988925464314736583979886, 3563957477016398640144988925464379550222337718⟩
  | 2, 1 => ⟨3635508324143145893340913541333155042579255779, 3635508324143145893340913541333259725573394954⟩
  | 0, 4 => ⟨5413177944406855199649540818710022215076152692, 5413177944406855199649540818710147082375675054⟩
  | 1, 3 => ⟨9281202311180949491834279802649860736828154491, 9281202311180949491834279802650049602340292582⟩
  | 2, 2 => ⟨13211377486507292128582842975048191962151953987, 13211377486507292128582842975048504134115564854⟩
  | 3, 1 => ⟨13439603704233158484966671666908507320767414506, 13439603704233158484966671666909040306098721516⟩
  | 0, 5 => ⟨-38116941673884572996372047823976626672258386878706, 38416082549317345551432567305454757973629334229756⟩
  | 1, 4 => ⟨-71975520885232598262977229493632317101422742898566, 72346641053392993678651562726747060048231783069825⟩
  | 2, 3 => ⟨-136460411794790979993183666945865314116392684466788, 136927477992824958309140379576777419874693932552133⟩
  | 3, 2 => ⟨-259145351024365565618456675949828531712485950238738, 259720088491956379263979396265578172590664104269397⟩
  | 4, 1 => ⟨-492373697401216524060527656039596154453494411267281, 492996066491653614276805363905409918629529617407559⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0156Geometry.ds, E8TAxisProd0156Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 143418146573784548267921102754641233950721821 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0156CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0157CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0157CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0157GraphCenterA.qJetBox,
   E8TAxisProd0157GraphCenterB.qJetBox,
   E8TAxisProd0157GraphCenterC.qJetBox,
   E8TAxisProd0157GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0157GraphWholeA.qJetBox,
   E8TAxisProd0157GraphWholeB.qJetBox,
   E8TAxisProd0157GraphWholeC.qJetBox,
   E8TAxisProd0157GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨146538188385276256472962079248700506953435928, 146538188385276256472962079248707171520240730⟩
  | 0, 2 => ⟨671495612439487718576974329051359119392799523, 671495612439487718576974329051374518457029433⟩
  | 1, 1 => ⟨688024289597130204943866889037186944466963724, 688024289597130204943866889037208796715453004⟩
  | 0, 3 => ⟨1909876973723755522233180534056288903889449933, 1909876973723755522233180534056327598997455060⟩
  | 1, 2 => ⟨2820646915486778814735465298181141705717705169, 2820646915486778814735465298181197234509978329⟩
  | 2, 1 => ⟨2879192990934904944835802003148880960478916117, 2879192990934904944835802003148969849029492023⟩
  | 0, 4 => ⟨4277750463374697586731226837946794501808415305, 4277750463374697586731226837946901939680918278⟩
  | 1, 3 => ⟨7442273753010045678552033696801943291532024647, 7442273753010045678552033696802103104289079737⟩
  | 2, 2 => ⟨10659271892959523645886856604443473411054901973, 10659271892959523645886856604443735103580158762⟩
  | 3, 1 => ⟨10848341119833224009556822532177766185878377132, 10848341119833224009556822532178210106593451078⟩
  | 0, 5 => ⟨-29925498832730163314145126421441524814663946184967, 30160731928656026297015717233037962562982154280081⟩
  | 1, 4 => ⟨-56262653363405067089309693070713940655395760916981, 56542041712484821151160024058709063877724988698742⟩
  | 2, 3 => ⟨-106259775251140890277718239686412456861157564587010, 106597949263629415910289398322546419675734611062030⟩
  | 3, 2 => ⟨-201047069014894758817696789278769337062332317417290, 201452776711643320462294261459270276765986228682548⟩
  | 4, 1 => ⟨-380568490675191826297884397126189433823099705425155, 381009505638754080214504532662876213855002629878158⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0157Geometry.ds, E8TAxisProd0157Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 106156661859580768964829317310991586335043779 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0157CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0158CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0158CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0158GraphCenterA.qJetBox,
   E8TAxisProd0158GraphCenterB.qJetBox,
   E8TAxisProd0158GraphCenterC.qJetBox,
   E8TAxisProd0158GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0158GraphWholeA.qJetBox,
   E8TAxisProd0158GraphWholeB.qJetBox,
   E8TAxisProd0158GraphWholeC.qJetBox,
   E8TAxisProd0158GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨193461474676184857266970192372804348709765106, 193461474676184857266970192372811713733865697⟩
  | 0, 2 => ⟨864124786597925444588950201796865701758556850, 864124786597925444588950201796883002450281432⟩
  | 1, 1 => ⟨881884761771271031409522181281782201729292853, 881884761771271031409522181281807119213241814⟩
  | 0, 3 => ⟨2417037804942375833896893163055353909049105533, 2417037804942375833896893163055398171936402267⟩
  | 1, 2 => ⟨3540817385266202248324138396976366770388385518, 3540817385266202248324138396976431316673218162⟩
  | 2, 1 => ⟨3602581302458294841613836432506692514394219397, 3602581302458294841613836432506796750272762682⟩
  | 0, 4 => ⟨5385197416553119569065181402190589049311846652, 5385197416553119569065181402190713396371827999⟩
  | 1, 3 => ⟨9230913015431919712975160495566516381402127087, 9230913015431919712975160495566704428805441854⟩
  | 2, 2 => ⟨13130310610180322403121088288062429561083404632, 13130310610180322403121088288062740330453012297⟩
  | 3, 1 => ⟨13327367903675867847970131713745005977305787074, 13327367903675867847970131713745536488289773436⟩
  | 0, 5 => ⟨-37887092092426286391649157859404417124443564350094, 38184262857747691845505908417820440965219257919138⟩
  | 1, 4 => ⟨-71533454321661948395660724624902554062920449884657, 71901656148391406468461075813167625302662247331919⟩
  | 2, 3 => ⟨-135607285224483060824321742571677406133168276092455, 136069992606184001377981861934669411440126582702887⟩
  | 3, 2 => ⟨-257495853894467273312576840627091194249728151993765, 258064180281406824367894903555852311493991528611869⟩
  | 4, 1 => ⟨-489180996126932367648441948361216160867700046914181, 489794463808567958693874287390277032299721616157652⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0158Geometry.ds, E8TAxisProd0158Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 141691064662605069333575151166775841099356864 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0158CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0159CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0159CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0159GraphCenterA.qJetBox,
   E8TAxisProd0159GraphCenterB.qJetBox,
   E8TAxisProd0159GraphCenterC.qJetBox,
   E8TAxisProd0159GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0159GraphWholeA.qJetBox,
   E8TAxisProd0159GraphWholeB.qJetBox,
   E8TAxisProd0159GraphWholeC.qJetBox,
   E8TAxisProd0159GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨144865406594269750256122669293325968324035267, 144865406594269750256122669293332611447404507⟩
  | 0, 2 => ⟨666734264741889117852551741433114149100524368, 666734264741889117852551741433129493318700719⟩
  | 1, 1 => ⟨680995887043798664289714890322655413290496272, 680995887043798664289714890322677184892328622⟩
  | 0, 3 => ⟨1899210466355515805387233465643679205698836649, 1899210466355515805387233465643717750817556274⟩
  | 1, 2 => ⟨2802092053745584741592161869374288516313947868, 2802092053745584741592161869374343819469072306⟩
  | 2, 1 => ⟨2852627536243606529529280603244675200721698738, 2852627536243606529529280603244763714848721282⟩
  | 0, 4 => ⟨4255473654293877903461595400285178040440437168, 4255473654293877903461595400285285038321476292⟩
  | 1, 3 => ⟨7401649976076562074250985672082237206204055064, 7401649976076562074250985672082396337934122139⟩
  | 2, 2 => ⟨10593150317169798602027278130609626583565114543, 10593150317169798602027278130609887116713431816⟩
  | 3, 1 => ⟨10756390325288111251822853218914040102901201480, 10756390325288111251822853218914481987454143750⟩
  | 0, 5 => ⟨-29746988238143210226430755142455025685620213708384, 29980803363579679196621721846003259327094686687345⟩
  | 1, 4 => ⟨-55920140999388787847653478801636598520810168357701, 56197492313462071791761505130113083834496186023866⟩
  | 2, 3 => ⟨-105600117709741502000605782281680259030377136169001, 105935341390584344731156158477238115170393042117208⟩
  | 3, 2 => ⟨-199774019684230428923933914538264324033234067549603, 200175541301991190979549579842969803156487107131024⟩
  | 4, 1 => ⟨-378108833549178865150401263653437634055758782253296, 378544354045284148923254126756342161691096538445653⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0159Geometry.ds, E8TAxisProd0159Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 104830015976773732082665994170585315045979147 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0159CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0160CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0160CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0160GraphCenterA.qJetBox,
   E8TAxisProd0160GraphCenterB.qJetBox,
   E8TAxisProd0160GraphCenterC.qJetBox,
   E8TAxisProd0160GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0160GraphWholeA.qJetBox,
   E8TAxisProd0160GraphWholeB.qJetBox,
   E8TAxisProd0160GraphWholeC.qJetBox,
   E8TAxisProd0160GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨333129103821281165528418581518142129805465513, 333129103821281165528418581518151215150654198⟩
  | 0, 2 => ⟨1415802766716810876814407004079218848980637896, 1415802766716810876814407004079241031251894384⟩
  | 1, 1 => ⟨1438746533341848878304101918394326208063529514, 1438746533341848878304101918394359112945308215⟩
  | 0, 3 => ⟨3839710055411864164799631718587964235604721665, 3839710055411864164799631718588022974113881134⟩
  | 1, 2 => ⟨5546925587181566401060451848044901233850628898, 5546925587181566401060451848044989556890406432⟩
  | 2, 1 => ⟨5624111739006941226482214660798185745004584485, 5624111739006941226482214660798330762706156113⟩
  | 0, 4 => ⟨8451548184048626624595948674654486367390498382, 8451548184048626624595948674654655382812694905⟩
  | 1, 3 => ⟨14121850464686805913697721424972189496723012451, 14121850464686805913697721424972453031919082704⟩
  | 2, 2 => ⟨19855488889944605662882649162579919939154742215, 19855488889944605662882649162580362902161741050⟩
  | 3, 1 => ⟨20095639735943910939169999601223394832776439481, 20095639735943910939169999601224160099860065018⟩
  | 0, 5 => ⟨-62020587053071484745964593186677704893659806841125, 62502288876535181693023553512694021556570514213486⟩
  | 1, 4 => ⟨-117998328543748587064612633226185138055604245591821, 118635171229864618582302372279546514122522048146451⟩
  | 2, 3 => ⟨-225223845637774633660416187836832689701608446371601, 226067008448252911419038571254247490213855139828146⟩
  | 3, 2 => ⟨-430481351156438541429130000568373929905549000123084, 431548780007980682253217907465014845773797228347452⟩
  | 4, 1 => ⟨-823217312820967370737119384386136803524697937692204, 824358640775979305859822141105061614787906590625075⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0160Geometry.ds, E8TAxisProd0160Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 247729784821049247463196027942104500411620536 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0160CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0161CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0161CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0161GraphCenterA.qJetBox,
   E8TAxisProd0161GraphCenterB.qJetBox,
   E8TAxisProd0161GraphCenterC.qJetBox,
   E8TAxisProd0161GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0161GraphWholeA.qJetBox,
   E8TAxisProd0161GraphWholeB.qJetBox,
   E8TAxisProd0161GraphWholeC.qJetBox,
   E8TAxisProd0161GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨253414949101585434928414418313525136812270981, 253414949101585434928414418313533294522690774⟩
  | 0, 2 => ⟨1105352967601463626396869880192351725708618994, 1105352967601463626396869880192371245374171285⟩
  | 1, 1 => ⟨1123914429793929120233588816948214562205405504, 1123914429793929120233588816948243095144174398⟩
  | 0, 3 => ⟨3044682355170594653130615708844688588797518241, 3044682355170594653130615708844739410745868048⟩
  | 1, 2 => ⟨4426323219117449310644014611174178764142405030, 4426323219117449310644014611174254040892754936⟩
  | 2, 1 => ⟨4489788653852670198998208554388543500119955095, 4489788653852670198998208554388666095324064499⟩
  | 0, 4 => ⟨6745513346433148624590024277937787931243255082, 6745513346433148624590024277937932421660725544⟩
  | 1, 3 => ⟨11407629662885459403521207435467740895738274058, 11407629662885459403521207435467962872185480436⟩
  | 2, 2 => ⟨16123324895501041504569983486793695219815413850, 16123324895501041504569983486794065265227694449⟩
  | 3, 1 => ⟨16323347551139520597878508504858477103283861988, 16323347551139520597878508504859112645192332108⟩
  | 0, 5 => ⟨-48214289708141119999850807207753981367225218192630, 48592516395884061921610573839065678487583597757377⟩
  | 1, 4 => ⟨-91389080896981938685154071622216045826979432459732, 91874413846980271076698111440336393233980109426342⟩
  | 2, 3 => ⟨-173852611177179568542029784009299131056815233825415, 174480270321660382806365183013706540493015287557989⟩
  | 3, 2 => ⟨-331224855311903648812767311596680523548538121805357, 332008692730177856035405966001586196914342998593575⟩
  | 4, 1 => ⟨-631366318699953225141888032825690169113263726917345, 632207065002456942242370208828282087749835062691265⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0161Geometry.ds, E8TAxisProd0161Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 187150219409281622141353469306831960857886454 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0161CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0162CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0162CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0162GraphCenterA.qJetBox,
   E8TAxisProd0162GraphCenterB.qJetBox,
   E8TAxisProd0162GraphCenterC.qJetBox,
   E8TAxisProd0162GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0162GraphWholeA.qJetBox,
   E8TAxisProd0162GraphWholeB.qJetBox,
   E8TAxisProd0162GraphWholeC.qJetBox,
   E8TAxisProd0162GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨329601574017150745361629612124802847954229701, 329601574017150745361629612124811903368711441⟩
  | 0, 2 => ⟨1406229857911225698487532131074442162023375128, 1406229857911225698487532131074464261460001545⟩
  | 1, 1 => ⟨1424923271708642419995541468994798879841596947, 1424923271708642419995541468994831657095417096⟩
  | 0, 3 => ⟨3818634870151488621152656801592156019989498056, 3818634870151488621152656801592214524719193602⟩
  | 1, 2 => ⟨5511715060541114378982634053485084370379619991, 5511715060541114378982634053485172326343764970⟩
  | 2, 1 => ⟨5574622156981436803217453669194488344614057973, 5574622156981436803217453669194632740226060375⟩
  | 0, 4 => ⟨8408633541515554861881555060171117384992210163, 8408633541515554861881555060171285689122765844⟩
  | 1, 3 => ⟨14046631660502087278196146879448795958132304256, 14046631660502087278196146879449058346125926036⟩
  | 2, 2 => ⟨19736277726958554445548335108673238751986021584, 19736277726958554445548335108673679725100247175⟩
  | 3, 1 => ⟨19932053254044324886201029283859731910023171884, 19932053254044324886201029283860493638201256983⟩
  | 0, 5 => ⟨-61638223165046476819102921402044799840985086851856, 62116593585051059617477542529910647851072077200692⟩
  | 1, 4 => ⟨-117259635008124627819208607621439527828928556521815, 117891339792210709333603790867095062402809599954798⟩
  | 2, 3 => ⟨-223792898008039531783763612894034408449967268977416, 224628057073221975349439876501320528145632008215188⟩
  | 3, 2 => ⟨-427705190812667333418878274156992948065687976012525, 428760275009250696593091591687181456119069806240969⟩
  | 4, 1 => ⟨-817826387588751116957208782454705617667884410217976, 818949434237860322227291875729464170517267369154300⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0162Geometry.ds, E8TAxisProd0162Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 244905889360819455976295154422510329385906411 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0162CertifiedArithmetic

end


