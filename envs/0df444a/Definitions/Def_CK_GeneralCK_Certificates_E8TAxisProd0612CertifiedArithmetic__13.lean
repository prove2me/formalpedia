-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0612CertifiedArithmetic__13
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0612CertifiedArithmetic__13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T13:57:07.602982+00:00
-- url     : https://prove2.me/theorems/36655cc0-a5bc-4f41-a5a9-e5564e584a32
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0612CertifiedArithmetic (+12 modules: GeneralCK.Certificates.E8TAxisProd0613CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0612CertifiedArithmetic (+12 modules: GeneralCK.Certificates.E8TAxisProd0613CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0614CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0615CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0616CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0617CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0618CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0619CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0620CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0621CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0622CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0623CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0624CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0612CertifiedArithmetic (+12 modules: GeneralCK.Certificates.E8TAxisProd0613CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0614CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0615CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0616CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0617CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0618CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0619CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0620CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0621CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0622CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0623CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0624CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0612CertifiedArithmetic (+12 modules: GeneralCK.Certificates.E8TAxisProd0613CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0614CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0615CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0616CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0617CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0618CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0619CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0620CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0621CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0622CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0623CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0624CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0612CertifiedArithmetic (+12 modules: GeneralCK/Certificates/E8TAxisProd0613CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0614CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0615CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0616CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0617CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0618CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0619CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0620CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0621CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0622CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0623CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0624CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0606GraphCenterA__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0600GraphCenterB__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0611GraphCenterC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0606GraphCenterD__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0601GraphWholeA__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0606GraphWholeB__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0606GraphWholeC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0602GraphWholeD__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0602Geometry__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0615GraphCenterB__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0615GraphWholeA__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0617GraphWholeD__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0618GraphCenterD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0618GraphWholeB__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0618Geometry__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0619GraphWholeC__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0621GraphCenterA__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0622GraphCenterC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0623GraphCenterB__14

-- ===== source module GeneralCK.Certificates.E8TAxisProd0612CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0612CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0612GraphCenterA.qJetBox,
   E8TAxisProd0612GraphCenterB.qJetBox,
   E8TAxisProd0612GraphCenterC.qJetBox,
   E8TAxisProd0612GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0612GraphWholeA.qJetBox,
   E8TAxisProd0612GraphWholeB.qJetBox,
   E8TAxisProd0612GraphWholeC.qJetBox,
   E8TAxisProd0612GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨13717697105389360023635223922176270871544466747, 13717697105389360023635223922176353410871044275⟩
  | 0, 2 => ⟨43833136786334297477271313700764028119274486565, 43833136786334297477271313700764327573919931294⟩
  | 1, 1 => ⟨43980655777994146186554323744437251630294377617, 43980655777994146186554323744437782073398207963⟩
  | 0, 3 => ⟨95459120079621088977522664482588186408323442209, 95459120079621088977522664482589141832250966874⟩
  | 1, 2 => ⟨129368217921099859367709294337796338528972197260, 129368217921099859367709294337798022174909514969⟩
  | 2, 1 => ⟨129749106471218487423316333744208865700880518352, 129749106471218487423316333744211891707224570314⟩
  | 0, 4 => ⟨171660669161081003587273573426026789078005106148, 171660669161081003587273573426029968637576009074⟩
  | 1, 3 => ⟨258958835110434929602818299159046116667738036370, 258958835110434929602818299159051816685857280558⟩
  | 2, 2 => ⟨346457951042792522529608417111869496063541576683, 346457951042792522529608417111879895076133293523⟩
  | 3, 1 => ⟨347335537389988494095808954791741835457526207964, 347335537389988494095808954791760980548440235015⟩
  | 0, 5 => ⟨-586249339872923389056218348321592217066231234899548, 589798309368941474992848376382465119230361165855039⟩
  | 1, 4 => ⟨-1142378146318679329644819444210750891798328154540638, 1147680614324915378167992345240193590489902392224001⟩
  | 2, 3 => ⟨-2228751931970406151385337807022815350451536418121011, 2236351869744596201313407087061075156181525178254597⟩
  | 3, 2 => ⟨-4351457357590384664478773407246083940087450422354674, 4361405335429840159025894020295376058525329008957117⟩
  | 4, 1 => ⟨-8500321822876580227612715954071181664836552842998264, 8510486086639256981435080795286229120973229447004646⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0612Geometry.ds, E8TAxisProd0612Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 12837560146347428091077677628838623847935324657 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0612CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0613CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0613CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0613GraphCenterA.qJetBox,
   E8TAxisProd0613GraphCenterB.qJetBox,
   E8TAxisProd0613GraphCenterC.qJetBox,
   E8TAxisProd0613GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0613GraphWholeA.qJetBox,
   E8TAxisProd0613GraphWholeB.qJetBox,
   E8TAxisProd0613GraphWholeC.qJetBox,
   E8TAxisProd0613GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨12218297896392855749045758987476409696332424286, 12218297896392855749045758987476484919589541594⟩
  | 0, 2 => ⟨39401417839378961211193090419452778761458214333, 39401417839378961211193090419453048472768242344⟩
  | 1, 1 => ⟨39535801771012717030118781975744683173694435419, 39535801771012717030118781975745159103928977598⟩
  | 0, 3 => ⟨86546304563590757137766750696390722637466104375, 86546304563590757137766750696391579308424619989⟩
  | 1, 2 => ⟨117437894656409710137954178862809451674544502659, 117437894656409710137954178862810956413512643862⟩
  | 2, 1 => ⟨117788372280747437807220495396731943306635477709, 117788372280747437807220495396734641772213489443⟩
  | 0, 4 => ⟨157005934609917030530586549286404488192993428546, 157005934609917030530586549286407326152094410195⟩
  | 1, 3 => ⟨237335561318456443810509310636662364576501075699, 237335561318456443810509310636667438956667403170⟩
  | 2, 2 => ⟨317852584494655986313077091211524287187394083861, 317852584494655986313077091211533528088534276034⟩
  | 3, 1 => ⟨318668136252862682784365199984349752306185431173, 318668136252862682784365199984366738615148703862⟩
  | 0, 5 => ⟨-509405838531828677104031051891616225174462403847879, 512548118135556139312728975514896833465629897867673⟩
  | 1, 4 => ⟨-991790105059892002202778231637655673996730365081277, 996476684979573533659737310148200166422495553891938⟩
  | 2, 3 => ⟨-1933403113343854477194028116005661134148381927991154, 1940112552541271333664320224439962750241836347312214⟩
  | 3, 2 => ⟨-3771858157838716308537476304976136590693440486996257, 3780635367048448049007980059733541649697016282739618⟩
  | 4, 1 => ⟨-7362386537994488323081332198829574673849110267451952, 7371355750047023049842653288705297847159238937148134⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0613Geometry.ds, E8TAxisProd0613Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 11428205035556116816489076382719017031545082533 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0613CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0614CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0614CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0614GraphCenterA.qJetBox,
   E8TAxisProd0614GraphCenterB.qJetBox,
   E8TAxisProd0614GraphCenterC.qJetBox,
   E8TAxisProd0614GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0614GraphWholeA.qJetBox,
   E8TAxisProd0614GraphWholeB.qJetBox,
   E8TAxisProd0614GraphWholeC.qJetBox,
   E8TAxisProd0614GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨13662980205992236217649073273768186852646540131, 13662980205992236217649073273768269224715560316⟩
  | 0, 2 => ⟨43713946908601138502932839628978820785311019539, 43713946908601138502932839628979119578847920456⟩
  | 1, 1 => ⟨43819147679229346350593843673370247040354587196, 43819147679229346350593843673370776290944011652⟩
  | 0, 3 => ⟨95244754288223771995242083056946734120576135097, 95244754288223771995242083056947687397816461481⟩
  | 1, 2 => ⟨129044850416184211857531406540062051984936444739, 129044850416184211857531406540063731791717657300⟩
  | 2, 1 => ⟨129316522072448133258960959162242954694517152473, 129316522072448133258960959162245973715517384929⟩
  | 0, 4 => ⟨171324694151312890309235361151948749706431282173, 171324694151312890309235361151951921850641960654⟩
  | 1, 3 => ⟨258429329783964703195676731620191740214439264439, 258429329783964703195676731620197426834632819815⟩
  | 2, 2 => ⟨345677327203513344608744563275108712136320226261, 345677327203513344608744563275119086516126445424⟩
  | 3, 1 => ⟨346303377736681418068256978518481318776239860799, 346303377736681418068256978518500418145458599888⟩
  | 0, 5 => ⟨-584622307347085602558679636832151471856552591264617, 588163059634665125115403840944365702328189790707029⟩
  | 1, 4 => ⟨-1139190742558613668626586237089371872183197524398602, 1144480869997932569817401457762391729050955076441098⟩
  | 2, 3 => ⟨-2222500444692232049457817030335404072520320051145380, 2230082711163589119300987621546562193210393483496619⟩
  | 3, 2 => ⟨-4339186669146582968350431968061883141762517055226103, 4349111539643611436873787594386205810171732880607430⟩
  | 4, 1 => ⟨-8476222263964453324939531538102284680875594404886021, 8486362433560539603681106104822934981903063297838630⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0614Geometry.ds, E8TAxisProd0614Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 12786006842625074186818625926105592408048919916 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0614CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0615CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0615CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0615GraphCenterA.qJetBox,
   E8TAxisProd0615GraphCenterB.qJetBox,
   E8TAxisProd0615GraphCenterC.qJetBox,
   E8TAxisProd0615GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0615GraphWholeA.qJetBox,
   E8TAxisProd0615GraphWholeB.qJetBox,
   E8TAxisProd0615GraphWholeC.qJetBox,
   E8TAxisProd0615GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨12169113687310599486286814162343100695545808458, 12169113687310599486286814162343175766935857339⟩
  | 0, 2 => ⟨39293357538832538236726847026711063709471614893, 39293357538832538236726847026711332825160226558⟩
  | 1, 1 => ⟨39389189693561869175418713785955039034709642390, 39389189693561869175418713785955513893586614963⟩
  | 0, 3 => ⟨86350240865245409462283515937186766764252073749, 86350240865245409462283515937187621507361283927⟩
  | 1, 2 => ⟨117141531249447461583222988974173371273244370375, 117141531249447461583222988974174872572542448559⟩
  | 2, 1 => ⟨117391508498620011682812988266055502403296882784, 117391508498620011682812988266058194620558341756⟩
  | 0, 4 => ⟨156696072710531592599548406655753184346972433636, 156696072710531592599548406655756015668360006144⟩
  | 1, 3 => ⟨236846035691749446674438335431429140087091109359, 236846035691749446674438335431434202496897027017⟩
  | 2, 2 => ⟨317129690436582741555401848921384561203825055749, 317129690436582741555401848921393780123928598977⟩
  | 3, 1 => ⟨317711482999618842076268178012571637427093572215, 317711482999618842076268178012588582979440368705⟩
  | 0, 5 => ⟨-507955305187617623826815643565104214182350368264049, 511090280242818427870964601436231911781187487044897⟩
  | 1, 4 => ⟨-988950092373672277811858439462574909751434905458973, 993625735175492917505556240436231951020716371747334⟩
  | 2, 3 => ⟨-1927836031203757970528147144910462649603024243869036, 1934529871131908307866856774684385812399376162741617⟩
  | 3, 2 => ⟨-3760936761969292623677960326950849226834093118341789, 3769693710891421895837388812222195111238159491534955⟩
  | 4, 1 => ⟨-7340948539005022664605182263975035434935681484771093, 7349896997610640458136924345746356556760987733131053⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0615Geometry.ds, E8TAxisProd0615Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 11381891236200276543267656885024662346687012190 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0615CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0616CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0616CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0616GraphCenterA.qJetBox,
   E8TAxisProd0616GraphCenterB.qJetBox,
   E8TAxisProd0616GraphCenterC.qJetBox,
   E8TAxisProd0616GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0616GraphWholeA.qJetBox,
   E8TAxisProd0616GraphWholeB.qJetBox,
   E8TAxisProd0616GraphWholeC.qJetBox,
   E8TAxisProd0616GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨17101556525691491540639721757921651901565867864, 17101556525691491540639721757921751088661438339⟩
  | 0, 2 => ⟨53790734651865215199948790593595731954734433558, 53790734651865215199948790593596099765867269156⟩
  | 1, 1 => ⟨53866470212003908322925381510755782924390891102, 53866470212003908322925381510756439083674264939⟩
  | 0, 3 => ⟨115261218682428288238545098385786263184522324123, 115261218682428288238545098385787446437438402209⟩
  | 1, 2 => ⟨155749422461296113852540994537777595910503446149, 155749422461296113852540994537779693591795525076⟩
  | 2, 1 => ⟨155941220324601975212763211814886869886956194632, 155941220324601975212763211814890655849232615984⟩
  | 0, 4 => ⟨203849963266232182595369915034037325534504729100, 203849963266232182595369915034041296763646620135⟩
  | 1, 3 => ⟨306260438886200421046399706777336440453698737241, 306260438886200421046399706777343593969829614246⟩
  | 2, 2 => ⟨408769637445921187439929287788803633763692313784, 408769637445921187439929287788816728698953031689⟩
  | 3, 1 => ⟨409203611304817281183244575823618534744890249366, 409203611304817281183244575823642714650021390647⟩
  | 0, 5 => ⟨-763340693376765314244899300601157062030771603506413, 767831622450673139578298419605632067599198827134816⟩
  | 1, 4 => ⟨-1489731424712055187101551269963412662351494793461048, 1496461879364008157986381399808254575829137038630222⟩
  | 2, 3 => ⟨-2910623100229093750186648923364276589669341980623126, 2920288619631346045054270275730959816923762781030611⟩
  | 3, 2 => ⟨-5690770203112152440191565771631022985084143422299695, 5703432891157793310883670837809318869937033858210491⟩
  | 4, 1 => ⟨-11132183094340198388350284114208957007958893899588509, 11145113324306098225948060672717565173494872982427135⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0616Geometry.ds, E8TAxisProd0616Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 16020688614220501652173772759462625210444739783 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0616CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0617CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0617CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0617GraphCenterA.qJetBox,
   E8TAxisProd0617GraphCenterB.qJetBox,
   E8TAxisProd0617GraphCenterC.qJetBox,
   E8TAxisProd0617GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0617GraphWholeA.qJetBox,
   E8TAxisProd0617GraphWholeB.qJetBox,
   E8TAxisProd0617GraphWholeC.qJetBox,
   E8TAxisProd0617GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨15263329775551881924156773954361470125605052998, 15263329775551881924156773954361560391324341520⟩
  | 0, 2 => ⟨48450185967187528724486122329802075709077385597, 48450185967187528724486122329802406812468483242⟩
  | 1, 1 => ⟨48519302369388882305713774853453120602532880988, 48519302369388882305713774853453709212304073037⟩
  | 0, 3 => ⟨104711728394018249156398962663570153762034979257, 104711728394018249156398962663571214599016849416⟩
  | 1, 2 => ⟨141662192490558986565708222543557728751801850717, 141662192490558986565708222543559603839248233052⟩
  | 2, 1 => ⟨141838947355643447914273355734420024377239058810, 141838947355643447914273355734423401533125502797⟩
  | 0, 4 => ⟨186780704253297109250225017158378079596729051880, 186780704253297109250225017158381624847261648074⟩
  | 1, 3 => ⟨281159653949789197485602729347311177010844705208, 281159653949789197485602729347317548151440582398⟩
  | 2, 2 => ⟨375630707682368576559673168458343720033818857280, 375630707682368576559673168458355363244893291230⟩
  | 3, 1 => ⟨376034259460631302225539018824102992764387312955, 376034259460631302225539018824124460286841989171⟩
  | 0, 5 => ⟨-668423709716681538144140567829433558876654609609605, 672411221631689470291478206212690399562778941274291⟩
  | 1, 4 => ⟨-1303512264425070512129380778803071923921992763638732, 1309478710239230443995684390216652743613262921871433⟩
  | 2, 3 => ⟨-2544974203167729711723748415248287425216751310526769, 2553533398247601041486318372276796450922754053263142⟩
  | 3, 2 => ⟨-4972387825453269648587733044138497620298227632323235, 4983594930173963911894268069226357962219765563292437⟩
  | 4, 1 => ⟨-9720130147718428966354913289301924807235304205435610, 9731575148924815452405511505991419806218859669748142⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0617Geometry.ds, E8TAxisProd0617Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 14290940764614137032612908105879566014469487448 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0617CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0618CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0618CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0618GraphCenterA.qJetBox,
   E8TAxisProd0618GraphCenterB.qJetBox,
   E8TAxisProd0618GraphCenterC.qJetBox,
   E8TAxisProd0618GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0618GraphWholeA.qJetBox,
   E8TAxisProd0618GraphWholeB.qJetBox,
   E8TAxisProd0618GraphWholeC.qJetBox,
   E8TAxisProd0618GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨13608412126578323810652813941790196189190039951, 13608412126578323810652813941790278394341657666⟩
  | 0, 2 => ⟨43595024725778372146318790662788933540339068338, 43595024725778372146318790662789231674194509347⟩
  | 1, 1 => ⟨43658043376414912924530773059557203671811718699, 43658043376414912924530773059557731732487397756⟩
  | 0, 3 => ⟨95030808101742985112758991215334036376227076727, 95030808101742985112758991215334987511510258855⟩
  | 1, 2 => ⟨128722144204387242506209360676347462956170500074, 128722144204387242506209360676349138932306642575⟩
  | 2, 1 => ⟨128884912553178663313106089559552157697131627384, 128884912553178663313106089559555169748350738770⟩
  | 0, 4 => ⟨170989301141161698015805064024579331701418731277, 170989301141161698015805064024582496447077874011⟩
  | 1, 3 => ⟨257900765864068074553977997884476295036845042530, 257900765864068074553977997884481968289548477081⟩
  | 2, 2 => ⟨344898143438866179415737113102106922146037736276, 344898143438866179415737113102117271949096487930⟩
  | 3, 1 => ⟨345273296241591311384702682339208950754621417311, 345273296241591311384702682339228004506360936112⟩
  | 0, 5 => ⟨-582998979865221230557371959269393494034488436045567, 586534886695872756671832558472335908464572071033865⟩
  | 1, 4 => ⟨-1136010619597811980532718938827860004344141537978648, 1141292459377808818792570389535468057939275659337619⟩
  | 2, 3 => ⟨-2216263283022112469237196972470081475749846542004251, 2223831946095474810024630333730654889898370549777460⟩
  | 3, 2 => ⟨-4326944191872247276296741482532182352394837589033818, 4336848700953449917644007200233763168934226252490939⟩
  | 4, 1 => ⟨-8452178296595921583930309308563591343566847545392985, 8462294454408753361360226486271450608092174261022171⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0618Geometry.ds, E8TAxisProd0618Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 12734594507690851501142222600523530286550415441 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0618CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0619CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0619CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0619GraphCenterA.qJetBox,
   E8TAxisProd0619GraphCenterB.qJetBox,
   E8TAxisProd0619GraphCenterC.qJetBox,
   E8TAxisProd0619GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0619GraphWholeA.qJetBox,
   E8TAxisProd0619GraphWholeB.qJetBox,
   E8TAxisProd0619GraphWholeC.qJetBox,
   E8TAxisProd0619GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨12120064400530084507905390572137551530361954796, 12120064400530084507905390572137626450193156428⟩
  | 0, 2 => ⟨39185542075969957320945503701673112405714790723, 39185542075969957320945503701673380927068959432⟩
  | 1, 1 => ⟨39242947688155658135852304362093940955775225195, 39242947688155658135852304362094414745635390136⟩
  | 0, 3 => ⟨86154564157072489617717709516499051637636509873, 86154564157072489617717709516499904457150143281⟩
  | 1, 2 => ⟨116845779202801259572464315137312279428611761204, 116845779202801259572464315137313777295880445361⟩
  | 2, 1 => ⟨116995547496304576646825830207452007692503730131, 116995547496304576646825830207454693675403651888⟩
  | 0, 4 => ⟨156386750191840454554183408784565009516527861415, 156386750191840454554183408784567834215275265777⟩
  | 1, 3 => ⟨236357384574902748114426253949499386537856224837, 236357384574902748114426253949504437004558076583⟩
  | 2, 2 => ⟨316408136422004506217483285466143825546802567185, 316408136422004506217483285466153022536010780796⟩
  | 3, 1 => ⟨316756765869836448179959089061453631211901190864, 316756765869836448179959089061470536100815507189⟩
  | 0, 5 => ⟨-506508206934123040713648739520853027180998649300506, 509639209569458277218565453591944075020953349488193⟩
  | 1, 4 => ⟨-986116827952657380981535826671073444514999525710562, 990785538077262411343311541486658704026260997754138⟩
  | 2, 3 => ⟨-1922282222663769884817746954340587639192471771376755, 1928964480685508584032681602213232194477675639957390⟩
  | 3, 2 => ⟨-3750041497037829690147696983962737469016473930123905, 3758780893003647429378244923897073605331917892194293⟩
  | 4, 1 => ⟨-7319562015129129643558001677290417558561047692629516, 7328489789983023216054483860278427767151755809852454⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0619Geometry.ds, E8TAxisProd0619Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 11335705159819085197296189110388307428334890649 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0619CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0620CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0620CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0620GraphCenterA.qJetBox,
   E8TAxisProd0620GraphCenterB.qJetBox,
   E8TAxisProd0620GraphCenterC.qJetBox,
   E8TAxisProd0620GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0620GraphWholeA.qJetBox,
   E8TAxisProd0620GraphWholeB.qJetBox,
   E8TAxisProd0620GraphWholeC.qJetBox,
   E8TAxisProd0620GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨10871129567634951080068580145173691587017121432, 10871129567634951080068580145173760195500424868⟩
  | 0, 2 => ⟨35380432538175628099311739491951572427454833233, 35380432538175628099311739491951815552093610207⟩
  | 1, 1 => ⟨35502735135874434676670097405214901829827990375, 35502735135874434676670097405215329159831261485⟩
  | 0, 3 => ⟨78381417739025922456092585205249306011868248898, 78381417739025922456092585205250075542941337883⟩
  | 1, 2 => ⟨106497429661394830762015359204732584594706390962, 106497429661394830762015359204733931943401475554⟩
  | 2, 1 => ⟨106819651693733809304763769445590549856558811134, 106819651693733809304763769445592960917387199979⟩
  | 0, 4 => ⟨143461180786552900665652441460452281307168728810, 143461180786552900665652441460454824139409458067⟩
  | 1, 3 => ⟨217316093708103891463975878766520529956604734371, 217316093708103891463975878766525065533830790845⟩
  | 2, 2 => ⟨291345706867186550181178972408400382072119566862, 291345706867186550181178972408408628155153979194⟩
  | 3, 1 => ⟨292103293203908341985357925127184395357618776464, 292103293203908341985357925127199531412375659508⟩
  | 0, 5 => ⟨-441201287407523949033161059461626217885992711154680, 443984401868941309112619975595379691795952269048937⟩
  | 1, 4 => ⟨-858222907222918992648279392906935521552270786671152, 862366595934389131172149750300870520898939174295105⟩
  | 2, 3 => ⟨-1671613675078394227745386384576947089266386832958825, 1677539244550845666332369923182920496964446075702849⟩
  | 3, 2 => ⟨-3258462313036385450744148661459223370761092904188567, 3266209757903111298028634563361133346305699349223056⟩
  | 4, 1 => ⟨-6355112105625900744543504556839197171575115484005286, 6363030412077772458232086023622646421082811622846788⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0620Geometry.ds, E8TAxisProd0620Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 10162641783421607060425362735084261876414154598 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0620CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0621CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0621CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0621GraphCenterA.qJetBox,
   E8TAxisProd0621GraphCenterB.qJetBox,
   E8TAxisProd0621GraphCenterC.qJetBox,
   E8TAxisProd0621GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0621GraphWholeA.qJetBox,
   E8TAxisProd0621GraphWholeB.qJetBox,
   E8TAxisProd0621GraphWholeC.qJetBox,
   E8TAxisProd0621GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨9662018121126666288968791446024319225167384906, 9662018121126666288968791446024381850718138333⟩
  | 0, 2 => ⟨31735931919369444266966681738999799966714512001, 31735931919369444266966681739000019235195581805⟩
  | 1, 1 => ⟨31847132015065938563191106769732790139593525482, 31847132015065938563191106769733173963403187145⟩
  | 0, 3 => ⟨70908809062269114379869480279627339458931061343, 70908809062269114379869480279628031139699999874⟩
  | 1, 2 => ⟨96473983269135008055333548138261756625877163248, 96473983269135008055333548138262963677894480467⟩
  | 2, 1 => ⟨96769964156702858019659883218213655275146438739, 96769964156702858019659883218215810623844525509⟩
  | 0, 4 => ⟨130949515659354893152620642882456236838312038886, 130949515659354893152620642882458517631977530352⟩
  | 1, 3 => ⟨198791253779493866771924234926396883919903468540, 198791253779493866771924234926400942007972346622⟩
  | 2, 2 => ⟨266795790210818405748102231657922916411896761080, 266795790210818405748102231657930282231932424327⟩
  | 3, 1 => ⟨267499186720421370442837434309501702939979612870, 267499186720421370442837434309515204095547944218⟩
  | 0, 5 => ⟨-380819007609926722995863086951617668367295690728786, 383282815964667907403032920141856560147348685532357⟩
  | 1, 4 => ⟨-740055990727526173798627079171328944626245380983344, 743717726684841727506158817612177056164039784395060⟩
  | 2, 3 => ⟨-1440165717621811782779245230183161359404772041362479, 1445396132453144282876232921649916113795687033059281⟩
  | 3, 2 => ⟨-2804876885450030057752515354948781380079095254022069, 2811711675453930551924539191030762657598008123285771⟩
  | 4, 1 => ⟨-5465792231497925682260413913554152682957028262069532, 5472779368468672943994767211077799086206461860897056⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0621Geometry.ds, E8TAxisProd0621Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 9027406596494168873568357450173000489450530440 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0621CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0622CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0622CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0622GraphCenterA.qJetBox,
   E8TAxisProd0622GraphCenterB.qJetBox,
   E8TAxisProd0622GraphCenterC.qJetBox,
   E8TAxisProd0622GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0622GraphWholeA.qJetBox,
   E8TAxisProd0622GraphWholeB.qJetBox,
   E8TAxisProd0622GraphWholeC.qJetBox,
   E8TAxisProd0622GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨10826965215768491714566073990049183589691199050, 10826965215768491714566073990049252060213707979⟩
  | 0, 2 => ⟨35282567770640886595464613628807627197653361769, 35282567770640886595464613628807869788326554891⟩
  | 1, 1 => ⟨35369783009151499649473341309508307956454536122, 35369783009151499649473341309508734329410162392⟩
  | 0, 3 => ⟨78202269817260584460677274899999085626962716902, 78202269817260584460677274899999853455261884688⟩
  | 1, 2 => ⟨106226067328466096934357583465505835895377128911, 106226067328466096934357583465507180217813950514⟩
  | 2, 1 => ⟨106455887878940558655555582742542544276847260933, 106455887878940558655555582742544949855921223166⟩
  | 0, 4 => ⟨143175577412887807303564209522257137552842432272, 143175577412887807303564209522259674655756364510⟩
  | 1, 3 => ⟨216863774494580503658622167310364971262350223101, 216863774494580503658622167310369496552955116775⟩
  | 2, 2 => ⟨290676604846101919985521881305054368738261942051, 290676604846101919985521881305062595989071473290⟩
  | 3, 1 => ⟨291217042188010488179679508115093013860094922990, 291217042188010488179679508115108115080747813991⟩
  | 0, 5 => ⟨-439920116085886870589197723055999324151468701857349, 442696828250736666489044284211997015396601781704861⟩
  | 1, 4 => ⟨-855716172077890151949405765709161103395393445997501, 859850298295833514911975925063727621301404869032205⟩
  | 2, 3 => ⟨-1666703030005692809738466874481048632655424457025815, 1672614989856300110423723592534740441657309365734619⟩
  | 3, 2 => ⟨-3248834701288583178921842789044704123297119855481793, 3256564504359341017548470294394587697501342900436547⟩
  | 4, 1 => ⟨-6336225360875709707868641589633436619443948109186857, 6344125648813623315883111545303598319955408230503280⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0622Geometry.ds, E8TAxisProd0622Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 10121078417280375724615068117790708876333241790 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0622CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0623CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0623CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0623GraphCenterA.qJetBox,
   E8TAxisProd0623GraphCenterB.qJetBox,
   E8TAxisProd0623GraphCenterC.qJetBox,
   E8TAxisProd0623GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0623GraphWholeA.qJetBox,
   E8TAxisProd0623GraphWholeB.qJetBox,
   E8TAxisProd0623GraphWholeC.qJetBox,
   E8TAxisProd0623GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨9622403561129158587903865700532133275885409631, 9622403561129158587903865700532195776043711447⟩
  | 0, 2 => ⟨31647398143813814904520240661873594450674158592, 31647398143813814904520240661873813237494978867⟩
  | 1, 1 => ⟨31726694732824821314882879448049543029214568573, 31726694732824821314882879448049925992330142865⟩
  | 0, 3 => ⟨70745286632111768515257790736923999852306682876, 70745286632111768515257790736924689999601409933⟩
  | 1, 2 => ⟨96225755334671009330672713835666815946580861292, 96225755334671009330672713835668020278730131141⟩
  | 2, 1 => ⟨96436856392567836977705893930530693969121387318, 96436856392567836977705893930532844397577346976⟩
  | 0, 4 => ⟨130686449852410629870480925991590007812151756219, 130686449852410629870480925991592283451163098327⟩
  | 1, 3 => ⟨198373567270597556379300507299016109888112646863, 198373567270597556379300507299020158725802637500⟩
  | 2, 2 => ⟨266176826077551118206938893065192026833771903618, 266176826077551118206938893065199375723324331642⟩
  | 3, 1 => ⟨266678601559133760714526647919624794256785103699, 266678601559133760714526647919638264108572430605⟩
  | 0, 5 => ⟨-379689425324808661942298997853006537523316355892647, 382147508049380966190089003529019909959797686438826⟩
  | 1, 4 => ⟨-737847307104520902924751843793392634921218604037601, 741500493798619950770633475223076795759196108421631⟩
  | 2, 3 => ⟨-1435841641614257337066557698850925407085300111654013, 1441059885003371908806484119603064132489976728552385⟩
  | 3, 2 => ⟨-2796404410014063511728111789222789654247981696982036, 2803223402959719786469083660556186990063290683954431⟩
  | 4, 1 => ⟨-5449181495109397459784244818400432387091079924943463, 5456152439666221858002026789659111737104080256462476⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0623Geometry.ds, E8TAxisProd0623Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 8990146421440048288834951365513676044976215783 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0623CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0624CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0624CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0624GraphCenterA.qJetBox,
   E8TAxisProd0624GraphCenterB.qJetBox,
   E8TAxisProd0624GraphCenterC.qJetBox,
   E8TAxisProd0624GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0624GraphWholeA.qJetBox,
   E8TAxisProd0624GraphWholeB.qJetBox,
   E8TAxisProd0624GraphWholeC.qJetBox,
   E8TAxisProd0624GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨8577977022056664850887646799464354197075267474, 8577977022056664850887646799464411409068333219⟩
  | 0, 2 => ⟨28436195535696331235423170280642274813956033908, 28436195535696331235423170280642472632895346740⟩
  | 1, 1 => ⟨28537201945961652439282725005739987809528217305, 28537201945961652439282725005740332604187086622⟩
  | 0, 3 => ⟨64076608840483252574827341266705062890751431529, 64076608840483252574827341266705684596946067205⟩
  | 1, 2 => ⟨87299616874228003984413544559994209270982002572, 87299616874228003984413544559995290430968980980⟩
  | 2, 1 => ⟨87571240290346183834951853293199350443307365021, 87571240290346183834951853293201276657357603997⟩
  | 0, 4 => ⟨119399566405432008212507586716694969572179070750, 119399566405432008212507586716697014715170129803⟩
  | 1, 3 => ⟨181659700277700779774228961142700379494116951522, 181659700277700779774228961142704008415993702225⟩
  | 2, 2 => ⟨244071467371814004804302393930085168802088348906, 244071467371814004804302393930091743924793446488⟩
  | 3, 1 => ⟨244724180249884539282057858553103416699149865234, 244724180249884539282057858553115450422098088468⟩
  | 0, 5 => ⟨-327619774772521896234657035550432180323528568469667, 329797960800535708961270332225627460562006323708577⟩
  | 1, 4 => ⟨-636020532167012395940191421244368144566186499466061, 639251574474004788235509015058205472561689808530126⟩
  | 2, 3 => ⟨-1236538687549987709624811653607400573397849921667132, 1241148317824369174427688041003765336394754910489209⟩
  | 3, 2 => ⟨-2406091685783212299902289038741784536781355262220079, 2412111814567998079001187825512274220917887081149826⟩
  | 4, 1 => ⟨-4684462768627402827222048388108956201721511580440533, 4690618922595994581793721179537713539042201193282030⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0624Geometry.ds, E8TAxisProd0624Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 8010162389619875735821550293771738653999456086 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0624CertifiedArithmetic

end


