-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0380CertifiedArithmetic__8
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0380CertifiedArithmetic__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T21:33:50.229976+00:00
-- url     : https://prove2.me/theorems/845043a7-16f1-4756-beab-7d2fdc5094d0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0380CertifiedArithmetic (+7 modules: GeneralCK.Certificates.E8TAxisProd0381CertifiedArithmetic, GeneralCK.Certificates.E8TAx…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0380CertifiedArithmetic (+7 modules: GeneralCK.Certificates.E8TAxisProd0381CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0382CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0383CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0384CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0385CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0386CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0387CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0380CertifiedArithmetic (+7 modules: GeneralCK.Certificates.E8TAxisProd0381CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0382CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0383CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0384CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0385CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0386CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0387CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0380CertifiedArithmetic (+7 modules: GeneralCK.Certificates.E8TAxisProd0381CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0382CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0383CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0384CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0385CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0386CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0387CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0380CertifiedArithmetic (+7 modules: GeneralCK/Certificates/E8TAxisProd0381CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0382CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0383CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0384CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0385CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0386CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0387CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0377GraphCenterA__5
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0380GraphCenterB__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0372GraphCenterC__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0380GraphCenterD__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0375GraphWholeA__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0378GraphWholeB__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0378GraphWholeC__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0376GraphWholeD__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0369Geometry__24
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0382GraphCenterA__18
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0382GraphCenterC__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0383GraphWholeA__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0387GraphWholeC__12

-- ===== source module GeneralCK.Certificates.E8TAxisProd0380CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0380CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0380GraphCenterA.qJetBox,
   E8TAxisProd0380GraphCenterB.qJetBox,
   E8TAxisProd0380GraphCenterC.qJetBox,
   E8TAxisProd0380GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0380GraphWholeA.qJetBox,
   E8TAxisProd0380GraphWholeB.qJetBox,
   E8TAxisProd0380GraphWholeC.qJetBox,
   E8TAxisProd0380GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨62410947347483842303551898569204592700905291446, 62410947347483842303551898569204915920899638251⟩
  | 0, 2 => ⟨176071911562617919865084448270927965576876793549, 176071911562617919865084448270929294310632375696⟩
  | 1, 1 => ⟨176571414008245314349882891116193183403310543665, 176571414008245314349882891116195631584879328448⟩
  | 0, 3 => ⟨341931016381918927919930859881274247125774100403, 341931016381918927919930859881278718319441819230⟩
  | 1, 2 => ⟨456675234354243360855937217308604633202674381113, 456675234354243360855937217308612789628562350976⟩
  | 2, 1 => ⟨457819490888552024221982309531018662548621003246, 457819490888552024221982309531033708265438881661⟩
  | 0, 4 => ⟨553870653702238963459682864104905468653288373936, 553870653702238963459682864104921318673193859150⟩
  | 1, 3 => ⟨816086495736632200766191148461930748626454701966, 816086495736632200766191148461959960449045932609⟩
  | 2, 2 => ⟨1078833522189175199757191136509330156395176630187, 1078833522189175199757191136509384573242947155048⟩
  | 3, 1 => ⟨1081238396607109972602905495463468110517184315862, 1081238396607109972602905495463570203186492809469⟩
  | 0, 5 => ⟨-3150857783368194313461782122988323262291842172787029, 3166076897314787471496575192552954481761974705376931⟩
  | 1, 4 => ⟨-6190851928998591335124163043057397093637562364280761, 6213785195158957178203111786049654260377670378532341⟩
  | 2, 3 => ⟨-12174901775315933849552558343616281389373001107441697, 12207931724326212399444471901911407084804721126960256⟩
  | 3, 2 => ⟨-23958394267309964651929212124461796758254312463084172, 24001686955436708991281024804334739041184807087611730⟩
  | 4, 1 => ⟨-47171071391480967739934938499573752048055757463170813, 47215124976608358020492978995070796342950260273882888⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0380Geometry.ds, E8TAxisProd0380Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 58827889418992379501716623077854995308586078074 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0380CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0381CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0381CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0381GraphCenterA.qJetBox,
   E8TAxisProd0381GraphCenterB.qJetBox,
   E8TAxisProd0381GraphCenterC.qJetBox,
   E8TAxisProd0381GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0381GraphWholeA.qJetBox,
   E8TAxisProd0381GraphWholeB.qJetBox,
   E8TAxisProd0381GraphWholeC.qJetBox,
   E8TAxisProd0381GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨56352846094367359628677786458291196777521168842, 56352846094367359628677786458291488993721873531⟩
  | 0, 2 => ⟨160339084941450482767953075944761498202155677479, 160339084941450482767953075944762691211350957494⟩
  | 1, 1 => ⟨160798982224095980323345133008511866536770704717, 160798982224095980323345133008514059952331048767⟩
  | 0, 3 => ⟨313725010836011801079693344560956262499528453551, 313725010836011801079693344560960261872501633699⟩
  | 1, 2 => ⟨419374909496421242414014037160031791607538096726, 419374909496421242414014037160039072744290218920⟩
  | 2, 1 => ⟨420435761331849268776429293161408740291911091225, 420435761331849268776429293161422149527322996524⟩
  | 0, 4 => ⟨511291343677011590266849109337707838423106985120, 511291343677011590266849109337721942929373177964⟩
  | 1, 3 => ⟨754396028265151007727703467433133902998908943623, 754396028265151007727703467433159855201290150929⟩
  | 2, 2 => ⟨997996043737323066866751748620861143329440827734, 997996043737323066866751748620909423877659613933⟩
  | 3, 1 => ⟨1000234790695111712162487366851143246385799268600, 1000234790695111712162487366851233715075496874166⟩
  | 0, 5 => ⟨-2835606564947956439191146621364569371368399489327051, 2849572673188253143685156982707203041351717668718048⟩
  | 1, 4 => ⟨-5569007686646761161964950437783722667358127722532384, 5590058342477595624612445164454006109685498362025114⟩
  | 2, 3 => ⟨-10947276539348679010288586538729614579793765520895671, 10977602171564313872891358944927289682374296333176717⟩
  | 3, 2 => ⟨-21533364060128747059167495782208205062071519298609919, 21573119537815103787513517285725957229689324438427919⟩
  | 4, 1 => ⟨-42378202428736112807157877646270679262145696190041540, 42418665567041335165557056495731284914811020218828936⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0381Geometry.ds, E8TAxisProd0381Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 53091919665386965943471986862694200246948175404 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0381CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0382CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0382CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0382GraphCenterA.qJetBox,
   E8TAxisProd0382GraphCenterB.qJetBox,
   E8TAxisProd0382GraphCenterC.qJetBox,
   E8TAxisProd0382GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0382GraphWholeA.qJetBox,
   E8TAxisProd0382GraphWholeB.qJetBox,
   E8TAxisProd0382GraphWholeC.qJetBox,
   E8TAxisProd0382GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨62191124411422074783964232850365437521396459989, 62191124411422074783964232850365760066342459463⟩
  | 0, 2 => ⟨175644930243151939830036969468028750404899370859, 175644930243151939830036969468030076227211570583⟩
  | 1, 1 => ⟨176001207132817584432442760029883870412092708035, 176001207132817584432442760029886313187686929442⟩
  | 0, 3 => ⟨341239303026528149068478967493800502610373685323, 341239303026528149068478967493804963806527059800⟩
  | 1, 2 => ⟨455656086240673513183222779526399661557398985431, 455656086240673513183222779526407799623019780050⟩
  | 2, 1 => ⟨456472339217443303005616634949606843348658990897, 456472339217443303005616634949621854987254755169⟩
  | 0, 4 => ⟨552870991840415708265229358205453563424823382833, 552870991840415708265229358205469376459276666678⟩
  | 1, 3 => ⟨814550925030984601112313414974100832903589512389, 814550925030984601112313414974129976368627203767⟩
  | 2, 2 => ⟨1076609814401223587974245717541900977949757303179, 1076609814401223587974245717541955267051845780157⟩
  | 3, 1 => ⟨1078325444890186816752351476434780199863091819547, 1078325444890186816752351476434882052011639528618⟩
  | 0, 5 => ⟨-3144222396525630214802868130221998427678974704991422, 3159409933144518880060985874808162451337341405863633⟩
  | 1, 4 => ⟨-6177781344020985063145891789781966115352609107189852, 6200665520598547128010632564214316898256607975346510⟩
  | 2, 3 => ⟨-12149128214577452733826402132103114903936313680130808, 12182083370049886866529584535776709446736603097818923⟩
  | 3, 2 => ⟨-23907534981515842450271791192980311066520668807195008, 23950717507417909665794991893133599945629520658189712⟩
  | 4, 1 => ⟨-47070652825320939373716421989858016359857491820076321, 47114554578907276223664666005672796935070884336370548⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0382Geometry.ds, E8TAxisProd0382Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 58619279835226438643283099209421995787268500050 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0382CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0383CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0383CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0383GraphCenterA.qJetBox,
   E8TAxisProd0383GraphCenterB.qJetBox,
   E8TAxisProd0383GraphCenterC.qJetBox,
   E8TAxisProd0383GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0383GraphWholeA.qJetBox,
   E8TAxisProd0383GraphWholeB.qJetBox,
   E8TAxisProd0383GraphWholeC.qJetBox,
   E8TAxisProd0383GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨56152667169494722487742300737949760249957449261, 56152667169494722487742300737950051856531126154⟩
  | 0, 2 => ⟨159947327882865112758033439206216029286235378620, 159947327882865112758033439206217219678077467184⟩
  | 1, 1 => ⟨160275352587804424668038257335464992017757549662, 160275352587804424668038257335467180580943892556⟩
  | 0, 3 => ⟨313086475942225992955413175959610350374945096764, 313086475942225992955413175959614340790387524701⟩
  | 1, 2 => ⟨418432805496913682388377116690112603549622743201, 418432805496913682388377116690119868260526546907⟩
  | 2, 1 => ⟨419189557819268241206904588097883035874737976768, 419189557819268241206904588097896414658529522951⟩
  | 0, 4 => ⟨510364743737628658683996738460026866137514774423, 510364743737628658683996738460040937651320870157⟩
  | 1, 3 => ⟨752970779339241278138508116622813357167813689375, 752970779339241278138508116622839248471626281362⟩
  | 2, 2 => ⟨995930193200521757747690115829321715072563435239, 995930193200521757747690115829369881928029359869⟩
  | 3, 1 => ⟨997527307885837763340256446230976215481759261180, 997527307885837763340256446231066470301717792427⟩
  | 0, 5 => ⟨-2829451448119657674283078758762458963650086518238771, 2843388296541563047483346147419942151189991768354146⟩
  | 1, 4 => ⟨-5556885817978425520617505061573900542136101545731421, 5577891037830193509853731922771019188219815247792535⟩
  | 2, 3 => ⟨-10923379264978629272627464155423111887295457732421665, 10953635819300775629525429224403447956924359988367627⟩
  | 3, 2 => ⟨-21486218602908183174008833155565295949060219948027792, 21525872754314051670958549333781350914178917500654914⟩
  | 4, 1 => ⟨-42285139602673048339309952411853326333155922968575919, 42325464240812547405147738792509816807356222055815908⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0383Geometry.ds, E8TAxisProd0383Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 52902043436524441957592454436363594042906182095 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0383CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0384CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0384CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0384GraphCenterA.qJetBox,
   E8TAxisProd0384GraphCenterB.qJetBox,
   E8TAxisProd0384GraphCenterC.qJetBox,
   E8TAxisProd0384GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0384GraphWholeA.qJetBox,
   E8TAxisProd0384GraphWholeB.qJetBox,
   E8TAxisProd0384GraphWholeC.qJetBox,
   E8TAxisProd0384GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨50838041305528351265604726302601209668784313772, 50838041305528351265604726302601473969196431864⟩
  | 0, 2 => ⟨145895788086754032529551933981934695713113797582, 145895788086754032529551933981935766968878995675⟩
  | 1, 1 => ⟨146318972784269150620496613513574104086483623202, 146318972784269150620496613513576069271425719101⟩
  | 0, 3 => ⟨287656302663204051594413036464793796447546913056, 287656302663204051594413036464797373690535974704⟩
  | 1, 2 => ⟨384875924641048400217489201544264305117280841060, 384875924641048400217489201544270804247478560103⟩
  | 2, 1 => ⟨385859134611299537946068174369530521658604418277, 385859134611299537946068174369542470694128888375⟩
  | 0, 4 => ⟨471774849052908394284142713515982441957910883621, 471774849052908394284142713515994991423256242977⟩
  | 1, 3 => ⟨697088832530284589577420500213902397398682836190, 697088832530284589577420500213925449070376448250⟩
  | 2, 2 => ⟨922864760628968738098748231660228748646136605140, 922864760628968738098748231660271574615927079024⟩
  | 3, 1 => ⟨924948787194409962006304272739791287460970284153, 924948787194409962006304272739871434062387677742⟩
  | 0, 5 => ⟨-2544239429439521065293585194272359507517849668591756, 2557032013712435447626181127748789918949040624668408⟩
  | 1, 4 => ⟨-4994496033852560097471430300106543369779704487330052, 5013781616948268757692985246815014322325554150157072⟩
  | 2, 3 => ⟨-9813541588420685794528272203103196365243321102878768, 9841329507024524960553688781156060229917332880140460⟩
  | 3, 2 => ⟨-19294708857442332707723001763321929916645375941136128, 19331142806218767474202389488132125111433453379784800⟩
  | 4, 1 => ⟨-37955516168111170321464955024167718284945081698636687, 37992605265577459824528045120103848155820345593812018⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0384Geometry.ds, E8TAxisProd0384Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 47873001366135702063706884802765273629811082751 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0384CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0385CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0385CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0385GraphCenterA.qJetBox,
   E8TAxisProd0385GraphCenterB.qJetBox,
   E8TAxisProd0385GraphCenterC.qJetBox,
   E8TAxisProd0385GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0385GraphWholeA.qJetBox,
   E8TAxisProd0385GraphWholeB.qJetBox,
   E8TAxisProd0385GraphWholeC.qJetBox,
   E8TAxisProd0385GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨45821855797055008686291858734383341038009581884, 45821855797055008686291858734383580196698239427⟩
  | 0, 2 => ⟨132644946186532552994532759629922343222862307694, 132644946186532552994532759629923305251083472606⟩
  | 1, 1 => ⟨133034110971226444979538661293785436660201299397, 133034110971226444979538661293787197381599247555⟩
  | 0, 3 => ⟨263572890528723437445988735687098192697224212517, 263572890528723437445988735687101392274439702124⟩
  | 1, 2 => ⟨352980387805648038944755798125574732472508003858, 352980387805648038944755798125580532977329239648⟩
  | 2, 1 => ⟨353891322905516292224900404444736985037261784350, 353891322905516292224900404444747631281025914990⟩
  | 0, 4 => ⟨435108064439505315675307417813936705848964394311, 435108064439505315675307417813947870103769875982⟩
  | 1, 3 => ⟨643861108975279395050384919722694606265529707835, 643861108975279395050384919722715077286249470623⟩
  | 2, 2 => ⟨853045007546762119849071426372055300272347720404, 853045007546762119849071426372093278424448221820⟩
  | 3, 1 => ⟨854984944301760452200146459090662993904936737993, 854984944301760452200146459090733976174222192284⟩
  | 0, 5 => ⟨-2278199391168896515818902203576641400959114131462622, 2289919596064899025362902439848323716518895109304668⟩
  | 1, 4 => ⟨-4470118543254183726494742918956670166034868998131980, 4487792099195437615627635171139818728689015071945589⟩
  | 2, 3 => ⟨-8779127362398651711097662012466941455345730574978870, 8804599120864809262418218376596971486547471412266661⟩
  | 3, 2 => ⟨-17252940690804281745651167238025719439844529883294972, 17286345892503950805075850272599497957379301137235318⟩
  | 4, 1 => ⟨-33923335931210086798986701918581887261295606367415995, 33957355309641324149290437570127836788888199188328975⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0385Geometry.ds, E8TAxisProd0385Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 43128205365858983750872860513660357310406216891 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0385CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0386CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0386CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0386GraphCenterA.qJetBox,
   E8TAxisProd0386GraphCenterB.qJetBox,
   E8TAxisProd0386GraphCenterC.qJetBox,
   E8TAxisProd0386GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0386GraphWholeA.qJetBox,
   E8TAxisProd0386GraphWholeB.qJetBox,
   E8TAxisProd0386GraphWholeC.qJetBox,
   E8TAxisProd0386GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨50655896148403734363325526397376508024787997548, 50655896148403734363325526397376771774477492534⟩
  | 0, 2 => ⟨145536586058826072468594830917693731094304774392, 145536586058826072468594830917694799996852505906⟩
  | 1, 1 => ⟨145838422134544296946949992388692016799965218840, 145838422134544296946949992388693977629259911635⟩
  | 0, 3 => ⟨287067120906620901082893811080583960744979740002, 287067120906620901082893811080587529962173396124⟩
  | 1, 2 => ⟨384005390459182385765935822007194955528204265197, 384005390459182385765935822007201439963841210530⟩
  | 2, 1 => ⟨384706753346861461237388179030995203491847974001, 384706753346861461237388179031007125318613975395⟩
  | 0, 4 => ⟨470916200589445357054600784293122042458346579588, 470916200589445357054600784293134562495444319310⟩
  | 1, 3 => ⟨695766238237437285380455208911449509268384445095, 695766238237437285380455208911472506693339653137⟩
  | 2, 2 => ⟨920945836360625692866219019388251696159067496249, 920945836360625692866219019388294420958516267539⟩
  | 3, 1 => ⟨922432573191653892052198819428272751842614267178, 922432573191653892052198819428352708305469328122⟩
  | 0, 5 => ⟨-2538576052800357693435392421672625198211074504708090, 2551341539965268960641730891011327817892481828956148⟩
  | 1, 4 => ⟨-4983346203741032274267744264238009371404155633049192, 5002589728074471500539547661575663774619499879040525⟩
  | 2, 3 => ⟨-9791567816095207201367957953578629615093108152300683, 9819291882711946926443041272575498032009313217150774⟩
  | 3, 2 => ⟨-19251372553121899800060070302666374295787251250429574, 19287713140392048055559827630229181152820994198294443⟩
  | 4, 1 => ⟨-37870001159992854128771638419345916816317972022699532, 37906963527249094253264324285233000595387171652465651⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0386Geometry.ds, E8TAxisProd0386Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 47700313117590532015976082468789892350248778952 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0386CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0387CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0387CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0387GraphCenterA.qJetBox,
   E8TAxisProd0387GraphCenterB.qJetBox,
   E8TAxisProd0387GraphCenterC.qJetBox,
   E8TAxisProd0387GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0387GraphWholeA.qJetBox,
   E8TAxisProd0387GraphWholeB.qJetBox,
   E8TAxisProd0387GraphWholeC.qJetBox,
   E8TAxisProd0387GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨45656255389070596432782095935899735730627434912, 45656255389070596432782095935899974391642901162⟩
  | 0, 2 => ⟨132315819794308030723238910540396378622765769083, 132315819794308030723238910540397338535033207181⟩
  | 1, 1 => ⟨132593388183267925455468770080677579817272809892, 132593388183267925455468770080679336628765355696⟩
  | 0, 3 => ⟨263029502752267243156657057366669352245706096868, 263029502752267243156657057366672544631922238174⟩
  | 1, 2 => ⟨352176328571899794765228143666675837497633804991, 352176328571899794765228143666681624857413047187⟩
  | 2, 1 => ⟨352826130849055900316170584208716483248289028125, 352826130849055900316170584208727105183013497803⟩
  | 0, 4 => ⟨434312599980840649457437385949252854709750295298, 434312599980840649457437385949263992718544988322⟩
  | 1, 3 => ⟨642634018118472951625906341511497839091378254965, 642634018118472951625906341511518261798763137709⟩
  | 2, 2 => ⟨851262816654544029983798807422262567569462178203, 851262816654544029983798807422300455712399111358⟩
  | 3, 1 => ⟨852646759570271038131268191408553239105431220095, 852646759570271038131268191408624052372299442463⟩
  | 0, 5 => ⟨-2273173193498739709960383819184940728777472103969499, 2284869636313531217160756677541015416289829385042252⟩
  | 1, 4 => ⟨-4460226983494668591396780825870364313924675710329738, 4477863742926677258745790452664713139006922233606651⟩
  | 2, 3 => ⟨-8759640282877787939133530414782650733507600631269825, 8785056252413709986281880108491960354553250213013558⟩
  | 3, 2 => ⟨-17214521512653525300629307617973178937193364044786667, 17247845103147365456171418921682991248760509354840908⟩
  | 4, 1 => ⟨-33847548248260244842985806149683709301961491067556707, 33881456420981264053673409018793719442117371921409900⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0387Geometry.ds, E8TAxisProd0387Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 42971267016503469094927821256969369257878161242 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0387CertifiedArithmetic

end


