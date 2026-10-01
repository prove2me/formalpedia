-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0568CertifiedArithmetic__14
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0568CertifiedArithmetic__14
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T13:53:24.894865+00:00
-- url     : https://prove2.me/theorems/951cb1c5-08cf-4664-841e-8fb48f1b1fb9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0568CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0569CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0568CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0569CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0570CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0571CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0572CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0573CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0574CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0575CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0576CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0577CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0578CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0579CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0580CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0581CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0568CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0569CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0570CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0571CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0572CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0573CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0574CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0575CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0576CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0577CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0578CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0579CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0580CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0581CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0568CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0569CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0570CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0571CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0572CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0573CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0574CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0575CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0576CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0577CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0578CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0579CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0580CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0581CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0568CertifiedArithmetic (+13 modules: GeneralCK/Certificates/E8TAxisProd0569CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0570CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0571CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0572CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0573CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0574CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0575CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0576CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0577CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0578CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0579CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0580CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0581CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0567GraphCenterA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0559GraphCenterB__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0562GraphCenterC__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0564GraphCenterD__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0565GraphWholeA__6
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0560GraphWholeB__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0565GraphWholeC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0563GraphWholeD__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0557Geometry__24
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0570GraphWholeB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0571GraphCenterB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0571GraphWholeA__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0572GraphWholeD__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0573GraphCenterD__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0576GraphCenterC__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0576GraphWholeC__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0578GraphCenterA__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0579GraphWholeA__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0581GraphCenterD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0581GraphWholeB__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0581Geometry__11

-- ===== source module GeneralCK.Certificates.E8TAxisProd0568CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0568CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0568GraphCenterA.qJetBox,
   E8TAxisProd0568GraphCenterB.qJetBox,
   E8TAxisProd0568GraphCenterC.qJetBox,
   E8TAxisProd0568GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0568GraphWholeA.qJetBox,
   E8TAxisProd0568GraphWholeB.qJetBox,
   E8TAxisProd0568GraphWholeC.qJetBox,
   E8TAxisProd0568GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4210417787762593564217494051200351339743539893, 4210417787762593564217494051200385638764164884⟩
  | 0, 2 => ⟨14636901956904945358642203434171149881653414417, 14636901956904945358642203434171258983708173013⟩
  | 1, 1 => ⟨14789282187004448958915115332902927397915490831, 14789282187004448958915115332903111969966844236⟩
  | 0, 3 => ⟨34544976168415385064672365798766750322196899316, 34544976168415385064672365798767083065344345744⟩
  | 1, 2 => ⟨47594634897907582462655883032561882087528567921, 47594634897907582462655883032562446567421372711⟩
  | 2, 1 => ⟨48029805406854803313018622841544056240665813212, 48029805406854803313018622841545046746916794503⟩
  | 0, 4 => ⟨67761102114839170962658147632274394367480876933, 67761102114839170962658147632275464152299591888⟩
  | 1, 3 => ⟨104701439320060063682132442928233619442027856386, 104701439320060063682132442928235479638406294499⟩
  | 2, 2 => ⟨141908599138695983391518386153973606742092978887, 141908599138695983391518386153976934530628563116⟩
  | 3, 1 => ⟨143030556489391364734653172937054474371607892630, 143030556489391364734653172937060501749065201926⟩
  | 0, 5 => ⟨-127551282233745179359229587438377348162653649921080, 128606906100789614043875287499581535200467492925262⟩
  | 1, 4 => ⟨-245755517214365466760063450982377784485913118640934, 247297249580775120269777508360644034195962117183921⟩
  | 2, 3 => ⟨-474549179292268489939252944213260094853879086537807, 476727739147984241075945830302388528675586397556944⟩
  | 3, 2 => ⟨-917431296804932459557862237337354479865668269068013, 920264461181714757463254976926845976097797319999105⟩
  | 4, 1 => ⟨-1774882775986478771482117224793772382169769122931024, 1777791509148619963310452891458150562476369912691513⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0568Geometry.ds, E8TAxisProd0568Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3918783158671556731924525018369230653822974292 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0568CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0569CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0569CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0569GraphCenterA.qJetBox,
   E8TAxisProd0569GraphCenterB.qJetBox,
   E8TAxisProd0569GraphCenterC.qJetBox,
   E8TAxisProd0569GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0569GraphWholeA.qJetBox,
   E8TAxisProd0569GraphWholeB.qJetBox,
   E8TAxisProd0569GraphWholeC.qJetBox,
   E8TAxisProd0569GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3708863033231422547187550730921126644030169897, 3708863033231422547187550730921158185918736481⟩
  | 0, 2 => ⟨13015227338462842516279053900361248978198694457, 13015227338462842516279053900361347754616549786⟩
  | 1, 1 => ⟨13152674045992478506261142409049371683936516926, 13152674045992478506261142409049537813940345430⟩
  | 0, 3 => ⟨30960845226177096308722306808886105552430976367, 30960845226177096308722306808886404846738837002⟩
  | 1, 2 => ⟨42733568042789015729280691796021718544916288274, 42733568042789015729280691796022223755644142389⟩
  | 2, 1 => ⟨43130002942980888080156043787545696806839152788, 43130002942980888080156043787546580705662668629⟩
  | 0, 4 => ⟨61247695042189366566525878833046818469046200752, 61247695042189366566525878833047775502290825499⟩
  | 1, 3 => ⟨94902155434803172268396322838775144850453709514, 94902155434803172268396322838776801978772260207⟩
  | 2, 2 => ⟨128803732078634286981704571980526293947002904865, 128803732078634286981704571980529250821435552380⟩
  | 3, 1 => ⟨129838463336125243099550316026630107390475358524, 129838463336125243099550316026635451959683763463⟩
  | 0, 5 => ⟨-107763817910067394179773634716236049127022744400290, 108698402464827657027585970526106116618045758386751⟩
  | 1, 4 => ⟨-207299949499804976922956737096837051265420193347087, 208659859691021625320327889646073695444826837460793⟩
  | 2, 3 => ⟨-399730652007730063302943914038342659143532794345773, 401647850944079061828674072691445432978040328080589⟩
  | 3, 2 => ⟨-771770463660475347813209228584379444918966059765957, 774261202848990022453383571475872152636912485114758⟩
  | 4, 1 => ⟨-1491177494930398572756771154038012852458744442479238, 1493737059928422512393896732052574453007268679123127⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0569Geometry.ds, E8TAxisProd0569Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3449834652591585051059931679073245622652714493 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0569CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0570CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0570CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0570GraphCenterA.qJetBox,
   E8TAxisProd0570GraphCenterB.qJetBox,
   E8TAxisProd0570GraphCenterC.qJetBox,
   E8TAxisProd0570GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0570GraphWholeA.qJetBox,
   E8TAxisProd0570GraphWholeB.qJetBox,
   E8TAxisProd0570GraphWholeC.qJetBox,
   E8TAxisProd0570GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4192148626533322820469670456062436275182411202, 4192148626533322820469670456062470508094910201⟩
  | 0, 2 => ⟨14593773637045276200887675223312421920122812366, 14593773637045276200887675223312530784186521930⟩
  | 1, 1 => ⟨14729870629809744538760060725636194282332469468, 14729870629809744538760060725636378440001994553⟩
  | 0, 3 => ⟨34460366000976667614235150937494349857236375259, 34460366000976667614235150937494681853711091526⟩
  | 1, 2 => ⟨47463905847353499562701458987250281756878015289, 47463905847353499562701458987250844938637318279⟩
  | 2, 1 => ⟨47852641704598474660486242242208552146222408056, 47852641704598474660486242242209540332941131100⟩
  | 0, 4 => ⟨67615211284829410953462412484035755123200074809, 67615211284829410953462412484036822407591739977⟩
  | 1, 3 => ⟨104465117384385968631960905179381800916305858267, 104465117384385968631960905179383656693850040433⟩
  | 2, 2 => ⟨141553443084156875198189321143048602975359824290, 141553443084156875198189321143051922747040019234⟩
  | 3, 1 => ⟨142555896813400370558323592932680663189066103002, 142555896813400370558323592932686675848549836739⟩
  | 0, 5 => ⟨-127126818558584579371905121599910286774663235228918, 128179947201592688799235897102656891622177842231485⟩
  | 1, 4 => ⟨-244930469575873181238071196701517936482692251281872, 246468429524370678990214721560167411798061065556330⟩
  | 2, 3 => ⟨-472942772491261710476481513523927363191802355691204, 475115852851510634911518509201375276302650245567897⟩
  | 3, 2 => ⟨-914300279225448819200768498286840328508579422775111, 917126065578590257408355910852839753803852553643031⟩
  | 4, 1 => ⟨-1768775854218302385437089041055226492845345075027258, 1771676297613528671950520127970269336300489655171210⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0570Geometry.ds, E8TAxisProd0570Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3901667596090901180056960969476428282940523240 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0570CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0571CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0571CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0571GraphCenterA.qJetBox,
   E8TAxisProd0571GraphCenterB.qJetBox,
   E8TAxisProd0571GraphCenterC.qJetBox,
   E8TAxisProd0571GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0571GraphWholeA.qJetBox,
   E8TAxisProd0571GraphWholeB.qJetBox,
   E8TAxisProd0571GraphWholeC.qJetBox,
   E8TAxisProd0571GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3692618167292129688098143713232223456009310153, 3692618167292129688098143713232254937506806987⟩
  | 0, 2 => ⟨12976574096964044695122612488540144188282309626, 12976574096964044695122612488540242749707808763⟩
  | 1, 1 => ⟨13099331171818120049717126997683334475374726803, 13099331171818120049717126997683500232743463448⟩
  | 0, 3 => ⟨30884368941020595540695084657957862242180442621, 30884368941020595540695084657958160864107756876⟩
  | 1, 2 => ⟨42615075758050834265861131219599967724099397400, 42615075758050834265861131219600471769978640585⟩
  | 2, 1 => ⟨42969202214090553145513209215680593625726519357, 42969202214090553145513209215681475447533255093⟩
  | 0, 4 => ⟨61114403253754015341338220312832999503602610676, 61114403253754015341338220312833954289533725390⟩
  | 1, 3 => ⟨94685570464869995416093628257678961652860623289, 94685570464869995416093628257680614820927473282⟩
  | 2, 2 => ⟨128477544456140535724677370371912464418553484378, 128477544456140535724677370371915414119493237797⟩
  | 3, 1 => ⟨129402044160655899525235902506397961416431082619, 129402044160655899525235902506403292832533865385⟩
  | 0, 5 => ⟨-107401180339723310913941800160395665029236149778242, 108333536197544968220878759487790742394915343531899⟩
  | 1, 4 => ⟨-206595862771019120273287825578404105351840990544060, 207952397570563747455163674009452188665372899330302⟩
  | 2, 3 => ⟨-398361143915038006419766869256415101192687447172369, 400273419205214355914930994631639051538214001438422⟩
  | 3, 2 => ⟨-769103724223756462142328228731164458869052599877627, 771587777167737514039270233503811208986386782212877⟩
  | 4, 1 => ⟨-1485980941062736555966458620638105478283398168423694, 1488532839328667725589775410630463574646475727970284⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0571Geometry.ds, E8TAxisProd0571Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3434624475489137654306377768381519575368111587 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0571CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0572CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0572CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0572GraphCenterA.qJetBox,
   E8TAxisProd0572GraphCenterB.qJetBox,
   E8TAxisProd0572GraphCenterC.qJetBox,
   E8TAxisProd0572GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0572GraphWholeA.qJetBox,
   E8TAxisProd0572GraphWholeB.qJetBox,
   E8TAxisProd0572GraphWholeC.qJetBox,
   E8TAxisProd0572GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3263059765228586144530555839443931572850286841, 3263059765228586144530555839443960610034882541⟩
  | 0, 2 => ⟨11560017613131085711778401227123793436224217616, 11560017613131085711778401227123882925423988029⟩
  | 1, 1 => ⟨11683867764612970898310585232797615536132891875, 11683867764612970898310585232797765131119133198⟩
  | 0, 3 => ⟨27714245317346004366622408424157934510259814483, 27714245317346004366622408424158203778067582303⟩
  | 1, 2 => ⟨38324135875382779273012193287418871248618685755, 38324135875382779273012193287419323391484298574⟩
  | 2, 1 => ⟨38684867500619653883148011345014942072818822278, 38684867500619653883148011345015730701781921055⟩
  | 0, 4 => ⟨55282027372434469461347436270176579541807789723, 55282027372434469461347436270177435475681176960⟩
  | 1, 3 => ⟨85907588185611294621890100576409111323512603758, 85907588185611294621890100576410586729450773801⟩
  | 2, 2 => ⟨116761758971814957988731401508910945473177218980, 116761758971814957988731401508913570916625994780⟩
  | 3, 1 => ⟨117714906151672648075796556599293639927766823249, 117714906151672648075796556599298375207645340114⟩
  | 0, 5 => ⟨-90878416670127576466533205006815177614946568856109, 91705787249382614419698406656139176682364119669495⟩
  | 1, 4 => ⟨-174521153791197885613656508804677774821200914033113, 175720229694937041278446836298517558702171742456552⟩
  | 2, 3 => ⟨-336024345665214290051493954980241807405952438371984, 337710551758414318646602095263814109678362920885764⟩
  | 3, 2 => ⟨-647871951527015049871571380023580038704421814989873, 650060155514013384773894007258434576517685037531337⟩
  | 4, 1 => ⟨-1250107616838916376170334952613196955197290531897130, 1252358549467865723101842139564255479756125204303277⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0572Geometry.ds, E8TAxisProd0572Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3033239817840430797978806192123239216373917547 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0572CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0573CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0573CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0573GraphCenterA.qJetBox,
   E8TAxisProd0573GraphCenterB.qJetBox,
   E8TAxisProd0573GraphCenterC.qJetBox,
   E8TAxisProd0573GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0573GraphWholeA.qJetBox,
   E8TAxisProd0573GraphWholeB.qJetBox,
   E8TAxisProd0573GraphWholeC.qJetBox,
   E8TAxisProd0573GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2867263083455365739598206665147589174131157481, 2867263083455365739598206665147615934462571160⟩
  | 0, 2 => ⟨10255712763631644760223367133098903453906724966, 10255712763631644760223367133098984588867402914⟩
  | 1, 1 => ⟨10367197925994075671726426278980912193318063457, 10367197925994075671726426278981046963455023802⟩
  | 0, 3 => ⟨24777262265521645980072684599483812653809416232, 24777262265521645980072684599484054973370501044⟩
  | 1, 2 => ⟨34329449853614382976035402168631255955054860850, 34329449853614382976035402168631660599224708387⟩
  | 2, 1 => ⟨34657313448440921212338502601147292486309240037, 34657313448440921212338502601147996013181986122⟩
  | 0, 4 => ⟨49825403985016535527751966138332278928918184668, 49825403985016535527751966138333044277330464017⟩
  | 1, 3 => ⟨77662351008592148934989479616887745248325525177, 77662351008592148934989479616889058173388887306⟩
  | 2, 2 => ⟨105710540699469377521971956879238206690756437162, 105710540699469377521971956879240536263180927143⟩
  | 3, 1 => ⟨106587434901494509235596973897504648111315886594, 106587434901494509235596973897508840256657971403⟩
  | 0, 5 => ⟨-76805036195685340924188606723921647944214911502692, 77528709243853169718349262357085385684409642552250⟩
  | 1, 4 => ⟨-147231084749071328620761147854894652659999898967111, 148273938397187660799936752535782879826043895613729⟩
  | 2, 3 => ⟨-283037849129998201202374669448657846585246687522140, 284498923527547636867319788066205936160592351968827⟩
  | 3, 2 => ⟨-544917873118824044187942095042527064934828002793677, 546810573928915927719833235875279483164386854802291⟩
  | 4, 1 => ⟨-1049970615849790421112803593477522192238305964626082, 1051919690162163200427474147444769038084676735359398⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0573Geometry.ds, E8TAxisProd0573Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2663559520732819292698839742233941636507983032 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0573CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0574CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0574CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0574GraphCenterA.qJetBox,
   E8TAxisProd0574GraphCenterB.qJetBox,
   E8TAxisProd0574GraphCenterC.qJetBox,
   E8TAxisProd0574GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0574GraphWholeA.qJetBox,
   E8TAxisProd0574GraphWholeB.qJetBox,
   E8TAxisProd0574GraphWholeC.qJetBox,
   E8TAxisProd0574GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3248631376980777248963647398779396221551838498, 3248631376980777248963647398779425203524531189⟩
  | 0, 2 => ⟨11525417963883630054347489508040701132726331478, 11525417963883630054347489508040790427652364877⟩
  | 1, 1 => ⟨11636029658422693426907971520654604549823097541, 11636029658422693426907971520654753809697851838⟩
  | 0, 3 => ⟨27645218814175556285884330828164937521450507796, 27645218814175556285884330828165206183819319919⟩
  | 1, 2 => ⟨38216875328147877108550831182715524571068771495, 38216875328147877108550831182715975668977293459⟩
  | 2, 1 => ⟨38539102368263211879767281089210090917158422999, 38539102368263211879767281089210877686977374808⟩
  | 0, 4 => ⟨55160416522079339810473169990032098498671864868, 55160416522079339810473169990032952413896780790⟩
  | 1, 3 => ⟨85709352558604211012681819311461196653885691565, 85709352558604211012681819311462668513400013691⟩
  | 2, 2 => ⟨116462555315554203633327572386231422509266895284, 116462555315554203633327572386234041539718491354⟩
  | 3, 1 => ⟨117314144053680603046709606969283431301362593649, 117314144053680603046709606969288154838312008932⟩
  | 0, 5 => ⟨-90569394397432621609751183326195340253888907827420, 91394771286242654898762572466812542680004215436557⟩
  | 1, 4 => ⟨-173921861956449092311582016196010298293081112246224, 175117912642516512384197882124919944610551104915207⟩
  | 2, 3 => ⟨-334859883995450724753793289568755717270526538344761, 336541657206067533618991435768871788209565624368744⟩
  | 3, 2 => ⟨-645606697079253597489269155305013361148603976335344, 647788827397580242146658330469928196038207310873963⟩
  | 4, 1 => ⟨-1245697586833823502200843969255692339207808050642359, 1247941410238019030366119175563313627469689892267466⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0574Geometry.ds, E8TAxisProd0574Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3019738410548725266001291873366488796466693738 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0574CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0575CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0575CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0575GraphCenterA.qJetBox,
   E8TAxisProd0575GraphCenterB.qJetBox,
   E8TAxisProd0575GraphCenterC.qJetBox,
   E8TAxisProd0575GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0575GraphWholeA.qJetBox,
   E8TAxisProd0575GraphWholeB.qJetBox,
   E8TAxisProd0575GraphWholeC.qJetBox,
   E8TAxisProd0575GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2854462783526785472266189120392349668007443747, 2854462783526785472266189120392376377820266511⟩
  | 0, 2 => ⟨10224780083031000471821115032804243817764455602, 10224780083031000471821115032804324777114549146⟩
  | 1, 1 => ⟨10324346740180403848402237007436630033160546175, 10324346740180403848402237007436764501907311113⟩
  | 0, 3 => ⟨24715049776801538314207782306870763736976901988, 24715049776801538314207782306871005511399303122⟩
  | 1, 2 => ⟨34232485196104613346203854089445204467094336867, 34232485196104613346203854089445608174109762068⟩
  | 2, 1 => ⟨34525346636402773683003504217672702423872926030, 34525346636402773683003504217673404287250476288⟩
  | 0, 4 => ⟨49714613775986274094926931685519928403896386181, 49714613775986274094926931685520691940095620407⟩
  | 1, 3 => ⟨77481161346880944325347003871564892089817216918, 77481161346880944325347003871566201841603205117⟩
  | 2, 2 => ⟨105436453753810577171160544077920947517103201439, 105436453753810577171160544077923271361715548323⟩
  | 3, 1 => ⟨106219896831639586743859454500230763629302374057, 106219896831639586743859454500234945301335581423⟩
  | 0, 5 => ⟨-76546580067437959184367145122191787191784950383987, 77268350995368885269615210480625392721389657821038⟩
  | 1, 4 => ⟨-146730434456463550641844537846272373400699504187317, 147770394992553972126116199900046077656944759903614⟩
  | 2, 3 => ⟨-282065999768791624417750376882738979976806225889705, 283522829388104973482779934051081751346120281937751⟩
  | 3, 2 => ⟨-543028957900965512060371653190480695399673693164975, 544915852882659653306931866557974434405014849606650⟩
  | 4, 1 => ⟨-1046296228686540874281698695066362165891859556790607, 1048238574854638025401741740389242942106840635055468⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0575Geometry.ds, E8TAxisProd0575Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2651588491106438610559011902847575075652270078 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0575CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0576CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0576CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0576GraphCenterA.qJetBox,
   E8TAxisProd0576GraphCenterB.qJetBox,
   E8TAxisProd0576GraphCenterC.qJetBox,
   E8TAxisProd0576GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0576GraphWholeA.qJetBox,
   E8TAxisProd0576GraphWholeB.qJetBox,
   E8TAxisProd0576GraphWholeC.qJetBox,
   E8TAxisProd0576GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨17508243132126971931437463609737472725158322528, 17508243132126971931437463609737573134965185371⟩
  | 0, 2 => ⟨54660949254587178332777653039712533452148205940, 54660949254587178332777653039712906167580657279⟩
  | 1, 1 => ⟨55043239255241132193076521470436013365821829254, 55043239255241132193076521470436678418360901866⟩
  | 0, 3 => ⟨116798974000145841341491001685334931186007363092, 116798974000145841341491001685336130465410329620⟩
  | 1, 2 => ⟨158060308030638000203793506836524794766816453857, 158060308030638000203793506836526921236632200222⟩
  | 2, 1 => ⟨159027467259716636305426237858124603488480761932, 159027467259716636305426237858128441994233955984⟩
  | 0, 4 => ⟨206222199175649247959825878235684137070286850860, 206222199175649247959825878235688164043978270416⟩
  | 1, 3 => ⟨309982281615237319194810547955738973876116719102, 309982281615237319194810547955746228460258190921⟩
  | 2, 2 => ⟨414239563539311043367307745456511160091175247792, 414239563539311043367307745456524441278297453074⟩
  | 3, 1 => ⟨416425924246800965851266463848184771961096087701, 416425924246800965851266463848209298277253745175⟩
  | 0, 5 => ⟨-775480546656130866863443488585402828284844402480063, 780030609581742956845812141274805451748063999242510⟩
  | 1, 4 => ⟨-1513538096860390979237258064138147628533156993949099, 1520359015028549428023169288141358705341928027958504⟩
  | 2, 3 => ⟨-2957361929169655787215976575723980470992132759668440, 2967159966436777728920843523727611648840780148580612⟩
  | 3, 2 => ⟨-5782601896379858049356949966059970337981984310280758, 5795443166792044654643192516173616551385321878753956⟩
  | 4, 1 => ⟨-11312718487943625023866949105962188992126530085957939, 11325844977937040992394017513037058042399930367278022⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0576Geometry.ds, E8TAxisProd0576Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 16404312083086686720434876972801667972298574021 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0576CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0577CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0577CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0577GraphCenterA.qJetBox,
   E8TAxisProd0577GraphCenterB.qJetBox,
   E8TAxisProd0577GraphCenterC.qJetBox,
   E8TAxisProd0577GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0577GraphWholeA.qJetBox,
   E8TAxisProd0577GraphWholeB.qJetBox,
   E8TAxisProd0577GraphWholeC.qJetBox,
   E8TAxisProd0577GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨15629664359065095737440998180855964432051707064, 15629664359065095737440998180856055806935979576⟩
  | 0, 2 => ⟨49240797617374008440948027259857120298298490198, 49240797617374008440948027259857455819255153196⟩
  | 1, 1 => ⟨49589708630059471932984832333962696695109785802, 49589708630059471932984832333963293295035085705⟩
  | 0, 3 => ⟨106120782725690615060209962551561828888999403892, 106120782725690615060209962551562904117689531476⟩
  | 1, 2 => ⟨143783782012906879031737532570129508490917079857, 143783782012906879031737532570131409373845354623⟩
  | 2, 1 => ⟨144675153617605159217174827497646879552347465613, 144675153617605159217174827497650303716325084296⟩
  | 0, 4 => ⟨188970897158643566283618185995633476381512356008, 188970897158643566283618185995637071519888082147⟩
  | 1, 3 => ⟨284603652987715692576029267061415108215392007046, 284603652987715692576029267061421569642972361981⟩
  | 2, 2 => ⟨380700280830211961435336107571347231440580364515, 380700280830211961435336107571359040834538367079⟩
  | 3, 1 => ⟨382733430487685295577322331493871405217975115261, 382733430487685295577322331493893181502850815064⟩
  | 0, 5 => ⟨-679355606128147795016413834739437040335632285376383, 683395355837427526907401635317258972391965277124891⟩
  | 1, 4 => ⟨-1324939667626749686867944130430895024549295235211876, 1330985861346271285757023756903951937770366993956636⟩
  | 2, 3 => ⟨-2587021917372069697842045438171625354328467113877889, 2595697592967369614974762626918869725866260519186571⟩
  | 3, 2 => ⟨-5054963522964604179301607744128029902255508603796827, 5066326714020261438127827260390781962030582959888440⟩
  | 4, 1 => ⟨-9882392077301263604560008148714226276898573360640483, 9894005811494214911815244842930751632831711653032131⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0577Geometry.ds, E8TAxisProd0577Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 14636301484604828948708036288955454917668824608 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0577CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0578CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0578CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0578GraphCenterA.qJetBox,
   E8TAxisProd0578GraphCenterB.qJetBox,
   E8TAxisProd0578GraphCenterC.qJetBox,
   E8TAxisProd0578GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0578GraphWholeA.qJetBox,
   E8TAxisProd0578GraphWholeB.qJetBox,
   E8TAxisProd0578GraphWholeC.qJetBox,
   E8TAxisProd0578GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨17440008127659884027912379214156017580253131414, 17440008127659884027912379214156117785232296097⟩
  | 0, 2 => ⟨54515111544731123174466053903781630403784982182, 54515111544731123174466053903782002297420767255⟩
  | 1, 1 => ⟨54845905881536937010442688478139872455335903467, 54845905881536937010442688478140536017593525074⟩
  | 0, 3 => ⟨116541444493182892193735590220748790989353200521, 116541444493182892193735590220749987582960613968⟩
  | 1, 2 => ⟨157673219697538975527105200808449804198859338465, 157673219697538975527105200808451925844025201600⟩
  | 2, 1 => ⟨158510240375784292110656695020388279260831489616, 158510240375784292110656695020392108960660687478⟩
  | 0, 4 => ⟨205825125683367458046787769123916262641343490422, 205825125683367458046787769123920280271641572165⟩
  | 1, 3 => ⟨309359234554749246256506511192133904594821681473, 309359234554749246256506511192141142238746732767⟩
  | 2, 2 => ⟨413323730212293963821429855804137084041861930697, 413323730212293963821429855804150334010792621403⟩
  | 3, 1 => ⟨415216186514624234092164538880055350602338845906, 415216186514624234092164538880079818855158088769⟩
  | 0, 5 => ⟨-773446622562447985256248410094147558745475137323153, 777986200257318289552330977549101639888326512093675⟩
  | 1, 4 => ⟨-1509549451386723315050933400711005960059718577869477, 1516354513423392523078074480834316917230175239320148⟩
  | 2, 3 => ⟨-2949531049290099870759642361291597359857777602448032, 2959306168939505031573128412238104109217248900537744⟩
  | 3, 2 => ⟨-5767215685410454263834963704168967237003111330198219, 5780026516869633547178983240692033523353235439510971⟩
  | 4, 1 => ⟨-11282469695018784015988784171870711764133572565160331, 11295563173595584758118202950865190199204990767331029⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0578Geometry.ds, E8TAxisProd0578Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 16339944325850410958073482363496133216045106786 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0578CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0579CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0579CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0579GraphCenterA.qJetBox,
   E8TAxisProd0579GraphCenterB.qJetBox,
   E8TAxisProd0579GraphCenterC.qJetBox,
   E8TAxisProd0579GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0579GraphWholeA.qJetBox,
   E8TAxisProd0579GraphWholeB.qJetBox,
   E8TAxisProd0579GraphWholeC.qJetBox,
   E8TAxisProd0579GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨15568196207420768884541135967292748041826275668, 15568196207420768884541135967292839230905740336⟩
  | 0, 2 => ⟨49108294176968119139830970127119054290965313020, 49108294176968119139830970127119389071681882700⟩
  | 1, 1 => ⟨49410201098938914257029578580123757869570455620, 49410201098938914257029578580124353130538375390⟩
  | 0, 3 => ⟨105884798300532806837472525936784917827504278016, 105884798300532806837472525936785990644297505935⟩
  | 1, 2 => ⟨143428387893456408408589428044556801992632895997, 143428387893456408408589428044558698552373256421⟩
  | 2, 1 => ⟨144199808939021709737057565402302072808898835428, 144199808939021709737057565402305489094354179143⟩
  | 0, 4 => ⟨188604288499382727863151942912039909102731345757, 188604288499382727863151942912043495878483176648⟩
  | 1, 3 => ⟨284027108299041474839587959475282558569179809608, 284027108299041474839587959475289004861833156488⟩
  | 2, 2 => ⟨379851464844568331473208253717162711466550403433, 379851464844568331473208253717174493002702519156⟩
  | 3, 1 => ⟨381611297766168979186802332907913681315926420905, 381611297766168979186802332907935405841132340037⟩
  | 0, 5 => ⟨-677523655253195835955281263476797049791551654471991, 681554080279026800356626033418979431189780674337489⟩
  | 1, 4 => ⟨-1321348842856256496156041408461343758927667652131606, 1327380983331961431247701340761254675558303512893232⟩
  | 2, 3 => ⟨-2579975410091940329865669611907599802452137717587588, 2588630865977829098426352649889638634072893888002981⟩
  | 3, 2 => ⟨-5041124961705226590360629444153902916995958368761366, 5052461499309375128206822042222142986151828465636622⟩
  | 4, 1 => ⟨-9855198726067943193472971282890701129121767405312277, 9866784088733314283958026905458546317761158300818091⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0579Geometry.ds, E8TAxisProd0579Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 14578350470204674405680526284401121658486416960 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0579CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0580CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0580CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0580GraphCenterA.qJetBox,
   E8TAxisProd0580GraphCenterB.qJetBox,
   E8TAxisProd0580GraphCenterC.qJetBox,
   E8TAxisProd0580GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0580GraphWholeA.qJetBox,
   E8TAxisProd0580GraphWholeB.qJetBox,
   E8TAxisProd0580GraphWholeC.qJetBox,
   E8TAxisProd0580GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨13938059611601241498743887057761021754829016224, 13938059611601241498743887057761104966601390509⟩
  | 0, 2 => ⟨44312583759263184777353941695950080727113549412, 44312583759263184777353941695950382840525127615⟩
  | 1, 1 => ⟨44630742701717255524918714602126429248830654441, 44630742701717255524918714602126964488110265089⟩
  | 0, 3 => ⟨96320793873183012104399321403833971558292503458, 96320793873183012104399321403834935616476809569⟩
  | 1, 2 => ⟨130668324455278224892002908423868505420788736676, 130668324455278224892002908423870204508834057923⟩
  | 2, 1 => ⟨131489228938768095357070149211794741544156116828, 131489228938768095357070149211797795648184474249⟩
  | 0, 4 => ⟨173010407646640505293704958810245731288674475515, 173010407646640505293704958810248940678528745086⟩
  | 1, 3 => ⟨261086301320963811305373993161520572303901809483, 261086301320963811305373993161526326219444435064⟩
  | 2, 2 => ⟨349594895548433468884411611029178839392139602529, 349594895548433468884411611029189337498760803444⟩
  | 3, 1 => ⟨351485029970020985660195044290147185110019100681, 351485029970020985660195044290166514134527913016⟩
  | 0, 5 => ⟨-592794647040854439605653305225002833860866045734664, 596376678438846039367851965155320621767958526125070⟩
  | 1, 4 => ⟨-1155200805647814052997820997318875452200452546382241, 1160552933730323162182461124961901960348981141707826⟩
  | 2, 3 => ⟨-2253901591118123330887786229206857083128110657148135, 2261572661782295449270215640791215033403353208166423⟩
  | 3, 2 => ⟨-4400823107977288053887500070455969860803797662364176, 4410864155425171658818921977536776732893193096026335⟩
  | 4, 1 => ⟨-8597277711401198938881066775075878160176796498357606, 8607539179114060447509582176263297384799771615618342⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0580Geometry.ds, E8TAxisProd0580Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 13045189456839630108562674126195484718887275386 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0580CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0581CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0581CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0581GraphCenterA.qJetBox,
   E8TAxisProd0581GraphCenterB.qJetBox,
   E8TAxisProd0581GraphCenterC.qJetBox,
   E8TAxisProd0581GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0581GraphWholeA.qJetBox,
   E8TAxisProd0581GraphWholeB.qJetBox,
   E8TAxisProd0581GraphWholeC.qJetBox,
   E8TAxisProd0581GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨12416390091823860599992347856930605670400222897, 12416390091823860599992347856930681504220511931⟩
  | 0, 2 => ⟨39836117114259418734355253869220251962823916030, 39836117114259418734355253869220524069544491323⟩
  | 1, 1 => ⟨40125966119485254868168973264014129625513767789, 40125966119485254868168973264014609864686709730⟩
  | 0, 3 => ⟨87334442769912979928798247270934648449188947780, 87334442769912979928798247270935512874268596343⟩
  | 1, 2 => ⟨118629483794837117611534720504392976831276150736, 118629483794837117611534720504394495405666532765⟩
  | 2, 1 => ⟨119384888778603165342075872228827856170996537522, 119384888778603165342075872228830579770003097313⟩
  | 0, 4 => ⟨158250793108840718845756161061141091779330054775, 158250793108840718845756161061143956440694517742⟩
  | 1, 3 => ⟨239302437526190500270038215000619147621956978652, 239302437526190500270038215000624270157350772737⟩
  | 2, 2 => ⟨320757606071437194523915526302694171017059381555, 320757606071437194523915526302703500346003139424⟩
  | 3, 1 => ⟨322514177659741422767923714225122492132295879840, 322514177659741422767923714225139642403726834287⟩
  | 0, 5 => ⟨-515242445531814282744809822562878399048638378186824, 518414117185575925847447401157675747940750079431759⟩
  | 1, 4 => ⟨-1003217870547292272389664299445355519119080811504833, 1007948463957116473980479851765511680665567267810838⟩
  | 2, 3 => ⟨-1955804627111469135561069417699595774994822472912713, 1962576857370188448627142660609200365930308908145937⟩
  | 3, 2 => ⟨-3815805929818269562353635795943402262123225848374346, 3824664736065257171481483340767801416079535964466018⟩
  | 4, 1 => ⟨-7448655014601266101563570592048607438587143987909839, 7457707942363809924389214860824797959923848835418234⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0581Geometry.ds, E8TAxisProd0581Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 11614743320992849020412501058226545203776252311 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0581CertifiedArithmetic

end


