-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0625CertifiedArithmetic__11
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0625CertifiedArithmetic__11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T16:20:45.322987+00:00
-- url     : https://prove2.me/theorems/3c516098-d707-4bce-82dc-88fcf1938b2b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0625CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0626CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0625CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0626CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0627CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0628CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0629CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0630CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0631CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0632CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0633CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0634CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0635CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0625CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0626CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0627CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0628CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0629CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0630CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0631CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0632CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0633CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0634CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0635CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0625CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0626CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0627CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0628CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0629CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0630CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0631CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0632CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0633CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0634CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0635CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0625CertifiedArithmetic (+10 modules: GeneralCK/Certificates/E8TAxisProd0626CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0627CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0628CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0629CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0630CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0631CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0632CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0633CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0634CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0635CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0621GraphCenterA__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0623GraphCenterB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0622GraphCenterC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0618GraphCenterD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0615GraphWholeA__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0618GraphWholeB__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0619GraphWholeC__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0617GraphWholeD__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0618Geometry__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0627GraphWholeA__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0628GraphWholeB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0629GraphCenterD__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0629GraphWholeD__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0629Geometry__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0630GraphCenterA__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0631GraphWholeC__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0633GraphCenterC__15

-- ===== source module GeneralCK.Certificates.E8TAxisProd0625CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0625CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0625GraphCenterA.qJetBox,
   E8TAxisProd0625GraphCenterB.qJetBox,
   E8TAxisProd0625GraphCenterC.qJetBox,
   E8TAxisProd0625GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0625GraphWholeA.qJetBox,
   E8TAxisProd0625GraphWholeB.qJetBox,
   E8TAxisProd0625GraphWholeC.qJetBox,
   E8TAxisProd0625GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨7607119249142127085681869006890011932403567910, 7607119249142127085681869006890064244019568078⟩
  | 0, 2 => ⟨25451861706240312331693879419508230290730091029, 25451861706240312331693879419508408823958532526⟩
  | 1, 1 => ⟨25543517763030616583288001247595861718303703063, 25543517763030616583288001247596171503441211976⟩
  | 0, 3 => ⟨57836457957229396600247268862833600516786074084, 57836457957229396600247268862834159315656293932⟩
  | 1, 2 => ⟨78910942679529423983404309087158102952897259084, 78910942679529423983404309087159071152684940668⟩
  | 2, 1 => ⟨79159970787465562535550318232837026946403316354, 79159970787465562535550318232838747880455283144⟩
  | 0, 4 => ⟨108745045650481322987991836729282992320701497264, 108745045650481322987991836729284825310569781365⟩
  | 1, 3 => ⟨165827301112541533981855827914748300959357707970, 165827301112541533981855827914751544015379023200⟩
  | 2, 2 => ⟨223050709339060391286118955008349280248726205193, 223050709339060391286118955008355145196915783858⟩
  | 3, 1 => ⟨223655998432073716160752589380342514083730268107, 223655998432073716160752589380353231148603497654⟩
  | 0, 5 => ⟨-280901349614097183289574364695012900277497010685326, 282824734688498000854152772143601562253415224911253⟩
  | 1, 4 => ⟨-544727911136753596742924334942990679553943314650080, 547575130979791949568728909959343693634348919748894⟩
  | 2, 3 => ⟨-1057984785604716353755830859681769651290759808530236, 1062041588187358230088919402247130271324377437390991⟩
  | 3, 2 => ⟨-2056666427770866895456974958284912346359071492069324, 2061961358506476713233232494699338563716086631905954⟩
  | 4, 1 => ⟨-4000347522520829900387101876903168773852909441440275, 4005763965986482595084558020819783997079854283462492⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0625Geometry.ds, E8TAxisProd0625Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 7099630595091327341120841149120474929500876897 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0625CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0626CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0626CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0626GraphCenterA.qJetBox,
   E8TAxisProd0626GraphCenterB.qJetBox,
   E8TAxisProd0626GraphCenterC.qJetBox,
   E8TAxisProd0626GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0626GraphWholeA.qJetBox,
   E8TAxisProd0626GraphWholeB.qJetBox,
   E8TAxisProd0626GraphWholeC.qJetBox,
   E8TAxisProd0626GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨8542481798640369434233818138833485226349508271, 8542481798640369434233818138833542324312095762⟩
  | 0, 2 => ⟨28356192992475453134364264459359751927147343504, 28356192992475453134364264459359949311558729810⟩
  | 1, 1 => ⟨28428219246088129471377399411173383235317752918, 28428219246088129471377399411173727255970072028⟩
  | 0, 3 => ⟨63927510755769766865482128965057389792849197431, 63927510755769766865482128965058010117293095816⟩
  | 1, 2 => ⟨87072783224108506353639644230392526190186186321, 87072783224108506353639644230393604905341801476⟩
  | 2, 1 => ⟨87266508705806762910824898428921390534186150979, 87266508705806762910824898428923312332372939200⟩
  | 0, 4 => ⟨119157440723443381959519893182604699286883610256, 119157440723443381959519893182606739781681722648⟩
  | 1, 3 => ⟨181274256899842393574941798989600105480235868739, 181274256899842393574941798989603726075139461798⟩
  | 2, 2 => ⟨243499248215931668709352105881413393303659406356, 243499248215931668709352105881419953201347076731⟩
  | 3, 1 => ⟨243964863063675927837201024273049737298396175514, 243964863063675927837201024273061742894414574816⟩
  | 0, 5 => ⟨-326626469234830944006651814705394638613696950731713, 328799666203633369777345311491489051714477734111749⟩
  | 1, 4 => ⟨-634079669375839825575227644094040026244274399459399, 637303227169675757507711515861780326460459663763321⟩
  | 2, 3 => ⟨-1232741447870785831909602458579049929081535718894057, 1237340354171158514371033437810611336855052008710562⟩
  | 3, 2 => ⟨-2398656249955425446937694556229392102286628791324704, 2404662346036568831722848234287063068679968839316197⟩
  | 4, 1 => ⟨-4669894439017169069465311619482487799214785481816451, 4676036051955022970934613502353025899343571857104901⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0626Geometry.ds, E8TAxisProd0626Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 7976795983017424153834007578068664712301305034 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0626CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0627CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0627CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0627GraphCenterA.qJetBox,
   E8TAxisProd0627GraphCenterB.qJetBox,
   E8TAxisProd0627GraphCenterC.qJetBox,
   E8TAxisProd0627GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0627GraphWholeA.qJetBox,
   E8TAxisProd0627GraphWholeB.qJetBox,
   E8TAxisProd0627GraphWholeC.qJetBox,
   E8TAxisProd0627GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨7575349571361458473964335597929606922990875271, 7575349571361458473964335597929659130850358369⟩
  | 0, 2 => ⟨25379651032848035254883064717949544416499627778, 25379651032848035254883064717949722557671805197⟩
  | 1, 1 => ⟨25445008544660341976489395940363015550883152191, 25445008544660341976489395940363324640001525166⟩
  | 0, 3 => ⟨57700665859808642154919625336162645636972869751, 57700665859808642154919625336163203190948018061⟩
  | 1, 2 => ⟨78703880758821807734025884295193068507960149834, 78703880758821807734025884295194034510681181626⟩
  | 2, 1 => ⟨78881487897710215458624791797135434742850298297, 78881487897710215458624791797137151714948922023⟩
  | 0, 4 => ⟨108522376545363142854144870236034902968062188392, 108522376545363142854144870236036731768335163146⟩
  | 1, 3 => ⟨165471880717969357353652362470828116919009953247, 165471880717969357353652362470831352483626696527⟩
  | 2, 2 => ⟨222522082187519482335717561629657450696820419548, 222522082187519482335717561629663301962528262551⟩
  | 3, 1 => ⟨222953861943144295510978317406714085575350490511, 222953861943144295510978317406724777385421889136⟩
  | 0, 5 => ⟨-280032429842892574870440978989458843786583513724615, 281951613933162435625193408027993419854959996525975⟩
  | 1, 4 => ⟨-543031370176189208193529864597349978042122145208801, 545872218182755425561813359437993085296102340567355⟩
  | 2, 3 => ⟨-1054667898500597384888904256809457611194503587378028, 1058715443142238336518315085501665842291668465769862⟩
  | 3, 2 => ⟨-2050176016363418200765766333916430927150357449321873, 2055458629802770873797769324750982059513089708168773⟩
  | 4, 1 => ⟨-3987639349997353565467791178831057751574844302484667, 3993042777296458832409494059404501812015395011703152⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0627Geometry.ds, E8TAxisProd0627Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 7069783472736949399972185137589777230840896503 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0627CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0628CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0628CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0628GraphCenterA.qJetBox,
   E8TAxisProd0628GraphCenterB.qJetBox,
   E8TAxisProd0628GraphCenterC.qJetBox,
   E8TAxisProd0628GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0628GraphWholeA.qJetBox,
   E8TAxisProd0628GraphWholeB.qJetBox,
   E8TAxisProd0628GraphWholeC.qJetBox,
   E8TAxisProd0628GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨10782923054995066047438754562178574853540060414, 10782923054995066047438754562178643186381154950⟩
  | 0, 2 => ⟨35184926715010937899583683094059894817138672572, 35184926715010937899583683094060136874991665224⟩
  | 1, 1 => ⟨35237169732181998623438123530616149233282366555, 35237169732181998623438123530616574651266494032⟩
  | 0, 3 => ⟨78023478587221148403924316481340621352349950453, 78023478587221148403924316481341387481535305678⟩
  | 1, 2 => ⟨105955269886642463688456959872083128693518744418, 105955269886642463688456959872084469996233572596⟩
  | 2, 1 => ⟨106092959661941670871824342503489332037187127877, 106092959661941670871824342503491732146390054931⟩
  | 0, 4 => ⟨142890473893392372614455645464397055505263515447, 142890473893392372614455645464399586891105041720⟩
  | 1, 3 => ⟨216412267719325226197951202032346795775525760241, 216412267719325226197951202032351310801475264113⟩
  | 2, 2 => ⟨290008750049653565656887877280362359139151585904, 290008750049653565656887877280370567597880073802⟩
  | 3, 1 => ⟨290332595515833183589037526028156994065747809673, 290332595515833183589037526028172060526502655995⟩
  | 0, 5 => ⟨-438642074988025214735468406487845755331432019213426, 441415667532763452268628841875320513167722194483992⟩
  | 1, 4 => ⟨-853215583369557670619943673807072292220506749075405, 857344090112973079482350543023727927290895501819314⟩
  | 2, 3 => ⟨-1661804469103693048959888008168940072133724562163301, 1667706770304548468624942787218275065632648317608738⟩
  | 3, 2 => ⟨-3239230867862850847632729492536221275667845109843701, 3246945679601448727457065809636950645676166022182576⟩
  | 4, 1 => ⟨-6317385435117461315536101356607720009081111504235314, 6325267738457713908506203775131028737287104806227508⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0628Geometry.ds, E8TAxisProd0628Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 10079630650521231858478523029855639126038092820 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0628CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0629CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0629CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0629GraphCenterA.qJetBox,
   E8TAxisProd0629GraphCenterB.qJetBox,
   E8TAxisProd0629GraphCenterC.qJetBox,
   E8TAxisProd0629GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0629GraphWholeA.qJetBox,
   E8TAxisProd0629GraphWholeB.qJetBox,
   E8TAxisProd0629GraphWholeC.qJetBox,
   E8TAxisProd0629GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨9582899540684792551117642210862402474833984115, 9582899540684792551117642210862464849853159065⟩
  | 0, 2 => ⟨31559068565896391641730910049932101509150713176, 31559068565896391641730910049932319815345580491⟩
  | 1, 1 => ⟨31606567409380849795146217004795780656011023999, 31606567409380849795146217004796162760303448429⟩
  | 0, 3 => ⟨70582092744640614573786303936384639343104968653, 70582092744640614573786303936385327960227907294⟩
  | 1, 2 => ⟨95978049036445156985937264784663670193298407348, 95978049036445156985937264784664871811470687291⟩
  | 2, 1 => ⟨96104521607730369728465648513030964094495827525, 96104521607730369728465648513033109613412947525⟩
  | 0, 4 => ⟨130423847239438016393651019729447069276225008922, 130423847239438016393651019729449339771630951360⟩
  | 1, 3 => ⟨197956635593823424680203702384965913880602214279, 197956635593823424680203702384969953487743897657⟩
  | 2, 2 => ⟨265559023013055886638709945395297599174280928063, 265559023013055886638709945395304931169624991850⟩
  | 3, 1 => ⟨265859698421897538975089860001263361256291516823, 265859698421897538975089860001276799871385175964⟩
  | 0, 5 => ⟨-378562699184286042049352560112800493701088759286776, 381018283511084440660559783039603673638186214083698⟩
  | 1, 4 => ⟨-735644229415195696842167344700233844409948134308505, 739292742915805156346262745846363018060981704043766⟩
  | 2, 3 => ⟨-1431528582582564540910150366724447077808362094894212, 1436738537699146164282011359602806344323884125308621⟩
  | 3, 2 => ⟨-2787953604014479889157061309086209409489103618791597, 2794759403424325449959470623583998000223110075323102⟩
  | 4, 1 => ⟨-5432613407681417339098794531589862825221109027064564, 5439568190232498725984131020665229562698736477546846⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0629Geometry.ds, E8TAxisProd0629Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 8952990755754067823092119945931671970191321415 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0629CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0630CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0630CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0630GraphCenterA.qJetBox,
   E8TAxisProd0630GraphCenterB.qJetBox,
   E8TAxisProd0630GraphCenterC.qJetBox,
   E8TAxisProd0630GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0630GraphWholeA.qJetBox,
   E8TAxisProd0630GraphWholeB.qJetBox,
   E8TAxisProd0630GraphWholeC.qJetBox,
   E8TAxisProd0630GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨8507086461999003442874749522614669741774747094, 8507086461999003442874749522614726725936635654⟩
  | 0, 2 => ⟨28276376632811588822295887384887341361315014828, 28276376632811588822295887384887538312132541197⟩
  | 1, 1 => ⟨28319519787332333894403889174167219627255608804, 28319519787332333894403889174167562875587365821⟩
  | 0, 3 => ⟨63778715059847729351834302042300273883173242383, 63778715059847729351834302042300892828849619381⟩
  | 1, 2 => ⟨86846430939749946484648537104229622359312230722, 86846430939749946484648537104230698634949252685⟩
  | 2, 1 => ⟨86962491719368222752818915448662522421471219071, 86962491719368222752818915448664439813437724627⟩
  | 0, 4 => ⟨118915744226083358492293297339620836389939686393, 118915744226083358492293297339622872246558469178⟩
  | 1, 3 => ⟨180889514870327654450501639713527173123983630356, 180889514870327654450501639713530785409869445413⟩
  | 2, 2 => ⟨242928110111664530924386345592864825908450259504, 242928110111664530924386345592871370613951591644⟩
  | 3, 1 => ⟨243207114282774932182204939803020110871728778311, 243207114282774932182204939803032088401519388415⟩
  | 0, 5 => ⟨-325635762673913296416814329855553018863778204490534, 327806883482430284259021326506479343147555000260100⟩
  | 1, 4 => ⟨-632143905501503552874318090761902160787715758352302, 635363477302343176498245624407385587341041824895114⟩
  | 2, 3 => ⟨-1228954224378462724554110108804135801639570614197309, 1233545911607768288514164172639779994668753581680692⟩
  | 3, 2 => ⟨-2391240506501601721391025076424689990109673301752534, 2397234919760892444654575405753849669908635442628146⟩
  | 4, 1 => ⟨-4655364850219190434470392923646188784840855668837339, 4661491949594352285559716937640300487039602213823530⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0630Geometry.ds, E8TAxisProd0630Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 7943523952728286598369778571111142197635177614 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0630CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0631CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0631CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0631GraphCenterA.qJetBox,
   E8TAxisProd0631GraphCenterB.qJetBox,
   E8TAxisProd0631GraphCenterC.qJetBox,
   E8TAxisProd0631GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0631GraphWholeA.qJetBox,
   E8TAxisProd0631GraphWholeB.qJetBox,
   E8TAxisProd0631GraphWholeC.qJetBox,
   E8TAxisProd0631GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨7543670050907405157416447893263013847356284382, 7543670050907405157416447893263065951667746673⟩
  | 0, 2 => ⟨25307609925720883938789720084444719188210552093, 25307609925720883938789720084444896938170078913⟩
  | 1, 1 => ⟨25346757876188540885148114257489852019893282301, 25346757876188540885148114257490160414511788102⟩
  | 0, 3 => ⟨57565151850190363791651180731797939212957370600, 57565151850190363791651180731798495524732348429⟩
  | 1, 2 => ⟨78497262706209086384295482756020145964078269955, 78497262706209086384295482756021109774523585404⟩
  | 2, 1 => ⟨78603665162548868239442516515012959956861520654, 78603665162548868239442516515014672975693956382⟩
  | 0, 4 => ⟨108300105061775421397087102174072098913004272528, 108300105061775421397087102174073923532756740820⟩
  | 1, 3 => ⟨165117111984446613941110121516117982881430152117, 165117111984446613941110121516121210970897570264⟩
  | 2, 2 => ⟨221994461711018805372567523978949711885712693309, 221994461711018805372567523978955549498647931406⟩
  | 3, 1 => ⟨222253188220310911139619345153393251010674043178, 222253188220310911139619345153403917620857267147⟩
  | 0, 5 => ⟨-279165856467740804006187558078328765108964318242052, 281083228379281626735022179836875459853014888438386⟩
  | 1, 4 => ⟨-541339430294552493017239144475991508441977483485738, 544176775747736852499883456900920379773737244007430⟩
  | 2, 3 => ⟨-1051360045247699404485702817118550703612140029089293, 1055401206943549932746343757375892367110022432363314⟩
  | 3, 2 => ⟨-2043703357473855081182393974850055656541880263353060, 2048975582180578702953950850089517258697547370794380⟩
  | 4, 1 => ⟨-3974966085298229755385057274493507891747890373941169, 3980356521080234898434525310930809647087842291912239⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0631Geometry.ds, E8TAxisProd0631Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 7040021478768893147563555363990553927064376233 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0631CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0632CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0632CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0632GraphCenterA.qJetBox,
   E8TAxisProd0632GraphCenterB.qJetBox,
   E8TAxisProd0632GraphCenterC.qJetBox,
   E8TAxisProd0632GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0632GraphWholeA.qJetBox,
   E8TAxisProd0632GraphWholeB.qJetBox,
   E8TAxisProd0632GraphWholeC.qJetBox,
   E8TAxisProd0632GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6853007942537291263642222956204052721118147806, 6853007942537291263642222956204100974731255061⟩
  | 0, 2 => ⟨23017726102719434579337355310868996174920025400, 23017726102719434579337355310869158796211925092⟩
  | 1, 1 => ⟨23196997160423881326496786300781956825723633362, 23196997160423881326496786300782237738225978868⟩
  | 0, 3 => ⟨52639933994121916815333574263511071049588143461, 52639933994121916815333574263511577857563419758⟩
  | 1, 2 => ⟨72008120715218190354994083838189416963906058521, 72008120715218190354994083838190291852431946678⟩
  | 2, 1 => ⟨72499881326314232313646823608928082049670686364, 72499881326314232313646823608929633575212370148⟩
  | 0, 4 => ⟨99746399327724718648233284315280940923475436448, 99746399327724718648233284315282598411384043991⟩
  | 1, 3 => ⟨152522459071359614064384266439099438026015543635, 152522459071359614064384266439102361854154542919⟩
  | 2, 2 => ⟨205581322545822020797257124403841698416532217006, 205581322545822020797257124403846976118539209018⟩
  | 3, 1 => ⟨206789670400089623435705227657487078182508028292, 206789670400089623435705227657496707272313825489⟩
  | 0, 5 => ⟨-243116144100932104109586419942086896280100601248848, 244830249589146629858522756761408054990805365065121⟩
  | 1, 4 => ⟨-470946158460458834145395696845467834399072468479203, 473477472831874891062000138133535363743657965869242⟩
  | 2, 3 => ⟨-913787998337589136480197806018138803364583808941944, 917389108748116751981632465973479855840292968016541⟩
  | 3, 2 => ⟨-1774694803620108155802123494154139653680546653086623, 1779391429986946453309046185705460449470573125101332⟩
  | 4, 1 => ⟨-3448731080496581680345799873156567641781466558727359, 3453538042208712057730735530415222405950757481699428⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0632Geometry.ds, E8TAxisProd0632Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 6392950602274046396276732835304731838819191172 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0632CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0633CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0633CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0633GraphCenterA.qJetBox,
   E8TAxisProd0633GraphCenterB.qJetBox,
   E8TAxisProd0633GraphCenterC.qJetBox,
   E8TAxisProd0633GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0633GraphWholeA.qJetBox,
   E8TAxisProd0633GraphWholeB.qJetBox,
   E8TAxisProd0633GraphWholeC.qJetBox,
   E8TAxisProd0633GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6064619179438970646978144719967988872805787791, 6064619179438970646978144719968033071969568001⟩
  | 0, 2 => ⟨20558715162121430032442075180663046190356236689, 20558715162121430032442075180663193092400682380⟩
  | 1, 1 => ⟨20721074291905752952491812067081325705034098996, 20721074291905752952491812067081578223515851933⟩
  | 0, 3 => ⟨47406236751436313648654952262243748569971929929, 47406236751436313648654952262244204199751828799⟩
  | 1, 2 => ⟨64949576861949655922844994169276088487129744576, 64949576861949655922844994169276871851668517416⟩
  | 2, 1 => ⟨65399537592433378328694231608039520189105118495, 65399537592433378328694231608040905924812569573⟩
  | 0, 4 => ⟨90634723368544494527033370623769963019266499356, 90634723368544494527033370623771447738579734896⟩
  | 1, 3 => ⟨138927282328716018073975625218028630531409202004, 138927282328716018073975625218031241045900115015⟩
  | 2, 2 => ⟨187482741524833167142015177326981756678799575417, 187482741524833167142015177326986459052042479457⟩
  | 3, 1 => ⟨188601629473899375604602753721279996092471346808, 188601629473899375604602753721288560813081792970⟩
  | 0, 5 => ⟨-207354752854136359133875986863159952498164126173798, 208870463997496237198422031519961784174298063283155⟩
  | 1, 4 => ⟨-401177349645886748418304874260194370626002478961632, 403410504517390150354008134097305204766028596359523⟩
  | 2, 3 => ⟨-777544774820531238284754329469789550815614379184278, 780717309566990155559134586097730802879653907527621⟩
  | 3, 2 => ⟨-1508484029891840857448408407383239183883105511388604, 1512619199575399939008215468315849948904550017681861⟩
  | 4, 1 => ⟨-2928346002585794881366490639239477819838884983372665, 2932580694015393567827536634821080202884019609489385⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0633Geometry.ds, E8TAxisProd0633Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5654262446164452416861261610689558491432132471 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0633CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0634CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0634CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0634GraphCenterA.qJetBox,
   E8TAxisProd0634GraphCenterB.qJetBox,
   E8TAxisProd0634GraphCenterC.qJetBox,
   E8TAxisProd0634GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0634GraphWholeA.qJetBox,
   E8TAxisProd0634GraphWholeB.qJetBox,
   E8TAxisProd0634GraphWholeC.qJetBox,
   E8TAxisProd0634GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6824276877404572954839960508180440649996738099, 6824276877404572954839960508180488808384906681⟩
  | 0, 2 => ⟨22952004058412943140830915456654749159033397807, 22952004058412943140830915456654911423672851610⟩
  | 1, 1 => ⟨23107106081751464119167492963250184151631521971, 23107106081751464119167492963250464433157232732⟩
  | 0, 3 => ⟨52515379827592507676273428421639501560033594101, 52515379827592507676273428421640007238223591471⟩
  | 1, 2 => ⟨71817673888513799882206096127434441998749427514, 71817673888513799882206096127435314898779351744⟩
  | 2, 1 => ⟨72243212105121926670590751488245409845648608129, 72243212105121926670590751488246957791436890820⟩
  | 0, 4 => ⟨99540328942960570970570837644455173341394644064, 99540328942960570970570837644456827029594662730⟩
  | 1, 3 => ⟨152192565305469660856104050323910917073570040266, 152192565305469660856104050323913834121695215394⟩
  | 2, 2 => ⟨205089588773086741587876613676622146009335438337, 205089588773086741587876613676627411343117390954⟩
  | 3, 1 => ⟨206135430512776497556753610479337644037761579414, 206135430512776497556753610479347250320578167753⟩
  | 0, 5 => ⟨-242350542486328978391459280898689930108543441296298, 244060638762910592528605261930596090394749577527597⟩
  | 1, 4 => ⟨-469452468763345718716463030506321686274223367965087, 471977760813427544560977864503011832878495728871856⟩
  | 2, 3 => ⟨-910869743445671859526836559770316704437261304674756, 914462234745108482770835516483900843397948210703851⟩
  | 3, 2 => ⟨-1768988261692858722489660597812263984640525769146828, 1773673631503521919931371457842008948157956930754451⟩
  | 4, 1 => ⟨-3437565080427118677093806263131220005664396485563878, 3442360370301884421752382304112660789999858526667314⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0634Geometry.ds, E8TAxisProd0634Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 6365972227821096792060631425043007551050769920 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0634CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0635CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0635CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0635GraphCenterA.qJetBox,
   E8TAxisProd0635GraphCenterB.qJetBox,
   E8TAxisProd0635GraphCenterC.qJetBox,
   E8TAxisProd0635GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0635GraphWholeA.qJetBox,
   E8TAxisProd0635GraphWholeB.qJetBox,
   E8TAxisProd0635GraphWholeC.qJetBox,
   E8TAxisProd0635GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6038957792120692977265135227523978044742615815, 6038957792120692977265135227524022157158280518⟩
  | 0, 2 => ⟨20499528125275478485462223928066464399361548944, 20499528125275478485462223928066610979500938790⟩
  | 1, 1 => ⟨20639995778646101624454594217735293050120991839, 20639995778646101624454594217735545001203792728⟩
  | 0, 3 => ⟨47293061611622311253676898273352347532126309078, 47293061611622311253676898273352802144145985819⟩
  | 1, 2 => ⟨64776107621204732102106120918318793338552416111, 64776107621204732102106120918319574916824877025⟩
  | 2, 1 => ⟨65165467724925691587061474656787139994310864070, 65165467724925691587061474656788522519936759694⟩
  | 0, 4 => ⟨90445557585959205387080603608304040550902816105, 90445557585959205387080603608305521848146410318⟩
  | 1, 3 => ⟨138623597294523510390276603634899559992867210754, 138623597294523510390276603634902164414233160770⟩
  | 2, 2 => ⟨187029193072274043580026008950377519894832851607, 187029193072274043580026008950382211166447658714⟩
  | 3, 1 => ⟨187997591662783363968780220659970568806230048665, 187997591662783363968780220659979113075731780907⟩
  | 0, 5 => ⟨-206693541386083347971659010324802097668833352127581, 208205695719232736495433153860049971761385454336580⟩
  | 1, 4 => ⟨-399888427557121111150565812865966096639063105363682, 402116271739339901603159694724346476420843564805525⟩
  | 2, 3 => ⟨-775028606299843942656330496968107393889017544204145, 778193554919541150625089041279847171709117842640968⟩
  | 3, 2 => ⟨-1503567594001195428340592418262718220485141019000858, 1507692819535195590319487764090535979902660039601175⟩
  | 4, 1 => ⟨-2918733401051759529540773522574297353492072312563378, 2922957594520859526004484251104293064588556072282818⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0635Geometry.ds, E8TAxisProd0635Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5630180176839405698651066754748127652059931254 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0635CertifiedArithmetic

end


