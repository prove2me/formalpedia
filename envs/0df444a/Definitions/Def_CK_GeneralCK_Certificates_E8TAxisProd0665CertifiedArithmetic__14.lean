-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0665CertifiedArithmetic__14
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0665CertifiedArithmetic__14
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T13:46:20.107348+00:00
-- url     : https://prove2.me/theorems/95614671-b93c-47f4-900c-402b692d95f8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0665CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0666CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0665CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0666CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0667CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0668CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0669CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0670CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0671CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0672CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0673CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0674CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0675CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0676CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0677CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0678CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0665CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0666CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0667CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0668CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0669CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0670CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0671CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0672CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0673CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0674CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0675CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0676CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0677CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0678CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0665CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0666CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0667CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0668CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0669CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0670CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0671CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0672CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0673CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0674CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0675CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0676CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0677CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0678CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0665CertifiedArithmetic (+13 modules: GeneralCK/Certificates/E8TAxisProd0666CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0667CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0668CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0669CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0670CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0671CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0672CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0673CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0674CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0675CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0676CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0677CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0678CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0659GraphCenterA__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0664GraphCenterB__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0659GraphCenterC__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0658GraphCenterD__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0664GraphWholeA__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0655GraphWholeB__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0654GraphWholeC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0665GraphWholeD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0659Geometry__24
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0667GraphCenterD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0667GraphWholeC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0668GraphCenterC__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0668GraphWholeB__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0674GraphCenterA__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0677GraphCenterB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0677GraphWholeA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0678GraphWholeC__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0678GraphWholeD__10

-- ===== source module GeneralCK.Certificates.E8TAxisProd0665CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0665CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0665GraphCenterA.qJetBox,
   E8TAxisProd0665GraphCenterB.qJetBox,
   E8TAxisProd0665GraphCenterC.qJetBox,
   E8TAxisProd0665GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0665GraphWholeA.qJetBox,
   E8TAxisProd0665GraphWholeB.qJetBox,
   E8TAxisProd0665GraphWholeC.qJetBox,
   E8TAxisProd0665GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5962416297303162243250301033464066364113882459, 5962416297303162243250301033464110217323323506⟩
  | 0, 2 => ⟨20322813762502444587193287714738257836683802168, 20322813762502444587193287714738403455262997017⟩
  | 1, 1 => ⟨20398057941923574220758539479483765850736665072, 20398057941923574220758539479484016107068117790⟩
  | 0, 3 => ⟨46954951933890306125712697362109697491521781156, 46954951933890306125712697362110149063520968316⟩
  | 1, 2 => ⟨64257972585970694442271170327504814892612929310, 64257972585970694442271170327505591135567008396⟩
  | 2, 1 => ⟨64466652050983673585652137452628320685637262589, 64466652050983673585652137452629693623496123681⟩
  | 0, 4 => ⟨89880117510602751793065344161076256792964470520, 89880117510602751793065344161077727868859146826⟩
  | 1, 3 => ⟨137715935291272893479182044854342678396264709878, 137715935291272893479182044854345264618405615939⟩
  | 2, 2 => ⟨185673814607138160678520631549395103045814109540, 185673814607138160678520631549399761158852991475⟩
  | 3, 1 => ⟨186193158129376106112253346672387217806518554336, 186193158129376106112253346672395700992900002745⟩
  | 0, 5 => ⟨-204721953331729130920739116132507642101321385782415, 206223500738840834125745055413667674328227811258936⟩
  | 1, 4 => ⟨-396045269634316452022058377834043208706612619737865, 398257277068754490151973437488040399643395420650117⟩
  | 2, 3 => ⟨-767526428168486669496912033086878925630806257470272, 770668751577235844684810528924026974877578520273296⟩
  | 3, 2 => ⟨-1488909273535772077482831062915236764792748429907822, 1493004828354259608517243354076244910888056221011782⟩
  | 4, 1 => ⟨-2890074405679632932754552787609831556782257993011117, 2894267236023201782438081764484900526148113592798730⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0665Geometry.ds, E8TAxisProd0665Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5558350773174334048071847980617857433869207954 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0665CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0666CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0666CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0666GraphCenterA.qJetBox,
   E8TAxisProd0666GraphCenterB.qJetBox,
   E8TAxisProd0666GraphCenterC.qJetBox,
   E8TAxisProd0666GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0666GraphWholeA.qJetBox,
   E8TAxisProd0666GraphWholeB.qJetBox,
   E8TAxisProd0666GraphWholeC.qJetBox,
   E8TAxisProd0666GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6710171229886599252932411169758849722755016606, 6710171229886599252932411169758897502147579376⟩
  | 0, 2 => ⟨22690667988140393071879788236611122579463411236, 22690667988140393071879788236611283425154101656⟩
  | 1, 1 => ⟨22749914636370469444223810705466089748783009508, 22749914636370469444223810705466367520164863191⟩
  | 0, 3 => ⟨52019732098327955901288154441383045275782674877, 52019732098327955901288154441383546459280149965⟩
  | 1, 2 => ⟨71059998838749400508070209268798027964201245358, 71059998838749400508070209268798892953623496124⟩
  | 2, 1 => ⟨71222664216222363970047528048617981039793927048, 71222664216222363970047528048619514745124989499⟩
  | 0, 4 => ⟨98719748039142474869251873115965043206249297008, 98719748039142474869251873115966681778087430239⟩
  | 1, 3 => ⟨150879074415867249244753532114516381715106034979, 150879074415867249244753532114519271790702959797⟩
  | 2, 2 => ⟨203132074983387293198714926933725191095335396368, 203132074983387293198714926933730407225662565123⟩
  | 3, 1 => ⟨203532185084524707932753945910907347707506650034, 203532185084524707932753945910916863260163599468⟩
  | 0, 5 => ⟨-239316286443052680923559372985105446686809044476780, 241011162293043454705096041915281353561517702317837⟩
  | 1, 4 => ⟨-463532947611004042312541315074464820556114999218676, 466035229442390798341781312733807905484512422946997⟩
  | 2, 3 => ⟨-899305223779522603231045522629803413473764791154541, 902864518354298340317946035556198234456423597986872⟩
  | 3, 2 => ⟨-1746375355192928260090053319521591488304423369155288, 1751016957127107829906950159359440446134249047710487⟩
  | 4, 1 => ⟨-3393320453025935843795201543317853105958921985561754, 3398069874365123997166990799888864008785950784079493⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0666Geometry.ds, E8TAxisProd0666Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 6258830726755767295509910265188305745153771389 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0666CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0667CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0667CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0667GraphCenterA.qJetBox,
   E8TAxisProd0667GraphCenterB.qJetBox,
   E8TAxisProd0667GraphCenterC.qJetBox,
   E8TAxisProd0667GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0667GraphWholeA.qJetBox,
   E8TAxisProd0667GraphWholeB.qJetBox,
   E8TAxisProd0667GraphWholeC.qJetBox,
   E8TAxisProd0667GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5937049434413673005238224885426811592722146550, 5937049434413673005238224885426855359874381349⟩
  | 0, 2 => ⟨20264190242499434782598780818103849392330526714, 20264190242499434782598780818103994691769741467⟩
  | 1, 1 => ⟨20317842988232546185022176378638636619196981512, 20317842988232546185022176378638886313084324743⟩
  | 0, 3 => ⟨46842719195105954357482487086412106572449387709, 46842719195105954357482487086412557135512813600⟩
  | 1, 2 => ⟨64086016116759408699244074032411692475941249798, 64086016116759408699244074032412466948255017497⟩
  | 2, 1 => ⟨64234841149999378772505495660497442340990297522, 64234841149999378772505495660498812097035989793⟩
  | 0, 4 => ⟨89692321434837091190569650570056638136871724468, 89692321434837091190569650570058105820551531438⟩
  | 1, 3 => ⟨137414509266857048984192235038491399482933046552, 137414509266857048984192235038493979665290139281⟩
  | 2, 2 => ⟨185223772586608196659875225333909233848294376080, 185223772586608196659875225333913880957077058609⟩
  | 3, 1 => ⟨185594233004349405618384208449898648987663986530, 185594233004349405618384208449907111902767232646⟩
  | 0, 5 => ⟨-204068500914968624510743030879292962830326241008401, 205567234200028259674862734168726900938141168660471⟩
  | 1, 4 => ⟨-394771548188680030807159578076280225939088645156627, 396979145121229919891296237783413185639350968821610⟩
  | 2, 3 => ⟨-765040079285607252955039942010375343983575797842179, 768175735230911959431217160450525790045322658453830⟩
  | 3, 2 => ⟨-1484051387535797765565488248080595801825307982789378, 1488137645927185471545652424835965659376348205376823⟩
  | 4, 1 => ⟨-2880576837958076895748797982231422679751137948509474, 2884759229059004167010529706227091866298098728569334⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0667Geometry.ds, E8TAxisProd0667Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5534546235147885049942904342782989338691717825 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0667CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0668CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0668CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0668GraphCenterA.qJetBox,
   E8TAxisProd0668GraphCenterB.qJetBox,
   E8TAxisProd0668GraphCenterC.qJetBox,
   E8TAxisProd0668GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0668GraphWholeA.qJetBox,
   E8TAxisProd0668GraphWholeB.qJetBox,
   E8TAxisProd0668GraphWholeC.qJetBox,
   E8TAxisProd0668GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5269583128518330894551749123966490280301269502, 5269583128518330894551749123966530489013791533⟩
  | 0, 2 => ⟨18129805274579036022808922248619863753862818069, 18129805274579036022808922248619995362508626428⟩
  | 1, 1 => ⟨18197876889225559604875950648047998752076155286, 18197876889225559604875950648048223772225279091⟩
  | 0, 3 => ⟨42232300178780845700983739723666398180632281960, 42232300178780845700983739723666804171691554950⟩
  | 1, 2 => ⟨57886897409929502161772409463019967467164834895, 57886897409929502161772409463020662379101092221⟩
  | 2, 1 => ⟨58077619809288525292103307334234999115023407665, 58077619809288525292103307334236224987527095380⟩
  | 0, 4 => ⟨81558969416482447199915877674570019501758465072, 81558969416482447199915877674571336635844614754⟩
  | 1, 3 => ⟨125279547123640849679480357031353151312886120459, 125279547123640849679480357031355458806222918622⟩
  | 2, 2 => ⟨169113494843329891418128160267729554705822143332, 169113494843329891418128160267733701639026216016⟩
  | 3, 1 => ⟨169593927675485762343917795951170880088587197166, 169593927675485762343917795951178418715042031307⟩
  | 0, 5 => ⟨-174108978601827837400243720368175834148918492451042, 175436544345866542904233348893136482031197278204514⟩
  | 1, 4 => ⟨-336378602266229433098731424106674279045990354306069, 338329633840088638417846100391251513992896881196325⟩
  | 2, 3 => ⟨-651119532955527672890351533664734923079871781632455, 653887139622467091054343112087678930203278903336318⟩
  | 3, 2 => ⟨-1261668218691861549863287413940986190639101654361157, 1265272982001407079220497885677218317112282528830786⟩
  | 4, 1 => ⟨-2446279290535496685219182981295239364288754021995631, 2449971244974526034262599618401594190029001029303496⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0668Geometry.ds, E8TAxisProd0668Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4909615652818127195267280604076422036295626042 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0668CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0669CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0669CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0669GraphCenterA.qJetBox,
   E8TAxisProd0669GraphCenterB.qJetBox,
   E8TAxisProd0669GraphCenterC.qJetBox,
   E8TAxisProd0669GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0669GraphWholeA.qJetBox,
   E8TAxisProd0669GraphWholeB.qJetBox,
   E8TAxisProd0669GraphWholeC.qJetBox,
   E8TAxisProd0669GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4651819081874942601919903275027712103726006605, 4651819081874942601919903275027749007213058080⟩
  | 0, 2 => ⟨16155346746871115174097693779711980716437381723, 16155346746871115174097693779712099727115538895⟩
  | 1, 1 => ⟨16216866544349163999254578665414343741195673594, 16216866544349163999254578665414546131614407002⟩
  | 0, 3 => ⟨37938707278350981179236121354376087775128013201, 37938707278350981179236121354376452823257199356⟩
  | 1, 2 => ⟨52087443062872797262841950283607036956049357685, 52087443062872797262841950283607658977935745520⟩
  | 2, 1 => ⟨52261561727043725364794883168266181550289285190, 52261561727043725364794883168267275850686103392⟩
  | 0, 4 => ⟨73911064420860022929095224543707045615271903244, 73911064420860022929095224543708224472877510354⟩
  | 1, 3 => ⟨113826452146271954177094952004437588480137515933, 113826452146271954177094952004439646024551592605⟩
  | 2, 2 => ⟨153847040792084549315193126016896239911294700737, 153847040792084549315193126016899929035825613452⟩
  | 3, 1 => ⟨154291042022047035211459901765022831354033133241, 154291042022047035211459901765029525061113238323⟩
  | 0, 5 => ⟨-147714942567419400212401059942963099696651355276018, 148890415289630936536759901393214179664194093314758⟩
  | 1, 4 => ⟨-284983551764152136231533530010048009584635654138769, 286705516108330962105216947336098885698779066085371⟩
  | 2, 3 => ⟨-550940957456389089946961246172169282222822078541742, 553378638944013060067678299432921312731231532709184⟩
  | 3, 2 => ⟨-1066281222650255898402627575757853526949363703018550, 1069453110294288984079038607779216730467992215805874⟩
  | 4, 1 => ⟨-2065034023983410796626773986522799438458468324262723, 2068284075432887786601961303221548203570662658894900⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0669Geometry.ds, E8TAxisProd0669Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4331482687411922282460064931908632733863746909 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0669CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0670CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0670CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0670GraphCenterA.qJetBox,
   E8TAxisProd0670GraphCenterB.qJetBox,
   E8TAxisProd0670GraphCenterC.qJetBox,
   E8TAxisProd0670GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0670GraphWholeA.qJetBox,
   E8TAxisProd0670GraphWholeB.qJetBox,
   E8TAxisProd0670GraphWholeC.qJetBox,
   E8TAxisProd0670GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5246953839374499083409310068958875857527356789, 5246953839374499083409310068958915987790256510⟩
  | 0, 2 => ⟨18077078572437326937642167164435685687786648125, 18077078572437326937642167164435817008335289241⟩
  | 1, 1 => ⟨18125616069892453053695991602649509078635870351, 18125616069892453053695991602649733593031742069⟩
  | 0, 3 => ⟨42130459121965149641717453543817530285441069505, 42130459121965149641717453543817935367734608444⟩
  | 1, 2 => ⟨57730471269314298052544355889806812285988657243, 57730471269314298052544355889807505607851117160⟩
  | 2, 1 => ⟨57866487191131884792765832128547542082008414123, 57866487191131884792765832128548765102407695664⟩
  | 0, 4 => ⟨81386774153110705183216445550655631553133720320, 81386774153110705183216445550656945633950681209⟩
  | 1, 3 => ⟨125002364997534729892886877937284927555201872376, 125002364997534729892886877937287229624781618027⟩
  | 2, 2 => ⟨168698829791787728269789477961374463306706550933, 168698829791787728269789477961378600371002731956⟩
  | 3, 1 => ⟨169041528648750338592570686932314458830452510113, 169041528648750338592570686932321979296376835043⟩
  | 0, 5 => ⟨-173544744235997838199135831654944717648138990516238, 174870013453276034489036541540300129467164681922604⟩
  | 1, 4 => ⟨-335279787363939255419675680659011683561251754951918, 337227132553079050880339680545104506712072628543020⟩
  | 2, 3 => ⟨-648976401173728710917169235955265443451502101629137, 651738278015945690398594441201139305656346262865275⟩
  | 3, 2 => ⟨-1257484262454718742973132689528954656248608661089829, 1261080781351666723599475375789955282128945687628481⟩
  | 4, 1 => ⟨-2438105695674512400947086711673367644751217063077873, 2441788003236008557545019641094347589827696249086116⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0670Geometry.ds, E8TAxisProd0670Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4888392340540152567068211750969335161930439454 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0670CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0671CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0671CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0671GraphCenterA.qJetBox,
   E8TAxisProd0671GraphCenterB.qJetBox,
   E8TAxisProd0671GraphCenterC.qJetBox,
   E8TAxisProd0671GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0671GraphWholeA.qJetBox,
   E8TAxisProd0671GraphWholeB.qJetBox,
   E8TAxisProd0671GraphWholeC.qJetBox,
   E8TAxisProd0671GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4631654514009665095974233562546532671398441054, 4631654514009665095974233562546569503321975430⟩
  | 0, 2 => ⟨16107981064703393984934415731714065142146241557, 16107981064703393984934415731714183892697413386⟩
  | 1, 1 => ⟨16151846101099614869819946818096324051576916636, 16151846101099614869819946818096525987222067244⟩
  | 0, 3 => ⟨37846417045861467948722569291729666433819622652, 37846417045861467948722569291730030663664414521⟩
  | 1, 2 => ⟨51945319180477960958158568060914869812396409210, 51945319180477960958158568060915490407097887553⟩
  | 2, 1 => ⟨52069491549143467599910060251463810343420607027, 52069491549143467599910060251464902088864580983⟩
  | 0, 4 => ⟨73753356292062884715629576161324105192378479845, 73753356292062884715629576161325281305211598815⟩
  | 1, 3 => ⟨113571840586738474598837860691119787324364075498, 113571840586738474598837860691121840005417442098⟩
  | 2, 2 => ⟨153465370056241817292343059146297736622378160004, 153465370056241817292343059146301416910509134079⟩
  | 3, 1 => ⟨153782076154640502661360396633764519716370319217, 153782076154640502661360396633771197181877578517⟩
  | 0, 5 => ⟨-147229130012161500767064749134617913100256357945898, 148402774569594664698198038907655556857245386958299⟩
  | 1, 4 => ⟨-284038364851591725324537861481484206259723944957351, 285757285526912784874290447295322461998000088359709⟩
  | 2, 3 => ⟨-549099081631066367074547340008399499633999670126924, 551531855453429310608413007474978217506538181763960⟩
  | 3, 2 => ⟨-1062688413075075840395933645134553228224303105290357, 1065852980349275626244515035573568740178092177217744⟩
  | 4, 1 => ⟨-2058021020022233129739135845177239879646087898461153, 2061262149547112912282822964920779597554744156266968⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0671Geometry.ds, E8TAxisProd0671Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4312581948109122437168736307062780781447191281 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0671CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0672CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0672CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0672GraphCenterA.qJetBox,
   E8TAxisProd0672GraphCenterB.qJetBox,
   E8TAxisProd0672GraphCenterC.qJetBox,
   E8TAxisProd0672GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0672GraphWholeA.qJetBox,
   E8TAxisProd0672GraphWholeB.qJetBox,
   E8TAxisProd0672GraphWholeC.qJetBox,
   E8TAxisProd0672GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6681848503198419627183215306638091590121934919, 6681848503198419627183215306638139275239695677⟩
  | 0, 2 => ⟨22625720394613607791725819876781527415629310469, 22625720394613607791725819876781687908489936934⟩
  | 1, 1 => ⟨22661207426940623879834513229868927080214301238, 22661207426940623879834513229869204227486205153⟩
  | 0, 3 => ⟨51896460090982479447449116977600668805690835450, 51896460090982479447449116977601168871601403374⟩
  | 1, 2 => ⟨70871604344126436294982412540503550944148316317, 70871604344126436294982412540504413966716758246⟩
  | 2, 1 => ⟨70969053614375064684996318054867000168662951952, 70969053614375064684996318054868530333435775906⟩
  | 0, 4 => ⟨98515525050300625008300327240972877962952906879, 98515525050300625008300327240974512776233132478⟩
  | 1, 3 => ⟨150552217809423789142412314886876041689457262311, 150552217809423789142412314886878925058651983738⟩
  | 2, 2 => ⟨202645044087957136213320197964158776855071388396, 202645044087957136213320197964163980751620662608⟩
  | 3, 1 => ⟨202884790606607970667214826274617301847861670903, 202884790606607970667214826274626794841922009984⟩
  | 0, 5 => ⟨-238564940901973940326650449979573352980022481150011, 240258336843551309622184269280989029421918176188023⟩
  | 1, 4 => ⟨-462067173917589769458415056610300419388854222522828, 464566525761779057448214487471229896001345384332305⟩
  | 2, 3 => ⟨-896441739511610804089719339943101417977597830510389, 899995601107184872448139587465246934014513964510404⟩
  | 3, 2 => ⟨-1740776398016388403241457730368507797249407451046288, 1745409035030471460536574576026707734398021759276359⟩
  | 4, 1 => ⟨-3382365938908140082935920599163644268434052401214235, 3387103993451984199468784090700218990084131318694688⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0672Geometry.ds, E8TAxisProd0672Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 6232237421673902195567330759147945827166400620 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0672CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0673CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0673CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0673GraphCenterA.qJetBox,
   E8TAxisProd0673GraphCenterB.qJetBox,
   E8TAxisProd0673GraphCenterC.qJetBox,
   E8TAxisProd0673GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0673GraphWholeA.qJetBox,
   E8TAxisProd0673GraphWholeB.qJetBox,
   E8TAxisProd0673GraphWholeC.qJetBox,
   E8TAxisProd0673GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5911755763303464119533997595839054225713931309, 5911755763303464119533997595839097906980809490⟩
  | 0, 2 => ⟨20205706866793077396222966222072985427382911214, 20205706866793077396222966222073130408369743112⟩
  | 1, 1 => ⟨20237842744785485057099150117842381654308747081, 20237842744785485057099150117842630786984083324⟩
  | 0, 3 => ⟨46730720988189655162528819934576787152143407840, 46730720988189655162528819934577236708465469453⟩
  | 1, 2 => ⟨63914436078443722300350873937111345404070051470, 63914436078443722300350873937112118109629275037⟩
  | 2, 1 => ⟨64003592255770715436864859121794319810098215531, 64003592255770715436864859121795686391360388067⟩
  | 0, 4 => ⟨89504866431637073542054162351350782471099210308, 89504866431637073542054162351352246769988997227⟩
  | 1, 3 => ⟨137113645706078907367770651276965074305291228135, 137113645706078907367770651276967648461130875040⟩
  | 2, 2 => ⟨184774603557605277368399853900137543523257956663, 184774603557605277368399853900142179652002405358⟩
  | 3, 1 => ⟨184996580624332649215795384150224521808433251861, 184996580624332649215795384150232964496986332364⟩
  | 0, 5 => ⟨-203416912467512833906025602493607492670569151983701, 204914341680601920340641920960089682088178824411797⟩
  | 1, 4 => ⟨-393501477620803065608765853318076818623603857909060, 395706477677568045446114848426878694273578004107268⟩
  | 2, 3 => ⟨-762560890524858099551788833394124170247185751601389, 765691695674439148330292410849182096400402267568693⟩
  | 3, 2 => ⟨-1479207556250625333820847637858637020246537465620570, 1483285734794376625088644087595043385597883022706800⟩
  | 4, 1 => ⟨-2871106876107069392184636645358355776953808430541811, 2875278835617657595432039050773268271248750541006839⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0673Geometry.ds, E8TAxisProd0673Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5510810717451436191049124697096163570439817503 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0673CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0674CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0674CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0674GraphCenterA.qJetBox,
   E8TAxisProd0674GraphCenterB.qJetBox,
   E8TAxisProd0674GraphCenterC.qJetBox,
   E8TAxisProd0674GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0674GraphWholeA.qJetBox,
   E8TAxisProd0674GraphWholeB.qJetBox,
   E8TAxisProd0674GraphWholeC.qJetBox,
   E8TAxisProd0674GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5224390379101046210080890305354645839857605601, 5224390379101046210080890305354685891826989334⟩
  | 0, 2 => ⟨18024479037171343536722294058016960698607093210, 18024479037171343536722294058017091731679686037⟩
  | 1, 1 => ⟨18053550566822675452844513229352306610331768568, 18053550566822675452844513229352530620084418488⟩
  | 0, 3 => ⟨42028833111841427920653921381763443762158212592, 42028833111841427920653921381763847937668059377⟩
  | 1, 2 => ⟨57574391279770688964040973013295949378407570812, 57574391279770688964040973013296641113698827503⟩
  | 2, 1 => ⟨57655872396128248696421529195327088488795934555, 57655872396128248696421529195328308663419979002⟩
  | 0, 4 => ⟨81214894625701180533733209494402274696977654102, 81214894625701180533733209494403585731249697605⟩
  | 1, 3 => ⟨124725705267414967668004896258668339268301091029, 124725705267414967668004896258670635926122879303⟩
  | 2, 2 => ⟨168284977574253383016036660140793932180653576470, 168284977574253383016036660140798059397933525983⟩
  | 3, 1 => ⟨168490316755126145891852344013027163450362879758, 168490316755126145891852344013034665796172121560⟩
  | 0, 5 => ⟨-172982161170805373621372347487575876800588003916666, 174306313717716426002558122762469297254872090266447⟩
  | 1, 4 => ⟨-334184204705675485926802409668181496847000507593588, 336129268588212987093180907620960876288407417466096⟩
  | 2, 3 => ⟨-646839604620729601489750991679408784173687890130549, 649597147349292115379812680057765149777939774165096⟩
  | 3, 2 => ⟨-1253312734386352121860718670228174901286639387911448, 1256901936390903799191082291845194806940922106686746⟩
  | 4, 1 => ⟨-2429956497673874550925079263847959029811370599276155, 2433629166090353789440391385998878097891185017109747⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0674Geometry.ds, E8TAxisProd0674Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4867231064981734800380290232171627164587399699 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0674CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0675CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0675CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0675GraphCenterA.qJetBox,
   E8TAxisProd0675GraphCenterB.qJetBox,
   E8TAxisProd0675GraphCenterC.qJetBox,
   E8TAxisProd0675GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0675GraphWholeA.qJetBox,
   E8TAxisProd0675GraphWholeB.qJetBox,
   E8TAxisProd0675GraphWholeC.qJetBox,
   E8TAxisProd0675GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4611549081196666604381839796446796048512889596, 4611549081196666604381839796446832809014768273⟩
  | 0, 2 => ⟨16060730622192918867321864327285314124569678740, 16060730622192918867321864327285432615554958230⟩
  | 1, 1 => ⟨16087003113914135064841072902664773065581738279, 16087003113914135064841072902664974547453257287⟩
  | 0, 3 => ⟨37754323765893704878428737808421382258293565308, 37754323765893704878428737808421745671643221785⟩
  | 1, 2 => ⟨51803513259317796945796471210420099043930576957, 51803513259317796945796471210420718214602084174⟩
  | 2, 1 => ⟨51877897986645155769864724557704427831359123352, 51877897986645155769864724557705517027544039179⟩
  | 0, 4 => ⟨73595940308373401448275871883556444041763331565, 73595940308373401448275871883557617415902308995⟩
  | 1, 3 => ⟨113317714038814484900405973865428818873798201965, 113317714038814484900405973865430866702320584138⟩
  | 2, 2 => ⟨153084455939579786138942241435908093990359984554, 153084455939579786138942241435911765461834131331⟩
  | 3, 1 => ⟨153274217333152665750909572678564159718690950262, 153274217333152665750909572678570820979054324199⟩
  | 0, 5 => ⟨-146744774492846946517769669071609935058024941824682, 147917428875847096925633935263288443525108849036487⟩
  | 1, 4 => ⟨-283096028014793625176891175008348413809210326375470, 284812912013288428252018582360195652234101378533611⟩
  | 2, 3 => ⟨-547262788421054174119356749780842604382468954610621, 549691664354093941528333771610489119142858985148876⟩
  | 3, 2 => ⟨-1059106548443361665643562580497903672852611898655487, 1062264473818102483864498444367482422539912693546695⟩
  | 4, 1 => ⟨-2051029488195637963279811065389680360396622803895556, 2054261704699959289005792192414077781184461595302290⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0675Geometry.ds, E8TAxisProd0675Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4293736900926019455672595618474854687701849558 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0675CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0676CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0676CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0676GraphCenterA.qJetBox,
   E8TAxisProd0676GraphCenterB.qJetBox,
   E8TAxisProd0676GraphCenterC.qJetBox,
   E8TAxisProd0676GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0676GraphWholeA.qJetBox,
   E8TAxisProd0676GraphWholeB.qJetBox,
   E8TAxisProd0676GraphWholeC.qJetBox,
   E8TAxisProd0676GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4101607851454851598534820863231075478115204827, 4101607851454851598534820863231109382440012138⟩
  | 0, 2 => ⟨14379712225607259717761106331754927146446428318, 14379712225607259717761106331755034828234521096⟩
  | 1, 1 => ⟨14435253885683213554862191059648151304722795504, 14435253885683213554862191059648333404129915648⟩
  | 0, 3 => ⟨34040041253408367385654713808583345571301825074, 34040041253408367385654713808583673858892852196⟩
  | 1, 2 => ⟨46814676028326921374724331350711069186689194107, 46814676028326921374724331350711625920848058828⟩
  | 2, 1 => ⟨46973457960975309243031882714213541341816228276, 46973457960975309243031882714214518008499447238⟩
  | 0, 4 => ⟨66889839926591669622807989548876448573544232207, 66889839926591669622807989548877503439054183817⟩
  | 1, 3 => ⟨103290310854983229666545611631373687300365194406, 103290310854983229666545611631375521131820766793⟩
  | 2, 2 => ⟨139788305404007050267333167871271752761997409559, 139788305404007050267333167871275032719130794083⟩
  | 3, 1 => ⟨140198202741231828925271313002782511579804816964, 140198202741231828925271313002788451146800592265⟩
  | 0, 5 => ⟨-125023963897893097940893017976204726766723755011200, 126064646545810496493731186341796152112631016970227⟩
  | 1, 4 => ⟨-240843212568417375904621655170996441373822503197368, 242362394414093574183695792532869335234439137442360⟩
  | 2, 3 => ⟨-464985043879597885789525363768138853610218857184751, 467130865501545962604102860435579659559951949790083⟩
  | 3, 2 => ⟨-898790756676769617458141319636773996660703237989278, 901579828818694370219861602446638963324442104627653⟩
  | 4, 1 => ⟨-1738526633578145493907659930284651167006969843769217, 1741385775114240488011754155383296094608652748533306⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0676Geometry.ds, E8TAxisProd0676Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3816847496024627110731296391979251712330915130 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0676CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0677CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0677CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0677GraphCenterA.qJetBox,
   E8TAxisProd0677GraphCenterB.qJetBox,
   E8TAxisProd0677GraphCenterC.qJetBox,
   E8TAxisProd0677GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0677GraphWholeA.qJetBox,
   E8TAxisProd0677GraphWholeB.qJetBox,
   E8TAxisProd0677GraphWholeC.qJetBox,
   E8TAxisProd0677GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3612115309525902546003536722142549393523960222, 3612115309525902546003536722142580574842302304⟩
  | 0, 2 => ⟨12784736107190942432573270906207725494432631212, 12784736107190942432573270906207822987834525511⟩
  | 1, 1 => ⟨12834829249576819237708006331589978913166094874, 12834829249576819237708006331590142819650202731⟩
  | 0, 3 => ⟨30504478083420825980562571770219693696961113445, 30504478083420825980562571770219988979088711358⟩
  | 1, 2 => ⟨42026660831909614833365832863056033294075820140, 42026660831909614833365832863056531554504190230⟩
  | 2, 1 => ⟨42171291888031130717072981970733632212449962704, 42171291888031130717072981970734503719001063037⟩
  | 0, 4 => ⟨60451717242872131431781320455130925228005809362, 60451717242872131431781320455131868852682851668⟩
  | 1, 3 => ⟨93608955186851509546582891492861491705193680624, 93608955186851509546582891492863125205742490371⟩
  | 2, 2 => ⟨126856503795962288111497484712768933955086775429, 126856503795962288111497484712771848031979733085⟩
  | 3, 1 => ⟨127234487875081241503199622143739412085523857735, 127234487875081241503199622143744678184717103227⟩
  | 0, 5 => ⟨-105604957355428577438547625911288053611547339189616, 106526196558559796622023992600700780198597438446785⟩
  | 1, 4 => ⟨-203108507310345848783482803485881918647445828867689, 204448238126410038958565791892681351569653449916526⟩
  | 2, 3 => ⟨-391578267422197009282251806996908882628527422558069, 393466043462513083770701514798449617480551675660497⟩
  | 3, 2 => ⟨-755896611417868760516532095433703118463333989060149, 758347380865866658860253252741228832622405913075241⟩
  | 4, 1 => ⟨-1460246169429577320595546984412944567679267815997136, 1462759846783409485370360310730851863329838895090506⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0677Geometry.ds, E8TAxisProd0677Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3359252213256383475556687326401547034254125900 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0677CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0678CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0678CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0678GraphCenterA.qJetBox,
   E8TAxisProd0678GraphCenterB.qJetBox,
   E8TAxisProd0678GraphCenterC.qJetBox,
   E8TAxisProd0678GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0678GraphWholeA.qJetBox,
   E8TAxisProd0678GraphWholeB.qJetBox,
   E8TAxisProd0678GraphWholeC.qJetBox,
   E8TAxisProd0678GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4083659783192781887080353566316497944131887719, 4083659783192781887080353566316531783127900846⟩
  | 0, 2 => ⟨14337214394142431838321900972023156246079556324, 14337214394142431838321900972023263692940807290⟩
  | 1, 1 => ⟨14376816175338969753736297173808623992860212298, 14376816175338969753736297173808805683330525975⟩
  | 0, 3 => ⟨33956519144640089679496208434730421024279524982, 33956519144640089679496208434730748574965369077⟩
  | 1, 2 => ⟨46685709190350675494117747390547430994568826224, 46685709190350675494117747390547986447777988395⟩
  | 2, 1 => ⟨46798941969667293382492863172662420894973554853, 46798941969667293382492863172663395273097299680⟩
  | 0, 4 => ⟨66745579164883910237969715786856973129806878931, 66745579164883910237969715786858025528109307181⟩
  | 1, 3 => ⟨103056704982593560543710859367999785751400185865, 103056704982593560543710859368001615223109676961⟩
  | 2, 2 => ⟨139437398120719638144159877630659177236732704247, 139437398120719638144159877630662449284640114956⟩
  | 3, 1 => ⟨139729772323209196334705530143676526716041671024, 139729772323209196334705530143682451763533506640⟩
  | 0, 5 => ⟨-124607253272070531280039764174771288847460467747142, 125646485839543836845549212421267033121190834299136⟩
  | 1, 4 => ⟨-240033305287881139684742783752272250258222638223815, 241549982056366464482404536392614836878239190819460⟩
  | 2, 3 => ⟨-463408264251041220586770406243319311057352854198241, 465549892687285998228080991558662571027970505048833⟩
  | 3, 2 => ⟨-895717782294460647534666698423176696102260392670186, 898500366812541154868899419815592237797243271605300⟩
  | 4, 1 => ⟨-1732533509272379252509873557479848409292309875966730, 1735384420131648537241437040403553013074919309407062⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0678Geometry.ds, E8TAxisProd0678Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3800034148477607074839265357119885782188959428 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0678CertifiedArithmetic

end


