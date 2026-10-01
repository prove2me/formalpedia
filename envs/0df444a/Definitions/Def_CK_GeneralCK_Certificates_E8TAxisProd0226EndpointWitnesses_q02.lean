-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0226EndpointWitnesses_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0226EndpointWitnesses_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T21:05:01.32631+00:00
-- url     : https://prove2.me/theorems/ca70d292-5762-4ff7-acd8-aa4483e76ae8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0226EndpointWitnesses (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0226EndpointWitnesses (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0226EndpointWitnesses (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0226EndpointWitnesses (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0226EndpointWitnesses (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0226EndpointWitnesses_q01

namespace GeneralCK.Certificates.E8TAxisProd0226EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisProd0226Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem wholeBUpper_yBox_eq : (yBox wholeBUpperInput).d0 = wholeBUpperYBox := by decide +kernel

theorem wholeBUpper_contains :
    wholeBUpperYBox.Contains (Y (upper E8TAxisProd0226PaddedInputs.wholeBInput.alpha)) := by
  have e : upper E8TAxisProd0226PaddedInputs.wholeBInput.alpha = ((2152866358974775393507357304141208389592583803750 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBUpperInput.alpha.Contains (upper E8TAxisProd0226PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 2152866358974775393507357304141208389592583803750
  have h := checked_yBox_d0_contains (i := wholeBUpperInput) (we := wholeBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBUpper_primitive_checks.1 wholeBUpper_primitive_checks.2 endpointLogTwo_checked
    wholeBUpper_denominators ha
  rw [wholeBUpper_yBox_eq] at h
  exact h

def wholeCLowerAlpha : DyadicInterval precision := ⟨839878545320647635022140068963565399041721833071, 839878545320647635022140068963565399041721833071⟩
def wholeCLowerExp : DyadicInterval precision := ⟨463072330686758284346753539973697736523841603103, 463072330686758284346753539973697736523841605152⟩
def wholeCLowerLog : DyadicInterval precision := ⟨402264005960247566147076127930220588071662103702, 402264005960247566147076127930220588071662105527⟩
def wholeCLowerYBox : DyadicInterval precision := ⟨4366692860787738375295447089250119359665740651718, 4366692860787738375295447089250119359665740684319⟩
def wholeCLowerInput : Inputs precision :=
  ⟨wholeCLowerAlpha, wholeCLowerExp, wholeCLowerLog, endpointLogTwo⟩
def wholeCLowerExpWitness : ExpWitness precision :=
  ⟨463072330686758284346753539973697736523841603103, scale precision, 463072330686758284346753539973697736523841605152, scale precision,
    1, 128, 1, 128,
    ⟨-1679757090641295270044280137927130798083443669820, -1679757090641295270044280137927130798083443669278⟩, ⟨-1679757090641295270044280137927130798083443663352, -1679757090641295270044280137927130798083443662810⟩⟩

theorem wholeCLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCLowerAlpha) wholeCLowerExp wholeCLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCLowerExp) wholeCLowerLog fastLogWitness = true := by decide +kernel

theorem wholeCLower_denominators : DenominatorsPositive wholeCLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeCLower_yBox_eq : (yBox wholeCLowerInput).d0 = wholeCLowerYBox := by decide +kernel

theorem wholeCLower_contains :
    wholeCLowerYBox.Contains (Y (lower E8TAxisProd0226PaddedInputs.wholeCInput.alpha)) := by
  have e : lower E8TAxisProd0226PaddedInputs.wholeCInput.alpha = ((839878545320647635022140068963565399041721833071 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCLowerInput.alpha.Contains (lower E8TAxisProd0226PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 839878545320647635022140068963565399041721833071
  have h := checked_yBox_d0_contains (i := wholeCLowerInput) (we := wholeCLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCLower_primitive_checks.1 wholeCLower_primitive_checks.2 endpointLogTwo_checked
    wholeCLower_denominators ha
  rw [wholeCLower_yBox_eq] at h
  exact h

def wholeCUpperAlpha : DyadicInterval precision := ⟨852516252437231778292034028692677701836477845154, 852516252437231778292034028692677701836477845154⟩
def wholeCUpperExp : DyadicInterval precision := ⟨455132744912058013903187661527957809317178570729, 455132744912058013903187661527957809317178572778⟩
def wholeCUpperLog : DyadicInterval precision := ⟨396222295604444985204344277862767903437607592932, 396222295604444985204344277862767903437607594759⟩
def wholeCUpperYBox : DyadicInterval precision := ⟨4421042452925981327566146618966756134459196206559, 4421042452925981327566146618966756134459196239761⟩
def wholeCUpperInput : Inputs precision :=
  ⟨wholeCUpperAlpha, wholeCUpperExp, wholeCUpperLog, endpointLogTwo⟩
def wholeCUpperExpWitness : ExpWitness precision :=
  ⟨455132744912058013903187661527957809317178570729, scale precision, 455132744912058013903187661527957809317178572778, scale precision,
    1, 128, 1, 128,
    ⟨-1705032504874463556584068057385355403672955694042, -1705032504874463556584068057385355403672955693502⟩, ⟨-1705032504874463556584068057385355403672955687462, -1705032504874463556584068057385355403672955686924⟩⟩

theorem wholeCUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCUpperAlpha) wholeCUpperExp wholeCUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCUpperExp) wholeCUpperLog fastLogWitness = true := by decide +kernel

theorem wholeCUpper_denominators : DenominatorsPositive wholeCUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeCUpper_yBox_eq : (yBox wholeCUpperInput).d0 = wholeCUpperYBox := by decide +kernel

theorem wholeCUpper_contains :
    wholeCUpperYBox.Contains (Y (upper E8TAxisProd0226PaddedInputs.wholeCInput.alpha)) := by
  have e : upper E8TAxisProd0226PaddedInputs.wholeCInput.alpha = ((852516252437231778292034028692677701836477845154 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCUpperInput.alpha.Contains (upper E8TAxisProd0226PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 852516252437231778292034028692677701836477845154
  have h := checked_yBox_d0_contains (i := wholeCUpperInput) (we := wholeCUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCUpper_primitive_checks.1 wholeCUpper_primitive_checks.2 endpointLogTwo_checked
    wholeCUpper_denominators ha
  rw [wholeCUpper_yBox_eq] at h
  exact h

def wholeDLowerAlpha : DyadicInterval precision := ⟨833959591445470778384083818034390997094871269362, 833959591445470778384083818034390997094871269362⟩
def wholeDLowerExp : DyadicInterval precision := ⟨466838367135635595432846250236128803062991394213, 466838367135635595432846250236128803062991396262⟩
def wholeDLowerLog : DyadicInterval precision := ⟨405121100734994108525530084726425876454680243246, 405121100734994108525530084726425876454680245063⟩
def wholeDLowerYBox : DyadicInterval precision := ⟨4341116582134447574226882604677584406821761831513, 4341116582134447574226882604677584406821761863813⟩
def wholeDLowerInput : Inputs precision :=
  ⟨wholeDLowerAlpha, wholeDLowerExp, wholeDLowerLog, endpointLogTwo⟩
def wholeDLowerExpWitness : ExpWitness precision :=
  ⟨466838367135635595432846250236128803062991394213, scale precision, 466838367135635595432846250236128803062991396262, scale precision,
    1, 128, 1, 128,
    ⟨-1667919182890941556768167636068781994189742542376, -1667919182890941556768167636068781994189742541838⟩, ⟨-1667919182890941556768167636068781994189742535962, -1667919182890941556768167636068781994189742535424⟩⟩

theorem wholeDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDLowerAlpha) wholeDLowerExp wholeDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDLowerExp) wholeDLowerLog fastLogWitness = true := by decide +kernel

theorem wholeDLower_denominators : DenominatorsPositive wholeDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeDLower_yBox_eq : (yBox wholeDLowerInput).d0 = wholeDLowerYBox := by decide +kernel

theorem wholeDLower_contains :
    wholeDLowerYBox.Contains (Y (lower E8TAxisProd0226PaddedInputs.wholeDInput.alpha)) := by
  have e : lower E8TAxisProd0226PaddedInputs.wholeDInput.alpha = ((833959591445470778384083818034390997094871269362 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeDLowerInput.alpha.Contains (lower E8TAxisProd0226PaddedInputs.wholeDInput.alpha) := by
    rw [e]; exact point_contains precision 833959591445470778384083818034390997094871269362
  have h := checked_yBox_d0_contains (i := wholeDLowerInput) (we := wholeDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeDLower_primitive_checks.1 wholeDLower_primitive_checks.2 endpointLogTwo_checked
    wholeDLower_denominators ha
  rw [wholeDLower_yBox_eq] at h
  exact h

def wholeDUpperAlpha : DyadicInterval precision := ⟨846134075813431409586727826645377644661772035307, 846134075813431409586727826645377644661772035307⟩
def wholeDUpperExp : DyadicInterval precision := ⟨459125158042315647897421247370792078562238777963, 459125158042315647897421247370792078562238780012⟩
def wholeDUpperLog : DyadicInterval precision := ⟨399263485746125009998379766489542016005500250370, 399263485746125009998379766489542016005500252195⟩
def wholeDUpperYBox : DyadicInterval precision := ⟨4393639297226026897849827528353325827840647472445, 4393639297226026897849827528353325827840647505345⟩
def wholeDUpperInput : Inputs precision :=
  ⟨wholeDUpperAlpha, wholeDUpperExp, wholeDUpperLog, endpointLogTwo⟩
def wholeDUpperExpWitness : ExpWitness precision :=
  ⟨459125158042315647897421247370792078562238777963, scale precision, 459125158042315647897421247370792078562238780012, scale precision,
    1, 128, 1, 128,
    ⟨-1692268151626862819173455653290755289323544074324, -1692268151626862819173455653290755289323544073786⟩, ⟨-1692268151626862819173455653290755289323544067804, -1692268151626862819173455653290755289323544067262⟩⟩

theorem wholeDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDUpperAlpha) wholeDUpperExp wholeDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDUpperExp) wholeDUpperLog fastLogWitness = true := by decide +kernel

theorem wholeDUpper_denominators : DenominatorsPositive wholeDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeDUpper_yBox_eq : (yBox wholeDUpperInput).d0 = wholeDUpperYBox := by decide +kernel

theorem wholeDUpper_contains :
    wholeDUpperYBox.Contains (Y (upper E8TAxisProd0226PaddedInputs.wholeDInput.alpha)) := by
  have e : upper E8TAxisProd0226PaddedInputs.wholeDInput.alpha = ((846134075813431409586727826645377644661772035307 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeDUpperInput.alpha.Contains (upper E8TAxisProd0226PaddedInputs.wholeDInput.alpha) := by
    rw [e]; exact point_contains precision 846134075813431409586727826645377644661772035307
  have h := checked_yBox_d0_contains (i := wholeDUpperInput) (we := wholeDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeDUpper_primitive_checks.1 wholeDUpper_primitive_checks.2 endpointLogTwo_checked
    wholeDUpper_denominators ha
  rw [wholeDUpper_yBox_eq] at h
  exact h

theorem centerA_covers_slope {s : ℝ} (hs : s ∈ Icc (centerT) (centerT)) :
    ∃ a : ℝ, E8TAxisProd0226PaddedInputs.centerAInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerALower_contains centerAUpper_contains _ _ hs
  · norm_num [centerALowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerAUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerA_covers :
    ∃ a : ℝ, E8TAxisProd0226PaddedInputs.centerAInput.alpha.Contains a ∧
      0 < a ∧ Y a = (centerT) :=
  centerA_covers_slope ⟨le_rfl, le_rfl⟩

theorem centerB_covers_slope {s : ℝ} (hs : s ∈ Icc (2 * centerS + centerT) (2 * centerS + centerT)) :
    ∃ a : ℝ, E8TAxisProd0226PaddedInputs.centerBInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerBLower_contains centerBUpper_contains _ _ hs
  · norm_num [centerBLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerBUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerB_covers :
    ∃ a : ℝ, E8TAxisProd0226PaddedInputs.centerBInput.alpha.Contains a ∧
      0 < a ∧ Y a = (2 * centerS + centerT) :=
  centerB_covers_slope ⟨le_rfl, le_rfl⟩

theorem centerC_covers_slope {s : ℝ} (hs : s ∈ Icc (centerS + centerT) (centerS + centerT)) :
    ∃ a : ℝ, E8TAxisProd0226PaddedInputs.centerCInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerCLower_contains centerCUpper_contains _ _ hs
  · norm_num [centerCLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerCUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerC_covers :
    ∃ a : ℝ, E8TAxisProd0226PaddedInputs.centerCInput.alpha.Contains a ∧
      0 < a ∧ Y a = (centerS + centerT) :=
  centerC_covers_slope ⟨le_rfl, le_rfl⟩

theorem centerD_covers_slope {s : ℝ} (hs : s ∈ Icc (centerS) (centerS)) :
    ∃ a : ℝ, E8TAxisProd0226PaddedInputs.centerDInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerDLower_contains centerDUpper_contains _ _ hs
  · norm_num [centerDLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerDUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerD_covers :
    ∃ a : ℝ, E8TAxisProd0226PaddedInputs.centerDInput.alpha.Contains a ∧
      0 < a ∧ Y a = (centerS) :=
  centerD_covers_slope ⟨le_rfl, le_rfl⟩

theorem wholeA_covers_slope {s : ℝ} (hs : s ∈ Icc (tLower) (tUpper)) :
    ∃ a : ℝ, E8TAxisProd0226PaddedInputs.wholeAInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    wholeALower_contains wholeAUpper_contains _ _ hs
  · norm_num [wholeALowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [wholeAUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem wholeB_covers_slope {s : ℝ} (hs : s ∈ Icc (2 * sLower + tLower) (2 * sUpper + tUpper)) :
    ∃ a : ℝ, E8TAxisProd0226PaddedInputs.wholeBInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    wholeBLower_contains wholeBUpper_contains _ _ hs
  · norm_num [wholeBLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [wholeBUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem wholeC_covers_slope {s : ℝ} (hs : s ∈ Icc (sLower + tLower) (sUpper + tUpper)) :
    ∃ a : ℝ, E8TAxisProd0226PaddedInputs.wholeCInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    wholeCLower_contains wholeCUpper_contains _ _ hs
  · norm_num [wholeCLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [wholeCUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

end GeneralCK.Certificates.E8TAxisProd0226EndpointWitnesses


