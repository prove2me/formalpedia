-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0061EndpointWitnesses_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0061EndpointWitnesses_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T00:47:49.806343+00:00
-- url     : https://prove2.me/theorems/053f3442-faf7-4671-abbc-694039816f61
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0061EndpointWitnesses (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0061EndpointWitnesses (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0061EndpointWitnesses (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0061EndpointWitnesses (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0061EndpointWitnesses (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0061EndpointWitnesses_q01

namespace GeneralCK.Certificates.E8TAxisZero0061EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0061Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem wholeCLower_yBox_eq : (yBox wholeCLowerInput).d0 = wholeCLowerYBox := by decide +kernel

theorem wholeCLower_contains :
    wholeCLowerYBox.Contains (Y (lower E8TAxisZero0061PaddedInputs.wholeCInput.alpha)) := by
  have e : lower E8TAxisZero0061PaddedInputs.wholeCInput.alpha = ((762469961061176672454638714549067897721924796276 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCLowerInput.alpha.Contains (lower E8TAxisZero0061PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 762469961061176672454638714549067897721924796276
  have h := checked_yBox_d0_contains (i := wholeCLowerInput) (we := wholeCLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCLower_primitive_checks.1 wholeCLower_primitive_checks.2 endpointLogTwo_checked
    wholeCLower_denominators ha
  rw [wholeCLower_yBox_eq] at h
  exact h

def wholeCUpperAlpha : DyadicInterval precision := ⟨774613246448220558536692060304546312326778027647, 774613246448220558536692060304546312326778027647⟩
def wholeCUpperExp : DyadicInterval precision := ⟨506333692325937324659679685745915128091147028340, 506333692325937324659679685745915128091147159413⟩
def wholeCUpperLog : DyadicInterval precision := ⟨434752446733309387933512762274426295145208782134, 434752446733309387933512762274426295145208880515⟩
def wholeCUpperYBox : DyadicInterval precision := ⟨4080329883723214584759912592339772655501980642750, 4080329883723214584759912592339772655501982401820⟩
def wholeCUpperInput : Inputs precision :=
  ⟨wholeCUpperAlpha, wholeCUpperExp, wholeCUpperLog, endpointLogTwo⟩
def wholeCUpperExpWitness : ExpWitness precision :=
  ⟨506333692325937324659679685745915128091147028340, scale precision, 506333692325937324659679685745915128091147159413, scale precision,
    0, 512, 0, 512, ⟨-1549226492896441117073384120609092624653556245417, -1549226492896441117073384120609092624653556244378⟩, ⟨-1549226492896441117073384120609092624653555867083, -1549226492896441117073384120609092624653555866044⟩⟩

theorem wholeCUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCUpperAlpha) wholeCUpperExp wholeCUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCUpperExp) wholeCUpperLog fastLogWitness = true := by decide +kernel

theorem wholeCUpper_denominators : DenominatorsPositive wholeCUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeCUpper_yBox_eq : (yBox wholeCUpperInput).d0 = wholeCUpperYBox := by decide +kernel

theorem wholeCUpper_contains :
    wholeCUpperYBox.Contains (Y (upper E8TAxisZero0061PaddedInputs.wholeCInput.alpha)) := by
  have e : upper E8TAxisZero0061PaddedInputs.wholeCInput.alpha = ((774613246448220558536692060304546312326778027647 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCUpperInput.alpha.Contains (upper E8TAxisZero0061PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 774613246448220558536692060304546312326778027647
  have h := checked_yBox_d0_contains (i := wholeCUpperInput) (we := wholeCUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCUpper_primitive_checks.1 wholeCUpper_primitive_checks.2 endpointLogTwo_checked
    wholeCUpper_denominators ha
  rw [wholeCUpper_yBox_eq] at h
  exact h

def wholeDLowerAlpha : DyadicInterval precision := ⟨762469961061176672454638714549067897721924796276, 762469961061176672454638714549067897721924796276⟩
def wholeDLowerExp : DyadicInterval precision := ⟨514818014850194000087183801285808386015802321396, 514818014850194000087183801285808386015802452469⟩
def wholeDLowerLog : DyadicInterval precision := ⟨441040166381185817721359138930122617251991386850, 441040166381185817721359138930122617251991484817⟩
def wholeDLowerYBox : DyadicInterval precision := ⟨4025980291584971632489213062623135880708375488721, 4025980291584971632489213062623135880708377213613⟩
def wholeDLowerInput : Inputs precision :=
  ⟨wholeDLowerAlpha, wholeDLowerExp, wholeDLowerLog, endpointLogTwo⟩
def wholeDLowerExpWitness : ExpWitness precision :=
  ⟨514818014850194000087183801285808386015802321396, scale precision, 514818014850194000087183801285808386015802452469, scale precision,
    0, 512, 0, 512, ⟨-1524939922122353344909277429098135795443849779565, -1524939922122353344909277429098135795443849778522⟩, ⟨-1524939922122353344909277429098135795443849407457, -1524939922122353344909277429098135795443849406420⟩⟩

theorem wholeDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDLowerAlpha) wholeDLowerExp wholeDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDLowerExp) wholeDLowerLog fastLogWitness = true := by decide +kernel

theorem wholeDLower_denominators : DenominatorsPositive wholeDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeDLower_yBox_eq : (yBox wholeDLowerInput).d0 = wholeDLowerYBox := by decide +kernel

theorem wholeDLower_contains :
    wholeDLowerYBox.Contains (Y (lower E8TAxisZero0061PaddedInputs.wholeDInput.alpha)) := by
  have e : lower E8TAxisZero0061PaddedInputs.wholeDInput.alpha = ((762469961061176672454638714549067897721924796276 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeDLowerInput.alpha.Contains (lower E8TAxisZero0061PaddedInputs.wholeDInput.alpha) := by
    rw [e]; exact point_contains precision 762469961061176672454638714549067897721924796276
  have h := checked_yBox_d0_contains (i := wholeDLowerInput) (we := wholeDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeDLower_primitive_checks.1 wholeDLower_primitive_checks.2 endpointLogTwo_checked
    wholeDLower_denominators ha
  rw [wholeDLower_yBox_eq] at h
  exact h

def wholeDUpperAlpha : DyadicInterval precision := ⟨774203834768265108571628471566363912561715644287, 774203834768265108571628471566363912561715644287⟩
def wholeDUpperExp : DyadicInterval precision := ⟨506617451172271417683927781753795730532533039461, 506617451172271417683927781753795730532533170534⟩
def wholeDUpperLog : DyadicInterval precision := ⟨434963177842048586751554818318029032814903557418, 434963177842048586751554818318029032814903655783⟩
def wholeDUpperYBox : DyadicInterval precision := ⟨4078503006676550956112157986298877301727410743419, 4078503006676550956112157986298877301727412501331⟩
def wholeDUpperInput : Inputs precision :=
  ⟨wholeDUpperAlpha, wholeDUpperExp, wholeDUpperLog, endpointLogTwo⟩
def wholeDUpperExpWitness : ExpWitness precision :=
  ⟨506617451172271417683927781753795730532533039461, scale precision, 506617451172271417683927781753795730532533170534, scale precision,
    0, 512, 0, 512, ⟨-1548407669536530217143256943132727825123431478591, -1548407669536530217143256943132727825123431477556⟩, ⟨-1548407669536530217143256943132727825123431100469, -1548407669536530217143256943132727825123431099438⟩⟩

theorem wholeDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDUpperAlpha) wholeDUpperExp wholeDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDUpperExp) wholeDUpperLog fastLogWitness = true := by decide +kernel

theorem wholeDUpper_denominators : DenominatorsPositive wholeDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeDUpper_yBox_eq : (yBox wholeDUpperInput).d0 = wholeDUpperYBox := by decide +kernel

theorem wholeDUpper_contains :
    wholeDUpperYBox.Contains (Y (upper E8TAxisZero0061PaddedInputs.wholeDInput.alpha)) := by
  have e : upper E8TAxisZero0061PaddedInputs.wholeDInput.alpha = ((774203834768265108571628471566363912561715644287 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeDUpperInput.alpha.Contains (upper E8TAxisZero0061PaddedInputs.wholeDInput.alpha) := by
    rw [e]; exact point_contains precision 774203834768265108571628471566363912561715644287
  have h := checked_yBox_d0_contains (i := wholeDUpperInput) (we := wholeDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeDUpper_primitive_checks.1 wholeDUpper_primitive_checks.2 endpointLogTwo_checked
    wholeDUpper_denominators ha
  rw [wholeDUpper_yBox_eq] at h
  exact h

theorem centerB_covers_slope {s : ℝ} (hs : s ∈ Icc (2 * centerS + centerT) (2 * centerS + centerT)) :
    ∃ a : ℝ, E8TAxisZero0061PaddedInputs.centerBInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerBLower_contains centerBUpper_contains _ _ hs
  · norm_num [centerBLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerBUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerB_covers :
    ∃ a : ℝ, E8TAxisZero0061PaddedInputs.centerBInput.alpha.Contains a ∧
      0 < a ∧ Y a = (2 * centerS + centerT) :=
  centerB_covers_slope ⟨le_rfl, le_rfl⟩

theorem centerC_covers_slope {s : ℝ} (hs : s ∈ Icc (centerS + centerT) (centerS + centerT)) :
    ∃ a : ℝ, E8TAxisZero0061PaddedInputs.centerCInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerCLower_contains centerCUpper_contains _ _ hs
  · norm_num [centerCLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerCUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerC_covers :
    ∃ a : ℝ, E8TAxisZero0061PaddedInputs.centerCInput.alpha.Contains a ∧
      0 < a ∧ Y a = (centerS + centerT) :=
  centerC_covers_slope ⟨le_rfl, le_rfl⟩

theorem centerD_covers_slope {s : ℝ} (hs : s ∈ Icc (centerS) (centerS)) :
    ∃ a : ℝ, E8TAxisZero0061PaddedInputs.centerDInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerDLower_contains centerDUpper_contains _ _ hs
  · norm_num [centerDLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerDUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerD_covers :
    ∃ a : ℝ, E8TAxisZero0061PaddedInputs.centerDInput.alpha.Contains a ∧
      0 < a ∧ Y a = (centerS) :=
  centerD_covers_slope ⟨le_rfl, le_rfl⟩

theorem wholeB_covers_slope {s : ℝ} (hs : s ∈ Icc (2 * sLower + tLower) (2 * sUpper + tUpper)) :
    ∃ a : ℝ, E8TAxisZero0061PaddedInputs.wholeBInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    wholeBLower_contains wholeBUpper_contains _ _ hs
  · norm_num [wholeBLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [wholeBUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem wholeC_covers_slope {s : ℝ} (hs : s ∈ Icc (sLower + tLower) (sUpper + tUpper)) :
    ∃ a : ℝ, E8TAxisZero0061PaddedInputs.wholeCInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    wholeCLower_contains wholeCUpper_contains _ _ hs
  · norm_num [wholeCLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [wholeCUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

end GeneralCK.Certificates.E8TAxisZero0061EndpointWitnesses


