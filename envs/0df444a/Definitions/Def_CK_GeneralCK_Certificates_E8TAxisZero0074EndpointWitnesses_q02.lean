-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0074EndpointWitnesses_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0074EndpointWitnesses_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T16:18:57.630976+00:00
-- url     : https://prove2.me/theorems/139d863b-b1f9-4dcc-8080-bab1dabc03c9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0074EndpointWitnesses (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0074EndpointWitnesses (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0074EndpointWitnesses (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0074EndpointWitnesses (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0074EndpointWitnesses (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0074EndpointWitnesses_q01

namespace GeneralCK.Certificates.E8TAxisZero0074EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0074Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem wholeCLower_yBox_eq : (yBox wholeCLowerInput).d0 = wholeCLowerYBox := by decide +kernel

theorem wholeCLower_contains :
    wholeCLowerYBox.Contains (Y (lower E8TAxisZero0074PaddedInputs.wholeCInput.alpha)) := by
  have e : lower E8TAxisZero0074PaddedInputs.wholeCInput.alpha = ((615985792935344704096715461380744242879772203333 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCLowerInput.alpha.Contains (lower E8TAxisZero0074PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 615985792935344704096715461380744242879772203333
  have h := checked_yBox_d0_contains (i := wholeCLowerInput) (we := wholeCLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCLower_primitive_checks.1 wholeCLower_primitive_checks.2 endpointLogTwo_checked
    wholeCLower_denominators ha
  rw [wholeCLower_yBox_eq] at h
  exact h

def wholeCUpperAlpha : DyadicInterval precision := ⟨627259614167087449859646268174292653717894354536, 627259614167087449859646268174292653717894354536⟩
def wholeCUpperExp : DyadicInterval precision := ⟨619456707788915396279231795820783167662362289354, 619456707788915396279231795820783167662362420427⟩
def wholeCUpperLog : DyadicInterval precision := ⟨516442217407178209762297451045170047053954068992, 516442217407178209762297451045170047053954162083⟩
def wholeCUpperYBox : DyadicInterval precision := ⟨3397534587532683377661628584555134182256480656580, 3397534587532683377661628584555134182256482021429⟩
def wholeCUpperInput : Inputs precision :=
  ⟨wholeCUpperAlpha, wholeCUpperExp, wholeCUpperLog, endpointLogTwo⟩
def wholeCUpperExpWitness : ExpWitness precision :=
  ⟨619456707788915396279231795820783167662362289354, scale precision, 619456707788915396279231795820783167662362420427, scale precision,
    0, 512, 0, 512, ⟨-1254519228334174899719292536348585307435788864667, -1254519228334174899719292536348585307435788863630⟩, ⟨-1254519228334174899719292536348585307435788555425, -1254519228334174899719292536348585307435788554386⟩⟩

theorem wholeCUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCUpperAlpha) wholeCUpperExp wholeCUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCUpperExp) wholeCUpperLog fastLogWitness = true := by decide +kernel

theorem wholeCUpper_denominators : DenominatorsPositive wholeCUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeCUpper_yBox_eq : (yBox wholeCUpperInput).d0 = wholeCUpperYBox := by decide +kernel

theorem wholeCUpper_contains :
    wholeCUpperYBox.Contains (Y (upper E8TAxisZero0074PaddedInputs.wholeCInput.alpha)) := by
  have e : upper E8TAxisZero0074PaddedInputs.wholeCInput.alpha = ((627259614167087449859646268174292653717894354536 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCUpperInput.alpha.Contains (upper E8TAxisZero0074PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 627259614167087449859646268174292653717894354536
  have h := checked_yBox_d0_contains (i := wholeCUpperInput) (we := wholeCUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCUpper_primitive_checks.1 wholeCUpper_primitive_checks.2 endpointLogTwo_checked
    wholeCUpper_denominators ha
  rw [wholeCUpper_yBox_eq] at h
  exact h

def wholeDLowerAlpha : DyadicInterval precision := ⟨615985792935344704096715461380744242879772203333, 615985792935344704096715461380744242879772203333⟩
def wholeDLowerExp : DyadicInterval precision := ⟨629087614762237432177832619094338712010530416968, 629087614762237432177832619094338712010530548041⟩
def wholeDLowerLog : DyadicInterval precision := ⟨523190605620864448684409715253755540103708435928, 523190605620864448684409715253755540103708528593⟩
def wholeDLowerYBox : DyadicInterval precision := ⟨3343184995394440425390929054838497407462863917963, 3343184995394440425390929054838497407462865254448⟩
def wholeDLowerInput : Inputs precision :=
  ⟨wholeDLowerAlpha, wholeDLowerExp, wholeDLowerLog, endpointLogTwo⟩
def wholeDLowerExpWitness : ExpWitness precision :=
  ⟨629087614762237432177832619094338712010530416968, scale precision, 629087614762237432177832619094338712010530548041, scale precision,
    0, 512, 0, 512, ⟨-1231971585870689408193430922761488485759544559889, -1231971585870689408193430922761488485759544558856⟩, ⟨-1231971585870689408193430922761488485759544255377, -1231971585870689408193430922761488485759544254344⟩⟩

theorem wholeDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDLowerAlpha) wholeDLowerExp wholeDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDLowerExp) wholeDLowerLog fastLogWitness = true := by decide +kernel

theorem wholeDLower_denominators : DenominatorsPositive wholeDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeDLower_yBox_eq : (yBox wholeDLowerInput).d0 = wholeDLowerYBox := by decide +kernel

theorem wholeDLower_contains :
    wholeDLowerYBox.Contains (Y (lower E8TAxisZero0074PaddedInputs.wholeDInput.alpha)) := by
  have e : lower E8TAxisZero0074PaddedInputs.wholeDInput.alpha = ((615985792935344704096715461380744242879772203333 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeDLowerInput.alpha.Contains (lower E8TAxisZero0074PaddedInputs.wholeDInput.alpha) := by
    rw [e]; exact point_contains precision 615985792935344704096715461380744242879772203333
  have h := checked_yBox_d0_contains (i := wholeDLowerInput) (we := wholeDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeDLower_primitive_checks.1 wholeDLower_primitive_checks.2 endpointLogTwo_checked
    wholeDLower_denominators ha
  rw [wholeDLower_yBox_eq] at h
  exact h

def wholeDUpperAlpha : DyadicInterval precision := ⟨626879646060933815899481326077700461408859425189, 626879646060933815899481326077700461408859425189⟩
def wholeDUpperExp : DyadicInterval precision := ⟨619778890111929048152500802482413363510569386287, 619778890111929048152500802482413363510569517360⟩
def wholeDUpperLog : DyadicInterval precision := ⟨516668475441837355502384214637433234445085170468, 516668475441837355502384214637433234445085263539⟩
def wholeDUpperYBox : DyadicInterval precision := ⟨3395707710486019749013873978514238828481910756487, 3395707710486019749013873978514238828481912120351⟩
def wholeDUpperInput : Inputs precision :=
  ⟨wholeDUpperAlpha, wholeDUpperExp, wholeDUpperLog, endpointLogTwo⟩
def wholeDUpperExpWitness : ExpWitness precision :=
  ⟨619778890111929048152500802482413363510569386287, scale precision, 619778890111929048152500802482413363510569517360, scale precision,
    0, 512, 0, 512, ⟨-1253759292121867631798962652155400922817719005887, -1253759292121867631798962652155400922817719004856⟩, ⟨-1253759292121867631798962652155400922817718696805, -1253759292121867631798962652155400922817718695772⟩⟩

theorem wholeDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDUpperAlpha) wholeDUpperExp wholeDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDUpperExp) wholeDUpperLog fastLogWitness = true := by decide +kernel

theorem wholeDUpper_denominators : DenominatorsPositive wholeDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeDUpper_yBox_eq : (yBox wholeDUpperInput).d0 = wholeDUpperYBox := by decide +kernel

theorem wholeDUpper_contains :
    wholeDUpperYBox.Contains (Y (upper E8TAxisZero0074PaddedInputs.wholeDInput.alpha)) := by
  have e : upper E8TAxisZero0074PaddedInputs.wholeDInput.alpha = ((626879646060933815899481326077700461408859425189 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeDUpperInput.alpha.Contains (upper E8TAxisZero0074PaddedInputs.wholeDInput.alpha) := by
    rw [e]; exact point_contains precision 626879646060933815899481326077700461408859425189
  have h := checked_yBox_d0_contains (i := wholeDUpperInput) (we := wholeDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeDUpper_primitive_checks.1 wholeDUpper_primitive_checks.2 endpointLogTwo_checked
    wholeDUpper_denominators ha
  rw [wholeDUpper_yBox_eq] at h
  exact h

theorem centerB_covers_slope {s : ℝ} (hs : s ∈ Icc (2 * centerS + centerT) (2 * centerS + centerT)) :
    ∃ a : ℝ, E8TAxisZero0074PaddedInputs.centerBInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerBLower_contains centerBUpper_contains _ _ hs
  · norm_num [centerBLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerBUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerB_covers :
    ∃ a : ℝ, E8TAxisZero0074PaddedInputs.centerBInput.alpha.Contains a ∧
      0 < a ∧ Y a = (2 * centerS + centerT) :=
  centerB_covers_slope ⟨le_rfl, le_rfl⟩

theorem centerC_covers_slope {s : ℝ} (hs : s ∈ Icc (centerS + centerT) (centerS + centerT)) :
    ∃ a : ℝ, E8TAxisZero0074PaddedInputs.centerCInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerCLower_contains centerCUpper_contains _ _ hs
  · norm_num [centerCLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerCUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerC_covers :
    ∃ a : ℝ, E8TAxisZero0074PaddedInputs.centerCInput.alpha.Contains a ∧
      0 < a ∧ Y a = (centerS + centerT) :=
  centerC_covers_slope ⟨le_rfl, le_rfl⟩

theorem centerD_covers_slope {s : ℝ} (hs : s ∈ Icc (centerS) (centerS)) :
    ∃ a : ℝ, E8TAxisZero0074PaddedInputs.centerDInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerDLower_contains centerDUpper_contains _ _ hs
  · norm_num [centerDLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerDUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerD_covers :
    ∃ a : ℝ, E8TAxisZero0074PaddedInputs.centerDInput.alpha.Contains a ∧
      0 < a ∧ Y a = (centerS) :=
  centerD_covers_slope ⟨le_rfl, le_rfl⟩

theorem wholeB_covers_slope {s : ℝ} (hs : s ∈ Icc (2 * sLower + tLower) (2 * sUpper + tUpper)) :
    ∃ a : ℝ, E8TAxisZero0074PaddedInputs.wholeBInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    wholeBLower_contains wholeBUpper_contains _ _ hs
  · norm_num [wholeBLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [wholeBUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem wholeC_covers_slope {s : ℝ} (hs : s ∈ Icc (sLower + tLower) (sUpper + tUpper)) :
    ∃ a : ℝ, E8TAxisZero0074PaddedInputs.wholeCInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    wholeCLower_contains wholeCUpper_contains _ _ hs
  · norm_num [wholeCLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [wholeCUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

end GeneralCK.Certificates.E8TAxisZero0074EndpointWitnesses


