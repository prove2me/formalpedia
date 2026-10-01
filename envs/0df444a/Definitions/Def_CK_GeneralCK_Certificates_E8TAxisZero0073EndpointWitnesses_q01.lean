-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0073EndpointWitnesses_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0073EndpointWitnesses_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T00:32:38.710932+00:00
-- url     : https://prove2.me/theorems/46c0c6f1-70f0-4bbc-9d01-40389892acd4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0073EndpointWitnesses (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0073EndpointWitnesses (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0073EndpointWitnesses (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0073EndpointWitnesses (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0073EndpointWitnesses (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0073EndpointWitnesses_q00

namespace GeneralCK.Certificates.E8TAxisZero0073EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0073Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerDLowerLog : DyadicInterval precision := ⟨513419890646572039308129704473371305847051568522, 513419890646572039308129704473371305847051661799⟩
def centerDLowerYBox : DyadicInterval precision := ⟨3421969068031809410825346440352109538991192160754, 3421969068031809410825346440352109538991193538472⟩
def centerDLowerInput : Inputs precision :=
  ⟨centerDLowerAlpha, centerDLowerExp, centerDLowerLog, endpointLogTwo⟩
def centerDLowerExpWitness : ExpWitness precision :=
  ⟨615157815904934041673261697075548684821454434631, scale precision, 615157815904934041673261697075548684821454565704, scale precision,
    0, 512, 0, 512, ⟨-1264697081903934623360950958793901668420802575705, -1264697081903934623360950958793901668420802574670⟩, ⟨-1264697081903934623360950958793901668420802264303, -1264697081903934623360950958793901668420802263264⟩⟩

theorem centerDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDLowerAlpha) centerDLowerExp centerDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDLowerExp) centerDLowerLog fastLogWitness = true := by decide +kernel

theorem centerDLower_denominators : DenominatorsPositive centerDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDLower_yBox_eq : (yBox centerDLowerInput).d0 = centerDLowerYBox := by decide +kernel

theorem centerDLower_contains :
    centerDLowerYBox.Contains (Y (lower E8TAxisZero0073PaddedInputs.centerDInput.alpha)) := by
  have e : lower E8TAxisZero0073PaddedInputs.centerDInput.alpha = ((632348540951967311680475479396950834210401209515 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDLowerInput.alpha.Contains (lower E8TAxisZero0073PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 632348540951967311680475479396950834210401209515
  have h := checked_yBox_d0_contains (i := centerDLowerInput) (we := centerDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDLower_primitive_checks.1 centerDLower_primitive_checks.2 endpointLogTwo_checked
    centerDLower_denominators ha
  rw [centerDLower_yBox_eq] at h
  exact h

def centerDUpperAlpha : DyadicInterval precision := ⟨632348540951967311680475479396950834210434763948, 632348540951967311680475479396950834210434763948⟩
def centerDUpperExp : DyadicInterval precision := ⟨615157815904934041673261697075548684821426187969, 615157815904934041673261697075548684821426319042⟩
def centerDUpperLog : DyadicInterval precision := ⟨513419890646572039308129704473371305847031689218, 513419890646572039308129704473371305847031782495⟩
def centerDUpperYBox : DyadicInterval precision := ⟨3421969068031809410825346440352109538991353070162, 3421969068031809410825346440352109538991354447871⟩
def centerDUpperInput : Inputs precision :=
  ⟨centerDUpperAlpha, centerDUpperExp, centerDUpperLog, endpointLogTwo⟩
def centerDUpperExpWitness : ExpWitness precision :=
  ⟨615157815904934041673261697075548684821426187969, scale precision, 615157815904934041673261697075548684821426319042, scale precision,
    0, 512, 0, 512, ⟨-1264697081903934623360950958793901668420869684575, -1264697081903934623360950958793901668420869683536⟩, ⟨-1264697081903934623360950958793901668420869373171, -1264697081903934623360950958793901668420869372132⟩⟩

theorem centerDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDUpperAlpha) centerDUpperExp centerDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDUpperExp) centerDUpperLog fastLogWitness = true := by decide +kernel

theorem centerDUpper_denominators : DenominatorsPositive centerDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDUpper_yBox_eq : (yBox centerDUpperInput).d0 = centerDUpperYBox := by decide +kernel

theorem centerDUpper_contains :
    centerDUpperYBox.Contains (Y (upper E8TAxisZero0073PaddedInputs.centerDInput.alpha)) := by
  have e : upper E8TAxisZero0073PaddedInputs.centerDInput.alpha = ((632348540951967311680475479396950834210434763948 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDUpperInput.alpha.Contains (upper E8TAxisZero0073PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 632348540951967311680475479396950834210434763948
  have h := checked_yBox_d0_contains (i := centerDUpperInput) (we := centerDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDUpper_primitive_checks.1 centerDUpper_primitive_checks.2 endpointLogTwo_checked
    centerDUpper_denominators ha
  rw [centerDUpper_yBox_eq] at h
  exact h

def wholeBLowerAlpha : DyadicInterval precision := ⟨1490432167721794696980616209388009438020822528313, 1490432167721794696980616209388009438020822528313⟩
def wholeBLowerExp : DyadicInterval precision := ⟨190115077622846987918604476073469168487389245259, 190115077622846987918604476073469168487389376332⟩
def wholeBLowerLog : DyadicInterval precision := ⟨178727341505497326528163329779799873134740860556, 178727341505497326528163329779799873134740977575⟩
def wholeBLowerYBox : DyadicInterval precision := ⟨6791415420972039498027747957028477656963604231482, 6791415420972039498027747957028477656963608798073⟩
def wholeBLowerInput : Inputs precision :=
  ⟨wholeBLowerAlpha, wholeBLowerExp, wholeBLowerLog, endpointLogTwo⟩
def wholeBLowerExpWitness : ExpWitness precision :=
  ⟨190115077622846987918604476073469168487389245259, scale precision, 190115077622846987918604476073469168487389376332, scale precision,
    0, 512, 0, 512, ⟨-2980864335443589393961232418776018876041645561274, -2980864335443589393961232418776018876041645560220⟩, ⟨-2980864335443589393961232418776018876041644553658, -2980864335443589393961232418776018876041644552608⟩⟩

theorem wholeBLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBLowerAlpha) wholeBLowerExp wholeBLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBLowerExp) wholeBLowerLog fastLogWitness = true := by decide +kernel

theorem wholeBLower_denominators : DenominatorsPositive wholeBLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBLower_yBox_eq : (yBox wholeBLowerInput).d0 = wholeBLowerYBox := by decide +kernel

theorem wholeBLower_contains :
    wholeBLowerYBox.Contains (Y (lower E8TAxisZero0073PaddedInputs.wholeBInput.alpha)) := by
  have e : lower E8TAxisZero0073PaddedInputs.wholeBInput.alpha = ((1490432167721794696980616209388009438020822528313 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBLowerInput.alpha.Contains (lower E8TAxisZero0073PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 1490432167721794696980616209388009438020822528313
  have h := checked_yBox_d0_contains (i := wholeBLowerInput) (we := wholeBLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBLower_primitive_checks.1 wholeBLower_primitive_checks.2 endpointLogTwo_checked
    wholeBLower_denominators ha
  rw [wholeBLower_yBox_eq] at h
  exact h

def wholeBUpperAlpha : DyadicInterval precision := ⟨1523176960709381972906813366267502281260670872926, 1523176960709381972906813366267502281260670872926⟩
def wholeBUpperExp : DyadicInterval precision := ⟨181784108770710961996236050710722837648198430074, 181784108770710961996236050710722837648198561147⟩
def wholeBUpperLog : DyadicInterval precision := ⟨171336682323016084429662620851658149867632241000, 171336682323016084429662620851658149867632358607⟩
def wholeBUpperYBox : DyadicInterval precision := ⟨6898287728201861773921392410420855852776053726888, 6898287728201861773921392410420855852776058476324⟩
def wholeBUpperInput : Inputs precision :=
  ⟨wholeBUpperAlpha, wholeBUpperExp, wholeBUpperLog, endpointLogTwo⟩
def wholeBUpperExpWitness : ExpWitness precision :=
  ⟨181784108770710961996236050710722837648198430074, scale precision, 181784108770710961996236050710722837648198561147, scale precision,
    0, 512, 0, 512, ⟨-3046353921418763945813626732535004562521342273591, -3046353921418763945813626732535004562521342272528⟩, ⟨-3046353921418763945813626732535004562521341219787, -3046353921418763945813626732535004562521341218736⟩⟩

theorem wholeBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBUpperAlpha) wholeBUpperExp wholeBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBUpperExp) wholeBUpperLog fastLogWitness = true := by decide +kernel

theorem wholeBUpper_denominators : DenominatorsPositive wholeBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBUpper_yBox_eq : (yBox wholeBUpperInput).d0 = wholeBUpperYBox := by decide +kernel

theorem wholeBUpper_contains :
    wholeBUpperYBox.Contains (Y (upper E8TAxisZero0073PaddedInputs.wholeBInput.alpha)) := by
  have e : upper E8TAxisZero0073PaddedInputs.wholeBInput.alpha = ((1523176960709381972906813366267502281260670872926 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBUpperInput.alpha.Contains (upper E8TAxisZero0073PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 1523176960709381972906813366267502281260670872926
  have h := checked_yBox_d0_contains (i := wholeBUpperInput) (we := wholeBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBUpper_primitive_checks.1 wholeBUpper_primitive_checks.2 endpointLogTwo_checked
    wholeBUpper_denominators ha
  rw [wholeBUpper_yBox_eq] at h
  exact h

def wholeCLowerAlpha : DyadicInterval precision := ⟨626879646060933815899481326077700461408825870756, 626879646060933815899481326077700461408825870756⟩
def wholeCLowerExp : DyadicInterval precision := ⟨619778890111929048152500802482413363510597845139, 619778890111929048152500802482413363510597976212⟩
def wholeCLowerLog : DyadicInterval precision := ⟨516668475441837355502384214637433234445105154636, 516668475441837355502384214637433234445105247709⟩
def wholeCLowerYBox : DyadicInterval precision := ⟨3395707710486019749013873978514238828481749412525, 3395707710486019749013873978514238828481750776395⟩
def wholeCLowerInput : Inputs precision :=
  ⟨wholeCLowerAlpha, wholeCLowerExp, wholeCLowerLog, endpointLogTwo⟩
def wholeCLowerExpWitness : ExpWitness precision :=
  ⟨619778890111929048152500802482413363510597845139, scale precision, 619778890111929048152500802482413363510597976212, scale precision,
    0, 512, 0, 512, ⟨-1253759292121867631798962652155400922817651897019, -1253759292121867631798962652155400922817651895988⟩, ⟨-1253759292121867631798962652155400922817651587939, -1253759292121867631798962652155400922817651586908⟩⟩

theorem wholeCLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCLowerAlpha) wholeCLowerExp wholeCLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCLowerExp) wholeCLowerLog fastLogWitness = true := by decide +kernel

theorem wholeCLower_denominators : DenominatorsPositive wholeCLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

end GeneralCK.Certificates.E8TAxisZero0073EndpointWitnesses


