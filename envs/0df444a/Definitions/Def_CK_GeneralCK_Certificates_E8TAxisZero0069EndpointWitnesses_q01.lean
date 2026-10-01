-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0069EndpointWitnesses_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0069EndpointWitnesses_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T00:54:06.764581+00:00
-- url     : https://prove2.me/theorems/cb5a0906-fcc1-4693-9e26-8412c901f31e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0069EndpointWitnesses (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0069EndpointWitnesses (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0069EndpointWitnesses (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0069EndpointWitnesses (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0069EndpointWitnesses (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0069EndpointWitnesses_q00

namespace GeneralCK.Certificates.E8TAxisZero0069EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0069Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerDLowerLog : DyadicInterval precision := ⟨487732559398326774108745629110692921277149540962, 487732559398326774108745629110692921277149635879⟩
def centerDLowerYBox : DyadicInterval precision := ⟨3632059928398126705317126135055075223066734166334, 3632059928398126705317126135055075223066735658359⟩
def centerDLowerInput : Inputs precision :=
  ⟨centerDLowerAlpha, centerDLowerExp, centerDLowerLog, endpointLogTwo⟩
def centerDLowerExpWitness : ExpWitness precision :=
  ⟨578977364869803800462989438501500577420216606942, scale precision, 578977364869803800462989438501500577420216738015, scale precision,
    0, 512, 0, 512, ⟨-1353286680026852150371218657192539012428191002211, -1353286680026852150371218657192539012428191001176⟩, ⟨-1353286680026852150371218657192539012428190671345, -1353286680026852150371218657192539012428190670308⟩⟩

theorem centerDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDLowerAlpha) centerDLowerExp centerDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDLowerExp) centerDLowerLog fastLogWitness = true := by decide +kernel

theorem centerDLower_denominators : DenominatorsPositive centerDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDLower_yBox_eq : (yBox centerDLowerInput).d0 = centerDLowerYBox := by decide +kernel

theorem centerDLower_contains :
    centerDLowerYBox.Contains (Y (lower E8TAxisZero0069PaddedInputs.centerDInput.alpha)) := by
  have e : lower E8TAxisZero0069PaddedInputs.centerDInput.alpha = ((676643340013426075185609328596269506214095417902 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDLowerInput.alpha.Contains (lower E8TAxisZero0069PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 676643340013426075185609328596269506214095417902
  have h := checked_yBox_d0_contains (i := centerDLowerInput) (we := centerDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDLower_primitive_checks.1 centerDLower_primitive_checks.2 endpointLogTwo_checked
    centerDLower_denominators ha
  rw [centerDLower_yBox_eq] at h
  exact h

def centerDUpperAlpha : DyadicInterval precision := ⟨676643340013426075185609328596269506214128972335, 676643340013426075185609328596269506214128972335⟩
def centerDUpperExp : DyadicInterval precision := ⟨578977364869803800462989438501500577420190021605, 578977364869803800462989438501500577420190152678⟩
def centerDUpperLog : DyadicInterval precision := ⟨487732559398326774108745629110692921277130499102, 487732559398326774108745629110692921277130594017⟩
def centerDUpperYBox : DyadicInterval precision := ⟨3632059928398126705317126135055075223066891556258, 3632059928398126705317126135055075223066893048271⟩
def centerDUpperInput : Inputs precision :=
  ⟨centerDUpperAlpha, centerDUpperExp, centerDUpperLog, endpointLogTwo⟩
def centerDUpperExpWitness : ExpWitness precision :=
  ⟨578977364869803800462989438501500577420190021605, scale precision, 578977364869803800462989438501500577420190152678, scale precision,
    0, 512, 0, 512, ⟨-1353286680026852150371218657192539012428258111077, -1353286680026852150371218657192539012428258110038⟩, ⟨-1353286680026852150371218657192539012428257780213, -1353286680026852150371218657192539012428257779170⟩⟩

theorem centerDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDUpperAlpha) centerDUpperExp centerDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDUpperExp) centerDUpperLog fastLogWitness = true := by decide +kernel

theorem centerDUpper_denominators : DenominatorsPositive centerDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDUpper_yBox_eq : (yBox centerDUpperInput).d0 = centerDUpperYBox := by decide +kernel

theorem centerDUpper_contains :
    centerDUpperYBox.Contains (Y (upper E8TAxisZero0069PaddedInputs.centerDInput.alpha)) := by
  have e : upper E8TAxisZero0069PaddedInputs.centerDInput.alpha = ((676643340013426075185609328596269506214128972335 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDUpperInput.alpha.Contains (upper E8TAxisZero0069PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 676643340013426075185609328596269506214128972335
  have h := checked_yBox_d0_contains (i := centerDUpperInput) (we := centerDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDUpper_primitive_checks.1 centerDUpper_primitive_checks.2 endpointLogTwo_checked
    centerDUpper_denominators ha
  rw [centerDUpper_yBox_eq] at h
  exact h

def wholeBLowerAlpha : DyadicInterval precision := ⟨1620903550425908375993486831338272100554110669578, 1620903550425908375993486831338272100554110669578⟩
def wholeBLowerExp : DyadicInterval precision := ⟨159028793201307320320006313149470072983206090023, 159028793201307320320006313149470072983206221096⟩
def wholeBLowerLog : DyadicInterval precision := ⟨150957182965409784487798469398587558183721412554, 150957182965409784487798469398587558183721531799⟩
def wholeBLowerYBox : DyadicInterval precision := ⟨7211597141704674087011307346434409025114686357855, 7211597141704674087011307346434409025114691695255⟩
def wholeBLowerInput : Inputs precision :=
  ⟨wholeBLowerAlpha, wholeBLowerExp, wholeBLowerLog, endpointLogTwo⟩
def wholeBLowerExpWitness : ExpWitness precision :=
  ⟨159028793201307320320006313149470072983206090023, scale precision, 159028793201307320320006313149470072983206221096, scale precision,
    0, 512, 0, 512, ⟨-3241807100851816751986973662676544201108221942252, -3241807100851816751986973662676544201108221941184⟩, ⟨-3241807100851816751986973662676544201108220737664, -3241807100851816751986973662676544201108220736598⟩⟩

theorem wholeBLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBLowerAlpha) wholeBLowerExp wholeBLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBLowerExp) wholeBLowerLog fastLogWitness = true := by decide +kernel

theorem wholeBLower_denominators : DenominatorsPositive wholeBLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBLower_yBox_eq : (yBox wholeBLowerInput).d0 = wholeBLowerYBox := by decide +kernel

theorem wholeBLower_contains :
    wholeBLowerYBox.Contains (Y (lower E8TAxisZero0069PaddedInputs.wholeBInput.alpha)) := by
  have e : lower E8TAxisZero0069PaddedInputs.wholeBInput.alpha = ((1620903550425908375993486831338272100554110669578 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBLowerInput.alpha.Contains (lower E8TAxisZero0069PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 1620903550425908375993486831338272100554110669578
  have h := checked_yBox_d0_contains (i := wholeBLowerInput) (we := wholeBLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBLower_primitive_checks.1 wholeBLower_primitive_checks.2 endpointLogTwo_checked
    wholeBLower_denominators ha
  rw [wholeBLower_yBox_eq] at h
  exact h

def wholeBUpperAlpha : DyadicInterval precision := ⟨1654799518693000536357843956327185517074366915700, 1654799518693000536357843956327185517074366915700⟩
def wholeBUpperExp : DyadicInterval precision := ⟨151820689458754004437475082095501807276022050853, 151820689458754004437475082095501807276022181926⟩
def wholeBUpperLog : DyadicInterval precision := ⟨144441937121773249280251983095422540705801162436, 144441937121773249280251983095422540705801282203⟩
def wholeBUpperYBox : DyadicInterval precision := ⟨7318469448934496362904951799826787220927132114927, 7318469448934496362904951799826787220927137672246⟩
def wholeBUpperInput : Inputs precision :=
  ⟨wholeBUpperAlpha, wholeBUpperExp, wholeBUpperLog, endpointLogTwo⟩
def wholeBUpperExpWitness : ExpWitness precision :=
  ⟨151820689458754004437475082095501807276022050853, scale precision, 151820689458754004437475082095501807276022181926, scale precision,
    0, 512, 0, 512, ⟨-3309599037386001072715687912654371034148734463080, -3309599037386001072715687912654371034148734462008⟩, ⟨-3309599037386001072715687912654371034148733201292, -3309599037386001072715687912654371034148733200230⟩⟩

theorem wholeBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBUpperAlpha) wholeBUpperExp wholeBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBUpperExp) wholeBUpperLog fastLogWitness = true := by decide +kernel

theorem wholeBUpper_denominators : DenominatorsPositive wholeBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBUpper_yBox_eq : (yBox wholeBUpperInput).d0 = wholeBUpperYBox := by decide +kernel

theorem wholeBUpper_contains :
    wholeBUpperYBox.Contains (Y (upper E8TAxisZero0069PaddedInputs.wholeBInput.alpha)) := by
  have e : upper E8TAxisZero0069PaddedInputs.wholeBInput.alpha = ((1654799518693000536357843956327185517074366915700 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBUpperInput.alpha.Contains (upper E8TAxisZero0069PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 1654799518693000536357843956327185517074366915700
  have h := checked_yBox_d0_contains (i := wholeBUpperInput) (we := wholeBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBUpper_primitive_checks.1 wholeBUpper_primitive_checks.2 endpointLogTwo_checked
    wholeBUpper_denominators ha
  rw [wholeBUpper_yBox_eq] at h
  exact h

def wholeCLowerAlpha : DyadicInterval precision := ⟨671052481512572809340093335645151882932857337321, 671052481512572809340093335645151882932857337321⟩
def wholeCLowerExp : DyadicInterval precision := ⟨583424017396714902499808941799093864691255393307, 583424017396714902499808941799093864691255524380⟩
def wholeCLowerLog : DyadicInterval precision := ⟨490914027605645316992013980560028281716326782698, 490914027605645316992013980560028281716326877407⟩
def wholeCLowerYBox : DyadicInterval precision := ⟨3605798570852337043505653673217204512557291413936, 3605798570852337043505653673217204512557292891305⟩
def wholeCLowerInput : Inputs precision :=
  ⟨wholeCLowerAlpha, wholeCLowerExp, wholeCLowerLog, endpointLogTwo⟩
def wholeCLowerExpWitness : ExpWitness precision :=
  ⟨583424017396714902499808941799093864691255393307, scale precision, 583424017396714902499808941799093864691255524380, scale precision,
    0, 512, 0, 512, ⟨-1342104963025145618680186671290303765865714839779, -1342104963025145618680186671290303765865714838746⟩, ⟨-1342104963025145618680186671290303765865714511435, -1342104963025145618680186671290303765865714510400⟩⟩

theorem wholeCLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCLowerAlpha) wholeCLowerExp wholeCLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCLowerExp) wholeCLowerLog fastLogWitness = true := by decide +kernel

theorem wholeCLower_denominators : DenominatorsPositive wholeCLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

end GeneralCK.Certificates.E8TAxisZero0069EndpointWitnesses


