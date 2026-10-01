-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0226EndpointWitnesses_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0226EndpointWitnesses_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T20:58:14.117515+00:00
-- url     : https://prove2.me/theorems/c24de8bb-0171-4dc1-ad83-435e4581068f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0226EndpointWitnesses (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0226EndpointWitnesses (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0226EndpointWitnesses (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0226EndpointWitnesses (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0226EndpointWitnesses (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0226EndpointWitnesses_q00

namespace GeneralCK.Certificates.E8TAxisProd0226EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisProd0226Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem centerCUpper_denominators : DenominatorsPositive centerCUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerCUpper_yBox_eq : (yBox centerCUpperInput).d0 = centerCUpperYBox := by decide +kernel

theorem centerCUpper_contains :
    centerCUpperYBox.Contains (Y (upper E8TAxisProd0226PaddedInputs.centerCInput.alpha)) := by
  have e : upper E8TAxisProd0226PaddedInputs.centerCInput.alpha = ((846187174545371411746829905880880780062512262423 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerCUpperInput.alpha.Contains (upper E8TAxisProd0226PaddedInputs.centerCInput.alpha) := by
    rw [e]; exact point_contains precision 846187174545371411746829905880880780062512262423
  have h := checked_yBox_d0_contains (i := centerCUpperInput) (we := centerCUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerCUpper_primitive_checks.1 centerCUpper_primitive_checks.2 endpointLogTwo_checked
    centerCUpper_denominators ha
  rw [centerCUpper_yBox_eq] at h
  exact h

def centerDLowerAlpha : DyadicInterval precision := ⟨840037336037815392922282998599371946229808653301, 840037336037815392922282998599371946229808653301⟩
def centerDLowerExp : DyadicInterval precision := ⟨462971716911096059979186904937436745845740942111, 462971716911096059979186904937436745845740944160⟩
def centerDLowerLog : DyadicInterval precision := ⟨402187598898660414610829051743418456518805520982, 402187598898660414610829051743418456518805522801⟩
def centerDLowerYBox : DyadicInterval precision := ⟨4367377939680237236038355066515455117331204370133, 4367377939680237236038355066515455117331204402725⟩
def centerDLowerInput : Inputs precision :=
  ⟨centerDLowerAlpha, centerDLowerExp, centerDLowerLog, endpointLogTwo⟩
def centerDLowerExpWitness : ExpWitness precision :=
  ⟨462971716911096059979186904937436745845740942111, scale precision, 462971716911096059979186904937436745845740944160, scale precision,
    1, 128, 1, 128,
    ⟨-1680074672075630785844565997198743892459617310278, -1680074672075630785844565997198743892459617309740⟩, ⟨-1680074672075630785844565997198743892459617303812, -1680074672075630785844565997198743892459617303272⟩⟩

theorem centerDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDLowerAlpha) centerDLowerExp centerDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDLowerExp) centerDLowerLog fastLogWitness = true := by decide +kernel

theorem centerDLower_denominators : DenominatorsPositive centerDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDLower_yBox_eq : (yBox centerDLowerInput).d0 = centerDLowerYBox := by decide +kernel

theorem centerDLower_contains :
    centerDLowerYBox.Contains (Y (lower E8TAxisProd0226PaddedInputs.centerDInput.alpha)) := by
  have e : lower E8TAxisProd0226PaddedInputs.centerDInput.alpha = ((840037336037815392922282998599371946229808653301 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDLowerInput.alpha.Contains (lower E8TAxisProd0226PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 840037336037815392922282998599371946229808653301
  have h := checked_yBox_d0_contains (i := centerDLowerInput) (we := centerDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDLower_primitive_checks.1 centerDLower_primitive_checks.2 endpointLogTwo_checked
    centerDLower_denominators ha
  rw [centerDLower_yBox_eq] at h
  exact h

def centerDUpperAlpha : DyadicInterval precision := ⟨840037336037815392922282998599371946229808784374, 840037336037815392922282998599371946229808784374⟩
def centerDUpperExp : DyadicInterval precision := ⟨462971716911096059979186904937436745845740859069, 462971716911096059979186904937436745845740861118⟩
def centerDUpperLog : DyadicInterval precision := ⟨402187598898660414610829051743418456518805457918, 402187598898660414610829051743418456518805459735⟩
def centerDUpperYBox : DyadicInterval precision := ⟨4367377939680237236038355066515455117331204935609, 4367377939680237236038355066515455117331204968192⟩
def centerDUpperInput : Inputs precision :=
  ⟨centerDUpperAlpha, centerDUpperExp, centerDUpperLog, endpointLogTwo⟩
def centerDUpperExpWitness : ExpWitness precision :=
  ⟨462971716911096059979186904937436745845740859069, scale precision, 462971716911096059979186904937436745845740861118, scale precision,
    1, 128, 1, 128,
    ⟨-1680074672075630785844565997198743892459617572428, -1680074672075630785844565997198743892459617571886⟩, ⟨-1680074672075630785844565997198743892459617565956, -1680074672075630785844565997198743892459617565418⟩⟩

theorem centerDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDUpperAlpha) centerDUpperExp centerDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDUpperExp) centerDUpperLog fastLogWitness = true := by decide +kernel

theorem centerDUpper_denominators : DenominatorsPositive centerDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDUpper_yBox_eq : (yBox centerDUpperInput).d0 = centerDUpperYBox := by decide +kernel

theorem centerDUpper_contains :
    centerDUpperYBox.Contains (Y (upper E8TAxisProd0226PaddedInputs.centerDInput.alpha)) := by
  have e : upper E8TAxisProd0226PaddedInputs.centerDInput.alpha = ((840037336037815392922282998599371946229808784374 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDUpperInput.alpha.Contains (upper E8TAxisProd0226PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 840037336037815392922282998599371946229808784374
  have h := checked_yBox_d0_contains (i := centerDUpperInput) (we := centerDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDUpper_primitive_checks.1 centerDUpper_primitive_checks.2 endpointLogTwo_checked
    centerDUpper_denominators ha
  rw [centerDUpper_yBox_eq] at h
  exact h

def wholeALowerAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864610368, 4432047174048269527644776165804031130864610368⟩
def wholeALowerExp : DyadicInterval precision := ⟨1452664369350591901250217311774540049762303959345, 1452664369350591901250217311774540049762303961394⟩
def wholeALowerLog : DyadicInterval precision := ⟨1008610412272733567070593870872814920969193762208, 1008610412272733567070593870872814920969193763499⟩
def wholeALowerYBox : DyadicInterval precision := ⟨25576278653290801068564484572534952843978439780, 25576278653290801068564484572534952843978442841⟩
def wholeALowerInput : Inputs precision :=
  ⟨wholeALowerAlpha, wholeALowerExp, wholeALowerLog, endpointLogTwo⟩
def wholeALowerExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049762303959345, scale precision, 1452664369350591901250217311774540049762303961394, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062261729222019, -8864094348096539055289552331608062261729221758⟩, ⟨-8864094348096539055289552331608062261729219957, -8864094348096539055289552331608062261729219696⟩⟩

theorem wholeALower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeALowerAlpha) wholeALowerExp wholeALowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeALowerExp) wholeALowerLog fastLogWitness = true := by decide +kernel

theorem wholeALower_denominators : DenominatorsPositive wholeALowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeALower_yBox_eq : (yBox wholeALowerInput).d0 = wholeALowerYBox := by decide +kernel

theorem wholeALower_contains :
    wholeALowerYBox.Contains (Y (lower E8TAxisProd0226PaddedInputs.wholeAInput.alpha)) := by
  have e : lower E8TAxisProd0226PaddedInputs.wholeAInput.alpha = ((4432047174048269527644776165804031130864610368 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeALowerInput.alpha.Contains (lower E8TAxisProd0226PaddedInputs.wholeAInput.alpha) := by
    rw [e]; exact point_contains precision 4432047174048269527644776165804031130864610368
  have h := checked_yBox_d0_contains (i := wholeALowerInput) (we := wholeALowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeALower_primitive_checks.1 wholeALower_primitive_checks.2 endpointLogTwo_checked
    wholeALower_denominators ha
  rw [wholeALower_yBox_eq] at h
  exact h

def wholeAUpperAlpha : DyadicInterval precision := ⟨4748624479255801076876082777124010865681716875, 4748624479255801076876082777124010865681716875⟩
def wholeAUpperExp : DyadicInterval precision := ⟨1452035179538035812075122148102075717554934481868, 1452035179538035812075122148102075717554934483917⟩
def wholeAUpperLog : DyadicInterval precision := ⟨1008294829281404787796718047455216464285448679886, 1008294829281404787796718047455216464285448681177⟩
def wholeAUpperYBox : DyadicInterval precision := ⟨27403155699954429716319090613430306618549111840, 27403155699954429716319090613430306618549114907⟩
def wholeAUpperInput : Inputs precision :=
  ⟨wholeAUpperAlpha, wholeAUpperExp, wholeAUpperLog, endpointLogTwo⟩
def wholeAUpperExpWitness : ExpWitness precision :=
  ⟨1452035179538035812075122148102075717554934481868, scale precision, 1452035179538035812075122148102075717554934483917, scale precision,
    0, 128, 0, 128, ⟨-9497248958511602153752165554248021731363435031, -9497248958511602153752165554248021731363434768⟩, ⟨-9497248958511602153752165554248021731363432969, -9497248958511602153752165554248021731363432706⟩⟩

theorem wholeAUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAUpperAlpha) wholeAUpperExp wholeAUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAUpperExp) wholeAUpperLog fastLogWitness = true := by decide +kernel

theorem wholeAUpper_denominators : DenominatorsPositive wholeAUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeAUpper_yBox_eq : (yBox wholeAUpperInput).d0 = wholeAUpperYBox := by decide +kernel

theorem wholeAUpper_contains :
    wholeAUpperYBox.Contains (Y (upper E8TAxisProd0226PaddedInputs.wholeAInput.alpha)) := by
  have e : upper E8TAxisProd0226PaddedInputs.wholeAInput.alpha = ((4748624479255801076876082777124010865681716875 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeAUpperInput.alpha.Contains (upper E8TAxisProd0226PaddedInputs.wholeAInput.alpha) := by
    rw [e]; exact point_contains precision 4748624479255801076876082777124010865681716875
  have h := checked_yBox_d0_contains (i := wholeAUpperInput) (we := wholeAUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeAUpper_primitive_checks.1 wholeAUpper_primitive_checks.2 endpointLogTwo_checked
    wholeAUpper_denominators ha
  rw [wholeAUpper_yBox_eq] at h
  exact h

def wholeBLowerAlpha : DyadicInterval precision := ⟨2116145138714690132284995274365497689374717396508, 2116145138714690132284995274365497689374717396508⟩
def wholeBLowerExp : DyadicInterval precision := ⟨80750906188308018010415608134044536127678535243, 80750906188308018010415608134044536127678537292⟩
def wholeBLowerLog : DyadicInterval precision := ⟨78598991658678767065311509805182105228281336940, 78598991658678767065311509805182105228281339147⟩
def wholeBLowerYBox : DyadicInterval precision := ⟨8707809442922185949522329693927703766487502813796, 8707809442922185949522329693927703766487502969517⟩
def wholeBLowerInput : Inputs precision :=
  ⟨wholeBLowerAlpha, wholeBLowerExp, wholeBLowerLog, endpointLogTwo⟩
def wholeBLowerExpWitness : ExpWitness precision :=
  ⟨80750906188308018010415608134044536127678535243, scale precision, 80750906188308018010415608134044536127678537292, scale precision,
    4, 128, 4, 128,
    ⟨-4232290277429380264569990548730995378749434812679, -4232290277429380264569990548730995378749434811316⟩, ⟨-4232290277429380264569990548730995378749434775593, -4232290277429380264569990548730995378749434774232⟩⟩

theorem wholeBLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBLowerAlpha) wholeBLowerExp wholeBLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBLowerExp) wholeBLowerLog fastLogWitness = true := by decide +kernel

theorem wholeBLower_denominators : DenominatorsPositive wholeBLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBLower_yBox_eq : (yBox wholeBLowerInput).d0 = wholeBLowerYBox := by decide +kernel

theorem wholeBLower_contains :
    wholeBLowerYBox.Contains (Y (lower E8TAxisProd0226PaddedInputs.wholeBInput.alpha)) := by
  have e : lower E8TAxisProd0226PaddedInputs.wholeBInput.alpha = ((2116145138714690132284995274365497689374717396508 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBLowerInput.alpha.Contains (lower E8TAxisProd0226PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 2116145138714690132284995274365497689374717396508
  have h := checked_yBox_d0_contains (i := wholeBLowerInput) (we := wholeBLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBLower_primitive_checks.1 wholeBLower_primitive_checks.2 endpointLogTwo_checked
    wholeBLower_denominators ha
  rw [wholeBLower_yBox_eq] at h
  exact h

def wholeBUpperAlpha : DyadicInterval precision := ⟨2152866358974775393507357304141208389592583803750, 2152866358974775393507357304141208389592583803750⟩
def wholeBUpperExp : DyadicInterval precision := ⟨76793333054186912306391913079452984399677327365, 76793333054186912306391913079452984399677329414⟩
def wholeBUpperLog : DyadicInterval precision := ⟨74843813222808788073639684759488081403370532642, 74843813222808788073639684759488081403370534851⟩
def wholeBUpperYBox : DyadicInterval precision := ⟨8814681750152008225415974147320081962299843259036, 8814681750152008225415974147320081962299843421701⟩
def wholeBUpperInput : Inputs precision :=
  ⟨wholeBUpperAlpha, wholeBUpperExp, wholeBUpperLog, endpointLogTwo⟩
def wholeBUpperExpWitness : ExpWitness precision :=
  ⟨76793333054186912306391913079452984399677327365, scale precision, 76793333054186912306391913079452984399677329414, scale precision,
    4, 128, 4, 128,
    ⟨-4305732717949550787014714608282416779185167628119, -4305732717949550787014714608282416779185167626752⟩, ⟨-4305732717949550787014714608282416779185167589123, -4305732717949550787014714608282416779185167587756⟩⟩

theorem wholeBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBUpperAlpha) wholeBUpperExp wholeBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBUpperExp) wholeBUpperLog fastLogWitness = true := by decide +kernel

theorem wholeBUpper_denominators : DenominatorsPositive wholeBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

end GeneralCK.Certificates.E8TAxisProd0226EndpointWitnesses


