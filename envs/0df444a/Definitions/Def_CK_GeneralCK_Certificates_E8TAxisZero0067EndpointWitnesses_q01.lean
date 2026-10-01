-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0067EndpointWitnesses_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0067EndpointWitnesses_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T00:52:38.846745+00:00
-- url     : https://prove2.me/theorems/012e48d7-b7fb-4c2b-ac3a-c070ab762b87
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0067EndpointWitnesses (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0067EndpointWitnesses (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0067EndpointWitnesses (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0067EndpointWitnesses (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0067EndpointWitnesses (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0067EndpointWitnesses_q00

namespace GeneralCK.Certificates.E8TAxisZero0067EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0067Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerDLowerLog : DyadicInterval precision := ⟨475091591069212524269724099885343167071092271624, 475091591069212524269724099885343167071092367359⟩
def centerDLowerYBox : DyadicInterval precision := ⟨3737105358581285352563015982406558065104505179852, 3737105358581285352563015982406558065104506731522⟩
def centerDLowerInput : Inputs precision :=
  ⟨centerDLowerAlpha, centerDLowerExp, centerDLowerLog, endpointLogTwo⟩
def centerDLowerExpWitness : ExpWitness precision :=
  ⟨561404751706234480105216227684808902845053230830, scale precision, 561404751706234480105216227684808902845053361903, scale precision,
    0, 512, 0, 512, ⟨-1398331995255797732509389745537493506794686472415, -1398331995255797732509389745537493506794686471374⟩, ⟨-1398331995255797732509389745537493506794686131191, -1398331995255797732509389745537493506794686130152⟩⟩

theorem centerDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDLowerAlpha) centerDLowerExp centerDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDLowerExp) centerDLowerLog fastLogWitness = true := by decide +kernel

theorem centerDLower_denominators : DenominatorsPositive centerDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDLower_yBox_eq : (yBox centerDLowerInput).d0 = centerDLowerYBox := by decide +kernel

theorem centerDLower_contains :
    centerDLowerYBox.Contains (Y (lower E8TAxisZero0067PaddedInputs.centerDInput.alpha)) := by
  have e : lower E8TAxisZero0067PaddedInputs.centerDInput.alpha = ((699165997627898866254694872768746753397343150419 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDLowerInput.alpha.Contains (lower E8TAxisZero0067PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 699165997627898866254694872768746753397343150419
  have h := checked_yBox_d0_contains (i := centerDLowerInput) (we := centerDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDLower_primitive_checks.1 centerDLower_primitive_checks.2 endpointLogTwo_checked
    centerDLower_denominators ha
  rw [centerDLower_yBox_eq] at h
  exact h

def centerDUpperAlpha : DyadicInterval precision := ⟨699165997627898866254694872768746753397376704852, 699165997627898866254694872768746753397376704852⟩
def centerDUpperExp : DyadicInterval precision := ⟨561404751706234480105216227684808902845027452387, 561404751706234480105216227684808902845027583460⟩
def centerDUpperLog : DyadicInterval precision := ⟨475091591069212524269724099885343167071073647312, 475091591069212524269724099885343167071073743051⟩
def centerDUpperYBox : DyadicInterval precision := ⟨3737105358581285352563015982406558065104660786094, 3737105358581285352563015982406558065104662337770⟩
def centerDUpperInput : Inputs precision :=
  ⟨centerDUpperAlpha, centerDUpperExp, centerDUpperLog, endpointLogTwo⟩
def centerDUpperExpWitness : ExpWitness precision :=
  ⟨561404751706234480105216227684808902845027452387, scale precision, 561404751706234480105216227684808902845027583460, scale precision,
    0, 512, 0, 512, ⟨-1398331995255797732509389745537493506794753581277, -1398331995255797732509389745537493506794753580238⟩, ⟨-1398331995255797732509389745537493506794753240055, -1398331995255797732509389745537493506794753239018⟩⟩

theorem centerDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDUpperAlpha) centerDUpperExp centerDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDUpperExp) centerDUpperLog fastLogWitness = true := by decide +kernel

theorem centerDUpper_denominators : DenominatorsPositive centerDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDUpper_yBox_eq : (yBox centerDUpperInput).d0 = centerDUpperYBox := by decide +kernel

theorem centerDUpper_contains :
    centerDUpperYBox.Contains (Y (upper E8TAxisZero0067PaddedInputs.centerDInput.alpha)) := by
  have e : upper E8TAxisZero0067PaddedInputs.centerDInput.alpha = ((699165997627898866254694872768746753397376704852 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDUpperInput.alpha.Contains (upper E8TAxisZero0067PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 699165997627898866254694872768746753397376704852
  have h := checked_yBox_d0_contains (i := centerDUpperInput) (we := centerDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDUpper_primitive_checks.1 centerDUpper_primitive_checks.2 endpointLogTwo_checked
    centerDUpper_denominators ha
  rw [centerDUpper_yBox_eq] at h
  exact h

def wholeBLowerAlpha : DyadicInterval precision := ⟨1687792230159663909779056938834163267773262872616, 1687792230159663909779056938834163267773262872616⟩
def wholeBLowerExp : DyadicInterval precision := ⟨145118564043866684838885550097705946206692668510, 145118564043866684838885550097705946206692799583⟩
def wholeBLowerLog : DyadicInterval precision := ⟨138357864920265176276282420721216897854066069194, 138357864920265176276282420721216897854066189459⟩
def wholeBLowerYBox : DyadicInterval precision := ⟨7421688002070991381503087041137374709190227259661, 7421688002070991381503087041137374709190233039702⟩
def wholeBLowerInput : Inputs precision :=
  ⟨wholeBLowerAlpha, wholeBLowerExp, wholeBLowerLog, endpointLogTwo⟩
def wholeBLowerExpWitness : ExpWitness precision :=
  ⟨145118564043866684838885550097705946206692668510, scale precision, 145118564043866684838885550097705946206692799583, scale precision,
    0, 512, 0, 512, ⟨-3375584460319327819558113877668326535546526406041, -3375584460319327819558113877668326535546526404972⟩, ⟨-3375584460319327819558113877668326535546525086003, -3375584460319327819558113877668326535546525084932⟩⟩

theorem wholeBLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBLowerAlpha) wholeBLowerExp wholeBLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBLowerExp) wholeBLowerLog fastLogWitness = true := by decide +kernel

theorem wholeBLower_denominators : DenominatorsPositive wholeBLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBLower_yBox_eq : (yBox wholeBLowerInput).d0 = wholeBLowerYBox := by decide +kernel

theorem wholeBLower_contains :
    wholeBLowerYBox.Contains (Y (lower E8TAxisZero0067PaddedInputs.wholeBInput.alpha)) := by
  have e : lower E8TAxisZero0067PaddedInputs.wholeBInput.alpha = ((1687792230159663909779056938834163267773262872616 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBLowerInput.alpha.Contains (lower E8TAxisZero0067PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 1687792230159663909779056938834163267773262872616
  have h := checked_yBox_d0_contains (i := wholeBLowerInput) (we := wholeBLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBLower_primitive_checks.1 wholeBLower_primitive_checks.2 endpointLogTwo_checked
    wholeBLower_denominators ha
  rw [wholeBLower_yBox_eq] at h
  exact h

def wholeBUpperAlpha : DyadicInterval precision := ⟨1722207537783939284051018161965604178270702666319, 1722207537783939284051018161965604178270702666319⟩
def wholeBUpperExp : DyadicInterval precision := ⟨138442527176722213024059573691808630350669772026, 138442527176722213024059573691808630350669903099⟩
def wholeBUpperLog : DyadicInterval precision := ⟨132272190786316562849960840484993255045795839308, 132272190786316562849960840484993255045795960073⟩
def wholeBUpperYBox : DyadicInterval precision := ⟨7528560309300813657396731494529752905002671409031, 7528560309300813657396731494529752905002677430869⟩
def wholeBUpperInput : Inputs precision :=
  ⟨wholeBUpperAlpha, wholeBUpperExp, wholeBUpperLog, endpointLogTwo⟩
def wholeBUpperExpWitness : ExpWitness precision :=
  ⟨138442527176722213024059573691808630350669772026, scale precision, 138442527176722213024059573691808630350669903099, scale precision,
    0, 512, 0, 512, ⟨-3444415075567878568102036323931208356541406025259, -3444415075567878568102036323931208356541406024192⟩, ⟨-3444415075567878568102036323931208356541404641555, -3444415075567878568102036323931208356541404640486⟩⟩

theorem wholeBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBUpperAlpha) wholeBUpperExp wholeBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBUpperExp) wholeBUpperLog fastLogWitness = true := by decide +kernel

theorem wholeBUpper_denominators : DenominatorsPositive wholeBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBUpper_yBox_eq : (yBox wholeBUpperInput).d0 = wholeBUpperYBox := by decide +kernel

theorem wholeBUpper_contains :
    wholeBUpperYBox.Contains (Y (upper E8TAxisZero0067PaddedInputs.wholeBInput.alpha)) := by
  have e : upper E8TAxisZero0067PaddedInputs.wholeBInput.alpha = ((1722207537783939284051018161965604178270702666319 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBUpperInput.alpha.Contains (upper E8TAxisZero0067PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 1722207537783939284051018161965604178270702666319
  have h := checked_yBox_d0_contains (i := wholeBUpperInput) (we := wholeBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBUpper_primitive_checks.1 wholeBUpper_primitive_checks.2 endpointLogTwo_checked
    wholeBUpper_denominators ha
  rw [wholeBUpper_yBox_eq] at h
  exact h

def wholeCLowerAlpha : DyadicInterval precision := ⟨693511205829020257423882496604739492695804637198, 693511205829020257423882496604739492695804637198⟩
def wholeCLowerExp : DyadicInterval precision := ⟨565765939962058116901418666290376203848163200635, 565765939962058116901418666290376203848163331708⟩
def wholeCLowerLog : DyadicInterval precision := ⟨478239054014281969770673762969782322801947091784, 478239054014281969770673762969782322801947187307⟩
def wholeCLowerYBox : DyadicInterval precision := ⟨3710844001035495690751543520568687354595062425947, 3710844001035495690751543520568687354595063962511⟩
def wholeCLowerInput : Inputs precision :=
  ⟨wholeCLowerAlpha, wholeCLowerExp, wholeCLowerLog, endpointLogTwo⟩
def wholeCLowerExpWitness : ExpWitness precision :=
  ⟨565765939962058116901418666290376203848163200635, scale precision, 565765939962058116901418666290376203848163331708, scale precision,
    0, 512, 0, 512, ⟨-1387022411658040514847764993209478985391609444659, -1387022411658040514847764993209478985391609443624⟩, ⟨-1387022411658040514847764993209478985391609106063, -1387022411658040514847764993209478985391609105030⟩⟩

theorem wholeCLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCLowerAlpha) wholeCLowerExp wholeCLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCLowerExp) wholeCLowerLog fastLogWitness = true := by decide +kernel

theorem wholeCLower_denominators : DenominatorsPositive wholeCLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

end GeneralCK.Certificates.E8TAxisZero0067EndpointWitnesses


