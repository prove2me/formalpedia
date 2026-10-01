-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051EndpointWitnesses_q01_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0051EndpointWitnesses_q01_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T21:46:46.808476+00:00
-- url     : https://prove2.me/theorems/3bbcaa7a-708e-41c5-b19b-360d93c833af
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses (piece 2 of 4) (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses (piece 2 of 4) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses (piece 2 of 4) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses (piece 2 of 4) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0051EndpointWitnesses (piece 2 of 4) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051EndpointWitnesses_q01_q01

namespace GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0051Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def wholeBUpperLog : DyadicInterval precision := ⟨62348334904882759125899443768122580646764573908, 62348334904882759125899443768122580646764701563⟩
def wholeBUpperYBox : DyadicInterval precision := ⟨9209287192231352013330969052153478377606987155609, 9209287192231352013330969052153478377606999106545⟩
def wholeBUpperInput : Inputs precision :=
  ⟨wholeBUpperAlpha, wholeBUpperExp, wholeBUpperLog, endpointLogTwo⟩
def wholeBUpperExpWitness : ExpWitness precision :=
  ⟨63697354158507276092122189314858435339962336501, scale precision, 63697354158507276092122189314858435339962467574, scale precision,
    0, 1024, 0, 1024, ⟨-4578996696412641633720338775141475941530541720269, -4578996696412641633720338775141475941530541718088⟩, ⟨-4578996696412641633720338775141475941530538712873, -4578996696412641633720338775141475941530538710696⟩⟩

theorem wholeBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBUpperAlpha) wholeBUpperExp wholeBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBUpperExp) wholeBUpperLog fastLogWitness = true := by decide +kernel

theorem wholeBUpper_denominators : DenominatorsPositive wholeBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBUpper_yBox_eq : (yBox wholeBUpperInput).d0 = wholeBUpperYBox := by decide +kernel

theorem wholeBUpper_contains :
    wholeBUpperYBox.Contains (Y (upper E8TAxisZero0051PaddedInputs.wholeBInput.alpha)) := by
  have e : upper E8TAxisZero0051PaddedInputs.wholeBInput.alpha = ((2289498348206320816860169387570737970765270107519 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBUpperInput.alpha.Contains (upper E8TAxisZero0051PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 2289498348206320816860169387570737970765270107519
  have h := checked_yBox_d0_contains (i := wholeBUpperInput) (we := wholeBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBUpper_primitive_checks.1 wholeBUpper_primitive_checks.2 endpointLogTwo_checked
    wholeBUpper_denominators ha
  rw [wholeBUpper_yBox_eq] at h
  exact h

def wholeCLowerAlpha : DyadicInterval precision := ⟨883118980747789020882084464779538700246857628050, 883118980747789020882084464779538700246857628050⟩
def wholeCLowerExp : DyadicInterval precision := ⟨436466074505762269046786189274013977157045631255, 436466074505762269046786189274013977157045762328⟩
def wholeCLowerLog : DyadicInterval precision := ⟨381918529993447746751868483809797875569916533574, 381918529993447746751868483809797875569916636563⟩
def wholeCLowerYBox : DyadicInterval precision := ⟨4551207442500764868718662299380550090897230581998, 4551207442500764868718662299380550090897232670121⟩
def wholeCLowerInput : Inputs precision :=
  ⟨wholeCLowerAlpha, wholeCLowerExp, wholeCLowerLog, endpointLogTwo⟩
def wholeCLowerExpWitness : ExpWitness precision :=
  ⟨436466074505762269046786189274013977157045631255, scale precision, 436466074505762269046786189274013977157045762328, scale precision,
    0, 1024, 0, 1024, ⟨-1766237961495578041764168929559077400493715477523, -1766237961495578041764168929559077400493715475458⟩, ⟨-1766237961495578041764168929559077400493715038631, -1766237961495578041764168929559077400493715036564⟩⟩

theorem wholeCLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCLowerAlpha) wholeCLowerExp wholeCLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCLowerExp) wholeCLowerLog fastLogWitness = true := by decide +kernel

end GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses


