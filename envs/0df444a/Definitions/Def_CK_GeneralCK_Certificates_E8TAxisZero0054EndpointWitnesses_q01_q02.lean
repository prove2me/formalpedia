-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0054EndpointWitnesses_q01_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0054EndpointWitnesses_q01_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T22:01:22.488746+00:00
-- url     : https://prove2.me/theorems/8bff60d6-fb65-4251-b31c-ebc23312c144
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses (piece 2 of 4) (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses (piece 2 of 4) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses (piece 2 of 4) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses (piece 2 of 4) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0054EndpointWitnesses (piece 2 of 4) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0054EndpointWitnesses_q01_q01

namespace GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0054Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def wholeBUpperLog : DyadicInterval precision := ⟨72157370145147136290993061142388451171244299330, 72157370145147136290993061142388451171244426147⟩
def wholeBUpperYBox : DyadicInterval precision := ⟨8894150901681876071593299510099029851493677869832, 8894150901681876071593299510099029851493688328999⟩
def wholeBUpperInput : Inputs precision :=
  ⟨wholeBUpperAlpha, wholeBUpperExp, wholeBUpperLog, endpointLogTwo⟩
def wholeBUpperExpWitness : ExpWitness precision :=
  ⟨73968330329506928068097021765167103284449408604, scale precision, 73968330329506928068097021765167103284449539677, scale precision,
    0, 1024, 0, 1024, ⟨-4360510959918382065833757155519524245225861835817, -4360510959918382065833757155519524245225861833658⟩, ⟨-4360510959918382065833757155519524245225859246009, -4360510959918382065833757155519524245225859243856⟩⟩

theorem wholeBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBUpperAlpha) wholeBUpperExp wholeBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBUpperExp) wholeBUpperLog fastLogWitness = true := by decide +kernel

theorem wholeBUpper_denominators : DenominatorsPositive wholeBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBUpper_yBox_eq : (yBox wholeBUpperInput).d0 = wholeBUpperYBox := by decide +kernel

theorem wholeBUpper_contains :
    wholeBUpperYBox.Contains (Y (upper E8TAxisZero0054PaddedInputs.wholeBInput.alpha)) := by
  have e : upper E8TAxisZero0054PaddedInputs.wholeBInput.alpha = ((2180255479959191032916878577759762122612930269664 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBUpperInput.alpha.Contains (upper E8TAxisZero0054PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 2180255479959191032916878577759762122612930269664
  have h := checked_yBox_d0_contains (i := wholeBUpperInput) (we := wholeBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBUpper_primitive_checks.1 wholeBUpper_primitive_checks.2 endpointLogTwo_checked
    wholeBUpper_denominators ha
  rw [wholeBUpper_yBox_eq] at h
  exact h

def wholeCLowerAlpha : DyadicInterval precision := ⟨846134075813431409586727826645377644661755192554, 846134075813431409586727826645377644661755192554⟩
def wholeCLowerExp : DyadicInterval precision := ⟨459125158042315647897421247370792078562249295625, 459125158042315647897421247370792078562249426698⟩
def wholeCLowerLog : DyadicInterval precision := ⟨399263485746125009998379766489542016005508253788, 399263485746125009998379766489542016005508355591⟩
def wholeCLowerYBox : DyadicInterval precision := ⟨4393639297226026897849827528353325827840574061999, 4393639297226026897849827528353325827840576037651⟩
def wholeCLowerInput : Inputs precision :=
  ⟨wholeCLowerAlpha, wholeCLowerExp, wholeCLowerLog, endpointLogTwo⟩
def wholeCLowerExpWitness : ExpWitness precision :=
  ⟨459125158042315647897421247370792078562249295625, scale precision, 459125158042315647897421247370792078562249426698, scale precision,
    0, 1024, 0, 1024, ⟨-1692268151626862819173455653290755289323510595687, -1692268151626862819173455653290755289323510593626⟩, ⟨-1692268151626862819173455653290755289323510178453, -1692268151626862819173455653290755289323510176392⟩⟩

theorem wholeCLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCLowerAlpha) wholeCLowerExp wholeCLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCLowerExp) wholeCLowerLog fastLogWitness = true := by decide +kernel

end GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses


