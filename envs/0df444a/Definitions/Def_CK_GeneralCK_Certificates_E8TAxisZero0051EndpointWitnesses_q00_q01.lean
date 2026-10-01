-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051EndpointWitnesses_q00_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0051EndpointWitnesses_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T18:54:56.105618+00:00
-- url     : https://prove2.me/theorems/7b16c253-51bd-4d61-8df8-1eb9cbfa27b3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses (piece 1 of 4) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0051EndpointWitnesses (piece 1 of 4) (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051EndpointWitnesses_q00_q00

namespace GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0051Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerBUpperExp : DyadicInterval precision := ⟨65338533038737916198760478190090577580669400577, 65338533038737916198760478190090577580669531650⟩
def centerBUpperLog : DyadicInterval precision := ⟨63920127221162978068403086142923875941005400406, 63920127221162978068403086142923875941005527927⟩
def centerBUpperYBox : DyadicInterval precision := ⟨9155851038616440875384146825457289279700817321477, 9155851038616440875384146825457289279700829003481⟩
def centerBUpperInput : Inputs precision :=
  ⟨centerBUpperAlpha, centerBUpperExp, centerBUpperLog, endpointLogTwo⟩
def centerBUpperExpWitness : ExpWitness precision :=
  ⟨65338533038737916198760478190090577580669400577, scale precision, 65338533038737916198760478190090577580669531650, scale precision,
    0, 1024, 0, 1024, ⟨-4541817660055187269132650145739880984720296542186, -4541817660055187269132650145739880984720296540000⟩, ⟨-4541817660055187269132650145739880984720293610324, -4541817660055187269132650145739880984720293608150⟩⟩

theorem centerBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBUpperAlpha) centerBUpperExp centerBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBUpperExp) centerBUpperLog fastLogWitness = true := by decide +kernel

theorem centerBUpper_denominators : DenominatorsPositive centerBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerBUpper_yBox_eq : (yBox centerBUpperInput).d0 = centerBUpperYBox := by decide +kernel

theorem centerBUpper_contains :
    centerBUpperYBox.Contains (Y (upper E8TAxisZero0051PaddedInputs.centerBInput.alpha)) := by
  have e : upper E8TAxisZero0051PaddedInputs.centerBInput.alpha = ((2270908830027593634566325072869940492360147537355 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerBUpperInput.alpha.Contains (upper E8TAxisZero0051PaddedInputs.centerBInput.alpha) := by
    rw [e]; exact point_contains precision 2270908830027593634566325072869940492360147537355
  have h := checked_yBox_d0_contains (i := centerBUpperInput) (we := centerBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerBUpper_primitive_checks.1 centerBUpper_primitive_checks.2 endpointLogTwo_checked
    centerBUpper_denominators ha
  rw [centerBUpper_yBox_eq] at h
  exact h

def centerCLowerAlpha : DyadicInterval precision := ⟨889568579085315104981341544877329197109774493106, 889568579085315104981341544877329197109774493106⟩
def centerCLowerExp : DyadicInterval precision := ⟨432630779971777265842043369804865287063813591256, 432630779971777265842043369804865287063813722329⟩
def centerCLowerLog : DyadicInterval precision := ⟨378962230865567891886960631990596730757415984902, 378962230865567891886960631990596730757416088099⟩
def centerCLowerYBox : DyadicInterval precision := ⟨4578382238569886344854012064238868478293958299184, 4578382238569886344854012064238868478293960407278⟩
def centerCLowerInput : Inputs precision :=
  ⟨centerCLowerAlpha, centerCLowerExp, centerCLowerLog, endpointLogTwo⟩
def centerCLowerExpWitness : ExpWitness precision :=
  ⟨432630779971777265842043369804865287063813591256, scale precision, 432630779971777265842043369804865287063813722329, scale precision,
    0, 1024, 0, 1024, ⟨-1779137158170630209962683089754658394219549209581, -1779137158170630209962683089754658394219549207518⟩, ⟨-1779137158170630209962683089754658394219548766791, -1779137158170630209962683089754658394219548764730⟩⟩

end GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses


