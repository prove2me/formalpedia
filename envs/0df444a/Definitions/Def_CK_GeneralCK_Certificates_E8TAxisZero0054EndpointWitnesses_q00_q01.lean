-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0054EndpointWitnesses_q00_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0054EndpointWitnesses_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T18:53:55.545637+00:00
-- url     : https://prove2.me/theorems/6dff50a6-b5d2-4b9d-a623-8285ebae5f80
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses (piece 1 of 4) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0054EndpointWitnesses (piece 1 of 4) (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0054EndpointWitnesses_q00_q00

namespace GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0054Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerBUpperExp : DyadicInterval precision := ⟨75857007209467699670786625005704562934094914305, 75857007209467699670786625005704562934095045378⟩
def centerBUpperLog : DyadicInterval precision := ⟨73953958922723310047967461309952003273923516702, 73953958922723310047967461309952003273923643363⟩
def centerBUpperYBox : DyadicInterval precision := ⟨8840714748066964933646477283402840753587508033727, 8840714748066964933646477283402840753587518261310⟩
def centerBUpperInput : Inputs precision :=
  ⟨centerBUpperAlpha, centerBUpperExp, centerBUpperLog, endpointLogTwo⟩
def centerBUpperExpWitness : ExpWitness precision :=
  ⟨75857007209467699670786625005704562934094914305, scale precision, 75857007209467699670786625005704562934095045378, scale precision,
    0, 1024, 0, 1024, ⟨-4323662044736293286784521155882163535320771146454, -4323662044736293286784521155882163535320771144302⟩, ⟨-4323662044736293286784521155882163535320768621122, -4323662044736293286784521155882163535320768618958⟩⟩

theorem centerBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBUpperAlpha) centerBUpperExp centerBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBUpperExp) centerBUpperLog fastLogWitness = true := by decide +kernel

theorem centerBUpper_denominators : DenominatorsPositive centerBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerBUpper_yBox_eq : (yBox centerBUpperInput).d0 = centerBUpperYBox := by decide +kernel

theorem centerBUpper_contains :
    centerBUpperYBox.Contains (Y (upper E8TAxisZero0054PaddedInputs.centerBInput.alpha)) := by
  have e : upper E8TAxisZero0054PaddedInputs.centerBInput.alpha = ((2161831022368146643392260577941081767660384941081 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerBUpperInput.alpha.Contains (upper E8TAxisZero0054PaddedInputs.centerBInput.alpha) := by
    rw [e]; exact point_contains precision 2161831022368146643392260577941081767660384941081
  have h := checked_yBox_d0_contains (i := centerBUpperInput) (we := centerBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerBUpper_primitive_checks.1 centerBUpper_primitive_checks.2 endpointLogTwo_checked
    centerBUpper_denominators ha
  rw [centerBUpper_yBox_eq] at h
  exact h

def centerCLowerAlpha : DyadicInterval precision := ⟨852462981405285549387058583896780795777561794292, 852462981405285549387058583896780795777561794292⟩
def centerCLowerExp : DyadicInterval precision := ⟨455165924860857228347636676448316249980419812485, 455165924860857228347636676448316249980419943558⟩
def centerCLowerLog : DyadicInterval precision := ⟨396247596272224741565612833007079880265600797868, 396247596272224741565612833007079880265600899879⟩
def centerCLowerYBox : DyadicInterval precision := ⟨4420814093295148373985177293211644215237301781572, 4420814093295148373985177293211644215237303776251⟩
def centerCLowerInput : Inputs precision :=
  ⟨centerCLowerAlpha, centerCLowerExp, centerCLowerLog, endpointLogTwo⟩
def centerCLowerExpWitness : ExpWitness precision :=
  ⟨455165924860857228347636676448316249980419812485, scale precision, 455165924860857228347636676448316249980419943558, scale precision,
    0, 1024, 0, 1024, ⟨-1704925962810571098774117167793561591555123800991, -1704925962810571098774117167793561591555123798932⟩, ⟨-1704925962810571098774117167793561591555123380125, -1704925962810571098774117167793561591555123378070⟩⟩

end GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses


