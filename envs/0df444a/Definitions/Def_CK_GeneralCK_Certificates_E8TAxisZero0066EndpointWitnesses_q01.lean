-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0066EndpointWitnesses_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0066EndpointWitnesses_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T00:54:11.136038+00:00
-- url     : https://prove2.me/theorems/8f745c19-fd6e-46e2-993f-d89a4aba676e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0066EndpointWitnesses (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0066EndpointWitnesses (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0066EndpointWitnesses (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0066EndpointWitnesses (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0066EndpointWitnesses (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0066EndpointWitnesses_q00

namespace GeneralCK.Certificates.E8TAxisZero0066EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0066Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerDLowerLog : DyadicInterval precision := ⟨468822363559667384554973018042110608872918511132, 468822363559667384554973018042110608872918607269⟩
def centerDLowerYBox : DyadicInterval precision := ⟨3789628073672864676185960906082299486123390688642, 3789628073672864676185960906082299486123392270755⟩
def centerDLowerInput : Inputs precision :=
  ⟨centerDLowerAlpha, centerDLowerExp, centerDLowerLog, endpointLogTwo⟩
def centerDLowerExpWitness : ExpWitness precision :=
  ⟨552745918518612785766768712299414360459413272069, scale precision, 552745918518612785766768712299414360459413403142, scale precision,
    0, 512, 0, 512, ⟨-1421049126807700713001781165221076079646714650557, -1421049126807700713001781165221076079646714649516⟩, ⟨-1421049126807700713001781165221076079646714303993, -1421049126807700713001781165221076079646714302950⟩⟩

theorem centerDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDLowerAlpha) centerDLowerExp centerDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDLowerExp) centerDLowerLog fastLogWitness = true := by decide +kernel

theorem centerDLower_denominators : DenominatorsPositive centerDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDLower_yBox_eq : (yBox centerDLowerInput).d0 = centerDLowerYBox := by decide +kernel

theorem centerDLower_contains :
    centerDLowerYBox.Contains (Y (lower E8TAxisZero0066PaddedInputs.centerDInput.alpha)) := by
  have e : lower E8TAxisZero0066PaddedInputs.centerDInput.alpha = ((710524563403850356500890582610538039823357238152 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDLowerInput.alpha.Contains (lower E8TAxisZero0066PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 710524563403850356500890582610538039823357238152
  have h := checked_yBox_d0_contains (i := centerDLowerInput) (we := centerDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDLower_primitive_checks.1 centerDLower_primitive_checks.2 endpointLogTwo_checked
    centerDLower_denominators ha
  rw [centerDLower_yBox_eq] at h
  exact h

def centerDUpperAlpha : DyadicInterval precision := ⟨710524563403850356500890582610538039823390792585, 710524563403850356500890582610538039823390792585⟩
def centerDUpperExp : DyadicInterval precision := ⟨552745918518612785766768712299414360459387891221, 552745918518612785766768712299414360459388022294⟩
def centerDUpperLog : DyadicInterval precision := ⟨468822363559667384554973018042110608872900095248, 468822363559667384554973018042110608872900191383⟩
def centerDUpperYBox : DyadicInterval precision := ⟨3789628073672864676185960906082299486123545398367, 3789628073672864676185960906082299486123546980478⟩
def centerDUpperInput : Inputs precision :=
  ⟨centerDUpperAlpha, centerDUpperExp, centerDUpperLog, endpointLogTwo⟩
def centerDUpperExpWitness : ExpWitness precision :=
  ⟨552745918518612785766768712299414360459387891221, scale precision, 552745918518612785766768712299414360459388022294, scale precision,
    0, 512, 0, 512, ⟨-1421049126807700713001781165221076079646781759421, -1421049126807700713001781165221076079646781758380⟩, ⟨-1421049126807700713001781165221076079646781412857, -1421049126807700713001781165221076079646781411814⟩⟩

theorem centerDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDUpperAlpha) centerDUpperExp centerDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDUpperExp) centerDUpperLog fastLogWitness = true := by decide +kernel

theorem centerDUpper_denominators : DenominatorsPositive centerDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDUpper_yBox_eq : (yBox centerDUpperInput).d0 = centerDUpperYBox := by decide +kernel

theorem centerDUpper_contains :
    centerDUpperYBox.Contains (Y (upper E8TAxisZero0066PaddedInputs.centerDInput.alpha)) := by
  have e : upper E8TAxisZero0066PaddedInputs.centerDInput.alpha = ((710524563403850356500890582610538039823390792585 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDUpperInput.alpha.Contains (upper E8TAxisZero0066PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 710524563403850356500890582610538039823390792585
  have h := checked_yBox_d0_contains (i := centerDUpperInput) (we := centerDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDUpper_primitive_checks.1 centerDUpper_primitive_checks.2 endpointLogTwo_checked
    centerDUpper_denominators ha
  rw [centerDUpper_yBox_eq] at h
  exact h

def wholeBLowerAlpha : DyadicInterval precision := ⟨1721617121406158624966933532531531410851308363558, 1721617121406158624966933532531531410851308363558⟩
def wholeBLowerExp : DyadicInterval precision := ⟨138554428200967600586296245961158630192405637895, 138554428200967600586296245961158630192405768968⟩
def wholeBLowerLog : DyadicInterval precision := ⟨132374405485356308080071161745818595726565731158, 132374405485356308080071161745818595726565851915⟩
def wholeBLowerYBox : DyadicInterval precision := ⟨7526733432254150028748976888488857551227997670735, 7526733432254150028748976888488857551228003688341⟩
def wholeBLowerInput : Inputs precision :=
  ⟨wholeBLowerAlpha, wholeBLowerExp, wholeBLowerLog, endpointLogTwo⟩
def wholeBLowerExpWitness : ExpWitness precision :=
  ⟨138554428200967600586296245961158630192405637895, scale precision, 138554428200967600586296245961158630192405768968, scale precision,
    0, 512, 0, 512, ⟨-3443234242812317249933867065063062821702617419191, -3443234242812317249933867065063062821702617418118⟩, ⟨-3443234242812317249933867065063062821702616036609, -3443234242812317249933867065063062821702616035542⟩⟩

theorem wholeBLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBLowerAlpha) wholeBLowerExp wholeBLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBLowerExp) wholeBLowerLog fastLogWitness = true := by decide +kernel

theorem wholeBLower_denominators : DenominatorsPositive wholeBLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBLower_yBox_eq : (yBox wholeBLowerInput).d0 = wholeBLowerYBox := by decide +kernel

theorem wholeBLower_contains :
    wholeBLowerYBox.Contains (Y (lower E8TAxisZero0066PaddedInputs.wholeBInput.alpha)) := by
  have e : lower E8TAxisZero0066PaddedInputs.wholeBInput.alpha = ((1721617121406158624966933532531531410851308363558 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBLowerInput.alpha.Contains (lower E8TAxisZero0066PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 1721617121406158624966933532531531410851308363558
  have h := checked_yBox_d0_contains (i := wholeBLowerInput) (we := wholeBLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBLower_primitive_checks.1 wholeBLower_primitive_checks.2 endpointLogTwo_checked
    wholeBLower_denominators ha
  rw [wholeBLower_yBox_eq] at h
  exact h

def wholeBUpperAlpha : DyadicInterval precision := ⟨1756277128622506345972574320203850945403900533919, 1756277128622506345972574320203850945403900533919⟩
def wholeBUpperExp : DyadicInterval precision := ⟨132136113374318253076307810432189809354121208826, 132136113374318253076307810432189809354121339899⟩
def wholeBUpperLog : DyadicInterval precision := ⟨126500085155101967253583616649889666623524393970, 126500085155101967253583616649889666623524515207⟩
def wholeBUpperYBox : DyadicInterval precision := ⟨7633605739483972304642621341881235747040441078442, 7633605739483972304642621341881235747040447349645⟩
def wholeBUpperInput : Inputs precision :=
  ⟨wholeBUpperAlpha, wholeBUpperExp, wholeBUpperLog, endpointLogTwo⟩
def wholeBUpperExpWitness : ExpWitness precision :=
  ⟨132136113374318253076307810432189809354121208826, scale precision, 132136113374318253076307810432189809354121339899, scale precision,
    0, 512, 0, 512, ⟨-3512554257245012691945148640407701890807801793490, -3512554257245012691945148640407701890807801792416⟩, ⟨-3512554257245012691945148640407701890807800343738, -3512554257245012691945148640407701890807800342666⟩⟩

theorem wholeBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBUpperAlpha) wholeBUpperExp wholeBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBUpperExp) wholeBUpperLog fastLogWitness = true := by decide +kernel

theorem wholeBUpper_denominators : DenominatorsPositive wholeBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBUpper_yBox_eq : (yBox wholeBUpperInput).d0 = wholeBUpperYBox := by decide +kernel

theorem wholeBUpper_contains :
    wholeBUpperYBox.Contains (Y (upper E8TAxisZero0066PaddedInputs.wholeBInput.alpha)) := by
  have e : upper E8TAxisZero0066PaddedInputs.wholeBInput.alpha = ((1756277128622506345972574320203850945403900533919 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBUpperInput.alpha.Contains (upper E8TAxisZero0066PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 1756277128622506345972574320203850945403900533919
  have h := checked_yBox_d0_contains (i := wholeBUpperInput) (we := wholeBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBUpper_primitive_checks.1 wholeBUpper_primitive_checks.2 endpointLogTwo_checked
    wholeBUpper_denominators ha
  rw [wholeBUpper_yBox_eq] at h
  exact h

def wholeCLowerAlpha : DyadicInterval precision := ⟨704837076587479092158941059188951191105645245622, 704837076587479092158941059188951191105645245622⟩
def wholeCLowerExp : DyadicInterval precision := ⟨557064765387537285209117120927584103824756909152, 557064765387537285209117120927584103824757040225⟩
def wholeCLowerLog : DyadicInterval precision := ⟨471952686082951260798866870121334519151406127994, 471952686082951260798866870121334519151406223925⟩
def wholeCLowerYBox : DyadicInterval precision := ⟨3763366716127075014374488444244428775613947934105, 3763366716127075014374488444244428775613949500919⟩
def wholeCLowerInput : Inputs precision :=
  ⟨wholeCLowerAlpha, wholeCLowerExp, wholeCLowerLog, endpointLogTwo⟩
def wholeCLowerExpWitness : ExpWitness precision :=
  ⟨557064765387537285209117120927584103824756909152, scale precision, 557064765387537285209117120927584103824757040225, scale precision,
    0, 512, 0, 512, ⟨-1409674153174958184317882118377902382211290664153, -1409674153174958184317882118377902382211290663116⟩, ⟨-1409674153174958184317882118377902382211290320271, -1409674153174958184317882118377902382211290319236⟩⟩

theorem wholeCLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCLowerAlpha) wholeCLowerExp wholeCLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCLowerExp) wholeCLowerLog fastLogWitness = true := by decide +kernel

theorem wholeCLower_denominators : DenominatorsPositive wholeCLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

end GeneralCK.Certificates.E8TAxisZero0066EndpointWitnesses


