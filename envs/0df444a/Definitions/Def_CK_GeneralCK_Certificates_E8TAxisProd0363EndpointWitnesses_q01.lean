-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0363EndpointWitnesses_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0363EndpointWitnesses_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T20:56:31.946562+00:00
-- url     : https://prove2.me/theorems/891727ae-d80e-48f9-8ae8-551ee047e985
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0363EndpointWitnesses (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0363EndpointWitnesses (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0363EndpointWitnesses (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0363EndpointWitnesses (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0363EndpointWitnesses (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0363EndpointWitnesses_q00

namespace GeneralCK.Certificates.E8TAxisProd0363EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisProd0363Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem centerCUpper_denominators : DenominatorsPositive centerCUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerCUpper_yBox_eq : (yBox centerCUpperInput).d0 = centerCUpperYBox := by decide +kernel

theorem centerCUpper_contains :
    centerCUpperYBox.Contains (Y (upper E8TAxisProd0363PaddedInputs.centerCInput.alpha)) := by
  have e : upper E8TAxisProd0363PaddedInputs.centerCInput.alpha = ((829795398584615555605671300841179250340519885491 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerCUpperInput.alpha.Contains (upper E8TAxisProd0363PaddedInputs.centerCInput.alpha) := by
    rw [e]; exact point_contains precision 829795398584615555605671300841179250340519885491
  have h := checked_yBox_d0_contains (i := centerCUpperInput) (we := centerCUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerCUpper_primitive_checks.1 centerCUpper_primitive_checks.2 endpointLogTwo_checked
    centerCUpper_denominators ha
  rw [centerCUpper_yBox_eq] at h
  exact h

def centerDLowerAlpha : DyadicInterval precision := ⟨827900739799584217789378743685278152778005614634, 827900739799584217789378743685278152778005614634⟩
def centerDLowerExp : DyadicInterval precision := ⟨470725140515848859951996893419642375106195668008, 470725140515848859951996893419642375106195670057⟩
def centerDLowerLog : DyadicInterval precision := ⟨408063947160780491089293755661542511144690515834, 408063947160780491089293755661542511144690517651⟩
def centerDLowerYBox : DyadicInterval precision := ⟨4314855224588657912415410142839713696312319292888, 4314855224588657912415410142839713696312319324903⟩
def centerDLowerInput : Inputs precision :=
  ⟨centerDLowerAlpha, centerDLowerExp, centerDLowerLog, endpointLogTwo⟩
def centerDLowerExpWitness : ExpWitness precision :=
  ⟨470725140515848859951996893419642375106195668008, scale precision, 470725140515848859951996893419642375106195670057, scale precision,
    1, 128, 1, 128,
    ⟨-1655801479599168435578757487370556305556011232896, -1655801479599168435578757487370556305556011232354⟩, ⟨-1655801479599168435578757487370556305556011226534, -1655801479599168435578757487370556305556011225994⟩⟩

theorem centerDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDLowerAlpha) centerDLowerExp centerDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDLowerExp) centerDLowerLog fastLogWitness = true := by decide +kernel

theorem centerDLower_denominators : DenominatorsPositive centerDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDLower_yBox_eq : (yBox centerDLowerInput).d0 = centerDLowerYBox := by decide +kernel

theorem centerDLower_contains :
    centerDLowerYBox.Contains (Y (lower E8TAxisProd0363PaddedInputs.centerDInput.alpha)) := by
  have e : lower E8TAxisProd0363PaddedInputs.centerDInput.alpha = ((827900739799584217789378743685278152778005614634 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDLowerInput.alpha.Contains (lower E8TAxisProd0363PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 827900739799584217789378743685278152778005614634
  have h := checked_yBox_d0_contains (i := centerDLowerInput) (we := centerDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDLower_primitive_checks.1 centerDLower_primitive_checks.2 endpointLogTwo_checked
    centerDLower_denominators ha
  rw [centerDLower_yBox_eq] at h
  exact h

def centerDUpperAlpha : DyadicInterval precision := ⟨827900739799584217789378743685278152778005745707, 827900739799584217789378743685278152778005745707⟩
def centerDUpperExp : DyadicInterval precision := ⟨470725140515848859951996893419642375106195583575, 470725140515848859951996893419642375106195585624⟩
def centerDUpperLog : DyadicInterval precision := ⟨408063947160780491089293755661542511144690451970, 408063947160780491089293755661542511144690453787⟩
def centerDUpperYBox : DyadicInterval precision := ⟨4314855224588657912415410142839713696312319861890, 4314855224588657912415410142839713696312319893908⟩
def centerDUpperInput : Inputs precision :=
  ⟨centerDUpperAlpha, centerDUpperExp, centerDUpperLog, endpointLogTwo⟩
def centerDUpperExpWitness : ExpWitness precision :=
  ⟨470725140515848859951996893419642375106195583575, scale precision, 470725140515848859951996893419642375106195585624, scale precision,
    1, 128, 1, 128,
    ⟨-1655801479599168435578757487370556305556011495042, -1655801479599168435578757487370556305556011494500⟩, ⟨-1655801479599168435578757487370556305556011488680, -1655801479599168435578757487370556305556011488140⟩⟩

theorem centerDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDUpperAlpha) centerDUpperExp centerDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDUpperExp) centerDUpperLog fastLogWitness = true := by decide +kernel

theorem centerDUpper_denominators : DenominatorsPositive centerDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDUpper_yBox_eq : (yBox centerDUpperInput).d0 = centerDUpperYBox := by decide +kernel

theorem centerDUpper_contains :
    centerDUpperYBox.Contains (Y (upper E8TAxisProd0363PaddedInputs.centerDInput.alpha)) := by
  have e : upper E8TAxisProd0363PaddedInputs.centerDInput.alpha = ((827900739799584217789378743685278152778005745707 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDUpperInput.alpha.Contains (upper E8TAxisProd0363PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 827900739799584217789378743685278152778005745707
  have h := checked_yBox_d0_contains (i := centerDUpperInput) (we := centerDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDUpper_primitive_checks.1 centerDUpper_primitive_checks.2 endpointLogTwo_checked
    centerDUpper_denominators ha
  rw [centerDUpper_yBox_eq] at h
  exact h

def wholeALowerAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011124059, 1266295042977660303900587558721132456011124059⟩
def wholeALowerExp : DyadicInterval precision := ⟨1458971240300741788424025014233787499648221111178, 1458971240300741788424025014233787499648221113227⟩
def wholeALowerLog : DyadicInterval precision := ⟨1011769992837296815097311935000023818281148672030, 1011769992837296815097311935000023818281148673317⟩
def wholeALowerYBox : DyadicInterval precision := ⟨7307508186654514591018424163581415098279283017, 7307508186654514591018424163581415098279286015⟩
def wholeALowerInput : Inputs precision :=
  ⟨wholeALowerAlpha, wholeALowerExp, wholeALowerLog, endpointLogTwo⟩
def wholeALowerExpWitness : ExpWitness precision :=
  ⟨1458971240300741788424025014233787499648221111178, scale precision, 1458971240300741788424025014233787499648221113227, scale precision,
    0, 128, 0, 128, ⟨-2532590085955320607801175117442264912022249399, -2532590085955320607801175117442264912022249136⟩, ⟨-2532590085955320607801175117442264912022247345, -2532590085955320607801175117442264912022247082⟩⟩

theorem wholeALower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeALowerAlpha) wholeALowerExp wholeALowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeALowerExp) wholeALowerLog fastLogWitness = true := by decide +kernel

theorem wholeALower_denominators : DenominatorsPositive wholeALowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeALower_yBox_eq : (yBox wholeALowerInput).d0 = wholeALowerYBox := by decide +kernel

theorem wholeALower_contains :
    wholeALowerYBox.Contains (Y (lower E8TAxisProd0363PaddedInputs.wholeAInput.alpha)) := by
  have e : lower E8TAxisProd0363PaddedInputs.wholeAInput.alpha = ((1266295042977660303900587558721132456011124059 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeALowerInput.alpha.Contains (lower E8TAxisProd0363PaddedInputs.wholeAInput.alpha) := by
    rw [e]; exact point_contains precision 1266295042977660303900587558721132456011124059
  have h := checked_yBox_d0_contains (i := wholeALowerInput) (we := wholeALowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeALower_primitive_checks.1 wholeALower_primitive_checks.2 endpointLogTwo_checked
    wholeALower_denominators ha
  rw [wholeALower_yBox_eq] at h
  exact h

def wholeAUpperAlpha : DyadicInterval precision := ⟨1582869063071984205522252427078437298396987515, 1582869063071984205522252427078437298396987515⟩
def wholeAUpperExp : DyadicInterval precision := ⟨1458339325360928401721230227698749081243624511931, 1458339325360928401721230227698749081243624513980⟩
def wholeAUpperLog : DyadicInterval precision := ⟨1011453727394019217297123487654775991858374821364, 1011453727394019217297123487654775991858374822653⟩
def wholeAUpperYBox : DyadicInterval precision := ⟨9134385233318143238773030204476768872849955092, 9134385233318143238773030204476768872849958087⟩
def wholeAUpperInput : Inputs precision :=
  ⟨wholeAUpperAlpha, wholeAUpperExp, wholeAUpperLog, endpointLogTwo⟩
def wholeAUpperExpWitness : ExpWitness precision :=
  ⟨1458339325360928401721230227698749081243624511931, scale precision, 1458339325360928401721230227698749081243624513980, scale precision,
    0, 128, 0, 128, ⟨-3165738126143968411044504854156874596793976311, -3165738126143968411044504854156874596793976046⟩, ⟨-3165738126143968411044504854156874596793974259, -3165738126143968411044504854156874596793973994⟩⟩

theorem wholeAUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAUpperAlpha) wholeAUpperExp wholeAUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAUpperExp) wholeAUpperLog fastLogWitness = true := by decide +kernel

theorem wholeAUpper_denominators : DenominatorsPositive wholeAUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeAUpper_yBox_eq : (yBox wholeAUpperInput).d0 = wholeAUpperYBox := by decide +kernel

theorem wholeAUpper_contains :
    wholeAUpperYBox.Contains (Y (upper E8TAxisProd0363PaddedInputs.wholeAInput.alpha)) := by
  have e : upper E8TAxisProd0363PaddedInputs.wholeAInput.alpha = ((1582869063071984205522252427078437298396987515 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeAUpperInput.alpha.Contains (upper E8TAxisProd0363PaddedInputs.wholeAInput.alpha) := by
    rw [e]; exact point_contains precision 1582869063071984205522252427078437298396987515
  have h := checked_yBox_d0_contains (i := wholeAUpperInput) (we := wholeAUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeAUpper_primitive_checks.1 wholeAUpper_primitive_checks.2 endpointLogTwo_checked
    wholeAUpper_denominators ha
  rw [wholeAUpper_yBox_eq] at h
  exact h

def wholeBLowerAlpha : DyadicInterval precision := ⟨2073945358355583370179844590123450346530242663358, 2073945358355583370179844590123450346530242663358⟩
def wholeBLowerExp : DyadicInterval precision := ⟨85551429271079398229205787359921125004721686036, 85551429271079398229205787359921125004721688085⟩
def wholeBLowerLog : DyadicInterval precision := ⟨83141098447720451170806673649633559212453881158, 83141098447720451170806673649633559212453883355⟩
def wholeBLowerYBox : DyadicInterval precision := ⟨8584495242272391015798893786167267386704033508427, 8584495242272391015798893786167267386704033656473⟩
def wholeBLowerInput : Inputs precision :=
  ⟨wholeBLowerAlpha, wholeBLowerExp, wholeBLowerLog, endpointLogTwo⟩
def wholeBLowerExpWitness : ExpWitness precision :=
  ⟨85551429271079398229205787359921125004721686036, scale precision, 85551429271079398229205787359921125004721688085, scale precision,
    4, 128, 4, 128,
    ⟨-4147890716711166740359689180246900693060485345353, -4147890716711166740359689180246900693060485343984⟩, ⟨-4147890716711166740359689180246900693060485310349, -4147890716711166740359689180246900693060485308982⟩⟩

theorem wholeBLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBLowerAlpha) wholeBLowerExp wholeBLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBLowerExp) wholeBLowerLog fastLogWitness = true := by decide +kernel

theorem wholeBLower_denominators : DenominatorsPositive wholeBLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBLower_yBox_eq : (yBox wholeBLowerInput).d0 = wholeBLowerYBox := by decide +kernel

theorem wholeBLower_contains :
    wholeBLowerYBox.Contains (Y (lower E8TAxisProd0363PaddedInputs.wholeBInput.alpha)) := by
  have e : lower E8TAxisProd0363PaddedInputs.wholeBInput.alpha = ((2073945358355583370179844590123450346530242663358 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBLowerInput.alpha.Contains (lower E8TAxisProd0363PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 2073945358355583370179844590123450346530242663358
  have h := checked_yBox_d0_contains (i := wholeBLowerInput) (we := wholeBLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBLower_primitive_checks.1 wholeBLower_primitive_checks.2 endpointLogTwo_checked
    wholeBLower_denominators ha
  rw [wholeBLower_yBox_eq] at h
  exact h

def wholeBUpperAlpha : DyadicInterval precision := ⟨2110507658231659998199062601393666866215129023297, 2110507658231659998199062601393666866215129023297⟩
def wholeBUpperExp : DyadicInterval precision := ⟨81376279632619547840531729731432639207953890980, 81376279632619547840531729731432639207953893029⟩
def wholeBUpperLog : DyadicInterval precision := ⟨79191501010895897489945208840241321029532759222, 79191501010895897489945208840241321029532761427⟩
def wholeBUpperYBox : DyadicInterval precision := ⟨8691367549502213291692538239559645582516373955508, 8691367549502213291692538239559645582516374110164⟩
def wholeBUpperInput : Inputs precision :=
  ⟨wholeBUpperAlpha, wholeBUpperExp, wholeBUpperLog, endpointLogTwo⟩
def wholeBUpperExpWitness : ExpWitness precision :=
  ⟨81376279632619547840531729731432639207953890980, scale precision, 81376279632619547840531729731432639207953893029, scale precision,
    4, 128, 4, 128,
    ⟨-4221015316463319996398125202787333732430258066133, -4221015316463319996398125202787333732430258064774⟩, ⟨-4221015316463319996398125202787333732430258029335, -4221015316463319996398125202787333732430258027976⟩⟩

theorem wholeBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBUpperAlpha) wholeBUpperExp wholeBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBUpperExp) wholeBUpperLog fastLogWitness = true := by decide +kernel

theorem wholeBUpper_denominators : DenominatorsPositive wholeBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

end GeneralCK.Certificates.E8TAxisProd0363EndpointWitnesses


