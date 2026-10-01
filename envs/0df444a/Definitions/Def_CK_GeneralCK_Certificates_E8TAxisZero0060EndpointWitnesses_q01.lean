-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060EndpointWitnesses_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0060EndpointWitnesses_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T00:36:23.940955+00:00
-- url     : https://prove2.me/theorems/495c7e74-ae57-4ee1-ae87-7df12d6e3976
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0060EndpointWitnesses (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0060EndpointWitnesses (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0060EndpointWitnesses (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0060EndpointWitnesses (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0060EndpointWitnesses (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060EndpointWitnesses_q00

namespace GeneralCK.Certificates.E8TAxisZero0060EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0060Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerDLowerLog : DyadicInterval precision := ⟨431938086327136521229594192068681256434647949330, 431938086327136521229594192068681256434648047895⟩
def centerDLowerYBox : DyadicInterval precision := ⟨4104764364222340617923630448136748012236703757227, 4104764364222340617923630448136748012236705531834⟩
def centerDLowerInput : Inputs precision :=
  ⟨centerDLowerAlpha, centerDLowerExp, centerDLowerLog, endpointLogTwo⟩
def centerDLowerExpWitness : ExpWitness precision :=
  ⟨502547949796029941349747428157944023660251951291, scale precision, 502547949796029941349747428157944023660252082364, scale precision,
    0, 512, 0, 512, ⟨-1560194865486296944131654645231953829430609397603, -1560194865486296944131654645231953829430609396564⟩, ⟨-1560194865486296944131654645231953829430609016419, -1560194865486296944131654645231953829430609015376⟩⟩

theorem centerDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDLowerAlpha) centerDLowerExp centerDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDLowerExp) centerDLowerLog fastLogWitness = true := by decide +kernel

theorem centerDLower_denominators : DenominatorsPositive centerDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDLower_yBox_eq : (yBox centerDLowerInput).d0 = centerDLowerYBox := by decide +kernel

theorem centerDLower_contains :
    centerDLowerYBox.Contains (Y (lower E8TAxisZero0060PaddedInputs.centerDInput.alpha)) := by
  have e : lower E8TAxisZero0060PaddedInputs.centerDInput.alpha = ((780097432743148472065827322615976914715304603026 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDLowerInput.alpha.Contains (lower E8TAxisZero0060PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 780097432743148472065827322615976914715304603026
  have h := checked_yBox_d0_contains (i := centerDLowerInput) (we := centerDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDLower_primitive_checks.1 centerDLower_primitive_checks.2 endpointLogTwo_checked
    centerDLower_denominators ha
  rw [centerDLower_yBox_eq] at h
  exact h

def centerDUpperAlpha : DyadicInterval precision := ⟨780097432743148472065827322615976914715338157459, 780097432743148472065827322615976914715338157459⟩
def centerDUpperExp : DyadicInterval precision := ⟨502547949796029941349747428157944023660228875420, 502547949796029941349747428157944023660229006493⟩
def centerDUpperLog : DyadicInterval precision := ⟨431938086327136521229594192068681256434630777962, 431938086327136521229594192068681256434630876523⟩
def centerDUpperYBox : DyadicInterval precision := ⟨4104764364222340617923630448136748012236853046308, 4104764364222340617923630448136748012236854820898⟩
def centerDUpperInput : Inputs precision :=
  ⟨centerDUpperAlpha, centerDUpperExp, centerDUpperLog, endpointLogTwo⟩
def centerDUpperExpWitness : ExpWitness precision :=
  ⟨502547949796029941349747428157944023660228875420, scale precision, 502547949796029941349747428157944023660229006493, scale precision,
    0, 512, 0, 512, ⟨-1560194865486296944131654645231953829430676506471, -1560194865486296944131654645231953829430676505428⟩, ⟨-1560194865486296944131654645231953829430676125283, -1560194865486296944131654645231953829430676124244⟩⟩

theorem centerDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDUpperAlpha) centerDUpperExp centerDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDUpperExp) centerDUpperLog fastLogWitness = true := by decide +kernel

theorem centerDUpper_denominators : DenominatorsPositive centerDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDUpper_yBox_eq : (yBox centerDUpperInput).d0 = centerDUpperYBox := by decide +kernel

theorem centerDUpper_contains :
    centerDUpperYBox.Contains (Y (upper E8TAxisZero0060PaddedInputs.centerDInput.alpha)) := by
  have e : upper E8TAxisZero0060PaddedInputs.centerDInput.alpha = ((780097432743148472065827322615976914715338157459 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDUpperInput.alpha.Contains (upper E8TAxisZero0060PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 780097432743148472065827322615976914715338157459
  have h := checked_yBox_d0_contains (i := centerDUpperInput) (we := centerDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDUpper_primitive_checks.1 centerDUpper_primitive_checks.2 endpointLogTwo_checked
    centerDUpper_denominators ha
  rw [centerDUpper_yBox_eq] at h
  exact h

def wholeBLowerAlpha : DyadicInterval precision := ⟨1929268073660617791113193735762571654657659057420, 1929268073660617791113193735762571654657659057420⟩
def wholeBLowerExp : DyadicInterval precision := ⟨104282351385864462439714513796768579328153800446, 104282351385864462439714513796768579328153931519⟩
def wholeBLowerLog : DyadicInterval precision := ⟨100729943133272929411895507856675173561303802054, 100729943133272929411895507856675173561303925427⟩
def wholeBLowerYBox : DyadicInterval precision := ⟨8157006013353101912224315972597754603454619596299, 8157006013353101912224315972597754603454627306755⟩
def wholeBLowerInput : Inputs precision :=
  ⟨wholeBLowerAlpha, wholeBLowerExp, wholeBLowerLog, endpointLogTwo⟩
def wholeBLowerExpWitness : ExpWitness precision :=
  ⟨104282351385864462439714513796768579328153800446, scale precision, 104282351385864462439714513796768579328153931519, scale precision,
    0, 512, 0, 512, ⟨-3858536147321235582226387471525143309315319034021, -3858536147321235582226387471525143309315319032926⟩, ⟨-3858536147321235582226387471525143309315317197051, -3858536147321235582226387471525143309315317195956⟩⟩

theorem wholeBLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBLowerAlpha) wholeBLowerExp wholeBLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBLowerExp) wholeBLowerLog fastLogWitness = true := by decide +kernel

theorem wholeBLower_denominators : DenominatorsPositive wholeBLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBLower_yBox_eq : (yBox wholeBLowerInput).d0 = wholeBLowerYBox := by decide +kernel

theorem wholeBLower_contains :
    wholeBLowerYBox.Contains (Y (lower E8TAxisZero0060PaddedInputs.wholeBInput.alpha)) := by
  have e : lower E8TAxisZero0060PaddedInputs.wholeBInput.alpha = ((1929268073660617791113193735762571654657659057420 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBLowerInput.alpha.Contains (lower E8TAxisZero0060PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 1929268073660617791113193735762571654657659057420
  have h := checked_yBox_d0_contains (i := wholeBLowerInput) (we := wholeBLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBLower_primitive_checks.1 wholeBLower_primitive_checks.2 endpointLogTwo_checked
    wholeBLower_denominators ha
  rw [wholeBLower_yBox_eq] at h
  exact h

def wholeBUpperAlpha : DyadicInterval precision := ⟨1965182150578005651608976553331225664541757296242, 1965182150578005651608976553331225664541757296242⟩
def wholeBUpperExp : DyadicInterval precision := ⟨99281109903711221103981782405705203612794211796, 99281109903711221103981782405705203612794342869⟩
def wholeBUpperLog : DyadicInterval precision := ⟨96054316820902904302303053035131401219152614110, 96054316820902904302303053035131401219152737873⟩
def wholeBUpperYBox : DyadicInterval precision := ⟨8263878320582924188117960425990132799267059347380, 8263878320582924188117960425990132799267067397273⟩
def wholeBUpperInput : Inputs precision :=
  ⟨wholeBUpperAlpha, wholeBUpperExp, wholeBUpperLog, endpointLogTwo⟩
def wholeBUpperExpWitness : ExpWitness precision :=
  ⟨99281109903711221103981782405705203612794211796, scale precision, 99281109903711221103981782405705203612794342869, scale precision,
    0, 512, 0, 512, ⟨-3930364301156011303217953106662451329083515557926, -3930364301156011303217953106662451329083515556826⟩, ⟨-3930364301156011303217953106662451329083513628424, -3930364301156011303217953106662451329083513627328⟩⟩

theorem wholeBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBUpperAlpha) wholeBUpperExp wholeBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBUpperExp) wholeBUpperLog fastLogWitness = true := by decide +kernel

theorem wholeBUpper_denominators : DenominatorsPositive wholeBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBUpper_yBox_eq : (yBox wholeBUpperInput).d0 = wholeBUpperYBox := by decide +kernel

theorem wholeBUpper_contains :
    wholeBUpperYBox.Contains (Y (upper E8TAxisZero0060PaddedInputs.wholeBInput.alpha)) := by
  have e : upper E8TAxisZero0060PaddedInputs.wholeBInput.alpha = ((1965182150578005651608976553331225664541757296242 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBUpperInput.alpha.Contains (upper E8TAxisZero0060PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 1965182150578005651608976553331225664541757296242
  have h := checked_yBox_d0_contains (i := wholeBUpperInput) (we := wholeBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBUpper_primitive_checks.1 wholeBUpper_primitive_checks.2 endpointLogTwo_checked
    wholeBUpper_denominators ha
  rw [wholeBUpper_yBox_eq] at h
  exact h

def wholeCLowerAlpha : DyadicInterval precision := ⟨774203834768265108571628471566363912561682089854, 774203834768265108571628471566363912561682089854⟩
def wholeCLowerExp : DyadicInterval precision := ⟨506617451172271417683927781753795730532556302194, 506617451172271417683927781753795730532556433267⟩
def wholeCLowerLog : DyadicInterval precision := ⟨434963177842048586751554818318029032814920832046, 434963177842048586751554818318029032814920930409⟩
def wholeCLowerYBox : DyadicInterval precision := ⟨4078503006676550956112157986298877301727261001048, 4078503006676550956112157986298877301727262758946⟩
def wholeCLowerInput : Inputs precision :=
  ⟨wholeCLowerAlpha, wholeCLowerExp, wholeCLowerLog, endpointLogTwo⟩
def wholeCLowerExpWitness : ExpWitness precision :=
  ⟨506617451172271417683927781753795730532556302194, scale precision, 506617451172271417683927781753795730532556433267, scale precision,
    0, 512, 0, 512, ⟨-1548407669536530217143256943132727825123364369725, -1548407669536530217143256943132727825123364368688⟩, ⟨-1548407669536530217143256943132727825123363991601, -1548407669536530217143256943132727825123363990570⟩⟩

theorem wholeCLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCLowerAlpha) wholeCLowerExp wholeCLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCLowerExp) wholeCLowerLog fastLogWitness = true := by decide +kernel

theorem wholeCLower_denominators : DenominatorsPositive wholeCLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

end GeneralCK.Certificates.E8TAxisZero0060EndpointWitnesses


