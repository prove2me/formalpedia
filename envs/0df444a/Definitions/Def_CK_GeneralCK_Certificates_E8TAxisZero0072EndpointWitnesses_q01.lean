-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0072EndpointWitnesses_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0072EndpointWitnesses_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T00:37:14.600979+00:00
-- url     : https://prove2.me/theorems/f3d32101-beb0-4e7e-af67-d1f00be4e6b3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0072EndpointWitnesses (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0072EndpointWitnesses (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0072EndpointWitnesses (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0072EndpointWitnesses (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0072EndpointWitnesses (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0072EndpointWitnesses_q00

namespace GeneralCK.Certificates.E8TAxisZero0072EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0072Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerDLowerLog : DyadicInterval precision := ⟨506947743551831449885580746844042864475445122268, 506947743551831449885580746844042864475445215961⟩
def centerDLowerYBox : DyadicInterval precision := ⟨3474491783123388734448291364027850960010077658984, 3474491783123388734448291364027850960010079064692⟩
def centerDLowerInput : Inputs precision :=
  ⟨centerDLowerAlpha, centerDLowerExp, centerDLowerLog, endpointLogTwo⟩
def centerDLowerExpWitness : ExpWitness precision :=
  ⟨605981822530277187962366989116632507249107569165, scale precision, 605981822530277187962366989116632507249107700238, scale precision,
    0, 512, 0, 512, ⟨-1286661780023143706382894975532410036634225538721, -1286661780023143706382894975532410036634225537680⟩, ⟨-1286661780023143706382894975532410036634225222597, -1286661780023143706382894975532410036634225221560⟩⟩

theorem centerDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDLowerAlpha) centerDLowerExp centerDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDLowerExp) centerDLowerLog fastLogWitness = true := by decide +kernel

theorem centerDLower_denominators : DenominatorsPositive centerDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDLower_yBox_eq : (yBox centerDLowerInput).d0 = centerDLowerYBox := by decide +kernel

theorem centerDLower_contains :
    centerDLowerYBox.Contains (Y (lower E8TAxisZero0072PaddedInputs.centerDInput.alpha)) := by
  have e : lower E8TAxisZero0072PaddedInputs.centerDInput.alpha = ((643330890011571853191447487766205018317112689841 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDLowerInput.alpha.Contains (lower E8TAxisZero0072PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 643330890011571853191447487766205018317112689841
  have h := checked_yBox_d0_contains (i := centerDLowerInput) (we := centerDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDLower_primitive_checks.1 centerDLower_primitive_checks.2 endpointLogTwo_checked
    centerDLower_denominators ha
  rw [centerDLower_yBox_eq] at h
  exact h

def centerDUpperAlpha : DyadicInterval precision := ⟨643330890011571853191447487766205018317146244274, 643330890011571853191447487766205018317146244274⟩
def centerDUpperExp : DyadicInterval precision := ⟨605981822530277187962366989116632507249079743843, 605981822530277187962366989116632507249079874916⟩
def centerDUpperLog : DyadicInterval precision := ⟨506947743551831449885580746844042864475425452576, 506947743551831449885580746844042864475425546273⟩
def centerDUpperYBox : DyadicInterval precision := ⟨3474491783123388734448291364027850960010237695420, 3474491783123388734448291364027850960010239101139⟩
def centerDUpperInput : Inputs precision :=
  ⟨centerDUpperAlpha, centerDUpperExp, centerDUpperLog, endpointLogTwo⟩
def centerDUpperExpWitness : ExpWitness precision :=
  ⟨605981822530277187962366989116632507249079743843, scale precision, 605981822530277187962366989116632507249079874916, scale precision,
    0, 512, 0, 512, ⟨-1286661780023143706382894975532410036634292647587, -1286661780023143706382894975532410036634292646548⟩, ⟨-1286661780023143706382894975532410036634292331469, -1286661780023143706382894975532410036634292330428⟩⟩

theorem centerDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDUpperAlpha) centerDUpperExp centerDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDUpperExp) centerDUpperLog fastLogWitness = true := by decide +kernel

theorem centerDUpper_denominators : DenominatorsPositive centerDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDUpper_yBox_eq : (yBox centerDUpperInput).d0 = centerDUpperYBox := by decide +kernel

theorem centerDUpper_contains :
    centerDUpperYBox.Contains (Y (upper E8TAxisZero0072PaddedInputs.centerDInput.alpha)) := by
  have e : upper E8TAxisZero0072PaddedInputs.centerDInput.alpha = ((643330890011571853191447487766205018317146244274 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDUpperInput.alpha.Contains (upper E8TAxisZero0072PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 643330890011571853191447487766205018317146244274
  have h := checked_yBox_d0_contains (i := centerDUpperInput) (we := centerDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDUpper_primitive_checks.1 centerDUpper_primitive_checks.2 endpointLogTwo_checked
    centerDUpper_denominators ha
  rw [centerDUpper_yBox_eq] at h
  exact h

def wholeBLowerAlpha : DyadicInterval precision := ⟨1522614624326126476353155181323798227424098146540, 1522614624326126476353155181323798227424098146540⟩
def wholeBLowerExp : DyadicInterval precision := ⟨181924051358533222199362926776269957540271310008, 181924051358533222199362926776269957540271441081⟩
def wholeBLowerLog : DyadicInterval precision := ⟨171461138835500366828241253176154037551607278292, 171461138835500366828241253176154037551607395887⟩
def wholeBLowerYBox : DyadicInterval precision := ⟨6896460851155198145273637804379960499001374803633, 6896460851155198145273637804379960499001379549858⟩
def wholeBLowerInput : Inputs precision :=
  ⟨wholeBLowerAlpha, wholeBLowerExp, wholeBLowerLog, endpointLogTwo⟩
def wholeBLowerExpWitness : ExpWitness precision :=
  ⟨181924051358533222199362926776269957540271310008, scale precision, 181924051358533222199362926776269957540271441081, scale precision,
    0, 512, 0, 512, ⟨-3045229248652252952706310362647596454848196820391, -3045229248652252952706310362647596454848196819332⟩, ⟨-3045229248652252952706310362647596454848195767407, -3045229248652252952706310362647596454848195766338⟩⟩

theorem wholeBLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBLowerAlpha) wholeBLowerExp wholeBLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBLowerExp) wholeBLowerLog fastLogWitness = true := by decide +kernel

theorem wholeBLower_denominators : DenominatorsPositive wholeBLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBLower_yBox_eq : (yBox wholeBLowerInput).d0 = wholeBLowerYBox := by decide +kernel

theorem wholeBLower_contains :
    wholeBLowerYBox.Contains (Y (lower E8TAxisZero0072PaddedInputs.wholeBInput.alpha)) := by
  have e : lower E8TAxisZero0072PaddedInputs.wholeBInput.alpha = ((1522614624326126476353155181323798227424098146540 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBLowerInput.alpha.Contains (lower E8TAxisZero0072PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 1522614624326126476353155181323798227424098146540
  have h := checked_yBox_d0_contains (i := wholeBLowerInput) (we := wholeBLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBLower_primitive_checks.1 wholeBLower_primitive_checks.2 endpointLogTwo_checked
    wholeBLower_denominators ha
  rw [wholeBLower_yBox_eq] at h
  exact h

def wholeBUpperAlpha : DyadicInterval precision := ⟨1555660400236567938276652742619986074567345824735, 1555660400236567938276652742619986074567345824735⟩
def wholeBUpperExp : DyadicInterval precision := ⟨173880385804471352621301659180749186077452408004, 173880385804471352621301659180749186077452539077⟩
def wholeBUpperLog : DyadicInterval precision := ⟨164290328593358241285855179044268992517120356858, 164290328593358241285855179044268992517120475025⟩
def wholeBUpperYBox : DyadicInterval precision := ⟨7003333158385020421167282257772338694813823297226, 7003333158385020421167282257772338694813828234814⟩
def wholeBUpperInput : Inputs precision :=
  ⟨wholeBUpperAlpha, wholeBUpperExp, wholeBUpperLog, endpointLogTwo⟩
def wholeBUpperExpWitness : ExpWitness precision :=
  ⟨173880385804471352621301659180749186077452408004, scale precision, 173880385804471352621301659180749186077452539077, scale precision,
    0, 512, 0, 512, ⟨-3111320800473135876553305485239972149134692201139, -3111320800473135876553305485239972149134692200088⟩, ⟨-3111320800473135876553305485239972149134691099447, -3111320800473135876553305485239972149134691098394⟩⟩

theorem wholeBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBUpperAlpha) wholeBUpperExp wholeBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBUpperExp) wholeBUpperLog fastLogWitness = true := by decide +kernel

theorem wholeBUpper_denominators : DenominatorsPositive wholeBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBUpper_yBox_eq : (yBox wholeBUpperInput).d0 = wholeBUpperYBox := by decide +kernel

theorem wholeBUpper_contains :
    wholeBUpperYBox.Contains (Y (upper E8TAxisZero0072PaddedInputs.wholeBInput.alpha)) := by
  have e : upper E8TAxisZero0072PaddedInputs.wholeBInput.alpha = ((1555660400236567938276652742619986074567345824735 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBUpperInput.alpha.Contains (upper E8TAxisZero0072PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 1555660400236567938276652742619986074567345824735
  have h := checked_yBox_d0_contains (i := wholeBUpperInput) (we := wholeBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBUpper_primitive_checks.1 wholeBUpper_primitive_checks.2 endpointLogTwo_checked
    wholeBUpper_denominators ha
  rw [wholeBUpper_yBox_eq] at h
  exact h

def wholeCLowerAlpha : DyadicInterval precision := ⟨637832247480472324939326434952621888088044164628, 637832247480472324939326434952621888088044164628⟩
def wholeCLowerExp : DyadicInterval precision := ⟨610558820864912509175272747825498145069509045415, 610558820864912509175272747825498145069509176488⟩
def wholeCLowerLog : DyadicInterval precision := ⟨510179642243321146984571771117295506705446295854, 510179642243321146984571771117295506705446389343⟩
def wholeCLowerYBox : DyadicInterval precision := ⟨3448230425577599072636818902189980249500634909578, 3448230425577599072636818902189980249500636301247⟩
def wholeCLowerInput : Inputs precision :=
  ⟨wholeCLowerAlpha, wholeCLowerExp, wholeCLowerLog, endpointLogTwo⟩
def wholeCLowerExpWitness : ExpWitness precision :=
  ⟨610558820864912509175272747825498145069509045415, scale precision, 610558820864912509175272747825498145069509176488, scale precision,
    0, 512, 0, 512, ⟨-1275664494960944649878652869905243776176088487107, -1275664494960944649878652869905243776176088486068⟩, ⟨-1275664494960944649878652869905243776176088173359, -1275664494960944649878652869905243776176088172318⟩⟩

theorem wholeCLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCLowerAlpha) wholeCLowerExp wholeCLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCLowerExp) wholeCLowerLog fastLogWitness = true := by decide +kernel

theorem wholeCLower_denominators : DenominatorsPositive wholeCLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

end GeneralCK.Certificates.E8TAxisZero0072EndpointWitnesses


