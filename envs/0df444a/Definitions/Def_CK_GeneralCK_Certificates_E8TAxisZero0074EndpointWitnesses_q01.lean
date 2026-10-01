-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0074EndpointWitnesses_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0074EndpointWitnesses_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T16:07:27.342701+00:00
-- url     : https://prove2.me/theorems/d32aa478-36ac-41c9-8679-386d411957df
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0074EndpointWitnesses (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0074EndpointWitnesses (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0074EndpointWitnesses (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0074EndpointWitnesses (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0074EndpointWitnesses (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0074EndpointWitnesses_q00

namespace GeneralCK.Certificates.E8TAxisZero0074EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0074Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerDLowerLog : DyadicInterval precision := ⟨519925384247664018477884675236132696792128133564, 519925384247664018477884675236132696792128226431⟩
def centerDLowerYBox : DyadicInterval precision := ⟨3369446352940230087202401516676368117972306664923, 3369446352940230087202401516676368117972308015042⟩
def centerDLowerInput : Inputs precision :=
  ⟨centerDLowerAlpha, centerDLowerExp, centerDLowerLog, endpointLogTwo⟩
def centerDLowerExpWitness : ExpWitness precision :=
  ⟨624422127721977427615890341813457420100418060714, scale precision, 624422127721977427615890341813457420100418191787, scale precision,
    0, 512, 0, 512, ⟨-1242850876558532744889859842277760123709329175945, -1242850876558532744889859842277760123709329174904⟩, ⟨-1242850876558532744889859842277760123709328869161, -1242850876558532744889859842277760123709328868118⟩⟩

theorem centerDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDLowerAlpha) centerDLowerExp centerDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDLowerExp) centerDLowerLog fastLogWitness = true := by decide +kernel

theorem centerDLower_denominators : DenominatorsPositive centerDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDLower_yBox_eq : (yBox centerDLowerInput).d0 = centerDLowerYBox := by decide +kernel

theorem centerDLower_contains :
    centerDLowerYBox.Contains (Y (lower E8TAxisZero0074PaddedInputs.centerDInput.alpha)) := by
  have e : lower E8TAxisZero0074PaddedInputs.centerDInput.alpha = ((621425438279266372444929921138880061854664510787 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDLowerInput.alpha.Contains (lower E8TAxisZero0074PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 621425438279266372444929921138880061854664510787
  have h := checked_yBox_d0_contains (i := centerDLowerInput) (we := centerDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDLower_primitive_checks.1 centerDLower_primitive_checks.2 endpointLogTwo_checked
    centerDLower_denominators ha
  rw [centerDLower_yBox_eq] at h
  exact h

def centerDUpperAlpha : DyadicInterval precision := ⟨621425438279266372444929921138880061854698065220, 621425438279266372444929921138880061854698065220⟩
def centerDUpperExp : DyadicInterval precision := ⟨624422127721977427615890341813457420100389388656, 624422127721977427615890341813457420100389519729⟩
def centerDUpperLog : DyadicInterval precision := ⟨519925384247664018477884675236132696792108044500, 519925384247664018477884675236132696792108137369⟩
def centerDUpperYBox : DyadicInterval precision := ⟨3369446352940230087202401516676368117972468442076, 3369446352940230087202401516676368117972469792210⟩
def centerDUpperInput : Inputs precision :=
  ⟨centerDUpperAlpha, centerDUpperExp, centerDUpperLog, endpointLogTwo⟩
def centerDUpperExpWitness : ExpWitness precision :=
  ⟨624422127721977427615890341813457420100389388656, scale precision, 624422127721977427615890341813457420100389519729, scale precision,
    0, 512, 0, 512, ⟨-1242850876558532744889859842277760123709396284811, -1242850876558532744889859842277760123709396283770⟩, ⟨-1242850876558532744889859842277760123709395978025, -1242850876558532744889859842277760123709395976980⟩⟩

theorem centerDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDUpperAlpha) centerDUpperExp centerDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDUpperExp) centerDUpperLog fastLogWitness = true := by decide +kernel

theorem centerDUpper_denominators : DenominatorsPositive centerDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDUpper_yBox_eq : (yBox centerDUpperInput).d0 = centerDUpperYBox := by decide +kernel

theorem centerDUpper_contains :
    centerDUpperYBox.Contains (Y (upper E8TAxisZero0074PaddedInputs.centerDInput.alpha)) := by
  have e : upper E8TAxisZero0074PaddedInputs.centerDInput.alpha = ((621425438279266372444929921138880061854698065220 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDUpperInput.alpha.Contains (upper E8TAxisZero0074PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 621425438279266372444929921138880061854698065220
  have h := checked_yBox_d0_contains (i := centerDUpperInput) (we := centerDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDUpper_primitive_checks.1 centerDUpper_primitive_checks.2 endpointLogTwo_checked
    centerDUpper_denominators ha
  rw [centerDUpper_yBox_eq] at h
  exact h

def wholeBLowerAlpha : DyadicInterval precision := ⟨1458553519812871335103393647216521494219391332362, 1458553519812871335103393647216521494219391332362⟩
def wholeBLowerExp : DyadicInterval precision := ⟨198592318493871213883856995355578140620827238669, 198592318493871213883856995355578140620827369742⟩
def wholeBLowerLog : DyadicInterval precision := ⟨186209594458958596667063557514777783248415398900, 186209594458958596667063557514777783248415515321⟩
def wholeBLowerYBox : DyadicInterval precision := ⟨6686369990788880850781858109676994814925833632361, 6686369990788880850781858109676994814925838027189⟩
def wholeBLowerInput : Inputs precision :=
  ⟨wholeBLowerAlpha, wholeBLowerExp, wholeBLowerLog, endpointLogTwo⟩
def wholeBLowerExpWitness : ExpWitness precision :=
  ⟨198592318493871213883856995355578140620827238669, scale precision, 198592318493871213883856995355578140620827369742, scale precision,
    0, 512, 0, 512, ⟨-2917107039625742670206787294433042988438783147878, -2917107039625742670206787294433042988438783146816⟩, ⟨-2917107039625742670206787294433042988438782183270, -2917107039625742670206787294433042988438782182212⟩⟩

theorem wholeBLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBLowerAlpha) wholeBLowerExp wholeBLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBLowerExp) wholeBLowerLog fastLogWitness = true := by decide +kernel

theorem wholeBLower_denominators : DenominatorsPositive wholeBLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBLower_yBox_eq : (yBox wholeBLowerInput).d0 = wholeBLowerYBox := by decide +kernel

theorem wholeBLower_contains :
    wholeBLowerYBox.Contains (Y (lower E8TAxisZero0074PaddedInputs.wholeBInput.alpha)) := by
  have e : lower E8TAxisZero0074PaddedInputs.wholeBInput.alpha = ((1458553519812871335103393647216521494219391332362 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBLowerInput.alpha.Contains (lower E8TAxisZero0074PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 1458553519812871335103393647216521494219391332362
  have h := checked_yBox_d0_contains (i := wholeBLowerInput) (we := wholeBLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBLower_primitive_checks.1 wholeBLower_primitive_checks.2 endpointLogTwo_checked
    wholeBLower_denominators ha
  rw [wholeBLower_yBox_eq] at h
  exact h

def wholeBUpperAlpha : DyadicInterval precision := ⟨1490989288915208105794532223244031738659832677471, 1490989288915208105794532223244031738659832677471⟩
def wholeBUpperExp : DyadicInterval precision := ⟨189970189966061363702036052536952023189241534835, 189970189966061363702036052536952023189241665908⟩
def wholeBUpperLog : DyadicInterval precision := ⟨178599126021686680927547529039288242261533701322, 178599126021686680927547529039288242261533818349⟩
def wholeBUpperYBox : DyadicInterval precision := ⟨6793242298018703126675502563069373010738284175257, 6793242298018703126675502563069373010738288744885⟩
def wholeBUpperInput : Inputs precision :=
  ⟨wholeBUpperAlpha, wholeBUpperExp, wholeBUpperLog, endpointLogTwo⟩
def wholeBUpperExpWitness : ExpWitness precision :=
  ⟨189970189966061363702036052536952023189241534835, scale precision, 189970189966061363702036052536952023189241665908, scale precision,
    0, 512, 0, 512, ⟨-2981978577830416211589064446488063477319665859980, -2981978577830416211589064446488063477319665858922⟩, ⟨-2981978577830416211589064446488063477319664851592, -2981978577830416211589064446488063477319664850540⟩⟩

theorem wholeBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBUpperAlpha) wholeBUpperExp wholeBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBUpperExp) wholeBUpperLog fastLogWitness = true := by decide +kernel

theorem wholeBUpper_denominators : DenominatorsPositive wholeBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBUpper_yBox_eq : (yBox wholeBUpperInput).d0 = wholeBUpperYBox := by decide +kernel

theorem wholeBUpper_contains :
    wholeBUpperYBox.Contains (Y (upper E8TAxisZero0074PaddedInputs.wholeBInput.alpha)) := by
  have e : upper E8TAxisZero0074PaddedInputs.wholeBInput.alpha = ((1490989288915208105794532223244031738659832677471 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBUpperInput.alpha.Contains (upper E8TAxisZero0074PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 1490989288915208105794532223244031738659832677471
  have h := checked_yBox_d0_contains (i := wholeBUpperInput) (we := wholeBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBUpper_primitive_checks.1 wholeBUpper_primitive_checks.2 endpointLogTwo_checked
    wholeBUpper_denominators ha
  rw [wholeBUpper_yBox_eq] at h
  exact h

def wholeCLowerAlpha : DyadicInterval precision := ⟨615985792935344704096715461380744242879772203333, 615985792935344704096715461380744242879772203333⟩
def wholeCLowerExp : DyadicInterval precision := ⟨629087614762237432177832619094338712010530416968, 629087614762237432177832619094338712010530548041⟩
def wholeCLowerLog : DyadicInterval precision := ⟨523190605620864448684409715253755540103708435928, 523190605620864448684409715253755540103708528593⟩
def wholeCLowerYBox : DyadicInterval precision := ⟨3343184995394440425390929054838497407462863917963, 3343184995394440425390929054838497407462865254448⟩
def wholeCLowerInput : Inputs precision :=
  ⟨wholeCLowerAlpha, wholeCLowerExp, wholeCLowerLog, endpointLogTwo⟩
def wholeCLowerExpWitness : ExpWitness precision :=
  ⟨629087614762237432177832619094338712010530416968, scale precision, 629087614762237432177832619094338712010530548041, scale precision,
    0, 512, 0, 512, ⟨-1231971585870689408193430922761488485759544559889, -1231971585870689408193430922761488485759544558856⟩, ⟨-1231971585870689408193430922761488485759544255377, -1231971585870689408193430922761488485759544254344⟩⟩

theorem wholeCLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCLowerAlpha) wholeCLowerExp wholeCLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCLowerExp) wholeCLowerLog fastLogWitness = true := by decide +kernel

theorem wholeCLower_denominators : DenominatorsPositive wholeCLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

end GeneralCK.Certificates.E8TAxisZero0074EndpointWitnesses


