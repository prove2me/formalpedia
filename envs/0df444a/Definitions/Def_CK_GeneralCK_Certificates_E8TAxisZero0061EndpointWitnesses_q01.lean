-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0061EndpointWitnesses_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0061EndpointWitnesses_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T00:36:56.438245+00:00
-- url     : https://prove2.me/theorems/a04806d2-36dc-4e4a-8774-2582e8872834
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0061EndpointWitnesses (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0061EndpointWitnesses (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0061EndpointWitnesses (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0061EndpointWitnesses (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0061EndpointWitnesses (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0061EndpointWitnesses_q00

namespace GeneralCK.Certificates.E8TAxisZero0061EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0061Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerDLowerLog : DyadicInterval precision := ⟨437997216266833750200638020923159196668620358736, 437997216266833750200638020923159196668620456903⟩
def centerDLowerYBox : DyadicInterval precision := ⟨4052241649130761294300685524461006591217818244867, 4052241649130761294300685524461006591217819986204⟩
def centerDLowerInput : Inputs precision :=
  ⟨centerDLowerAlpha, centerDLowerExp, centerDLowerLog, endpointLogTwo⟩
def centerDLowerExpWitness : ExpWitness precision :=
  ⟨510707457819051547382306257729904115875005418082, scale precision, 510707457819051547382306257729904115875005549155, scale precision,
    0, 512, 0, 512, ⟨-1536656097223701017555733112474691192438946435947, -1536656097223701017555733112474691192438946434914⟩, ⟨-1536656097223701017555733112474691192438946060855, -1536656097223701017555733112474691192438946059822⟩⟩

theorem centerDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDLowerAlpha) centerDLowerExp centerDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDLowerExp) centerDLowerLog fastLogWitness = true := by decide +kernel

theorem centerDLower_denominators : DenominatorsPositive centerDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDLower_yBox_eq : (yBox centerDLowerInput).d0 = centerDLowerYBox := by decide +kernel

theorem centerDLower_contains :
    centerDLowerYBox.Contains (Y (lower E8TAxisZero0061PaddedInputs.centerDInput.alpha)) := by
  have e : lower E8TAxisZero0061PaddedInputs.centerDInput.alpha = ((768328048611850508777866556237345596219473123723 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDLowerInput.alpha.Contains (lower E8TAxisZero0061PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 768328048611850508777866556237345596219473123723
  have h := checked_yBox_d0_contains (i := centerDLowerInput) (we := centerDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDLower_primitive_checks.1 centerDLower_primitive_checks.2 endpointLogTwo_checked
    centerDLower_denominators ha
  rw [centerDLower_yBox_eq] at h
  exact h

def centerDUpperAlpha : DyadicInterval precision := ⟨768328048611850508777866556237345596219506678156, 768328048611850508777866556237345596219506678156⟩
def centerDUpperExp : DyadicInterval precision := ⟨510707457819051547382306257729904115874981967545, 510707457819051547382306257729904115874982098618⟩
def centerDUpperLog : DyadicInterval precision := ⟨437997216266833750200638020923159196668602980762, 437997216266833750200638020923159196668603078929⟩
def centerDUpperYBox : DyadicInterval precision := ⟨4052241649130761294300685524461006591217968440417, 4052241649130761294300685524461006591217970181754⟩
def centerDUpperInput : Inputs precision :=
  ⟨centerDUpperAlpha, centerDUpperExp, centerDUpperLog, endpointLogTwo⟩
def centerDUpperExpWitness : ExpWitness precision :=
  ⟨510707457819051547382306257729904115874981967545, scale precision, 510707457819051547382306257729904115874982098618, scale precision,
    0, 512, 0, 512, ⟨-1536656097223701017555733112474691192439013544813, -1536656097223701017555733112474691192439013543780⟩, ⟨-1536656097223701017555733112474691192439013169719, -1536656097223701017555733112474691192439013168686⟩⟩

theorem centerDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDUpperAlpha) centerDUpperExp centerDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDUpperExp) centerDUpperLog fastLogWitness = true := by decide +kernel

theorem centerDUpper_denominators : DenominatorsPositive centerDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDUpper_yBox_eq : (yBox centerDUpperInput).d0 = centerDUpperYBox := by decide +kernel

theorem centerDUpper_contains :
    centerDUpperYBox.Contains (Y (upper E8TAxisZero0061PaddedInputs.centerDInput.alpha)) := by
  have e : upper E8TAxisZero0061PaddedInputs.centerDInput.alpha = ((768328048611850508777866556237345596219506678156 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDUpperInput.alpha.Contains (upper E8TAxisZero0061PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 768328048611850508777866556237345596219506678156
  have h := checked_yBox_d0_contains (i := centerDUpperInput) (we := centerDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDUpper_primitive_checks.1 centerDUpper_primitive_checks.2 endpointLogTwo_checked
    centerDUpper_denominators ha
  rw [centerDUpper_yBox_eq] at h
  exact h

def wholeBLowerAlpha : DyadicInterval precision := ⟨1894150053562829778049475167569232974415509042768, 1894150053562829778049475167569232974415509042768⟩
def wholeBLowerExp : DyadicInterval precision := ⟨109416268601682423356072899456224121173001533169, 109416268601682423356072899456224121173001664242⟩
def wholeBLowerLog : DyadicInterval precision := ⟨105514098828591461453288669743455508384580205538, 105514098828591461453288669743455508384580328513⟩
def wholeBLowerYBox : DyadicInterval precision := ⟨8051960583169943264978426125246271761416849338307, 8051960583169943264978426125246271761416856731238⟩
def wholeBLowerInput : Inputs precision :=
  ⟨wholeBLowerAlpha, wholeBLowerExp, wholeBLowerLog, endpointLogTwo⟩
def wholeBLowerExpWitness : ExpWitness precision :=
  ⟨109416268601682423356072899456224121173001533169, scale precision, 109416268601682423356072899456224121173001664242, scale precision,
    0, 512, 0, 512, ⟨-3788300107125659556098950335138465948831018961624, -3788300107125659556098950335138465948831018960544⟩, ⟨-3788300107125659556098950335138465948831017210854, -3788300107125659556098950335138465948831017209764⟩⟩

theorem wholeBLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBLowerAlpha) wholeBLowerExp wholeBLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBLowerExp) wholeBLowerLog fastLogWitness = true := by decide +kernel

theorem wholeBLower_denominators : DenominatorsPositive wholeBLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBLower_yBox_eq : (yBox wholeBLowerInput).d0 = wholeBLowerYBox := by decide +kernel

theorem wholeBLower_contains :
    wholeBLowerYBox.Contains (Y (lower E8TAxisZero0061PaddedInputs.wholeBInput.alpha)) := by
  have e : lower E8TAxisZero0061PaddedInputs.wholeBInput.alpha = ((1894150053562829778049475167569232974415509042768 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBLowerInput.alpha.Contains (lower E8TAxisZero0061PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 1894150053562829778049475167569232974415509042768
  have h := checked_yBox_d0_contains (i := wholeBLowerInput) (we := wholeBLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBLower_primitive_checks.1 wholeBLower_primitive_checks.2 endpointLogTwo_checked
    wholeBLower_denominators ha
  rw [wholeBLower_yBox_eq] at h
  exact h

def wholeBUpperAlpha : DyadicInterval precision := ⟨1929880448118816680501041306907956802475272209503, 1929880448118816680501041306907956802475272209503⟩
def wholeBUpperExp : DyadicInterval precision := ⟨104194998629268025762902089605650128134021352084, 104194998629268025762902089605650128134021483157⟩
def wholeBUpperLog : DyadicInterval precision := ⟨100648405859295802650490660502936120629637503052, 100648405859295802650490660502936120629637626435⟩
def wholeBUpperYBox : DyadicInterval precision := ⟨8158832890399765540872070578638649957229289610968, 8158832890399765540872070578638649957229297327121⟩
def wholeBUpperInput : Inputs precision :=
  ⟨wholeBUpperAlpha, wholeBUpperExp, wholeBUpperLog, endpointLogTwo⟩
def wholeBUpperExpWitness : ExpWitness precision :=
  ⟨104194998629268025762902089605650128134021352084, scale precision, 104194998629268025762902089605650128134021483157, scale precision,
    0, 512, 0, 512, ⟨-3859760896237633361002082613815913604950545338969, -3859760896237633361002082613815913604950545337888⟩, ⟨-3859760896237633361002082613815913604950543500463, -3859760896237633361002082613815913604950543499376⟩⟩

theorem wholeBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBUpperAlpha) wholeBUpperExp wholeBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBUpperExp) wholeBUpperLog fastLogWitness = true := by decide +kernel

theorem wholeBUpper_denominators : DenominatorsPositive wholeBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBUpper_yBox_eq : (yBox wholeBUpperInput).d0 = wholeBUpperYBox := by decide +kernel

theorem wholeBUpper_contains :
    wholeBUpperYBox.Contains (Y (upper E8TAxisZero0061PaddedInputs.wholeBInput.alpha)) := by
  have e : upper E8TAxisZero0061PaddedInputs.wholeBInput.alpha = ((1929880448118816680501041306907956802475272209503 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBUpperInput.alpha.Contains (upper E8TAxisZero0061PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 1929880448118816680501041306907956802475272209503
  have h := checked_yBox_d0_contains (i := wholeBUpperInput) (we := wholeBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBUpper_primitive_checks.1 wholeBUpper_primitive_checks.2 endpointLogTwo_checked
    wholeBUpper_denominators ha
  rw [wholeBUpper_yBox_eq] at h
  exact h

def wholeCLowerAlpha : DyadicInterval precision := ⟨762469961061176672454638714549067897721924796276, 762469961061176672454638714549067897721924796276⟩
def wholeCLowerExp : DyadicInterval precision := ⟨514818014850194000087183801285808386015802321396, 514818014850194000087183801285808386015802452469⟩
def wholeCLowerLog : DyadicInterval precision := ⟨441040166381185817721359138930122617251991386850, 441040166381185817721359138930122617251991484817⟩
def wholeCLowerYBox : DyadicInterval precision := ⟨4025980291584971632489213062623135880708375488721, 4025980291584971632489213062623135880708377213613⟩
def wholeCLowerInput : Inputs precision :=
  ⟨wholeCLowerAlpha, wholeCLowerExp, wholeCLowerLog, endpointLogTwo⟩
def wholeCLowerExpWitness : ExpWitness precision :=
  ⟨514818014850194000087183801285808386015802321396, scale precision, 514818014850194000087183801285808386015802452469, scale precision,
    0, 512, 0, 512, ⟨-1524939922122353344909277429098135795443849779565, -1524939922122353344909277429098135795443849778522⟩, ⟨-1524939922122353344909277429098135795443849407457, -1524939922122353344909277429098135795443849406420⟩⟩

theorem wholeCLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCLowerAlpha) wholeCLowerExp wholeCLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCLowerExp) wholeCLowerLog fastLogWitness = true := by decide +kernel

theorem wholeCLower_denominators : DenominatorsPositive wholeCLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

end GeneralCK.Certificates.E8TAxisZero0061EndpointWitnesses


