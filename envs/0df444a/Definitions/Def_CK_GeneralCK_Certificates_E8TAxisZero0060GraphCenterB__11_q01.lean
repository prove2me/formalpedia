-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphCenterB__11_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0060GraphCenterB__11_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T07:50:24.941484+00:00
-- url     : https://prove2.me/theorems/18cfcad0-674f-4de8-954f-a044bf80a04e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062Gra…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062GraphCenterB, GeneralCK.Certificates.E8TAxisZero0063GraphCenterB, GeneralCK.Certificates.E8TAxisZero0064GraphCenterB, GeneralCK.Certificates.E8TAxisZero0065GraphCenterB, GeneralCK.Certificates.E8TAxisZero0066GraphCenterB, GeneralCK.Certificates.E8TAxisZero0067GraphCenterB, GeneralCK.Certificates.E8TAxisZero0068GraphCenterB, GeneralCK.Certificates.E8TAxisZero0069GraphCenterB, GeneralCK.Certificates.E8TAxisZero0070GraphCenterB) (piece 2 of 11)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062GraphCenterB, GeneralCK.Certificates.E8TAxisZero0063GraphCenterB, GeneralCK.Certificates.E8TAxisZero0064GraphCenterB, GeneralCK.Certificates.E8TAxisZero0065GraphCenterB, GeneralCK.Certificates.E8TAxisZero0066GraphCenterB, GeneralCK.Certificates.E8TAxisZero0067GraphCenterB, GeneralCK.Certificates.E8TAxisZero0068GraphCenterB, GeneralCK.Certificates.E8TAxisZero0069GraphCenterB, GeneralCK.Certificates.E8TAxisZero0070GraphCenterB) (piece 2 of 11)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062GraphCenterB, GeneralCK.Certificates.E8TAxisZero0063GraphCenterB, GeneralCK.Certificates.E8TAxisZero0064GraphCenterB, GeneralCK.Certificates.E8TAxisZero0065GraphCenterB, GeneralCK.Certificates.E8TAxisZero0066GraphCenterB, GeneralCK.Certificates.E8TAxisZero0067GraphCenterB, GeneralCK.Certificates.E8TAxisZero0068GraphCenterB, GeneralCK.Certificates.E8TAxisZero0069GraphCenterB, GeneralCK.Certificates.E8TAxisZero0070GraphCenterB) (piece 2 of 11) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK/Certificates/E8TAxisZero0061GraphCenterB, GeneralCK/Certificates/E8TAxisZero0062GraphCenterB, GeneralCK/Certificates/E8TAxisZero0063GraphCenterB, GeneralCK/Certificates/E8TAxisZero0064GraphCenterB, GeneralCK/Certificates/E8TAxisZero0065GraphCenterB, GeneralCK/Certificates/E8TAxisZero0066GraphCenterB, GeneralCK/Certificates/E8TAxisZero0067GraphCenterB, GeneralCK/Certificates/E8TAxisZero0068GraphCenterB, GeneralCK/Certificates/E8TAxisZero0069GraphCenterB, GeneralCK/Certificates/E8TAxisZero0070GraphCenterB) (piece 2 of 11).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphCenterB__11_q01_q01

namespace GeneralCK.Certificates.E8TAxisZero0061GraphCenterB
open DyadicInterval E8TAxisStableInterval E8TAxisZero0061PaddedInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def yDenominator : DyadicJet5Enclosure precision :=
  ⟨⟨511418899159785805026447263254719206581157770825, 511418899159785805026447263254719219105904569431⟩,
   ⟨-563137665214089360644922207923868528343602650479, -563137665214089360644922207923868488124275352466⟩,
   ⟨253880256684888870058410771085080472637496068056, 253880256684888870058410771085080612826686115016⟩,
   ⟨887380527725466366833607645770238007036824261017, 887380527725466366833607645770238564601339100407⟩,
   ⟨-2796833138586089732930688988337866937271496931462, -2796833138586089732930688988337864303976602108400⟩,
   ⟨666150698567025312079807576491478849782490626088, 666150698567025312079807576491493982552118831641⟩⟩

theorem yDenominator_checked : qData.mul ellData = yDenominator := by decide

def yDenominatorInv : DyadicJet5Enclosure precision :=
  ⟨⟨4176589952835415834947162131533037286792106151189, 4176589952835415834947162131533037389077594088392⟩,
   ⟨4598960105816330288729382350404537095861869164596, 4598960105816330288729382350404537649578715554908⟩,
   ⟨8054730848387916630903591427751664143941746803773, 8054730848387916630903591427751667581188229723680⟩,
   ⟨12511831043583299154439551280344258059050490441204, 12511831043583299154439551280344282962107920087488⟩,
   ⟨22038733992800347263996114211986791632840877530670, 22038733992800347263996114211987002800504473006559⟩,
   ⟨39778361730092239865071028535587872140878821325976, 39778361730092239865071028535589947073910325622730⟩⟩

theorem yDenominatorInv_checked : yDenominator.inv = yDenominatorInv := by decide

def yCorrection : DyadicJet5Enclosure precision :=
  ⟨⟨897125189417838922967156235425294985895369183234, 897125189417838922967156235425295030146523754276⟩,
   ⟨53513233836965732845808456532946027310390748393, 53513233836965732845808456532946261565326086915⟩,
   ⟨-332881122135216858591209420579839308024595134411, -332881122135216858591209420579837911041552688431⟩,
   ⟨954723365339985669544948341198694764624422200202, 954723365339985669544948341198704442863268342276⟩,
   ⟨-2303944908082083369776637895178522274824036797538, -2303944908082083369776637895178442804184873678434⟩,
   ⟨4178337190057240276434602372573310341987562265593, 4178337190057240276434602372574081110749258103952⟩⟩

theorem yCorrection_checked : yNumerator.mul yDenominatorInv = yCorrection := by decide

def ySum : DyadicJet5Enclosure precision :=
  ⟨⟨2809116447711101489913319243431739648969135679925, 2809116447711101489913319243431739693220323805400⟩,
   ⟨1515014871167868651049493289249229046966323291369, 1515014871167868651049493289249229281221258629891⟩,
   ⟨-332881122135216858591209420579839308024595134411, -332881122135216858591209420579837911041552688431⟩,
   ⟨954723365339985669544948341198694764624422200202, 954723365339985669544948341198704442863268342276⟩,
   ⟨-2303944908082083369776637895178522274824036797538, -2303944908082083369776637895178442804184873678434⟩,
   ⟨4178337190057240276434602372573310341987562265593, 4178337190057240276434602372574081110749258103952⟩⟩

theorem ySum_checked : alphaJet.add yCorrection = ySum := by decide

def yJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨8105396736784854402925248351942460786684805057622, 8105396736784854402925248351942460931961341717484⟩,
   ⟨4371408883013831784629881184193635171126281819064, 4371408883013831784629881184193635856532280795456⟩,
   ⟨-960491888220061415586073687329913328997171613978, -960491888220061415586073687329909296071191588828⟩,
   ⟨2754749329193638750124687811496970546801699972138, 2754749329193638750124687811496998478275882346051⟩,
   ⟨-6647779786742800612602877406784304830801528418412, -6647779786742800612602877406784075512576984619317⟩,
   ⟨12056132686515013456944814497380734728902204669001, 12056132686515013456944814497382958723613109601919⟩⟩

theorem yJetBox_checked : yConstant.mul ySum = yJetBox := by decide

def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨1759620007318940711272892992776945386425224575758, 1759620007318940711272892992776945433945595386335⟩,
   ⟨958391652629119589151571269388739539068772357092, 958391652629119589151571269388739770210672511053⟩,
   ⟨573286290839463846052781559036602594632598613792, 573286290839463846052781559036603419641158243177⟩,
   ⟨352423351216620351089850676374950923448085549882, 352423351216620351089850676374953107484471062479⟩,
   ⟨205790056253431270235438146726386170614117879556, 205790056253431270235438146726393311732418414969⟩,
   ⟨135300469660949627159821753730436722801747865799, 135300469660949627159821753730465164395277313565⟩⟩

theorem qJetBox_checked : E8TAxisReparamInterval.eval xJetBox yJetBox = qJetBox := by decide

theorem onePlusZBox_eq : onePlusZBox centerBInput = onePlusZ := by
  simp only [onePlusZBox, one_checked, zData_checked, onePlusZ_checked]

theorem rBox_eq : rBox centerBInput = rData := by
  simp only [rBox, one_checked, zData_checked, onePlusZBox_eq, negativeZ_checked, rNumerator_checked, onePlusZInv_checked, rData_checked]

theorem qBox_eq : qBox centerBInput = qData := by
  simp only [qBox, four_checked, zData_checked, onePlusZBox_eq, qNumerator_checked, qDenominator_checked, qDenominatorInv_checked, qData_checked]

theorem l1Box_eq : l1Box centerBInput = l1Data := by
  simp only [l1Box, onePlusZBox_eq, l1Data_checked]

theorem ellBox_eq : ellBox centerBInput = ellData := by
  simp only [ellBox, alphaJet_checked, l1Box_eq, ellData_checked]

theorem hBox_eq : hBox centerBInput = hData := by
  simp only [hBox, l1Box_eq, two_checked, alphaJet_checked, zData_checked, onePlusZBox_eq, twiceAlpha_checked, twiceAlphaZ_checked, onePlusZInv_checked, hCorrection_checked, hData_checked]

theorem xBox_eq : xBox centerBInput = xJetBox := by
  simp only [xBox, logtwo_checked, rBox_eq, two_checked, hBox_eq, xNumerator_checked, xDenominator_checked, xDenominatorInv_checked, xJetBox_checked]

theorem yBox_eq : yBox centerBInput = yJetBox := by
  simp only [yBox, two_checked, logtwo_checked, alphaJet_checked, rBox_eq, hBox_eq, qBox_eq, ellBox_eq, logtwoInv_checked, yConstant_checked, yNumerator_checked, yDenominator_checked, yDenominatorInv_checked, yCorrection_checked, ySum_checked, yJetBox_checked]

theorem stable_eval_eq :
    E8TAxisReparamInterval.eval (xBox centerBInput) (yBox centerBInput) = qJetBox := by
  rw [xBox_eq, yBox_eq, qJetBox_checked]

theorem denominatorsPositive : DenominatorsPositive centerBInput := by
  simp only [DenominatorsPositive, onePlusZBox_eq, qDenominator_checked,
    two_checked, hBox_eq, xDenominator_checked, qBox_eq, ellBox_eq, yDenominator_checked]
  exact ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem yPrime_pos : 0 < (yBox centerBInput).d1.lo := by
  rw [yBox_eq]
  decide

theorem qJetBox_contains {a : ℝ} (ha : centerBInput.alpha.Contains a) (hapos : 0 < a) :
    qJetBox.Contains
      (E8InverseJet5Bridge.e8QJet5 E8InverseJet5Bridge.e8ThetaCanonicalJet5)
      (E8TAxisStableScalar.Y a) := by
  rw [← stable_eval_eq]
  exact checked_stable_contains_canonical
    centerB_primitive_checks.1 centerB_primitive_checks.2
    E8TAxisZero0061StableWitnesses.logTwo_checked denominatorsPositive yPrime_pos ha hapos

#print axioms stable_eval_eq
#print axioms qJetBox_contains
end GeneralCK.Certificates.E8TAxisZero0061GraphCenterB


