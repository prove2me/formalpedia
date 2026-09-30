-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphWholeC__12
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0060GraphWholeC__12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T09:19:42.270496+00:00
-- url     : https://prove2.me/theorems/0d7d4b99-9291-48e4-bcbc-fe2b7b2e9dc2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisZero0061GraphWholeC, GeneralCK.Certificates.E8TAxisZero0062Graph…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisZero0061GraphWholeC, GeneralCK.Certificates.E8TAxisZero0062GraphWholeC, GeneralCK.Certificates.E8TAxisZero0063GraphWholeC, GeneralCK.Certificates.E8TAxisZero0064GraphWholeC, GeneralCK.Certificates.E8TAxisZero0065GraphWholeC, GeneralCK.Certificates.E8TAxisZero0066GraphWholeC, GeneralCK.Certificates.E8TAxisZero0067GraphWholeC, GeneralCK.Certificates.E8TAxisZero0068GraphWholeC, GeneralCK.Certificates.E8TAxisZero0069GraphWholeC, GeneralCK.Certificates.E8TAxisZero0070GraphWholeC, GeneralCK.Certificates.E8TAxisZero0071GraphWholeC)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisZero0061GraphWholeC, GeneralCK.Certificates.E8TAxisZero0062GraphWholeC, GeneralCK.Certificates.E8TAxisZero0063GraphWholeC, GeneralCK.Certificates.E8TAxisZero0064GraphWholeC, GeneralCK.Certificates.E8TAxisZero0065GraphWholeC, GeneralCK.Certificates.E8TAxisZero0066GraphWholeC, GeneralCK.Certificates.E8TAxisZero0067GraphWholeC, GeneralCK.Certificates.E8TAxisZero0068GraphWholeC, GeneralCK.Certificates.E8TAxisZero0069GraphWholeC, GeneralCK.Certificates.E8TAxisZero0070GraphWholeC, GeneralCK.Certificates.E8TAxisZero0071GraphWholeC)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisZero0061GraphWholeC, GeneralCK.Certificates.E8TAxisZero0062GraphWholeC, GeneralCK.Certificates.E8TAxisZero0063GraphWholeC, GeneralCK.Certificates.E8TAxisZero0064GraphWholeC, GeneralCK.Certificates.E8TAxisZero0065GraphWholeC, GeneralCK.Certificates.E8TAxisZero0066GraphWholeC, GeneralCK.Certificates.E8TAxisZero0067GraphWholeC, GeneralCK.Certificates.E8TAxisZero0068GraphWholeC, GeneralCK.Certificates.E8TAxisZero0069GraphWholeC, GeneralCK.Certificates.E8TAxisZero0070GraphWholeC, GeneralCK.Certificates.E8TAxisZero0071GraphWholeC) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK/Certificates/E8TAxisZero0061GraphWholeC, GeneralCK/Certificates/E8TAxisZero0062GraphWholeC, GeneralCK/Certificates/E8TAxisZero0063GraphWholeC, GeneralCK/Certificates/E8TAxisZero0064GraphWholeC, GeneralCK/Certificates/E8TAxisZero0065GraphWholeC, GeneralCK/Certificates/E8TAxisZero0066GraphWholeC, GeneralCK/Certificates/E8TAxisZero0067GraphWholeC, GeneralCK/Certificates/E8TAxisZero0068GraphWholeC, GeneralCK/Certificates/E8TAxisZero0069GraphWholeC, GeneralCK/Certificates/E8TAxisZero0070GraphWholeC, GeneralCK/Certificates/E8TAxisZero0071GraphWholeC).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphWholeC__12_q101

namespace GeneralCK.Certificates.E8TAxisZero0071GraphWholeC
open DyadicInterval E8TAxisStableInterval E8TAxisZero0071PaddedInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def yDenominator : DyadicJet5Enclosure precision :=
  ⟨⟨932006973678034672628444191768060887729867077806, 970479193477123492872756557689426699363218207782⟩,
   ⟨-366602474464162794407795439087602866333142086526, -220636842620439542011016086539058627185675419222⟩,
   ⟨-1181575328054880097444345947749345862425128739116, -333909268409647667736767977107253257827953403065⟩,
   ⟨-3591920811695501862299227500908230410503682175779, 3483607067951312697653780446253813805769171613510⟩,
   ⟨-34164142344695647382734969648194705335443989602294, 44161975795796546970261411236592381379398769555535⟩,
   ⟨-526117305728889190653437163986027839900638875534751, 550906714946645262048049034306900092230668309864605⟩⟩

theorem yDenominator_checked : qData.mul ellData = yDenominator := by decide

def yDenominatorInv : DyadicJet5Enclosure precision :=
  ⟨⟨2200961185234581112774600432728613165176117851735, 2291814435134038886792503539732385425669329573425⟩,
   ⟨500384892230814646743772273770073175242102458327, 901479137669061257115146421030609818744711819932⟩,
   ⟨984800118350801608514518715410074118591796777244, 3614694367397312016263779921880195359379412452487⟩,
   ⟨-7378049584430181380306013716084864738285503239661, 16526679116308388938366801682400803860920033774733⟩,
   ⟨-132437214123729726289029279279835511793573479087844, 151405658123986592314529517505505947123895242449699⟩,
   ⟨-2070936243844130326021807372342712925922590084939782, 2105558398159775991469426866575097658042527703626727⟩⟩

theorem yDenominatorInv_checked : yDenominator.inv = yDenominatorInv := by decide

def yCorrection : DyadicJet5Enclosure precision :=
  ⟨⟨545940884310088556185514707053454586047673816439, 591200825118999481264062872773114276866005874201⟩,
   ⟨823557879843032727359567052638765855650428313635, 1066864023376340684065724683602858598408557224682⟩,
   ⟨-2535986896015338390231365305371782132593138966723, -897792108409797860813190705697035293790979812400⟩,
   ⟨-6497647817856615469015081954038331674636340579018, 7272791164016954934589996464920736979657481404721⟩,
   ⟨-58941884290428560683960922403527935868721247551034, 92253211505832428243831474271778904918753296773861⟩,
   ⟨-1111368566806399881567970816650358564003708255924910, 1006928977261912403920084002262438367531453739937284⟩⟩

theorem yCorrection_checked : yNumerator.mul yDenominatorInv = yCorrection := by decide

def ySum : DyadicJet5Enclosure precision :=
  ⟨⟨1194785477037500732832942727830320860506226946431, 1251504755299160545200882160059256016839476355290⟩,
   ⟨2285059517173935645563251885355048875306360856611, 2528365660707243602269409516319141618064489767658⟩,
   ⟨-2535986896015338390231365305371782132593138966723, -897792108409797860813190705697035293790979812400⟩,
   ⟨-6497647817856615469015081954038331674636340579018, 7272791164016954934589996464920736979657481404721⟩,
   ⟨-58941884290428560683960922403527935868721247551034, 92253211505832428243831474271778904918753296773861⟩,
   ⟨-1111368566806399881567970816650358564003708255924910, 1006928977261912403920084002262438367531453739937284⟩⟩

theorem ySum_checked : alphaJet.add yCorrection = ySum := by decide

def yJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨3447422165296313539971722643914918737956015308144, 3611079408238109132645798016534259811484542573062⟩,
   ⟨6593288067125932135080935324280393866333695868000, 7295321200512575579719896718121969584269029994316⟩,
   ⟨-7317311437281448023220578785398449479358241487844, -2590480445104123985981250788876862036611787674052⟩,
   ⟨-18748248568529467424643857126427684288678907034184, 20984839491496665148436354875358897908879411742863⟩,
   ⟨-170070328332904764536246440003995441417931640841320, 266186501491090209077304364066278628958359626600933⟩,
   ⟨-3206731839862935474751264490105210167375647383357350, 2905382884046313641292351038608563933064333934204967⟩⟩

theorem yJetBox_checked : yConstant.mul ySum = yJetBox := by decide

def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨346591273537928935844912166956453167348194199434, 360445800218139317519638529024053656372348871157⟩,
   ⟨174796104020994889858207457740950452819649134692, 210024359632714658825538082554230418731108390170⟩,
   ⟨34623666727143133488284821952799253939380935733, 109728491285303946531718052199226818644410862826⟩,
   ⟨-16802867942220476204165126586014837970174875984, 164336644707882293235739696531401737502183339202⟩,
   ⟨-266064814788297186032072427298420143986354210920, 412558374412624002405705980808277089551440055633⟩,
   ⟨-1562351463056708632255874274763016274211097419187, 1713489784549798801327671088492710849843008591673⟩⟩

theorem qJetBox_checked : E8TAxisReparamInterval.eval xJetBox yJetBox = qJetBox := by decide

theorem onePlusZBox_eq : onePlusZBox wholeCInput = onePlusZ := by
  simp only [onePlusZBox, one_checked, zData_checked, onePlusZ_checked]

theorem rBox_eq : rBox wholeCInput = rData := by
  simp only [rBox, one_checked, zData_checked, onePlusZBox_eq, negativeZ_checked, rNumerator_checked, onePlusZInv_checked, rData_checked]

theorem qBox_eq : qBox wholeCInput = qData := by
  simp only [qBox, four_checked, zData_checked, onePlusZBox_eq, qNumerator_checked, qDenominator_checked, qDenominatorInv_checked, qData_checked]

theorem l1Box_eq : l1Box wholeCInput = l1Data := by
  simp only [l1Box, onePlusZBox_eq, l1Data_checked]

theorem ellBox_eq : ellBox wholeCInput = ellData := by
  simp only [ellBox, alphaJet_checked, l1Box_eq, ellData_checked]

theorem hBox_eq : hBox wholeCInput = hData := by
  simp only [hBox, l1Box_eq, two_checked, alphaJet_checked, zData_checked, onePlusZBox_eq, twiceAlpha_checked, twiceAlphaZ_checked, onePlusZInv_checked, hCorrection_checked, hData_checked]

theorem xBox_eq : xBox wholeCInput = xJetBox := by
  simp only [xBox, logtwo_checked, rBox_eq, two_checked, hBox_eq, xNumerator_checked, xDenominator_checked, xDenominatorInv_checked, xJetBox_checked]

theorem yBox_eq : yBox wholeCInput = yJetBox := by
  simp only [yBox, two_checked, logtwo_checked, alphaJet_checked, rBox_eq, hBox_eq, qBox_eq, ellBox_eq, logtwoInv_checked, yConstant_checked, yNumerator_checked, yDenominator_checked, yDenominatorInv_checked, yCorrection_checked, ySum_checked, yJetBox_checked]

theorem stable_eval_eq :
    E8TAxisReparamInterval.eval (xBox wholeCInput) (yBox wholeCInput) = qJetBox := by
  rw [xBox_eq, yBox_eq, qJetBox_checked]

theorem denominatorsPositive : DenominatorsPositive wholeCInput := by
  simp only [DenominatorsPositive, onePlusZBox_eq, qDenominator_checked,
    two_checked, hBox_eq, xDenominator_checked, qBox_eq, ellBox_eq, yDenominator_checked]
  exact ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem yPrime_pos : 0 < (yBox wholeCInput).d1.lo := by
  rw [yBox_eq]
  decide

theorem qJetBox_contains {a : ℝ} (ha : wholeCInput.alpha.Contains a) (hapos : 0 < a) :
    qJetBox.Contains
      (E8InverseJet5Bridge.e8QJet5 E8InverseJet5Bridge.e8ThetaCanonicalJet5)
      (E8TAxisStableScalar.Y a) := by
  rw [← stable_eval_eq]
  exact checked_stable_contains_canonical
    wholeC_primitive_checks.1 wholeC_primitive_checks.2
    E8TAxisZero0071StableWitnesses.logTwo_checked denominatorsPositive yPrime_pos ha hapos

#print axioms stable_eval_eq
#print axioms qJetBox_contains
end GeneralCK.Certificates.E8TAxisZero0071GraphWholeC


