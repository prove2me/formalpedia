-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphWholeC__12_q05
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0060GraphWholeC__12_q05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T08:14:21.506732+00:00
-- url     : https://prove2.me/theorems/5a521065-9403-41be-bdd7-e9dc480e9820
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisZero0061GraphWholeC, GeneralCK.Certificates.E8TAxisZero0062Graph…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisZero0061GraphWholeC, GeneralCK.Certificates.E8TAxisZero0062GraphWholeC, GeneralCK.Certificates.E8TAxisZero0063GraphWholeC, GeneralCK.Certificates.E8TAxisZero0064GraphWholeC, GeneralCK.Certificates.E8TAxisZero0065GraphWholeC, GeneralCK.Certificates.E8TAxisZero0066GraphWholeC, GeneralCK.Certificates.E8TAxisZero0067GraphWholeC, GeneralCK.Certificates.E8TAxisZero0068GraphWholeC, GeneralCK.Certificates.E8TAxisZero0069GraphWholeC, GeneralCK.Certificates.E8TAxisZero0070GraphWholeC, GeneralCK.Certificates.E8TAxisZero0071GraphWholeC) (piece 6 of 12)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisZero0061GraphWholeC, GeneralCK.Certificates.E8TAxisZero0062GraphWholeC, GeneralCK.Certificates.E8TAxisZero0063GraphWholeC, GeneralCK.Certificates.E8TAxisZero0064GraphWholeC, GeneralCK.Certificates.E8TAxisZero0065GraphWholeC, GeneralCK.Certificates.E8TAxisZero0066GraphWholeC, GeneralCK.Certificates.E8TAxisZero0067GraphWholeC, GeneralCK.Certificates.E8TAxisZero0068GraphWholeC, GeneralCK.Certificates.E8TAxisZero0069GraphWholeC, GeneralCK.Certificates.E8TAxisZero0070GraphWholeC, GeneralCK.Certificates.E8TAxisZero0071GraphWholeC) (piece 6 of 12)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisZero0061GraphWholeC, GeneralCK.Certificates.E8TAxisZero0062GraphWholeC, GeneralCK.Certificates.E8TAxisZero0063GraphWholeC, GeneralCK.Certificates.E8TAxisZero0064GraphWholeC, GeneralCK.Certificates.E8TAxisZero0065GraphWholeC, GeneralCK.Certificates.E8TAxisZero0066GraphWholeC, GeneralCK.Certificates.E8TAxisZero0067GraphWholeC, GeneralCK.Certificates.E8TAxisZero0068GraphWholeC, GeneralCK.Certificates.E8TAxisZero0069GraphWholeC, GeneralCK.Certificates.E8TAxisZero0070GraphWholeC, GeneralCK.Certificates.E8TAxisZero0071GraphWholeC) (piece 6 of 12) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK/Certificates/E8TAxisZero0061GraphWholeC, GeneralCK/Certificates/E8TAxisZero0062GraphWholeC, GeneralCK/Certificates/E8TAxisZero0063GraphWholeC, GeneralCK/Certificates/E8TAxisZero0064GraphWholeC, GeneralCK/Certificates/E8TAxisZero0065GraphWholeC, GeneralCK/Certificates/E8TAxisZero0066GraphWholeC, GeneralCK/Certificates/E8TAxisZero0067GraphWholeC, GeneralCK/Certificates/E8TAxisZero0068GraphWholeC, GeneralCK/Certificates/E8TAxisZero0069GraphWholeC, GeneralCK/Certificates/E8TAxisZero0070GraphWholeC, GeneralCK/Certificates/E8TAxisZero0071GraphWholeC) (piece 6 of 12).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphWholeC__12_q05_q01

namespace GeneralCK.Certificates.E8TAxisZero0065GraphWholeC
open DyadicInterval E8TAxisStableInterval E8TAxisZero0065PaddedInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def yDenominator : DyadicJet5Enclosure precision :=
  ⟨⟨917906360458307317298785591124003391405155805337, 955816720024617117358635323279005559612381630620⟩,
   ⟨-399274602008954128949716051597217590729174706365, -257625992549675781499075536643930810302657638372⟩,
   ⟨-1148962210752064676267616812352644892047183312975, -360355430157141088279305975527650304540972927302⟩,
   ⟨-2970771584679530037932822952277764458339644155957, 3335154780648526481747441231335256204559495801477⟩,
   ⟨-27877568573760355437808301478330655997165304367724, 38642736592762449864760249250396038432062456698437⟩,
   ⟨-431444479127129414357153304861329329637354081986589, 442894629381291609318304457063872579496299381772073⟩⟩

theorem yDenominator_checked : qData.mul ellData = yDenominator := by decide

def yDenominatorInv : DyadicJet5Enclosure precision :=
  ⟨⟨2234724493902866239109520829490905476354803774976, 2327020628612290583537071408380522982438944419776⟩,
   ⟨602336309624265639014659331456076966813556901916, 1012216796157608291825748473217497515216647805147⟩,
   ⟨1167221771853555432618027807681465689502632291194, 3793375700156081494544121008437243589298039581338⟩,
   ⟨-6829995302994077999053061268023433697317108292242, 16282531276342514662649018811329550704511697547084⟩,
   ⟨-122994913993066503264014178292396147445548033487493, 140597580594959202654869518799125707501412082080699⟩,
   ⟨-1844539942447268441315915756088287764082209406049767, 1879852746414079401121553577006065907761768931881250⟩⟩

theorem yDenominatorInv_checked : yDenominator.inv = yDenominatorInv := by decide

def yCorrection : DyadicJet5Enclosure precision :=
  ⟨⟨586136516507040584960929239998573065705571036395, 634329995181353156801184906175323246664073419717⟩,
   ⟨739655370009030543194134038431063627079815784853, 989660270201935745499802014269725041027448623118⟩,
   ⟨-2517398564341782166979590210209544686667674668396, -874430152248876630604321773427827783889523324253⟩,
   ⟨-5676634743193224098112856982317412437263302478122, 7770751552074583450102099288286258171792527001928⟩,
   ⟨-56943256567161817944007981853627141510226242598469, 85465027139047587147270610279538783029682386966082⟩,
   ⟨-1010863798871469601186014549378823934052783653672287, 907145148589875944894057412556080696468107209574368⟩⟩

theorem yCorrection_checked : yNumerator.mul yDenominatorInv = yCorrection := by decide

def ySum : DyadicJet5Enclosure precision :=
  ⟨⟨1302365094815140312319012179137508956665453471673, 1362416418368954642215215242131202389777190999050⟩,
   ⟨2201157007339933461397818871147346646735748327829, 2451161907532838663703486846986008060683381166094⟩,
   ⟨-2517398564341782166979590210209544686667674668396, -874430152248876630604321773427827783889523324253⟩,
   ⟨-5676634743193224098112856982317412437263302478122, 7770751552074583450102099288286258171792527001928⟩,
   ⟨-56943256567161817944007981853627141510226242598469, 85465027139047587147270610279538783029682386966082⟩,
   ⟨-1010863798871469601186014549378823934052783653672287, 907145148589875944894057412556080696468107209574368⟩⟩

theorem ySum_checked : alphaJet.add yCorrection = ySum := by decide

def yJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨3757831327433375115600376554125534339917622094850, 3931102820813188187650472477800749813965948186889⟩,
   ⟨6351196597414627264135493485844178520468011943383, 7072558256827116437112986790743756151808809838298⟩,
   ⟨-7263676849433770405004319680674448164500776987330, -2523072088506471136372372600319284377899479081438⟩,
   ⟨-16379305585885717463205343262599370658394455707368, 22421649456316434062016062064464188248540629006681⟩,
   ⟨-164303507723024506018635781191203141609927061540200, 246599941645889252073942474846940930775544781275218⟩,
   ⟨-2916736379292095436326841019738179312553251803745636, 2617467614474191724348902496957764036313615342101633⟩⟩

theorem yJetBox_checked : yConstant.mul ySum = yJetBox := by decide

def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨388859052258689629531642150960808544659203837261, 404140559565306994080631577951399143353342839406⟩,
   ⟨188065336581183553490675797418793796882838857525, 228260098810688171209752895249304138439995170665⟩,
   ⟨40604656566373956569815525103179551648049025264, 130359718293067313514114577944213173589173709559⟩,
   ⟨-23961186522277342778261591065249150690108889141, 198919470868981069496543899577028094061363670215⟩,
   ⟨-346290546189497076647430821936853589557523895394, 519065849518673315955650126789059509359163535699⟩,
   ⟨-2088435244536896062915892629174440438811445468130, 2247308751981489473455273560382653330016183466045⟩⟩

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
    E8TAxisZero0065StableWitnesses.logTwo_checked denominatorsPositive yPrime_pos ha hapos

#print axioms stable_eval_eq
#print axioms qJetBox_contains
end GeneralCK.Certificates.E8TAxisZero0065GraphWholeC


