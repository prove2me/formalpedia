-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0631GraphWholeC__12
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0631GraphWholeC__12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T07:16:54.478053+00:00
-- url     : https://prove2.me/theorems/ea4dbbc3-f883-4a70-8cbc-49066bc1941c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0631GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisProd0632GraphWholeC, GeneralCK.Certificates.E8TAxisProd0633Graph…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0631GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisProd0632GraphWholeC, GeneralCK.Certificates.E8TAxisProd0633GraphWholeC, GeneralCK.Certificates.E8TAxisProd0634GraphWholeC, GeneralCK.Certificates.E8TAxisProd0635GraphWholeC, GeneralCK.Certificates.E8TAxisProd0636GraphWholeC, GeneralCK.Certificates.E8TAxisProd0637GraphWholeC, GeneralCK.Certificates.E8TAxisProd0638GraphWholeC, GeneralCK.Certificates.E8TAxisProd0639GraphWholeC, GeneralCK.Certificates.E8TAxisProd0640GraphWholeC, GeneralCK.Certificates.E8TAxisProd0641GraphWholeC, GeneralCK.Certificates.E8TAxisProd0642GraphWholeC)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0631GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisProd0632GraphWholeC, GeneralCK.Certificates.E8TAxisProd0633GraphWholeC, GeneralCK.Certificates.E8TAxisProd0634GraphWholeC, GeneralCK.Certificates.E8TAxisProd0635GraphWholeC, GeneralCK.Certificates.E8TAxisProd0636GraphWholeC, GeneralCK.Certificates.E8TAxisProd0637GraphWholeC, GeneralCK.Certificates.E8TAxisProd0638GraphWholeC, GeneralCK.Certificates.E8TAxisProd0639GraphWholeC, GeneralCK.Certificates.E8TAxisProd0640GraphWholeC, GeneralCK.Certificates.E8TAxisProd0641GraphWholeC, GeneralCK.Certificates.E8TAxisProd0642GraphWholeC)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0631GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisProd0632GraphWholeC, GeneralCK.Certificates.E8TAxisProd0633GraphWholeC, GeneralCK.Certificates.E8TAxisProd0634GraphWholeC, GeneralCK.Certificates.E8TAxisProd0635GraphWholeC, GeneralCK.Certificates.E8TAxisProd0636GraphWholeC, GeneralCK.Certificates.E8TAxisProd0637GraphWholeC, GeneralCK.Certificates.E8TAxisProd0638GraphWholeC, GeneralCK.Certificates.E8TAxisProd0639GraphWholeC, GeneralCK.Certificates.E8TAxisProd0640GraphWholeC, GeneralCK.Certificates.E8TAxisProd0641GraphWholeC, GeneralCK.Certificates.E8TAxisProd0642GraphWholeC) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0631GraphWholeC (+11 modules: GeneralCK/Certificates/E8TAxisProd0632GraphWholeC, GeneralCK/Certificates/E8TAxisProd0633GraphWholeC, GeneralCK/Certificates/E8TAxisProd0634GraphWholeC, GeneralCK/Certificates/E8TAxisProd0635GraphWholeC, GeneralCK/Certificates/E8TAxisProd0636GraphWholeC, GeneralCK/Certificates/E8TAxisProd0637GraphWholeC, GeneralCK/Certificates/E8TAxisProd0638GraphWholeC, GeneralCK/Certificates/E8TAxisProd0639GraphWholeC, GeneralCK/Certificates/E8TAxisProd0640GraphWholeC, GeneralCK/Certificates/E8TAxisProd0641GraphWholeC, GeneralCK/Certificates/E8TAxisProd0642GraphWholeC).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0631GraphWholeC__12_q101

namespace GeneralCK.Certificates.E8TAxisProd0642GraphWholeC
open DyadicInterval E8TAxisStableInterval E8TAxisProd0642PaddedInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def yDenominator : DyadicJet5Enclosure precision :=
  ⟨⟨940022725822214369090879187853931349994365081730, 978830494132380690633394679073104418497093582317⟩,
   ⟨-346167644721370613703871730811429401666987723183, -197522290992597820841755784353307025843544135168⟩,
   ⟨-1197328033748889208739452431477949004193296376061, -311277458605124736421957247721491059297266550075⟩,
   ⟨-3988539007092513775685676758363527190370037693899, 3608952548184656511123652262519343137607598245561⟩,
   ⟨-38715461588376335569826292833596625836670824656399, 47937670501830771048064765205608133080395634217457⟩,
   ⟨-596143897074405037934485766124534593006533520151804, 629084131619123554934820956608334358551861691681237⟩⟩

theorem yDenominator_checked : qData.mul ellData = yDenominator := by decide

def yDenominatorInv : DyadicJet5Enclosure precision :=
  ⟨⟨2182182766807049659240400025946098903635608798228, 2272271698593899037209529818004053474036869476691⟩,
   ⟨440351768818105726659366319897976436575101800834, 836774389024765593680629078907326975607817543470⟩,
   ⟨871675832963368019743890330065104629409025845123, 3510535387278007721909115160743861895923684465679⟩,
   ⟨-7775941785871528705943654742674592652601510224052, 16717070209862877771646306095022053710315899848511⟩,
   ⟨-139149647026510265571326249639254486530851907562926, 159240072178122422457555477896829746385028957130076⟩,
   ⟨-2235129568336717479321135265285377400580869403444150, 2268431842759955730446328879856817393116278058867110⟩⟩

theorem yDenominatorInv_checked : yDenominator.inv = yDenominatorInv := by decide

def yCorrection : DyadicJet5Enclosure precision :=
  ⟨⟨518915728884544522266255788785419099525912397643, 562249851823675361390901025693743079567745693232⟩,
   ⟨876447372129718851281163201553340465731750167122, 1115199222414903953920476215978633777896575792903⟩,
   ⟨-2529619493328097799804157066994842188149725996760, -898328637193514972139749668701251388083850773634⟩,
   ⟨-7059138539745382409190266152825239342177663970032, 6885342330757382633483395269424401125711441197360⟩,
   ⟨-60284877784484695959887847968936279932899044536320, 96329688972336210570226299524982470165185993594125⟩,
   ⟨-1174970061818883466065276100706635618376630265917107, 1074807665121549063823166873398691635107427494139847⟩⟩

theorem yCorrection_checked : yNumerator.mul yDenominatorInv = yCorrection := by decide

def ySum : DyadicJet5Enclosure precision :=
  ⟨⟨1125569629467415964386521307068894459760500856287, 1180126051412025861492117800536085023541146460567⟩,
   ⟨2337949009460621769484848034269623485387682710098, 2576700859745806872124161048694916797552508335879⟩,
   ⟨-2529619493328097799804157066994842188149725996760, -898328637193514972139749668701251388083850773634⟩,
   ⟨-7059138539745382409190266152825239342177663970032, 6885342330757382633483395269424401125711441197360⟩,
   ⟨-60284877784484695959887847968936279932899044536320, 96329688972336210570226299524982470165185993594125⟩,
   ⟨-1174970061818883466065276100706635618376630265917107, 1074807665121549063823166873398691635107427494139847⟩⟩

theorem ySum_checked : alphaJet.add yCorrection = ySum := by decide

def yJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨3247707445215738132938905827162642485851756393053, 3405124003992007165007707026259516636740470180244⟩,
   ⟨6745894883600206439671377452325917916125813130447, 7434787104419208022476642550204346451223656431217⟩,
   ⟨-7298938996720997905050804900139595100152061181395, -2592028539935249713440599339985081872885622435510⟩,
   ⟨-20368368328477643827919731282037042704720346078672, 19866898470813065495796481351617507906243314715219⟩,
   ⟨-173945388440546620369620759373476380228533975303009, 277948729141531433481661626149207894711739223602489⟩,
   ⟨-3390246962758203889061596268672591093135685189213982, 3101239376760609031474686832491530584560047856662722⟩⟩

theorem yJetBox_checked : yConstant.mul ySum = yJetBox := by decide

def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨321023423086246965516742440799353508214168239841, 334041248774460647220780230492301454204018906333⟩,
   ⟨167336309943332295754524466234123798743252903555, 199800200259767845251417072188462194124226495683⟩,
   ⟨31101107608896341490650339978115732434528485249, 98248969542190147268705419589528855359495324148⟩,
   ⟨-13237241455948143447602375895332577794467130601, 145745844738854775734214606216306939580162697041⟩,
   ⟨-225246121089628474750927996928904509431932223363, 356722465013643752424269331432164094875269370374⟩,
   ⟨-1299746107423875420522517800649010141326849270170, 1445237571745963533895262968165823262313664608718⟩⟩

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
    E8TAxisProd0642StableWitnesses.logTwo_checked denominatorsPositive yPrime_pos ha hapos

#print axioms stable_eval_eq
#print axioms qJetBox_contains
end GeneralCK.Certificates.E8TAxisProd0642GraphWholeC


