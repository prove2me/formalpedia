-- Prove2me | Definitions.Def_OAIQ057D011
-- name    : OAIQ057D011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T21:24:52.034337+00:00
-- url     : https://prove2.me/theorems/da55808b-77bd-40e1-ae4e-0c91296ea410
-- title:
--   Definitions bundle OAIQ057D011 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.exists_channel_fin21`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 92 declarations of OpenAI's Lean: 12 definitions, 3 instances and 77 theorems. The definitions and types are `OAI.DimensionTen.Border.E`, `OAI.DimensionTen.Border.alpha`, `OAI.DimensionTen.Border.basis`, `OAI.DimensionTen.Border.complexEmbedding`, `OAI.DimensionTen.Border.embeddingRootEquiv`, `OAI.DimensionTen.Border.embeddingsC`, `OAI.DimensionTen.Border.embeddingsK`, `OAI.DimensionTen.Border.evaluationMatrix`, `OAI.DimensionTen.Border.points`, `OAI.DimensionTen.Border.rho`, `OAI.DimensionTen.compositeChoi`, `OAI.DimensionTen.pencil`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/InformationTheory, in whole or in part: `Quantum_DimensionTen_Annihilator`, `Quantum_DimensionTen_BorderField`, `Quantum_DimensionTen_EvaluationMinors`, `Quantum_DimensionTen_ExteriorMaps`, `Quantum_DimensionTen_GaloisField`, `Quantum_DimensionTen_IntegerPolynomials`, `Quantum_DimensionTen_Kraus`, `Quantum_DimensionTen_LowBasis`, `Quantum_DimensionTen_Mod41Powers09`, `Quantum_DimensionTen_Mod41Powers10`, `Quantum_DimensionTen_Mod41Result`, `Quantum_DimensionTen_NormalizedMatrices`, `Quantum_DimensionTen_PencilKraus`, `Quantum_DimensionTen_PencilModel`, `Quantum_DimensionTen_TensorKraus`.
--
--   **Imports.** It imports the bundles `OAIQ057D008`, `OAIQ057D009` and `OAIQ057D010` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ057D013`; the statements `OAI_DimensionTen_Border_high_alpha`, `OAI.DimensionTen.Border.high_alpha_s2`, `OAI_DimensionTen_Border_minors_embedding`, `OAI.DimensionTen.Border.minors_embedding_s2`, `OAI_DimensionTen_Border_rank_points`, `OAI.DimensionTen.Border.rank_points_s2`, `OAI_DimensionTen_Border_some_ten_minor`, `OAI.DimensionTen.Border.some_ten_minor_s2`, `OAI_DimensionTen_compositeChoi_veronese`, `OAI.DimensionTen.compositeChoi_veronese_s2`, `OAI_DimensionTen_veronese_family_general_position` and `OAI.DimensionTen.veronese_family_general_position_s2`; the proofs of `OAI_DimensionTen_Border_high_alpha`, `OAI.DimensionTen.Border.high_alpha_s2`, `OAI_DimensionTen_Border_minors_embedding`, `OAI.DimensionTen.Border.minors_embedding_s2`, `OAI_DimensionTen_Border_rank_points`, `OAI.DimensionTen.Border.rank_points_s2`, `OAI_DimensionTen_Border_some_ten_minor`, `OAI.DimensionTen.Border.some_ten_minor_s2`, `OAI_DimensionTen_root_action_full_symmetric`, `OAI.DimensionTen.root_action_full_symmetric_s2`, `OAI_DimensionTen_veronese_family_general_position` and `OAI.DimensionTen.veronese_family_general_position_s2`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis, lean/OAI/InformationTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ057D008
import Definitions.Def_OAIQ057D009
import Definitions.Def_OAIQ057D010

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers09
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41

theorem pow17_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow17_4 z * u16 z = pow17_5_q z * f z + pow17_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow17_5_mul_integer z


theorem pow17_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow17_4 z * u16 z = pow17_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_5_mul z


theorem pow17_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z ^ 5 = pow17_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow17_4_pow z hz]
  exact pow17_5_root z hz


theorem pow17_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z ^ 10 = pow17_10 z := by
  calc
    _ = u16 z ^ 5 * u16 z ^ 5 := by ring
    _ = pow17_5 z * pow17_5 z := by rw [pow17_5_pow z hz]
    _ = _ := pow17_10_root z hz


theorem pow17_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z ^ 20 = pow17_20 z := by
  calc
    _ = u16 z ^ 10 * u16 z ^ 10 := by ring
    _ = pow17_10 z * pow17_10 z := by rw [pow17_10_pow z hz]
    _ = _ := pow17_20_root z hz


theorem pow17_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z ^ 40 = pow17_40 z := by
  calc
    _ = u16 z ^ 20 * u16 z ^ 20 := by ring
    _ = pow17_20 z * pow17_20 z := by rw [pow17_20_pow z hz]
    _ = _ := pow17_40_root z hz


theorem pow17_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z ^ 41 = pow17_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow17_40_pow z hz]
  exact pow17_41_root z hz


theorem iterate17 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 17) = u17 z := by
  calc
    _ = (z ^ (41 ^ 16)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u16 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate16 z hz)
    _ = _ := pow17_41_pow z hz


theorem iterate18 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 18) = u18 z := by
  calc
    _ = (z ^ (41 ^ 17)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u17 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate17 z hz)
    _ = _ := pow18_41_pow z hz

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers10
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41

theorem iterate19 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 19) = u19 z := by
  calc
    _ = (z ^ (41 ^ 18)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u18 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate18 z hz)
    _ = _ := pow19_41_pow z hz


theorem iterate20 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 20) = u20 z := by
  calc
    _ = (z ^ (41 ^ 19)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u19 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate19 z hz)
    _ = _ := pow20_41_pow z hz

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Result
attribute [-instance] _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial

section
noncomputable section
open Polynomial
namespace DimensionTen.Mod41

section Field
variable (k : Type*) [Field k] [CharP k 41]

attribute [local instance] OAI.DimensionTen.Mod41.charP_root
lemma divides_twenty : f (X : k[X]) ∣ X ^ 41 ^ 20 - X := by
  apply AdjoinRoot.mk_eq_zero.mp
  simp only [map_sub, map_pow, AdjoinRoot.mk_X]
  rw [iterate20 _ (root_f k)]
  simp only [u20, u0, mul_one, zero_add, sub_self]


theorem irreducible_f_of_card [Finite k] (hc : Nat.card k = 41) :
    Irreducible (f (X : k[X])) := by
  apply irreducible_degree_twenty _ degree_f.natDegree_eq
  · simpa only [hc] using divides_twenty k
  · simpa only [hc] using coprime_four k
  · simpa only [hc] using coprime_ten k

end Field

theorem irreducible_f : Irreducible (f (X : (ZMod 41)[X])) :=
  irreducible_f_of_card (ZMod 41) (by simp)

end DimensionTen.Mod41

end
end

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_IntegerPolynomials
attribute [-instance] _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Polynomial Matrix
namespace DimensionTen.Border

lemma F_irreducible : Irreducible (F.map (algebraMap ℤ ℚ)) := by
  apply F_monic.irreducible_iff_irreducible_map_fraction_map.mp
  apply Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 41)) F F_monic
  rw [F_reduction_41]
  exact Mod41.irreducible_f

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Annihilator
attribute [-instance] _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

lemma W_add_step0 : (-665456935831295645613234276870960 : ℤ) • e0 + B0 *ᵥ e0 = W1 := by
  simpa only [W0_eq, add_comm] using W_step0

lemma W_add_step1 : (-70575490389691608208970825963579579734790687104242531156794252400 : ℤ) • e0 + B0 *ᵥ W1 = W2 := by
  simpa only [W0_eq, add_comm] using W_step1

lemma W_add_step2 : (145204575748123705650598860122042297964140180806502873813425954437770925496552439336297911807152000 : ℤ) • e0 + B0 *ᵥ W2 = W3 := by
  simpa only [W0_eq, add_comm] using W_step2

lemma W_add_step3 : (-35324838830202393213114710617144206880545881202172927720865474148390980209388806187550300213113700416597412380444619467558313120000 : ℤ) • e0 + B0 *ᵥ W3 = W4 := by
  simpa only [W0_eq, add_comm] using W_step3

lemma W_add_step4 : (373565650934774887461173450615958673493665750145833416276706195065625377037257320323651912502138867646885039242665453554378883071785987397285956044288246752000000 : ℤ) • e0 + B0 *ᵥ W4 = W5 := by
  simpa only [W0_eq, add_comm] using W_step4

lemma W_add_step5 : (1221247532914883428738232812315046413061003261754365921877331401690772085408337009866167041104811173917721563989083295894997519285879820644602218589359930080044045784701600336896172318351552000000 : ℤ) • e0 + B0 *ᵥ W5 = W6 := by
  simpa only [W0_eq, add_comm] using W_step5

lemma W_add_step6 : (-248227637152475705027939375857278526128191272750984168929977414072990649655673065160190565283923935144328649963473688624322944637031495498096318971767466342970191076754053510390097551205920734946099494349011595986009016320000000 : ℤ) • e0 + B0 *ᵥ W6 = W7 := by
  simpa only [W0_eq, add_comm] using W_step6

lemma W_add_step7 : (23987898748033982540672860523700865395338187584784902027097207883389242545617842033943633110512117271742643190645306300993695952546671697315106563700443682653623151506540994176376096734479969113402657992738820843936302180323975678376815544328820255590400000000 : ℤ) • e0 + B0 *ᵥ W7 = W8 := by
  simpa only [W0_eq, add_comm] using W_step7

lemma W_add_step8 : (-1171308828589766784667174319064418542798135133484982791854491081649943231360093785409472006445243262855246426572170988410104927443954726055604498601479060662278001768673622504306995915615815163705741569269783733808816002389524109550321410806269620903448193875229330238654480165635072000000000 : ℤ) • e0 + B0 *ᵥ W8 = W9 := by
  simpa only [W0_eq, add_comm] using W_step8

lemma W_add_step9 : (9418076163852223744432430014364091808485209898268329041429484569331398431107415197968026807215347240401736075163106970860375437764441639386759444924342265991793540088391019157445548247844788073792441943995585891632831540649213169911827703330754567896340380609774093821467596292667988969060929685782740051333867520000000000 : ℤ) • e0 + B0 *ᵥ W9 = W10 := by
  simpa only [W0_eq, add_comm] using W_step9

lemma W_add_step10 : (2379351982660918187351912781958188527717967481429203927909200858573699275008394894183277671168447409642612098439982572413522546000040986498273641717234153243897007250606150778122646421703817983494954617791128567739285620364189110954410697514797765886291714388494664729026689529953663266988303413000134427206176735476450561111234207094565608243200000000000 : ℤ) • e0 + B0 *ᵥ W10 = W11 := by
  simpa only [W0_eq, add_comm] using W_step10

lemma W_add_step11 : (-156443788709025742196345911143201398522107585903943872656350511938867845971206431668038085111377071526334593976793592772236822162619007312610358668945562381934474011199900422427845078146852059081562149156225635557185181304351482728149253212060717470179340715966538846953566303581355673324261441159585174786519237690702352218433699357759363998509903389517501570746482257203200000000000000 : ℤ) • e0 + B0 *ᵥ W11 = W12 := by
  simpa only [W0_eq, add_comm] using W_step11

lemma W_add_step12 : (4900890101564280273384249662632200864363178448207658026058163336136819615272493885470202054565224538142000936511937843307007141485106069287814351270516554069895222315717069012981831431598688971184588468042505208877149369556657292564526267236422804943134514567637453529579229073192380181445210152334600678520463948715012876905929334440543179125298895959992011293893481380162364702394538413670540082328535040000000000000 : ℤ) • e0 + B0 *ᵥ W12 = W13 := by
  simpa only [W0_eq, add_comm] using W_step12

lemma W_add_step13 : (-84104307174298673686167552255023640494586429007832021068263654225131496108888450236021703884431876764525210998671836899723767574650679562923240549613170660460307111553062077806825303303373793065431974171250181275915638689447630046090976265566391394588988957333827128766847100966792731531401924178962941086742313997809833999852121787629675539133006863302099166667861554529199671567381395010640407518426305516067478326139731889369074892800000000000000 : ℤ) • e0 + B0 *ᵥ W13 = W14 := by
  simpa only [W0_eq, add_comm] using W_step13

lemma W_add_step14 : (675860552142364300469163135239922215844669725914434221808961587832864654839688852714377465846874183474661558953416089505955745772157789761536300845401390976278172003633735629354916823207663419987549669250042714970662428618786997007804393564088687435177258735743667457380692013561927748177389045537156630683615468224776124736218311770991358194005151667711594323471452495210584512969519473278662518864183000362256079240789122668752515792267237678356626639740742926336000000000000000 : ℤ) • e0 + B0 *ᵥ W14 = W15 := by
  simpa only [W0_eq, add_comm] using W_step14

lemma W_add_step15 : (464264497883407444747214497780812992686704524760753459744647662220415750416845824659077752493206710993356675945744931523943090697063536003409707838510945285234954377033375647019503467236967613563967236378430128420958879199174432425365805238966092079988382033895233428997733820972532862160052383779427027697929911022006616671493677356268258333730255560145075340313333181727787699892890692686951362386275741868725537594362933484314558383739147305382918898686952977786128912938230214944318784798720000000000000000 : ℤ) • e0 + B0 *ᵥ W15 = W16 := by
  simpa only [W0_eq, add_comm] using W_step15

lemma W_add_step16 : (-46078962234330275978393081039900872188683319775920327128308452687890209275764118451319687474009314096598155961959548923384930131718444660825818480828257818821039017264033763526190311506189940321255132637170583750838824867220822705767283964636390962873055630047046796945200799791451986485780961563108553013724002067700649315332952049979688029591671182364417015107032858404981473456796680608866020804392285926068306658664953047502713815667799656452571900290324373867393260683805253816278147547319199730096639224635584878424883200000000000000000 : ℤ) • e0 + B0 *ᵥ W16 = W17 := by
  simpa only [W0_eq, add_comm] using W_step16

lemma W_add_step17 : (229540072167944847226680415208013118338761677374944768373442556047077491167862762106359122660044266376402295481008188646997320599898453491372250113733518589454936121739510066262153803563671695844108844188342855909377211756360861260377168676543780626494372504766738464872238720120608406900323489717675021679247953712129677892949203666168430318973900550171283869938908653927859069485683785552618689290268121667910013497695005067467335610102307071987167020413797861407454637885276358908659560709050422061741810597789529542860159000644434640948505635320758272000000000000000000 : ℤ) • e0 + B0 *ᵥ W17 = W18 := by
  simpa only [W0_eq, add_comm] using W_step17

lemma W_add_step18 : (50511259664407229159646828548337393831498164764442804655127386655612901648776121372469336914091639720740949450692522422501871756701072556552050895980619323103036951478408656634191362563383127130617057997298235140794077506240567579912973487530312823172729903267062062135892781938802036475675819137510666873059408131836941370912492276716379814401275115222108476610434649500821249715911952605938441183268983422802130006238945591464489363332367504221919288966190285721674362152675650209632960747379797873753029847424190752816297979945928310952397381467134670500671900306775579122183700480000000000000000000 : ℤ) • e0 + B0 *ᵥ W18 = W19 := by
  simpa only [W0_eq, add_comm] using W_step18

lemma W_add_step19 : (-1424105438854051274637383580879187889947095521139556310680850766315834321551239556574203521562568408091279110770199392239672103401933480228396676040102864674581064663417300893715619893996546336746566239320115175015022647808252252957375990525415013961893949766339014426315700834891145618186295338735724851165176076792616990913196521711297962346422135606209029955414419424094778362387247876506714514958332570454743222106183632267250532813404938217795375126355778437850775218722352764943835257588425767268897713027152377493877523758390937382693586850604084390990278979077079727932490410447293788987687686157708243763200000000000000000000 : ℤ) • e0 + B0 *ᵥ W19 = W20 := by
  simpa only [W0_eq, add_comm] using W_step19

lemma FP_annihilates_e0 : (FP B0) *ᵥ e0 = 0 := by
  simp only [FP, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.intCast_mulVec,
    Int.cast_id, Matrix.one_mulVec, W_add_step0, W_add_step1, W_add_step2, W_add_step3, W_add_step4, W_add_step5, W_add_step6, W_add_step7, W_add_step8, W_add_step9, W_add_step10, W_add_step11, W_add_step12, W_add_step13, W_add_step14, W_add_step15, W_add_step16, W_add_step17, W_add_step18, W_add_step19, W20_eq]

lemma annihilate_0 : (FP B0) *ᵥ (Pi.single 0 1 : Fin 20 → ℤ) = 0 := by
  exact FP_annihilates_e0
lemma annihilate_1 : (FP B0) *ᵥ (Pi.single 1 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute ((show Commute B0 B2 from commute_02))) annihilate_0 shift_1
lemma annihilate_2 : (FP B0) *ᵥ (Pi.single 2 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute ((show Commute B0 B1 from commute_01))) annihilate_0 shift_2
lemma annihilate_3 : (FP B0) *ᵥ (Pi.single 3 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute (Commute.refl B0)) annihilate_0 shift_3
lemma annihilate_4 : (FP B0) *ᵥ (Pi.single 4 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute ((show Commute B0 B2 from commute_02))) annihilate_1 shift_4
lemma annihilate_5 : (FP B0) *ᵥ (Pi.single 5 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute ((show Commute B0 B1 from commute_01))) annihilate_1 shift_5
lemma annihilate_6 : (FP B0) *ᵥ (Pi.single 6 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute ((show Commute B0 B1 from commute_01))) annihilate_2 shift_6
lemma annihilate_7 : (FP B0) *ᵥ (Pi.single 7 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute (Commute.refl B0)) annihilate_1 shift_7
lemma annihilate_8 : (FP B0) *ᵥ (Pi.single 8 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute (Commute.refl B0)) annihilate_2 shift_8
lemma annihilate_9 : (FP B0) *ᵥ (Pi.single 9 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute (Commute.refl B0)) annihilate_3 shift_9
lemma annihilate_10 : (FP B0) *ᵥ (Pi.single 10 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute ((show Commute B0 B2 from commute_02))) annihilate_4 shift_10
lemma annihilate_11 : (FP B0) *ᵥ (Pi.single 11 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute ((show Commute B0 B1 from commute_01))) annihilate_4 shift_11
lemma annihilate_12 : (FP B0) *ᵥ (Pi.single 12 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute ((show Commute B0 B1 from commute_01))) annihilate_5 shift_12
lemma annihilate_13 : (FP B0) *ᵥ (Pi.single 13 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute ((show Commute B0 B1 from commute_01))) annihilate_6 shift_13
lemma annihilate_14 : (FP B0) *ᵥ (Pi.single 14 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute (Commute.refl B0)) annihilate_4 shift_14
lemma annihilate_15 : (FP B0) *ᵥ (Pi.single 15 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute (Commute.refl B0)) annihilate_5 shift_15
lemma annihilate_16 : (FP B0) *ᵥ (Pi.single 16 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute (Commute.refl B0)) annihilate_6 shift_16
lemma annihilate_17 : (FP B0) *ᵥ (Pi.single 17 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute (Commute.refl B0)) annihilate_7 shift_17
lemma annihilate_18 : (FP B0) *ᵥ (Pi.single 18 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute (Commute.refl B0)) annihilate_8 shift_18
lemma annihilate_19 : (FP B0) *ᵥ (Pi.single 19 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute (Commute.refl B0)) annihilate_9 shift_19

lemma FP_B0 : FP B0 = 0 := by
  have h (j : Fin 20) : (FP B0) *ᵥ Pi.single j 1 = 0 := by
    fin_cases j
    · exact annihilate_0
    · exact annihilate_1
    · exact annihilate_2
    · exact annihilate_3
    · exact annihilate_4
    · exact annihilate_5
    · exact annihilate_6
    · exact annihilate_7
    · exact annihilate_8
    · exact annihilate_9
    · exact annihilate_10
    · exact annihilate_11
    · exact annihilate_12
    · exact annihilate_13
    · exact annihilate_14
    · exact annihilate_15
    · exact annihilate_16
    · exact annihilate_17
    · exact annihilate_18
    · exact annihilate_19

  ext i j
  have hh := congrFun (h j) i
  simpa [Matrix.mulVec_single] using hh

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_NormalizedMatrices
attribute [-instance] _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

lemma QB_annihilator : aeval (B0.map (Int.castRingHom ℚ)) (F.map (algebraMap ℤ ℚ)) = 0 := by
  rw [Polynomial.aeval_map_algebraMap, aeval_F]
  have h := congrArg (Int.castRingHom ℚ).mapMatrix FP_B0
  simpa only [map_FP, map_zero, RingHom.mapMatrix_apply] using h

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_BorderField
attribute [-instance] _root_.OAI.DimensionTen.Border.instIsSplittingFieldRatKFQ _root_.OAI.DimensionTen.Border.instNumberFieldK _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

instance instFactIrreduciblePolynomialRatFQ : Fact (Irreducible fQ) := ⟨F_irreducible⟩
instance instFiniteDimensionalRatL : FiniteDimensional ℚ L := (AdjoinRoot.powerBasis F_irreducible.ne_zero).finite

lemma representation_exists :
    ∃ ρ : L →ₐ[ℚ] Matrix (Fin 20) (Fin 20) ℚ,
      ρ (AdjoinRoot.root fQ) = B0.map (Int.castRingHom ℚ) ∧
      Function.Bijective (fun a => ρ a *ᵥ eQ 0) :=
  Arithmetic.field_representation fQ F_irreducible fQ_degree _ QB_annihilator _ eQ_ne

def rho : L →ₐ[ℚ] Matrix (Fin 20) (Fin 20) ℚ := representation_exists.choose

lemma rho_root : rho (AdjoinRoot.root fQ) = B0.map (Int.castRingHom ℚ) :=
  representation_exists.choose_spec.1

lemma rho_eval_bijective : Function.Bijective (fun a => rho a *ᵥ eQ 0) :=
  representation_exists.choose_spec.2

def E : L →ₗ[ℚ] (Fin 20 → ℚ) :=
  { toFun := fun a => rho a *ᵥ eQ 0
    map_add' := fun a b => by simp only [map_add, Matrix.add_mulVec]
    map_smul' := fun c a => by simp only [map_smul, RingHom.id_apply, Matrix.smul_mulVec] }

lemma E_injective : Function.Injective E := rho_eval_bijective.1
lemma E_surjective : Function.Surjective E := rho_eval_bijective.2

lemma NB_in_image (i : Fin 3) : ∃ a : L, rho a = NB i := by
  have hc : Commute (rho (AdjoinRoot.root fQ)) (NB i) := by
    rw [rho_root, QB_eq]
    exact (NB_commute 0 i).smul_left _
  exact Arithmetic.centralizer_in_image fQ rho (eQ 0) rho_eval_bijective.2 (NB i) hc

def alpha : Fin 3 → L :=
  ![(d : ℚ)⁻¹ • AdjoinRoot.root fQ, (NB_in_image 1).choose, (NB_in_image 2).choose]

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_LowBasis
attribute [-instance] _root_.OAI.DimensionTen.Border.instIsSplittingFieldRatKFQ _root_.OAI.DimensionTen.Border.instNumberFieldK _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border


def basis : Module.Basis (Fin 20) ℚ L :=
  (Pi.basisFun ℚ (Fin 20)).map (LinearEquiv.ofBijective E ⟨E_injective, E_surjective⟩).symm

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_PencilModel
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix ComplexOrder
open Matrix Complex

namespace DimensionTen

def pencil (x : Fin 4 → ℂ) : Matrix (Fin 6) (Fin 4) ℂ :=
  ∑ i : Fin 4, x i • blocks i


def compositeChoi : Matrix (Fin 10 × Fin 10) (Fin 10 × Fin 10) ℂ :=
  choi (phiTwo ∘ phiOne)


theorem blocks_transpose_mul_comm (i j : Fin 4) :
    (blocks i)ᵀ * blocks j = (blocks j)ᵀ * blocks i := by
  have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℤ =>
    A.map (Int.castRingHom ℂ)) (blocksZ_transpose_mul_comm i j)
  simpa only [Matrix.map_mul, Matrix.transpose_map, blocks] using h

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_GaloisField
attribute [-instance] _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Polynomial Matrix
namespace DimensionTen.Border

instance instIsGaloisRatK : IsGalois ℚ K := IsGalois.of_separable_splitting_field (p := fQ) F_irreducible.separable

lemma F_separable_K : (F.map (algebraMap ℤ K)).Separable := by
  rw [F_map_K]; exact F_irreducible.separable.map
lemma roots_card_K : Fintype.card (F.rootSet K) = 20 :=
  (roots_card_int F F_monic F_separable_K F_splits_K).trans F_degree

lemma aroot_iff_root {R : Type*} [Field R] [Algebra ℚ R] (x : R) :
    x ∈ fQ.aroots R ↔ x ∈ F.rootSet R := by
  let : CharZero R := Algebra.charZero_of_charZero ℚ R
  rw [mem_aroots, mem_rootSet]
  have h : aeval x fQ = aeval x F := by
    rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq ℤ ℚ R, aeval_def]
  constructor
  · intro hx; exact ⟨F_monic.ne_zero, h ▸ hx.2⟩
  · intro hx; exact ⟨F_irreducible.ne_zero, h.symm ▸ hx.2⟩

def embeddingRootEquiv {R : Type*} [Field R] [Algebra ℚ R] :
    (L →ₐ[ℚ] R) ≃ F.rootSet R :=
  (AdjoinRoot.equiv R ℚ fQ F_irreducible.ne_zero).trans
    (Equiv.subtypeEquivRight aroot_iff_root)

lemma embeddings_card_K : Fintype.card (L →ₐ[ℚ] K) = 20 :=
  (Fintype.card_congr (embeddingRootEquiv (R := K))).trans roots_card_K

def embeddingsK : Fin 20 ≃ (L →ₐ[ℚ] K) :=
  (Fintype.equivFinOfCardEq embeddings_card_K).symm

def complexEmbedding : K →ₐ[ℚ] ℂ := IsAlgClosed.lift

lemma finrank_L : Module.finrank ℚ L = 20 := by
  simpa using Module.finrank_eq_card_basis basis

lemma embeddings_card_complex : Fintype.card (L →ₐ[ℚ] ℂ) = 20 :=
  (AlgHom.card ℚ L ℂ).trans finrank_L

lemma complex_embeddings_bijective :
    Function.Bijective (fun i : Fin 20 => complexEmbedding.comp (embeddingsK i)) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by simpa using embeddings_card_complex.symm⟩
  intro i j hij
  apply embeddingsK.injective
  apply DFunLike.ext
  intro a
  exact complexEmbedding.injective (congrArg (fun σ : L →ₐ[ℚ] ℂ => σ a) hij)

def embeddingsC : Fin 20 ≃ (L →ₐ[ℚ] ℂ) :=
  Equiv.ofBijective _ complex_embeddings_bijective

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_EvaluationMinors
attribute [-instance] _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Polynomial Matrix
namespace DimensionTen.Border

def evaluationMatrix : Matrix (Fin 20) (Fin 20) K :=
  fun i j => embeddingsK j (low alpha i)

def points (i : Fin 20) : Fin 3 → ℂ := fun j => embeddingsC i (alpha j)

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Kraus
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix ComplexOrder Kronecker
open Matrix
namespace DimensionTen

lemma krausMap_single {r : Type*} [Fintype r] {a b : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) (i j : Fin a) (u v : Fin b) :
    krausMap Q (Matrix.single i j 1) u v = ∑ k, Q k u i * star (Q k v j) := by
  simp [krausMap_entry, Matrix.single_apply, ite_and]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_PencilKraus
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma pencilMap_kraus : pencilMap = krausMap pencilKraus := by
  funext A
  ext u v
  simp only [pencilMap, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, krausMap_entry,
    pencilKraus_real]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [pencilKraus]
  ring

lemma pencilMap_output_transpose (A : Mat 4) : (pencilMap A)ᵀ = pencilMap A := by
  simp only [pencilMap, Matrix.transpose_sum, Matrix.transpose_smul,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [blocks_transpose_mul_comm j i]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_TensorKraus
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma tensorMap_kraus {r s : Type*} [Fintype r] [Fintype s] {a b c d : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) (R : s → Matrix (Fin d) (Fin c) ℂ)
    (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    tensorMap (krausMap Q) (krausMap R) X =
      krausMap (fun p : r × s => Q p.1 ⊗ₖ R p.2) X := by
  conv_rhs => arg 2; rw [block_expansion X]
  simp only [tensorMap, Matrix.kronecker, krausMap, Fintype.sum_prod_type, Matrix.conjTranspose_kronecker,
    Matrix.mul_sum, Matrix.sum_mul, ← Matrix.mul_kronecker_mul,
    sum_kronecker, kronecker_sum]
  conv_lhs => arg 2; ext i; arg 2; ext j; rw [Finset.sum_comm]
  exact sum_four_comm (fun (i j : Fin c) (k : r) (l : s) =>
    (Q k * Matrix.of (fun a b => X (a, i) (b, j)) * (Q k)ᴴ) ⊗ₖ
      (R l * Matrix.single i j 1 * (R l)ᴴ))

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_ExteriorMaps
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma exteriorMap_kraus : exteriorMap = krausMap exteriorKraus := by
  funext A
  unfold exteriorMap
  rw [pencilMap_kraus, tensorMap_kraus]
  have h := krausMap_conjugate (fun p : Fin 6 × Fin 6 => pencilKraus p.1 ⊗ₖ pencilKraus p.2)
    symmetricIsometry exteriorIsometryᴴ A
  unfold exteriorKraus
  simpa only [Matrix.conjTranspose_conjTranspose] using h

end DimensionTen

end
end

end OAI
end


