-- Prove2me | Definitions.Def_OAIQ084L018
-- name    : OAIQ084L018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:30:22.407721+00:00
-- url     : https://prove2.me/theorems/79a83792-8cf2-4a28-815c-411d72d40847
-- title:
--   Definitions bundle OAIQ084L018 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 14 definitions. The definitions and types are `OAI.LaughlinFock.fourHighestCache_22_2`, `OAI.LaughlinFock.fourHighestCache_22_3`, `OAI.LaughlinFock.fourHighestCache_22_4`, `OAI.LaughlinFock.fourHighestCache_22_5`, `OAI.LaughlinFock.fourHighestCache_22_6`, `OAI.LaughlinFock.fourHighestCache_22_7`, `OAI.LaughlinFock.fourHighestCache_22_8`, `OAI.LaughlinFock.fourHighestCache_22_9`, `OAI.LaughlinFock.fourHighestCache_23_0`, `OAI.LaughlinFock.fourHighestCache_9_0`, `OAI.LaughlinFock.fourHighestShellEquiv`, `OAI.LaughlinFock.highestThreeAnnihilator`, `OAI.LaughlinFock.limitPairAnnihilator`, `OAI.LaughlinFock.rationalFourFactor`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinFock_BesselComparison`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/BesselComparison.lean), [`LaughlinFock_Certificate09`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate09.lean), [`LaughlinFock_Certificate22`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate22.lean), [`LaughlinFock_Certificate23`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate23.lean), [`LaughlinFock_HighestTails`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/HighestTails.lean), [`LaughlinFock_LocalEnergy`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/LocalEnergy.lean), [`LaughlinFock_RationalFour`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/RationalFour.lean).
--
--   **Imports.** It imports the published bundle `Def_LaughlinFock`; the bundles `OAIQ084L000` and `OAIQ084L001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ084L022`, `OAIQ084L023`, `OAIQ084L028`, `OAIQ084L034` and `OAIQ084L035`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L000
import Definitions.Def_OAIQ084L001

section
-- module Solutions.OAIQ084_LF.LaughlinFock_LocalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local Energy. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology
open Filter Topology


def limitPairAnnihilator (L p : ℕ) : FockMatrix L :=
  coefficientPairAnnihilator L (fun i j => (limitPairCoefficient p i.val j.val : ℂ))

open Filter Topology

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_BesselComparison
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bessel Comparison. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder



def fourHighestShellEquiv {Q D : ℕ} (hQ : 1 ≤ Q) (hD : D ≤ Q) :
    FourHighestShell Q D ≃ ((n : Fin (D+1)) × Fin ((n.val+1)/2)) where
  toFun b := ⟨⟨b.val.2.val.1.val+b.val.2.val.2.val, by have := b.property; omega⟩,
    ⟨b.val.2.val.1.val, by
      change b.val.2.val.1.val < (b.val.2.val.1.val+b.val.2.val.2.val+1)/2
      have hlt : b.val.2.val.1.val < b.val.2.val.2.val := b.val.2.property
      omega⟩⟩
  invFun c := by
    let n := c.1.val
    let j := c.2.val
    have hn := c.1.isLt
    have hj := c.2.isLt
    refine ⟨(⟨D-n, by dsimp [n] at *; omega⟩,
      ⟨(⟨j, by dsimp [n,j] at *; omega⟩,
        ⟨n-j, by dsimp [n,j] at *; omega⟩), ?_⟩), ?_⟩
    · change j < n-j
      dsimp [n,j] at *
      omega
    · change D-n+j+(n-j)=D
      dsimp [n,j] at *
      omega
  left_inv b := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      dsimp
      have := b.property
      omega
    · apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        rfl
      · apply Fin.ext
        dsimp
        omega
  right_inv c := by
    rcases c with ⟨n,j⟩
    apply Sigma.ext
    · apply Fin.ext
      dsimp
      have := j.isLt
      omega
    · apply (Fin.heq_ext_iff ?_).mpr
      · rfl
      · dsimp
        have := j.isLt
        omega

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_HighestTails
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Highest Tails. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder



def highestThreeAnnihilator (Q z : ℕ) (hz : z ≤ Q) : FockMatrix Q :=
  ∑ p : Fin (z+1), (highestCoefficient (2*Q-2) Q z p.val : ℂ) •
    (annihilator Q ⟨z-p.val, by omega⟩ * pairAnnihilator Q p.val)



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RationalFour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Four. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def rationalFourFactor {t : ℕ} (D : ℕ) (b c : RowEntry t) : ℚ :=
  2 * 2^(rowP b) * 2^(rowP c) * (t.factorial : ℚ) *
    (rowI b).factorial * (rowI c).factorial /
    (2^t * (2^(rowFourLevel b c))^2 * ((rowFourLevel b c-D).factorial : ℚ))

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate09
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate09. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_9_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,7}, [1935360, 241920, -60480, -30240, 362880]),
  ({0,1,3,6}, [-1935360, -241920, 60480, 30240, -362880]),
  ({0,1,4,5}, [2580480, 138240, -34560, -40320, 362880]),
  ({0,2,3,5}, [-645120, 103680, -25920, 10080, 0])
]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate22
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate22. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_22_2 : List (Occupation 24 × List ℚ) := [
  ({0,1,10,12}, [0, -934234371139829760000, -295021380359946240000, -35115136724828160000, 90386452316160000, 1472256252149760000, -926461136240640000, 1581762915532800000, -3841424223436800000, 14597412049059840000, -102181884343418880000]),
  ({0,2,3,18}, [0, 1121081245367795712000, 196680920239964160000, -161339817384345600000, -183773734849216512000, -76060199624048640000, 23509516247433216000, 43023951302492160000, -23048545340620800000, -113859813982666752000, -102181884343418880000]),
  ({0,2,4,17}, [0, 186846874227965952000, 185754202448855040000, 209741762599649280000, 155808166502596608000, 61974977471447040000, -17977865365684224000, -37645957389680640000, 17414456479580160000, 105101366753230848000, 102181884343418880000]),
  ({0,2,5,16}, [0, 0, -305948098151055360000, -238740749384417280000, -103402101449687040000, -25021982882856960000, 7999201029980160000, 19297507569500160000, -2560949482291200000, -72987060245299200000, -102181884343418880000])
]

def fourHighestCache_22_3 : List (Occupation 24 × List ℚ) := [
  ({0,2,6,15}, [0, 467117185569914880000, 311411457046609920000, 196613130400727040000, 65213825346109440000, 2734190182563840000, -3525071640330240000, -4982553183928320000, -6658468653957120000, 43792236147179520000, 102181884343418880000]),
  ({0,2,7,14}, [0, -653964059797880832000, -344191610419937280000, -134291671528734720000, -34102808458887168000, 2319918942781440000, 3005349539512320000, -1660851061309440000, 7768213429616640000, -20436376868683776000, -102181884343418880000]),
  ({0,2,8,13}, [0, 747387496911863808000, 327801533733273600000, 90265937046405120000, 11280229249056768000, -911396727521280000, -2526301342236672000, 2372644373299200000, -4012154188922880000, 2919482409811968000, 102181884343418880000]),
  ({0,2,9,12}, [0, -934234371139829760000, -295021380359946240000, -57892522708500480000, -1211178461036544000, 516245698805760000, 772804167303168000, -316352583106560000, -768284844687360000, 8758447229435904000, -102181884343418880000])
]

def fourHighestCache_22_4 : List (Occupation 24 × List ℚ) := [
  ({0,2,10,11}, [0, 934234371139829760000, 295021380359946240000, 35115136724828160000, -90386452316160000, -1472256252149760000, 926461136240640000, -1581762915532800000, 3841424223436800000, -14597412049059840000, 102181884343418880000]),
  ({0,3,4,16}, [0, -1494774993823727616000, -262241226986618880000, -19402958430535680000, -24440496706289664000, -22867772435988480000, 4447013453955072000, 12970455907368960000, -9219418136248320000, -23355859278495744000, 0]),
  ({0,3,5,15}, [0, 1167792963924787200000, 319606495389941760000, 54966261314764800000, 17331602231623680000, 15535171491840000000, -1694745980928000000, -10953708190064640000, 6402373705728000000, 21896118073589760000, 0]),
  ({0,3,6,14}, [0, -1307928119595761664000, -229461073613291520000, -52198176212582400000, -16070711221813248000, -4225566645780480000, -203369517711360000, 5219817621258240000, -768284844687360000, -17516894458871808000, 0])
]

def fourHighestCache_22_5 : List (Occupation 24 × List ℚ) := [
  ({0,3,7,13}, [0, 1167792963924787200000, 188485881896632320000, 27970840889671680000, 13571525815271424000, -372844115804160000, -275678679564288000, -619523808583680000, -2817044430520320000, 13137670844153856000, 0]),
  ({0,3,8,12}, [0, -747387496911863808000, -131120613493309440000, -16450334321541120000, -6435515404910592000, -114721266401280000, 1355796784742400000, -1529037485015040000, 3585329275207680000, -8758447229435904000, 0]),
  ({0,3,9,11}, [0, 467117185569914880000, 49170230059991040000, 11863221866496000000, 858671297003520000, 860409498009600000, -1301564913352704000, 1423586623979520000, -2304854534062080000, 4379223614717952000, 0]),
  ({0,4,5,14}, [0, 0, -152974049075527680000, -25730010092666880000, 4555477196734464000, -5385526117171200000, -158176291553280000, 3796230997278720000, -3158504361492480000, -2919482409811968000, 0])
]

def fourHighestCache_22_6 : List (Occupation 24 × List ℚ) := [
  ({0,4,6,13}, [0, 373693748455931904000, 131120613493309440000, 30158946256158720000, -3290066864308224000, 2734190182563840000, 998770298093568000, -3268976692101120000, 2304854534062080000, 2919482409811968000, 0]),
  ({0,4,7,12}, [0, -747387496911863808000, -131120613493309440000, -11388692991836160000, -1518492398911488000, -38240422133760000, -885787232698368000, 1529037485015040000, -512189896458240000, -2919482409811968000, 0]),
  ({0,4,8,11}, [0, 747387496911863808000, 131120613493309440000, -421803444142080000, 2386202341146624000, -140214881157120000, -54231871389696000, 52725430517760000, -853649827430400000, 2919482409811968000, 0]),
  ({0,4,9,10}, [0, -934234371139829760000, -98340460119982080000, -949057749319680000, -415777680654336000, -764808442675200000, 903864523161600000, -949057749319680000, 1536569689374720000, -2919482409811968000, 0])
]

def fourHighestCache_22_7 : List (Occupation 24 × List ℚ) := [
  ({0,5,6,12}, [0, 0, 0, -17715744653967360000, 3615458092646400000, -879529709076480000, -542318713896960000, 1159959471390720000, -1024379792916480000, 0, 0]),
  ({0,5,7,11}, [0, 233558592784957440000, 2731679447777280000, 12680466039521280000, -1739939207086080000, -28680316600320000, 790881457766400000, -1067689967984640000, 853649827430400000, 0, 0]),
  ({0,5,8,10}, [0, 0, -21853435582218240000, -2109017220710400000, -361545809264640000, 478005276672000000, -564915326976000000, 579979735695360000, -426824913715200000, 0, 0]),
  ({0,6,7,10}, [0, -467117185569914880000, 16390076686663680000, -6379777092648960000, 949057749319680000, 38240422133760000, -293755970027520000, 342715298365440000, -256094948229120000, 0, 0])
]

def fourHighestCache_22_8 : List (Occupation 24 × List ℚ) := [
  ({0,6,8,9}, [0, 373693748455931904000, 0, 3163525831065600000, -108463742779392000, -325043588136960000, 393181067575296000, -369078013624320000, 256094948229120000, 0, 0]),
  ({1,2,3,17}, [0, -1307928119595761664000, -382435122688819200000, -48401945215303680000, 27965568346619904000, 14085222152601600000, -5531650881748992000, -5377993912811520000, 5634088861040640000, 8758447229435904000, 0]),
  ({1,2,4,16}, [0, 1307928119595761664000, 382435122688819200000, 48401945215303680000, -27965568346619904000, -14085222152601600000, 5531650881748992000, 5377993912811520000, -5634088861040640000, -8758447229435904000, 0]),
  ({1,2,5,15}, [0, -1634910149494702080000, -325069854285496320000, -12838642331074560000, 20856673871953920000, 6752621208453120000, -2779383408721920000, -3361246195507200000, 2817044430520320000, 7298706024529920000, 0])
]

def fourHighestCache_22_9 : List (Occupation 24 × List ℚ) := [
  ({1,2,6,14}, [0, 1494774993823727616000, 262241226986618880000, -10123282659409920000, -15040305665409024000, -828542479564800000, 723091618529280000, 1423586623979520000, -341459930972160000, -5838964819623936000, 0]),
  ({1,2,7,13}, [0, -1261216401038770176000, -172095805209968640000, 16054893592657920000, 9251053394558976000, -1035678099456000000, -203369517711360000, -92269503406080000, -939014810173440000, 4379223614717952000, 0]),
  ({1,2,8,12}, [0, 934234371139829760000, 98340460119982080000, -15923080016363520000, -3633535383109632000, 509872295116800000, 397700390191104000, -527254305177600000, 1195109758402560000, -2919482409811968000, 0]),
  ({1,2,9,11}, [0, -467117185569914880000, -49170230059991040000, 10914164117176320000, 442893616349184000, 95601055334400000, -397700390191104000, 474528874659840000, -768284844687360000, 1459741204905984000, 0])
]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate23
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate23. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_23_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,21}, [179840116444417228800000, 65396405979788083200000, 45164392879791144960000, 28304381963127029760000, 15122918882825994240000, 5620003638888038400000, -204363768686837760000, -2350183339898634240000, -817455074747351040000, 4393821026767011840000, 13283644964644454400000, 25852016738884976640000]),
  ({0,1,3,20}, [-179840116444417228800000, -65396405979788083200000, -45164392879791144960000, -28304381963127029760000, -15122918882825994240000, -5620003638888038400000, 204363768686837760000, 2350183339898634240000, 817455074747351040000, -4393821026767011840000, -13283644964644454400000, -25852016738884976640000]),
  ({0,1,4,19}, [323712209599951011840000, 95291905856262635520000, 51587254181377474560000, 25443289201511301120000, 10749534232927666176000, 3211430650793164800000, -218961180735897600000, -1328364496464445440000, -642286130158632960000, 2574983485454155776000, 10320370318685306880000, 25852016738884976640000]),
  ({0,1,5,18}, [-323712209599951011840000, -95291905856262635520000, -47456954856338227200000, -20624606655632179200000, -6851564244921876480000, -1250767727151022080000, 258911992659640320000, 467885470414602240000, 433312652403671040000, -963429195237949440000, -7459277557069578240000, -25852016738884976640000])
]

end LaughlinFock
end

end OAI
end


