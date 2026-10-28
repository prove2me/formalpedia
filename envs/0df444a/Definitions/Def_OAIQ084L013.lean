-- Prove2me | Definitions.Def_OAIQ084L013
-- name    : OAIQ084L013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:28:57.979998+00:00
-- url     : https://prove2.me/theorems/a245d295-9f40-4392-b1bc-ea69324e7056
-- title:
--   Definitions bundle OAIQ084L013 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 27 definitions. The definitions and types are `OAI.LaughlinFock.fourHighestCache_17_5`, `OAI.LaughlinFock.fourHighestCache_17_6`, `OAI.LaughlinFock.fourHighestCache_17_7`, `OAI.LaughlinFock.fourHighestCache_18`, `OAI.LaughlinFock.fourHighestCache_18_0`, `OAI.LaughlinFock.fourHighestCache_18_1`, `OAI.LaughlinFock.fourHighestCache_18_2`, `OAI.LaughlinFock.fourHighestCache_18_3`, `OAI.LaughlinFock.fourHighestCache_18_4`, `OAI.LaughlinFock.fourHighestCache_18_5`, `OAI.LaughlinFock.fourHighestCache_18_6`, `OAI.LaughlinFock.fourHighestCache_18_7`, `OAI.LaughlinFock.fourHighestCache_18_8`, `OAI.LaughlinFock.fourHighestCache_18_9`, `OAI.LaughlinFock.fourHighestCache_19_0`, `OAI.LaughlinFock.fourHighestCache_19_1`, `OAI.LaughlinFock.fourHighestCache_19_10`, `OAI.LaughlinFock.fourHighestCache_19_11`, `OAI.LaughlinFock.fourHighestCache_19_2`, `OAI.LaughlinFock.fourHighestCache_20_13`, `OAI.LaughlinFock.fourSpinCopyEquiv`, `OAI.LaughlinFock.intertwinerSubgroup`, `OAI.LaughlinFock.memoScaledFourTrace`, `OAI.LaughlinFock.memoScaledRowsFourTrace`, `OAI.LaughlinFock.oneParticleMatrix`, `OAI.LaughlinFock.partialHamiltonian`, `OAI.LaughlinFock.scaledFourFactor`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinFock_Certificate17`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate17.lean), [`LaughlinFock_Certificate18`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate18.lean), [`LaughlinFock_Certificate19`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate19.lean), [`LaughlinFock_Certificate20`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate20.lean), [`LaughlinFock_FastTrace`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/FastTrace.lean), [`LaughlinFock_FourCopies`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/FourCopies.lean), [`LaughlinFock_RectangularOrbit`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/RectangularOrbit.lean), [`LaughlinFock_RelativePerturbation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/RelativePerturbation.lean), [`LaughlinFock_TableTrace`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/TableTrace.lean), [`LaughlinFock_WedgeLie`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/WedgeLie.lean).
--
--   **Imports.** It imports the published bundle `Def_LaughlinFock`; the bundles `OAIQ084L000` and `OAIQ084L001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ084L022` and `OAIQ084L029`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L000
import Definitions.Def_OAIQ084L001

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RelativePerturbation
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative Perturbation. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology
open Filter Topology
open Filter Topology
open scoped Kronecker



def partialHamiltonian (Q P : ℕ) : FockMatrix Q :=
  ∑ p ∈ Finset.range P, (pairAnnihilator Q p)ᴴ * pairAnnihilator Q p

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FastTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def scaledFourFactor (D : ℕ) (t : Fin 8) (b c : RowEntry t.val) : ℕ :=
  2 * 2^(53+rowP b+rowP c-(t.val+2*rowFourLevel b c)) *
    t.val.factorial * (rowI b).factorial * (rowI c).factorial *
      ((23).factorial / (rowFourLevel b c-D).factorial)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_TableTrace
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Table Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def memoScaledFourTrace (D : ℕ) (t : Fin 8) (r s : CopyLabel D) : ℤ :=
  -(∑ b : RowEntry t.val, ∑ c : RowEntry t.val, if D ≤ rowFourLevel b c then
    certificateAlphaData t b.val.1 b.val.2 * certificateAlphaData t c.val.1 c.val.2 *
      (scaledFourFactor D t b c : ℤ) *
      memoIntegerCopyPolynomial D (rowFourLevel b c) r.val.val (rowP b) (rowJ b) (rowI c) *
      memoIntegerCopyPolynomial D (rowFourLevel b c) s.val.val (rowP c) (rowJ c) (rowI b)
    else 0)

def memoScaledRowsFourTrace (D : ℕ) (r s : CopyLabel D) : ℤ :=
  ∑ t : Fin 8, memoScaledFourTrace D t r s

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate17
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate17. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_17_5 : List (Occupation 24 × List ℚ) := [
  ({1,2,4,11}, [-1673823191040000, -188305108992000, -14542488576000, 13881466368000, 643778150400, -3592512000000, 2092278988800, 2615348736000, 0]),
  ({1,2,5,10}, [2678117105664000, 167382319104000, -5058256896000, -7461974016000, -146313216000, 1839366144000, -747242496000, -2615348736000, 0]),
  ({1,2,6,9}, [-2678117105664000, -167382319104000, 19773186048000, 2779951104000, -555990220800, -229920768000, -448345497600, 2615348736000, 0]),
  ({1,2,7,8}, [3012881743872000, 138090413260800, -22934596608000, -1225373184000, 1068086476800, -603542016000, 1046139494400, -2615348736000, 0])
]

def fourHighestCache_17_6 : List (Occupation 24 × List ℚ) := [
  ({1,3,4,10}, [-1004293914624000, 20922789888000, 19600745472000, -6419492352000, -497464934400, 1753145856000, -1345036492800, 0, 0]),
  ({1,3,5,9}, [0, 0, -14714929152000, 4682022912000, 702303436800, -1609445376000, 1195587993600, 0, 0]),
  ({1,3,6,8}, [-334764638208000, 29291905843200, 3161410560000, -1554577920000, -512096256000, 833462784000, -597793996800, 0, 0]),
  ({1,4,5,8}, [1339058552832000, -50214695731200, 6667702272000, -1389975552000, -395045683200, 632282112000, -448345497600, 0, 0])
]

def fourHighestCache_17_7 : List (Occupation 24 × List ℚ) := [
  ({1,4,6,7}, [-1004293914624000, 20922789888000, -2471648256000, 603542016000, 555990220800, -661022208000, 448345497600, 0, 0]),
  ({2,3,4,9}, [1004293914624000, -20922789888000, -4885816320000, 1737469440000, -204838502400, -143700480000, 149448499200, 0, 0]),
  ({2,3,5,8}, [-1004293914624000, 20922789888000, 4885816320000, -1737469440000, 204838502400, 143700480000, -149448499200, 0, 0]),
  ({2,3,6,7}, [1339058552832000, -50214695731200, -689762304000, 951035904000, -43893964800, -172440576000, 149448499200, 0, 0])
]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate18
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate18. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_18_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,16}, [0, -14060114804736000, -8034351316992000, -3640565440512000, -753220435968000, 627683696640000, 502146957312000, -1129830653952000, -4268249137152000]),
  ({0,1,3,15}, [0, 14060114804736000, 8034351316992000, 3640565440512000, 753220435968000, -627683696640000, -502146957312000, 1129830653952000, 4268249137152000]),
  ({0,1,4,14}, [0, -17575143505920000, -7364822040576000, -2374736652288000, -338949196185600, 334764638208000, 324303243264000, -596299511808000, -3556874280960000]),
  ({0,1,5,13}, [0, 16068702633984000, 6121410527232000, 1339058552832000, 0, -104613949440000, -149448499200000, 125536739328000, 2845499424768000])
]

def fourHighestCache_18_1 : List (Occupation 24 × List ℚ) := [
  ({0,1,6,12}, [0, -13557967847424000, -4304116776960000, -668724553728000, 101395058688000, 24141680640000, 22417274880000, 125536739328000, -2134124568576000]),
  ({0,1,7,11}, [0, 10042939146240000, 2678117105664000, 234979024896000, -57940033536000, -24141680640000, 41845579776000, -188305108992000, 1422749712384000]),
  ({0,1,8,10}, [0, -5021469573120000, -1339058552832000, -27360571392000, 7900913664000, 24141680640000, -41845579776000, 125536739328000, -711374856192000]),
  ({0,2,3,14}, [0, 3515028701184000, -669529276416000, -1265828788224000, -414271239782400, 292919058432000, 177843714048000, -533531142144000, -711374856192000])
]

def fourHighestCache_18_2 : List (Occupation 24 × List ℚ) := [
  ({0,2,4,13}, [0, 1506440871936000, 1243411513344000, 1035678099456000, 338949196185600, -230150688768000, -174854744064000, 470762772480000, 711374856192000]),
  ({0,2,5,12}, [0, -2510734786560000, -1817293750272000, -670333999104000, -101395058688000, 80472268800000, 127031224320000, -251073478656000, -711374856192000]),
  ({0,2,6,11}, [0, 3515028701184000, 1625999671296000, 433745528832000, -43455025152000, 0, -64262854656000, 62768369664000, 711374856192000]),
  ({0,2,7,10}, [0, -5021469573120000, -1339058552832000, -207618453504000, 50039119872000, 0, 0, 62768369664000, -711374856192000])
]

def fourHighestCache_18_3 : List (Occupation 24 × List ℚ) := [
  ({0,2,8,9}, [0, 5021469573120000, 1339058552832000, 27360571392000, -7900913664000, -24141680640000, 41845579776000, -125536739328000, 711374856192000]),
  ({0,3,4,12}, [0, -4017175658496000, 0, -135193411584000, -162232093900800, 86910050304000, 44834549760000, -156920924160000, 0]),
  ({0,3,5,11}, [0, 4017175658496000, 382588157952000, 70815596544000, 115880067072000, -52306974720000, -52306974720000, 141228831744000, 0]),
  ({0,3,6,10}, [0, -2510734786560000, -286941118464000, -103809226752000, -17118646272000, 0, 49318004736000, -94152554496000, 0])
]

def fourHighestCache_18_4 : List (Occupation 24 × List ℚ) := [
  ({0,3,7,9}, [0, 2008587829248000, 0, 106223394816000, -24229468569600, 16899176448000, -31384184832000, 47076277248000, 0]),
  ({0,4,5,10}, [0, -2510734786560000, -286941118464000, 76448655360000, -59256852480000, 24141680640000, 7472424960000, -31384184832000, 0]),
  ({0,4,6,9}, [0, 2510734786560000, 286941118464000, -50697529344000, 33973928755200, -9656672256000, -13450364928000, 31384184832000, 0]),
  ({0,4,7,8}, [0, -4017175658496000, 0, -32188907520000, 6320730931200, -9656672256000, 20922789888000, -31384184832000, 0])
]

def fourHighestCache_18_5 : List (Occupation 24 × List ℚ) := [
  ({0,5,6,8}, [0, 1004293914624000, -191294078976000, 46673915904000, -18435465216000, 8047226880000, -2988969984000, 0, 0]),
  ({1,2,3,13}, [0, -5021469573120000, -573882236928000, 230150688768000, 75322043596800, -62768369664000, -2988969984000, 62768369664000, 0]),
  ({1,2,4,12}, [0, 5021469573120000, 573882236928000, -230150688768000, -75322043596800, 62768369664000, 2988969984000, -62768369664000, 0]),
  ({1,2,5,11}, [0, -5021469573120000, -191294078976000, 165772873728000, 28970016768000, -28165294080000, -10461394944000, 47076277248000, 0])
]

def fourHighestCache_18_6 : List (Occupation 24 × List ℚ) := [
  ({1,2,6,10}, [0, 4017175658496000, 0, -122317848576000, 10534551552000, 0, 14944849920000, -31384184832000, 0]),
  ({1,2,7,9}, [0, -2008587829248000, 0, 74034487296000, -17908737638400, 7242504192000, -10461394944000, 15692092416000, 0]),
  ({1,3,4,11}, [0, 0, -382588157952000, 64377815040000, 46352026828800, -34603075584000, 7472424960000, 15692092416000, 0]),
  ({1,3,5,10}, [0, 1004293914624000, 191294078976000, -43455025152000, -39504568320000, 28165294080000, -4483454976000, -15692092416000, 0])
]

def fourHighestCache_18_7 : List (Occupation 24 × List ℚ) := [
  ({1,3,6,9}, [0, -2008587829248000, 0, 48283361280000, 7374186086400, -7242504192000, -4483454976000, 15692092416000, 0]),
  ({1,3,7,8}, [0, 2008587829248000, 0, -74034487296000, 17908737638400, -7242504192000, 10461394944000, -15692092416000, 0]),
  ({1,4,5,9}, [0, 0, 0, -25751126016000, 25282923724800, -14485008384000, 5977939968000, 0, 0]),
  ({1,4,6,8}, [0, 502146957312000, -95647039488000, 36212520960000, -21859194470400, 11266117632000, -4483454976000, 0, 0])
]

def fourHighestCache_18_8 : List (Occupation 24 × List ℚ) := [
  ({1,5,6,7}, [0, -1004293914624000, 191294078976000, -46673915904000, 18435465216000, -8047226880000, 2988969984000, 0, 0]),
  ({2,3,4,10}, [0, -1004293914624000, 191294078976000, -20922789888000, -6847458508800, 6437781504000, -2988969984000, 0, 0]),
  ({2,3,5,9}, [0, 1004293914624000, -191294078976000, 20922789888000, 6847458508800, -6437781504000, 2988969984000, 0, 0]),
  ({2,3,6,8}, [0, -502146957312000, 95647039488000, -10461394944000, -3423729254400, 3218890752000, -1494484992000, 0, 0])
]

def fourHighestCache_18_9 : List (Occupation 24 × List ℚ) := [
  ({2,4,5,8}, [0, -502146957312000, 95647039488000, -10461394944000, -3423729254400, 3218890752000, -1494484992000, 0, 0]),
  ({2,4,6,7}, [0, 502146957312000, -95647039488000, 10461394944000, 3423729254400, -3218890752000, 1494484992000, 0, 0]),
  ({3,4,5,7}, [0, 0, 0, 0, 0, 0, 0, 0, 0])
]

def fourHighestCache_18 : List (Occupation 24 × List ℚ) := fourHighestCache_18_0 ++ fourHighestCache_18_1 ++ fourHighestCache_18_2 ++ fourHighestCache_18_3 ++ fourHighestCache_18_4 ++ fourHighestCache_18_5 ++ fourHighestCache_18_6 ++ fourHighestCache_18_7 ++ fourHighestCache_18_8 ++ fourHighestCache_18_9

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate19
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate19. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_19_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,17}, [819503834333184000, 273167944777728000, 166461716348928000, 83230858174464000, 25609494822912000, -6402373705728000, -12804747411456000, 6402373705728000, 51218989645824000, 121645100408832000]),
  ({0,1,3,16}, [-819503834333184000, -273167944777728000, -166461716348928000, -83230858174464000, -25609494822912000, 6402373705728000, 12804747411456000, -6402373705728000, -51218989645824000, -121645100408832000]),
  ({0,1,4,15}, [1434131710083072000, 365562984923136000, 161251941666816000, 59033651668992000, 13369662738432000, -3828870549504000, -7249746696192000, 1977203644416000, 36280117665792000, 121645100408832000]),
  ({0,1,5,14}, [-1434131710083072000, -365562984923136000, -137818416992256000, -37943479461888000, -3577797070848000, 1987665039360000, 2353813862400000, 1537825056768000, -22052620541952000, -121645100408832000])
]

def fourHighestCache_19_1 : List (Occupation 24 × List ℚ) := [
  ({0,1,6,13}, [1843883627249664000, 373597336240128000, 101873063964672000, 21309861500928000, -188305108992000, -1255367393280000, 112086374400000, -2385198047232000, 10670622842880000, 121645100408832000]),
  ({0,1,7,12}, [-1843883627249664000, -373597336240128000, -71744246525952000, -9026574391296000, 593885343744000, 830473814016000, -596299511808000, 1380904132608000, -2134124568576000, -121645100408832000]),
  ({0,1,8,11}, [2048759585832960000, 361545809264640000, 49921776672768000, 2351399694336000, -463520268288000, -275215159296000, 125536739328000, 125536739328000, -3556874280960000, 121645100408832000]),
  ({0,1,9,10}, [-2048759585832960000, -361545809264640000, -36531191144448000, -188305108992000, 568865783808000, -188305108992000, 376610217984000, -1129830653952000, 6402373705728000, -121645100408832000])
]

def fourHighestCache_19_2 : List (Occupation 24 × List ℚ) := [
  ({0,2,3,15}, [-614627875749888000, -92395040145408000, 5209774682112000, 24197206505472000, 12239832084480000, -2573503156224000, -5555000715264000, 4425170061312000, 14938871980032000, 0]),
  ({0,2,4,14}, [0, 0, -23433524674560000, -21090172207104000, -9791865667584000, 1841205510144000, 4895932833792000, -3515028701184000, -14227497123840000, 0]),
  ({0,2,5,13}, [-409751917166592000, -8034351316992000, 35945353027584000, 16633617960960000, 3766102179840000, -732297646080000, -2465900236800000, 847372990464000, 11381997699072000, 0]),
  ({0,2,6,12}, [0, 0, -30128817438720000, -12283287109632000, -405580234752000, 424893579264000, 484213137408000, 1004293914624000, -8536498274304000, 0])
]

def fourHighestCache_19_10 : List (Occupation 24 × List ℚ) := [
  ({2,3,6,9}, [614627875749888000, -4017175658496000, -2196892938240000, 253487646720000, 88226869248000, -38626689024000, -13450364928000, 31384184832000, 0, 0]),
  ({2,3,7,8}, [-614627875749888000, 4017175658496000, 2866422214656000, -639754536960000, 85593231360000, -25751126016000, 31384184832000, -31384184832000, 0, 0]),
  ({2,4,5,9}, [-204875958583296000, 12051526975488000, -271996268544000, -354882705408000, 201473298432000, -78862823424000, 22417274880000, 0, 0, 0]),
  ({2,4,6,8}, [0, 0, -669529276416000, 386266890240000, -173820100608000, 64377815040000, -17933819904000, 0, 0, 0])
]

def fourHighestCache_19_11 : List (Occupation 24 × List ℚ) := [
  ({2,5,6,7}, [204875958583296000, -12051526975488000, 1611054821376000, -417651075072000, 146166902784000, -49892806656000, 13450364928000, 0, 0, 0]),
  ({3,4,5,8}, [204875958583296000, -12051526975488000, 941525544960000, -31384184832000, -27653197824000, 14485008384000, -4483454976000, 0, 0, 0]),
  ({3,4,6,7}, [-204875958583296000, 12051526975488000, -941525544960000, 31384184832000, 27653197824000, -14485008384000, 4483454976000, 0, 0, 0])
]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate20
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate20. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_20_13 : List (Occupation 24 × List ℚ) := [
  ({3,4,6,8}, [0, 68291986194432000, -17575143505920000, 4582090985472000, -1245710721024000, 318670184448000, -62768369664000, 0, 0, 0]),
  ({3,5,6,7}, [0, -68291986194432000, 17575143505920000, -4582090985472000, 1245710721024000, -318670184448000, 62768369664000, 0, 0, 0])
]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_WedgeLie
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Wedge Lie. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder


def oneParticleMatrix (Q : ℕ) : Matrix (SectorOccupation Q 1) (Orbital Q) ℂ := fun S i =>
  if S.val={i} then 1 else 0

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourCopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Copies. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourSpinCopyEquiv {Q : ℕ} (_hQ : 1 ≤ Q) : FourSpinIndex Q ≃ ValidFourCopy Q where
  toFun b := by
    have hr := b.1.val.isLt
    have hz := b.2.isLt
    have hr0 := b.1.property.pos
    refine ⟨⟨⟨b.1.val.val+b.2.val, by omega⟩,
      ⟨⟨b.1.val.val, by dsimp; omega⟩, b.1.property⟩⟩, ?_⟩
    dsimp
    omega
  invFun b := by
    have hr := b.val.2.val.isLt
    have hd := b.property
    have hr0 := b.val.2.property.pos
    refine ⟨⟨⟨b.val.2.val.val, by omega⟩, b.val.2.property⟩,
      ⟨b.val.1.val-b.val.2.val.val, ?_⟩⟩
    dsimp only
    omega
  left_inv b := by
    apply Sigma.ext
    · apply Subtype.ext
      apply Fin.ext
      rfl
    · apply (Fin.heq_ext_iff rfl).mpr
      dsimp
      omega
  right_inv b := by
    rcases b with ⟨⟨⟨D,hD⟩,⟨⟨r,hr⟩,hor⟩⟩,h⟩
    have he : r+(D-r)=D := by dsimp only at hr; omega
    apply Subtype.ext
    dsimp
    have hs {d e : Fin (2*Q)} (u : CopyLabel d.val) (v : CopyLabel e.val)
        (hde : d=e) (huv : u.val.val=v.val.val) : (⟨d,u⟩ : (D : Fin (2*Q)) × CopyLabel D.val) = ⟨e,v⟩ := by
      subst e
      congr 1
      exact Subtype.ext (Fin.ext huv)
    exact hs _ _ (Fin.ext he) rfl


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RectangularOrbit
attribute [-instance] _root_.OAI.LaughlinFock.rotationHaar_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangular Orbit. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open NormedSpace MeasureTheory Topology

section Groups
variable {J σ : Type*} {I : J → Type*}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]

 
def intertwinerSubgroup {i j : J} (C : Matrix (I j) (I i) ℂ) :
    Subgroup (UnitaryFamily I) where
  carrier := {g | (g j).val * C = C * (g i).val}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change (g j).val * C = C * (g i).val at hg
    change (h j).val * C = C * (h i).val at hh
    change ((g j).val * (h j).val) * C = C * ((g i).val * (h i).val)
    rw [Matrix.mul_assoc, hh, ← Matrix.mul_assoc, hg, Matrix.mul_assoc]
  inv_mem' := by
    intro g hg
    change (g j).val * C = C * (g i).val at hg
    have he := congrArg (fun A => ((g j)⁻¹).val * A * ((g i)⁻¹).val) hg
    change ((g j)⁻¹).val * C = C * ((g i)⁻¹).val
    have hj : ((g j)⁻¹).val * (g j).val = 1 := by
      exact congrArg Subtype.val (inv_mul_cancel (g j))
    have hi : (g i).val * ((g i)⁻¹).val = 1 := by
      exact congrArg Subtype.val (mul_inv_cancel (g i))
    have heL : ((g j)⁻¹).val * ((g j).val*C) * ((g i)⁻¹).val = C*((g i)⁻¹).val := by
      rw [← Matrix.mul_assoc ((g j)⁻¹).val (g j).val C, hj, Matrix.one_mul]
    have heR : ((g j)⁻¹).val * (C*(g i).val) * ((g i)⁻¹).val = ((g j)⁻¹).val*C := by
      rw [Matrix.mul_assoc ((g j)⁻¹).val (C*(g i).val), Matrix.mul_assoc C, hi, Matrix.mul_one]
    rw [heL, heR] at he
    exact he.symm

open scoped Matrix.Norms.Elementwise

end Groups
end LaughlinFock
end

end OAI
end


