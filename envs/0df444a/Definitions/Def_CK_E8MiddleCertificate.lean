-- Prove2me | Definitions.Def_CK_E8MiddleCertificate
-- name    : CK_E8MiddleCertificate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T11:25:16.379574+00:00
-- url     : https://prove2.me/theorems/c2d6af9a-ba01-4538-a9d2-e811b64d73fc
-- title:
--   Courtade–Kumar proof module `E8MiddleCertificate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `E8MiddleCertificate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `E8MiddleCertificate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module E8MiddleCertificate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/E8MiddleCertificate.lean)

import Definitions.Def_CK_E8CompactCertificate

-- ===== source module E8MiddleCertificate =====
section

namespace GeneralCK.E8RatioMonotonicity.MiddleCertificate
open Certificates DyadicInterval Certificates.E8TAxisStableInterval
open Certificates.E8HistoricalLogConvexityBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def p : ℕ := 96
def wl : FastLogBoxWitness := ⟨0,32,0,32⟩
def c0 : Inputs p := ⟨⟨21625265061266486677144076288, 21625265061266486677144076288⟩, ⟨45898543540327926721956028300, 45898543540327926721956036493⟩, ⟨36206878044363313089274413886, 36206878044363313089274419147⟩, ⟨0, 0⟩⟩
def c0Exp : ExpWitness p := ⟨45898543540327926721956028300, scale p, 45898543540327926721956036493, scale p, 0,32,0,32,⟨-43250530122532973354288159687, -43250530122532973354288159616⟩,⟨-43250530122532973354288145545, -43250530122532973354288145476⟩⟩
theorem c0_primitives :
 expBoxCheck ((ofInt p (-2)).mul c0.alpha) c0.expNegTwo c0Exp = true ∧
 logBoxCheck ((ofInt p 1).add c0.expNegTwo) c0.logOnePlusExp wl = true := by decide +kernel
theorem c0_denominators : CompactDenominators c0 := by decide +kernel
def w0 : Inputs p := ⟨⟨19807040628566084398385987584, 23443489493966888955902164992⟩, ⟨43839487306287060870817817135, 48054309677596482279189099350⟩, ⟨34892271318796476781663157218, 37560248346893815527215715261⟩, ⟨0, 0⟩⟩
def w0Exp : ExpWitness p := ⟨43839487306287060870817817135, scale p, 48054309677596482279189099350, scale p, 0,32,0,32,⟨-46886978987933777911804337437, -46886978987933777911804337354⟩,⟨-39614081257132168796771968457, -39614081257132168796771968386⟩⟩
theorem w0_primitives :
 expBoxCheck ((ofInt p (-2)).mul w0.alpha) w0.expNegTwo w0Exp = true ∧
 logBoxCheck ((ofInt p 1).add w0.expNegTwo) w0.logOnePlusExp wl = true := by decide +kernel
theorem w0_denominators : CompactDenominators w0 := by decide +kernel
theorem checked0 : centeredTaylorCheck (compactBox c0) (compactBox w0)
 (w0.alpha.sub c0.alpha) = true := by decide +kernel
theorem positive0 : PositiveInterval p 19807040628566084398385987584 23443489493966888955902164992 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 21625265061266486677144076288) rfl (by decide +kernel)
  c0_primitives.1 c0_primitives.2 w0_primitives.1 w0_primitives.2
  c0_denominators w0_denominators checked0 ha
def c1 : Inputs p := ⟨⟨25261713926667291234660253696, 25261713926667291234660253696⟩, ⟨41872802468981636221824457645, 41872802468981636221824465838⟩, ⟨33615938602599366653638371014, 33615938602599366653638376447⟩, ⟨0, 0⟩⟩
def c1Exp : ExpWitness p := ⟨41872802468981636221824457645, scale p, 41872802468981636221824465838, scale p, 0,32,0,32,⟨-50523427853334582469320515187, -50523427853334582469320515114⟩,⟨-50523427853334582469320499681, -50523427853334582469320499614⟩⟩
theorem c1_primitives :
 expBoxCheck ((ofInt p (-2)).mul c1.alpha) c1.expNegTwo c1Exp = true ∧
 logBoxCheck ((ofInt p 1).add c1.expNegTwo) c1.logOnePlusExp wl = true := by decide +kernel
theorem c1_denominators : CompactDenominators c1 := by decide +kernel
def w1 : Inputs p := ⟨⟨23443489493966888955902164992, 27079938359367693513418342400⟩, ⟨39994345151817223186156421277, 43839487306287060870817825328⟩, ⟨32377360023826426599202601706, 34892271318796476781663162567⟩, ⟨0, 0⟩⟩
def w1Exp : ExpWitness p := ⟨39994345151817223186156421277, scale p, 43839487306287060870817825328, scale p, 0,32,0,32,⟨-54159876718735387026836692957, -54159876718735387026836692882⟩,⟨-46886978987933777911804322627, -46886978987933777911804322548⟩⟩
theorem w1_primitives :
 expBoxCheck ((ofInt p (-2)).mul w1.alpha) w1.expNegTwo w1Exp = true ∧
 logBoxCheck ((ofInt p 1).add w1.expNegTwo) w1.logOnePlusExp wl = true := by decide +kernel
theorem w1_denominators : CompactDenominators w1 := by decide +kernel
theorem checked1 : centeredTaylorCheck (compactBox c1) (compactBox w1)
 (w1.alpha.sub c1.alpha) = true := by decide +kernel
theorem positive1 : PositiveInterval p 23443489493966888955902164992 27079938359367693513418342400 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 25261713926667291234660253696) rfl (by decide +kernel)
  c1_primitives.1 c1_primitives.2 w1_primitives.1 w1_primitives.2
  c1_denominators w1_denominators checked1 ha
def c2 : Inputs p := ⟨⟨28898162792068095792176431104, 28898162792068095792176431104⟩, ⟨38200157376798273844790597650, 38200157376798273844790605843⟩, ⟨31175987302690258637811572922, 31175987302690258637811578527⟩, ⟨0, 0⟩⟩
def c2Exp : ExpWitness p := ⟨38200157376798273844790597650, scale p, 38200157376798273844790605843, scale p, 1,32,1,32,⟨-57796325584136191584352870804, -57796325584136191584352870658⟩,⟨-57796325584136191584352853814, -57796325584136191584352853666⟩⟩
theorem c2_primitives :
 expBoxCheck ((ofInt p (-2)).mul c2.alpha) c2.expNegTwo c2Exp = true ∧
 logBoxCheck ((ofInt p 1).add c2.expNegTwo) c2.logOnePlusExp wl = true := by decide +kernel
theorem c2_denominators : CompactDenominators c2 := by decide +kernel
def w2 : Inputs p := ⟨⟨27079938359367693513418342400, 30716387224768498070934519808⟩, ⟨36486458724924304445106195123, 39994345151817223186156429470⟩, ⟨30011245707446056790641329434, 32377360023826426599202607221⟩, ⟨0, 0⟩⟩
def w2Exp : ExpWitness p := ⟨36486458724924304445106195123, scale p, 39994345151817223186156429470, scale p, 1,32,0,32,⟨-61432774449536996141869048610, -61432774449536996141869048466⟩,⟨-54159876718735387026836676729, -54159876718735387026836676650⟩⟩
theorem w2_primitives :
 expBoxCheck ((ofInt p (-2)).mul w2.alpha) w2.expNegTwo w2Exp = true ∧
 logBoxCheck ((ofInt p 1).add w2.expNegTwo) w2.logOnePlusExp wl = true := by decide +kernel
theorem w2_denominators : CompactDenominators w2 := by decide +kernel
theorem checked2 : centeredTaylorCheck (compactBox c2) (compactBox w2)
 (w2.alpha.sub c2.alpha) = true := by decide +kernel
theorem positive2 : PositiveInterval p 27079938359367693513418342400 30716387224768498070934519808 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 28898162792068095792176431104) rfl (by decide +kernel)
  c2_primitives.1 c2_primitives.2 w2_primitives.1 w2_primitives.2
  c2_denominators w2_denominators checked2 ha
def c3 : Inputs p := ⟨⟨32534611657468900349692608512, 32534611657468900349692608512⟩, ⟨34849638370709348601576297125, 34849638370709348601576305318⟩, ⟨28882536055859979088768816634, 28882536055859979088768822399⟩, ⟨0, 0⟩⟩
def c3Exp : ExpWitness p := ⟨34849638370709348601576297125, scale p, 34849638370709348601576305318, scale p, 1,32,1,32,⟨-65069223314937800699385226434, -65069223314937800699385226290⟩,⟨-65069223314937800699385207808, -65069223314937800699385207664⟩⟩
theorem c3_primitives :
 expBoxCheck ((ofInt p (-2)).mul c3.alpha) c3.expNegTwo c3Exp = true ∧
 logBoxCheck ((ofInt p 1).add c3.expNegTwo) c3.logOnePlusExp wl = true := by decide +kernel
theorem c3_denominators : CompactDenominators c3 := by decide +kernel
def w3 : Inputs p := ⟨⟨30716387224768498070934519808, 34352836090169302628450697216⟩, ⟨33286247474041123522594794171, 36486458724924304445106203316⟩, ⟨27789236748663572592878355354, 30011245707446056790641335119⟩, ⟨0, 0⟩⟩
def w3Exp : ExpWitness p := ⟨33286247474041123522594794171, scale p, 36486458724924304445106203316, scale p, 1,32,1,32,⟨-68705672180338605256901404280, -68705672180338605256901404136⟩,⟨-61432774449536996141869030820, -61432774449536996141869030676⟩⟩
theorem w3_primitives :
 expBoxCheck ((ofInt p (-2)).mul w3.alpha) w3.expNegTwo w3Exp = true ∧
 logBoxCheck ((ofInt p 1).add w3.expNegTwo) w3.logOnePlusExp wl = true := by decide +kernel
theorem w3_denominators : CompactDenominators w3 := by decide +kernel
theorem checked3 : centeredTaylorCheck (compactBox c3) (compactBox w3)
 (w3.alpha.sub c3.alpha) = true := by decide +kernel
theorem positive3 : PositiveInterval p 30716387224768498070934519808 34352836090169302628450697216 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 32534611657468900349692608512) rfl (by decide +kernel)
  c3_primitives.1 c3_primitives.2 w3_primitives.1 w3_primitives.2
  c3_denominators w3_denominators checked3 ha
def c4 : Inputs p := ⟨⟨36171060522869704907208785920, 36171060522869704907208785920⟩, ⟨31792991913349279377974984574, 31792991913349279377974992767⟩, ⟨26730705821730198673157738398, 26730705821730198673157744321⟩, ⟨0, 0⟩⟩
def c4Exp : ExpWitness p := ⟨31792991913349279377974984574, scale p, 31792991913349279377974992767, scale p, 1,32,1,32,⟨-72342121045739409814417582140, -72342121045739409814417581996⟩,⟨-72342121045739409814417561724, -72342121045739409814417561580⟩⟩
theorem c4_primitives :
 expBoxCheck ((ofInt p (-2)).mul c4.alpha) c4.expNegTwo c4Exp = true ∧
 logBoxCheck ((ofInt p 1).add c4.expNegTwo) c4.logOnePlusExp wl = true := by decide +kernel
theorem c4_denominators : CompactDenominators c4 := by decide +kernel
def w4 : Inputs p := ⟨⟨34352836090169302628450697216, 37989284955570107185966874624⟩, ⟨30366725344771252593011623300, 33286247474041123522594802364⟩, ⟨25706283004171616655893625570, 27789236748663572592878361195⟩, ⟨0, 0⟩⟩
def w4Exp : ExpWitness p := ⟨30366725344771252593011623300, scale p, 33286247474041123522594802364, scale p, 1,32,1,32,⟨-75978569911140214371933760032, -75978569911140214371933759882⟩,⟨-68705672180338605256901384782, -68705672180338605256901384634⟩⟩
theorem w4_primitives :
 expBoxCheck ((ofInt p (-2)).mul w4.alpha) w4.expNegTwo w4Exp = true ∧
 logBoxCheck ((ofInt p 1).add w4.expNegTwo) w4.logOnePlusExp wl = true := by decide +kernel
theorem w4_denominators : CompactDenominators w4 := by decide +kernel
theorem checked4 : centeredTaylorCheck (compactBox c4) (compactBox w4)
 (w4.alpha.sub c4.alpha) = true := by decide +kernel
theorem positive4 : PositiveInterval p 34352836090169302628450697216 37989284955570107185966874624 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 36171060522869704907208785920) rfl (by decide +kernel)
  c4_primitives.1 c4_primitives.2 w4_primitives.1 w4_primitives.2
  c4_denominators w4_denominators checked4 ha
def c5 : Inputs p := ⟨⟨39807509388270509464724963328, 39807509388270509464724963328⟩, ⟨29004442572691132681884303642, 29004442572691132681884311835⟩, ⟨24715291770129413861875085930, 24715291770129413861875091995⟩, ⟨0, 0⟩⟩
def c5Exp : ExpWitness p := ⟨29004442572691132681884303642, scale p, 29004442572691132681884311835, scale p, 1,32,1,32,⟨-79615018776541018929449937938, -79615018776541018929449937796⟩,⟨-79615018776541018929449915558, -79615018776541018929449915416⟩⟩
theorem c5_primitives :
 expBoxCheck ((ofInt p (-2)).mul c5.alpha) c5.expNegTwo c5Exp = true ∧
 logBoxCheck ((ofInt p 1).add c5.expNegTwo) c5.logOnePlusExp wl = true := by decide +kernel
theorem c5_denominators : CompactDenominators c5 := by decide +kernel
def w5 : Inputs p := ⟨⟨37989284955570107185966874624, 41625733820970911743483052032⟩, ⟨27703273217683026515376956560, 30366725344771252593011631493⟩, ⟨23757041372711719094514142896, 25706283004171616655893631565⟩, ⟨0, 0⟩⟩
def w5Exp : ExpWitness p := ⟨27703273217683026515376956560, scale p, 30366725344771252593011631493, scale p, 1,32,1,32,⟨-83251467641941823486966115868, -83251467641941823486966115722⟩,⟨-75978569911140214371933738658, -75978569911140214371933738506⟩⟩
theorem w5_primitives :
 expBoxCheck ((ofInt p (-2)).mul w5.alpha) w5.expNegTwo w5Exp = true ∧
 logBoxCheck ((ofInt p 1).add w5.expNegTwo) w5.logOnePlusExp wl = true := by decide +kernel
theorem w5_denominators : CompactDenominators w5 := by decide +kernel
theorem checked5 : centeredTaylorCheck (compactBox c5) (compactBox w5)
 (w5.alpha.sub c5.alpha) = true := by decide +kernel
theorem positive5 : PositiveInterval p 37989284955570107185966874624 41625733820970911743483052032 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 39807509388270509464724963328) rfl (by decide +kernel)
  c5_primitives.1 c5_primitives.2 w5_primitives.1 w5_primitives.2
  c5_denominators w5_denominators checked5 ha
def c6 : Inputs p := ⟨⟨43443958253671314022241140736, 43443958253671314022241140736⟩, ⟨26460475668517046027807954637, 26460475668517046027807962830⟩, ⟨22830828849284859925956064516, 22830828849284859925956070731⟩, ⟨0, 0⟩⟩
def c6Exp : ExpWitness p := ⟨26460475668517046027807954637, scale p, 26460475668517046027807962830, scale p, 1,32,1,32,⟨-86887916507342628044482293824, -86887916507342628044482293674⟩,⟨-86887916507342628044482269290, -86887916507342628044482269142⟩⟩
theorem c6_primitives :
 expBoxCheck ((ofInt p (-2)).mul c6.alpha) c6.expNegTwo c6Exp = true ∧
 logBoxCheck ((ofInt p 1).add c6.expNegTwo) c6.logOnePlusExp wl = true := by decide +kernel
theorem c6_denominators : CompactDenominators c6 := by decide +kernel
def w6 : Inputs p := ⟨⟨41625733820970911743483052032, 45262182686371716300999229440⟩, ⟨25273431305484575663460677432, 27703273217683026515376964753⟩, ⟨21935940988156310578293929094, 23757041372711719094514149039⟩, ⟨0, 0⟩⟩
def w6Exp : ExpWitness p := ⟨25273431305484575663460677432, scale p, 27703273217683026515376964753, scale p, 1,32,1,32,⟨-90524365372743432601998471814, -90524365372743432601998471662⟩,⟨-83251467641941823486966092434, -83251467641941823486966092288⟩⟩
theorem w6_primitives :
 expBoxCheck ((ofInt p (-2)).mul w6.alpha) w6.expNegTwo w6Exp = true ∧
 logBoxCheck ((ofInt p 1).add w6.expNegTwo) w6.logOnePlusExp wl = true := by decide +kernel
theorem w6_denominators : CompactDenominators w6 := by decide +kernel
theorem checked6 : centeredTaylorCheck (compactBox c6) (compactBox w6)
 (w6.alpha.sub c6.alpha) = true := by decide +kernel
theorem positive6 : PositiveInterval p 41625733820970911743483052032 45262182686371716300999229440 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 43443958253671314022241140736) rfl (by decide +kernel)
  c6_primitives.1 c6_primitives.2 w6_primitives.1 w6_primitives.2
  c6_denominators w6_denominators checked6 ha
def c7 : Inputs p := ⟨⟨47080407119072118579757318144, 47080407119072118579757318144⟩, ⟨24139638982871155468811041157, 24139638982871155468811049350⟩, ⟨21071656247563501670560920730, 21071656247563501670560927079⟩, ⟨0, 0⟩⟩
def c7Exp : ExpWitness p := ⟨24139638982871155468811041157, scale p, 24139638982871155468811049350, scale p, 1,32,1,32,⟨-94160814238144237159514649822, -94160814238144237159514649676⟩,⟨-94160814238144237159514622930, -94160814238144237159514622784⟩⟩
theorem c7_primitives :
 expBoxCheck ((ofInt p (-2)).mul c7.alpha) c7.expNegTwo c7Exp = true ∧
 logBoxCheck ((ofInt p 1).add c7.expNegTwo) c7.logOnePlusExp wl = true := by decide +kernel
theorem c7_denominators : CompactDenominators c7 := by decide +kernel
def w7 : Inputs p := ⟨⟨45262182686371716300999229440, 48898631551772520858515406848⟩, ⟨23056709758951349203221369793, 25273431305484575663460685625⟩, ⟨20237246618797304515305903586, 21935940988156310578293935383⟩, ⟨0, 0⟩⟩
def w7Exp : ExpWitness p := ⟨23056709758951349203221369793, scale p, 25273431305484575663460685625, scale p, 1,32,1,32,⟨-97797263103545041717030827866, -97797263103545041717030827714⟩,⟨-90524365372743432601998446128, -90524365372743432601998445980⟩⟩
theorem w7_primitives :
 expBoxCheck ((ofInt p (-2)).mul w7.alpha) w7.expNegTwo w7Exp = true ∧
 logBoxCheck ((ofInt p 1).add w7.expNegTwo) w7.logOnePlusExp wl = true := by decide +kernel
theorem w7_denominators : CompactDenominators w7 := by decide +kernel
theorem checked7 : centeredTaylorCheck (compactBox c7) (compactBox w7)
 (w7.alpha.sub c7.alpha) = true := by decide +kernel
theorem positive7 : PositiveInterval p 45262182686371716300999229440 48898631551772520858515406848 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 47080407119072118579757318144) rfl (by decide +kernel)
  c7_primitives.1 c7_primitives.2 w7_primitives.1 w7_primitives.2
  c7_denominators w7_denominators checked7 ha
def c8 : Inputs p := ⟨⟨50716855984472923137273495552, 50716855984472923137273495552⟩, ⟨22022361862401504679913595103, 22022361862401504679913603296⟩, ⟨19431979426224422205899223038, 19431979426224422205899229523⟩, ⟨0, 0⟩⟩
def c8Exp : ExpWitness p := ⟨22022361862401504679913595103, scale p, 22022361862401504679913603296, scale p, 1,32,1,32,⟨-101433711968945846274547005928, -101433711968945846274547005782⟩,⟨-101433711968945846274546976454, -101433711968945846274546976310⟩⟩
theorem c8_primitives :
 expBoxCheck ((ofInt p (-2)).mul c8.alpha) c8.expNegTwo c8Exp = true ∧
 logBoxCheck ((ofInt p 1).add c8.expNegTwo) c8.logOnePlusExp wl = true := by decide +kernel
theorem c8_denominators : CompactDenominators c8 := by decide +kernel
def w8 : Inputs p := ⟨⟨48898631551772520858515406848, 52535080417173325416031584256⟩, ⟨21034415884524454660174730819, 23056709758951349203221377986⟩, ⟨18655119057915595556523218680, 20237246618797304515305910003⟩, ⟨0, 0⟩⟩
def w8Exp : ExpWitness p := ⟨21034415884524454660174730819, scale p, 23056709758951349203221377986, scale p, 1,32,1,32,⟨-105070160834346650832063184026, -105070160834346650832063183874⟩,⟨-97797263103545041717030799712, -97797263103545041717030799558⟩⟩
theorem w8_primitives :
 expBoxCheck ((ofInt p (-2)).mul w8.alpha) w8.expNegTwo w8Exp = true ∧
 logBoxCheck ((ofInt p 1).add w8.expNegTwo) w8.logOnePlusExp wl = true := by decide +kernel
theorem w8_denominators : CompactDenominators w8 := by decide +kernel
theorem checked8 : centeredTaylorCheck (compactBox c8) (compactBox w8)
 (w8.alpha.sub c8.alpha) = true := by decide +kernel
theorem positive8 : PositiveInterval p 48898631551772520858515406848 52535080417173325416031584256 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 50716855984472923137273495552) rfl (by decide +kernel)
  c8_primitives.1 c8_primitives.2 w8_primitives.1 w8_primitives.2
  c8_denominators w8_denominators checked8 ha
def c9 : Inputs p := ⟨⟨54353304849873727694789672960, 54353304849873727694789672960⟩, ⟨20090790187156000608351285356, 20090790187156000608351293549⟩, ⟨17905928621523648165613028926, 17905928621523648165613035535⟩, ⟨0, 0⟩⟩
def c9Exp : ExpWitness p := ⟨20090790187156000608351285356, scale p, 20090790187156000608351293549, scale p, 1,32,1,32,⟨-108706609699747455389579362158, -108706609699747455389579362010⟩,⟨-108706609699747455389579329848, -108706609699747455389579329700⟩⟩
theorem c9_primitives :
 expBoxCheck ((ofInt p (-2)).mul c9.alpha) c9.expNegTwo c9Exp = true ∧
 logBoxCheck ((ofInt p 1).add c9.expNegTwo) c9.logOnePlusExp wl = true := by decide +kernel
theorem c9_denominators : CompactDenominators c9 := by decide +kernel
def w9 : Inputs p := ⟨⟨52535080417173325416031584256, 56171529282574129973547761664⟩, ⟨19189496516577470988514500260, 21034415884524454660174739012⟩, ⟨17183671520975384939707679492, 18655119057915595556523225229⟩, ⟨0, 0⟩⟩
def w9Exp : ExpWitness p := ⟨19189496516577470988514500260, scale p, 21034415884524454660174739012, scale p, 2,32,1,32,⟨-112343058565148259947095540385, -112343058565148259947095540166⟩,⟨-105070160834346650832063153164, -105070160834346650832063153014⟩⟩
theorem w9_primitives :
 expBoxCheck ((ofInt p (-2)).mul w9.alpha) w9.expNegTwo w9Exp = true ∧
 logBoxCheck ((ofInt p 1).add w9.expNegTwo) w9.logOnePlusExp wl = true := by decide +kernel
theorem w9_denominators : CompactDenominators w9 := by decide +kernel
theorem checked9 : centeredTaylorCheck (compactBox c9) (compactBox w9)
 (w9.alpha.sub c9.alpha) = true := by decide +kernel
theorem positive9 : PositiveInterval p 52535080417173325416031584256 56171529282574129973547761664 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 54353304849873727694789672960) rfl (by decide +kernel)
  c9_primitives.1 c9_primitives.2 w9_primitives.1 w9_primitives.2
  c9_denominators w9_denominators checked9 ha
def c10 : Inputs p := ⟨⟨57989753715274532252305850368, 57989753715274532252305850368⟩, ⟨18328635814192708087109267428, 18328635814192708087109275621⟩, ⟨16487612950434004018099030528, 16487612950434004018099037255⟩, ⟨0, 0⟩⟩
def c10Exp : ExpWitness p := ⟨18328635814192708087109267428, scale p, 18328635814192708087109275621, scale p, 2,32,2,32,⟨-115979507430549064504611718587, -115979507430549064504611718366⟩,⟨-115979507430549064504611683173, -115979507430549064504611682950⟩⟩
theorem c10_primitives :
 expBoxCheck ((ofInt p (-2)).mul c10.alpha) c10.expNegTwo c10Exp = true ∧
 logBoxCheck ((ofInt p 1).add c10.expNegTwo) c10.logOnePlusExp wl = true := by decide +kernel
theorem c10_denominators : CompactDenominators c10 := by decide +kernel
def w10 : Inputs p := ⟨⟨56171529282574129973547761664, 59807978147974934531063939072⟩, ⟨17506394215142427164521600486, 19189496516577470988514508453⟩, ⟨15817021302845169991358396856, 17183671520975384939707686163⟩, ⟨0, 0⟩⟩
def w10Exp : ExpWitness p := ⟨17506394215142427164521600486, scale p, 19189496516577470988514508453, scale p, 2,32,2,32,⟨-119615956295949869062127896817, -119615956295949869062127896600⟩,⟨-112343058565148259947095506559, -112343058565148259947095506340⟩⟩
theorem w10_primitives :
 expBoxCheck ((ofInt p (-2)).mul w10.alpha) w10.expNegTwo w10Exp = true ∧
 logBoxCheck ((ofInt p 1).add w10.expNegTwo) w10.logOnePlusExp wl = true := by decide +kernel
theorem w10_denominators : CompactDenominators w10 := by decide +kernel
theorem checked10 : centeredTaylorCheck (compactBox c10) (compactBox w10)
 (w10.alpha.sub c10.alpha) = true := by decide +kernel
theorem positive10 : PositiveInterval p 56171529282574129973547761664 59807978147974934531063939072 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 57989753715274532252305850368) rfl (by decide +kernel)
  c10_primitives.1 c10_primitives.2 w10_primitives.1 w10_primitives.2
  c10_denominators w10_denominators checked10 ha
def c11 : Inputs p := ⟨⟨61626202580675336809822027776, 61626202580675336809822027776⟩, ⟨16721039226424882628163093545, 16721039226424882628163101738⟩, ⟨15171169491192837054381513154, 15171169491192837054381519997⟩, ⟨0, 0⟩⟩
def c11Exp : ExpWitness p := ⟨16721039226424882628163093545, scale p, 16721039226424882628163101738, scale p, 2,32,2,32,⟨-123252405161350673619644075103, -123252405161350673619644074876⟩,⟨-123252405161350673619644036283, -123252405161350673619644036056⟩⟩
theorem c11_primitives :
 expBoxCheck ((ofInt p (-2)).mul c11.alpha) c11.expNegTwo c11Exp = true ∧
 logBoxCheck ((ofInt p 1).add c11.expNegTwo) c11.logOnePlusExp wl = true := by decide +kernel
theorem c11_denominators : CompactDenominators c11 := by decide +kernel
def w11 : Inputs p := ⟨⟨59807978147974934531063939072, 63444427013375739088580116480⟩, ⟨15970916076470002247605537366, 17506394215142427164521608679⟩, ⟨14549336181354322691838139092, 15817021302845169991358403635⟩, ⟨0, 0⟩⟩
def w11Exp : ExpWitness p := ⟨15970916076470002247605537366, scale p, 17506394215142427164521608679, scale p, 2,32,2,32,⟨-126888854026751478177160253421, -126888854026751478177160253196⟩,⟨-119615956295949869062127859739, -119615956295949869062127859518⟩⟩
theorem w11_primitives :
 expBoxCheck ((ofInt p (-2)).mul w11.alpha) w11.expNegTwo w11Exp = true ∧
 logBoxCheck ((ofInt p 1).add w11.expNegTwo) w11.logOnePlusExp wl = true := by decide +kernel
theorem w11_denominators : CompactDenominators w11 := by decide +kernel
theorem checked11 : centeredTaylorCheck (compactBox c11) (compactBox w11)
 (w11.alpha.sub c11.alpha) = true := by decide +kernel
theorem positive11 : PositiveInterval p 59807978147974934531063939072 63444427013375739088580116480 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 61626202580675336809822027776) rfl (by decide +kernel)
  c11_primitives.1 c11_primitives.2 w11_primitives.1 w11_primitives.2
  c11_denominators w11_denominators checked11 ha
def c12 : Inputs p := ⟨⟨65262651446076141367338205184, 65262651446076141367338205184⟩, ⟨15254444228475409135155733459, 15254444228475409135155741652⟩, ⟨13950806936153396946910159062, 13950806936153396946910165999⟩, ⟨0, 0⟩⟩
def c12Exp : ExpWitness p := ⟨15254444228475409135155733459, scale p, 15254444228475409135155741652, scale p, 2,32,2,32,⟨-130525302892152282734676431781, -130525302892152282734676431558⟩,⟨-130525302892152282734676389227, -130525302892152282734676389004⟩⟩
theorem c12_primitives :
 expBoxCheck ((ofInt p (-2)).mul c12.alpha) c12.expNegTwo c12Exp = true ∧
 logBoxCheck ((ofInt p 1).add c12.expNegTwo) c12.logOnePlusExp wl = true := by decide +kernel
theorem c12_denominators : CompactDenominators c12 := by decide +kernel
def w12 : Inputs p := ⟨⟨63444427013375739088580116480, 67080875878776543646096293888⟩, ⟨14570114050157803478286371478, 15970916076470002247605545559⟩, ⟨13374875270861943874268133858, 14549336181354322691838145983⟩, ⟨0, 0⟩⟩
def w12Exp : ExpWitness p := ⟨14570114050157803478286371478, scale p, 15970916076470002247605545559, scale p, 2,32,2,32,⟨-134161751757553087292192610187, -134161751757553087292192609962⟩,⟨-126888854026751478177160212777, -126888854026751478177160212552⟩⟩
theorem w12_primitives :
 expBoxCheck ((ofInt p (-2)).mul w12.alpha) w12.expNegTwo w12Exp = true ∧
 logBoxCheck ((ofInt p 1).add w12.expNegTwo) w12.logOnePlusExp wl = true := by decide +kernel
theorem w12_denominators : CompactDenominators w12 := by decide +kernel
theorem checked12 : centeredTaylorCheck (compactBox c12) (compactBox w12)
 (w12.alpha.sub c12.alpha) = true := by decide +kernel
theorem positive12 : PositiveInterval p 63444427013375739088580116480 67080875878776543646096293888 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 65262651446076141367338205184) rfl (by decide +kernel)
  c12_primitives.1 c12_primitives.2 w12_primitives.1 w12_primitives.2
  c12_denominators w12_denominators checked12 ha
def c13 : Inputs p := ⟨⟨68899100311476945924854382592, 68899100311476945924854382592⟩, ⟨13916483632902748871221344131, 13916483632902748871221352324⟩, ⟨12820843620992949339282902100, 12820843620992949339282909139⟩, ⟨0, 0⟩⟩
def c13Exp : ExpWitness p := ⟨13916483632902748871221344131, scale p, 13916483632902748871221352324, scale p, 2,32,2,32,⟨-137798200622953891849708788639, -137798200622953891849708788412⟩,⟨-137798200622953891849708741995, -137798200622953891849708741772⟩⟩
theorem c13_primitives :
 expBoxCheck ((ofInt p (-2)).mul c13.alpha) c13.expNegTwo c13Exp = true ∧
 logBoxCheck ((ofInt p 1).add c13.expNegTwo) c13.logOnePlusExp wl = true := by decide +kernel
theorem c13_denominators : CompactDenominators c13 := by decide +kernel
def w13 : Inputs p := ⟨⟨67080875878776543646096293888, 70717324744177348203612471296⟩, ⟨13292175753610695973736598129, 14570114050157803478286379671⟩, ⟨12288024223759152545696940926, 13374875270861943874268140851⟩, ⟨0, 0⟩⟩
def w13Exp : ExpWitness p := ⟨13292175753610695973736598129, scale p, 14570114050157803478286379671, scale p, 2,32,2,32,⟨-141434649488354696407224967143, -141434649488354696407224966922⟩,⟨-134161751757553087292192565635, -134161751757553087292192565408⟩⟩
theorem w13_primitives :
 expBoxCheck ((ofInt p (-2)).mul w13.alpha) w13.expNegTwo w13Exp = true ∧
 logBoxCheck ((ofInt p 1).add w13.expNegTwo) w13.logOnePlusExp wl = true := by decide +kernel
theorem w13_denominators : CompactDenominators w13 := by decide +kernel
theorem checked13 : centeredTaylorCheck (compactBox c13) (compactBox w13)
 (w13.alpha.sub c13.alpha) = true := by decide +kernel
theorem positive13 : PositiveInterval p 67080875878776543646096293888 70717324744177348203612471296 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 68899100311476945924854382592) rfl (by decide +kernel)
  c13_primitives.1 c13_primitives.2 w13_primitives.1 w13_primitives.2
  c13_denominators w13_denominators checked13 ha
def c14 : Inputs p := ⟨⟨72535549176877750482370560000, 72535549176877750482370560000⟩, ⟨12695874972837742395412392589, 12695874972837742395412400782⟩, ⟨11775739915042634370087957170, 11775739915042634370087964305⟩, ⟨0, 0⟩⟩
def c14Exp : ExpWitness p := ⟨12695874972837742395412392589, scale p, 12695874972837742395412400782, scale p, 2,32,2,32,⟨-145071098353755500964741145693, -145071098353755500964741145472⟩,⟨-145071098353755500964741094567, -145071098353755500964741094342⟩⟩
theorem c14_primitives :
 expBoxCheck ((ofInt p (-2)).mul c14.alpha) c14.expNegTwo c14Exp = true ∧
 logBoxCheck ((ofInt p 1).add c14.expNegTwo) c14.logOnePlusExp wl = true := by decide +kernel
theorem c14_denominators : CompactDenominators c14 := by decide +kernel
def w14 : Inputs p := ⟨⟨70717324744177348203612471296, 74353773609578152761128648704⟩, ⟨12126324863116805677732857459, 13292175753610695973736606322⟩, ⟨11283324844131738382360529562, 12288024223759152545696948013⟩, ⟨0, 0⟩⟩
def w14Exp : ExpWitness p := ⟨12126324863116805677732857459, scale p, 13292175753610695973736606322, scale p, 2,32,2,32,⟨-148707547219156305522257324299, -148707547219156305522257324076⟩,⟨-141434649488354696407224918309, -141434649488354696407224918084⟩⟩
theorem w14_primitives :
 expBoxCheck ((ofInt p (-2)).mul w14.alpha) w14.expNegTwo w14Exp = true ∧
 logBoxCheck ((ofInt p 1).add w14.expNegTwo) w14.logOnePlusExp wl = true := by decide +kernel
theorem w14_denominators : CompactDenominators w14 := by decide +kernel
theorem checked14 : centeredTaylorCheck (compactBox c14) (compactBox w14)
 (w14.alpha.sub c14.alpha) = true := by decide +kernel
theorem positive14 : PositiveInterval p 70717324744177348203612471296 74353773609578152761128648704 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 72535549176877750482370560000) rfl (by decide +kernel)
  c14_primitives.1 c14_primitives.2 w14_primitives.1 w14_primitives.2
  c14_denominators w14_denominators checked14 ha
def c15 : Inputs p := ⟨⟨76171998042278555039886737408, 76171998042278555039886737408⟩, ⟨11582325361619181119026863886, 11582325361619181119026872079⟩, ⟨10810125108834611361811700780, 10810125108834611361811708005⟩, ⟨0, 0⟩⟩
def c15Exp : ExpWitness p := ⟨11582325361619181119026863886, scale p, 11582325361619181119026872079, scale p, 2,32,2,32,⟨-152343996084557110079773502967, -152343996084557110079773502742⟩,⟨-152343996084557110079773446923, -152343996084557110079773446698⟩⟩
theorem c15_primitives :
 expBoxCheck ((ofInt p (-2)).mul c15.alpha) c15.expNegTwo c15Exp = true ∧
 logBoxCheck ((ofInt p 1).add c15.expNegTwo) c15.logOnePlusExp wl = true := by decide +kernel
theorem c15_denominators : CompactDenominators c15 := by decide +kernel
def w15 : Inputs p := ⟨⟨74353773609578152761128648704, 77990222474978957318644826112⟩, ⟨11062730241578445907568990329, 12126324863116805677732865652⟩, ⟨10355499313875516339587444806, 11283324844131738382360536737⟩, ⟨0, 0⟩⟩
def w15Exp : ExpWitness p := ⟨11062730241578445907568990329, scale p, 12126324863116805677732865652, scale p, 2,32,2,32,⟨-155980444949957914637289681687, -155980444949957914637289681466⟩,⟨-148707547219156305522257270771, -148707547219156305522257270546⟩⟩
theorem w15_primitives :
 expBoxCheck ((ofInt p (-2)).mul w15.alpha) w15.expNegTwo w15Exp = true ∧
 logBoxCheck ((ofInt p 1).add w15.expNegTwo) w15.logOnePlusExp wl = true := by decide +kernel
theorem w15_denominators : CompactDenominators w15 := by decide +kernel
theorem checked15 : centeredTaylorCheck (compactBox c15) (compactBox w15)
 (w15.alpha.sub c15.alpha) = true := by decide +kernel
theorem positive15 : PositiveInterval p 74353773609578152761128648704 77990222474978957318644826112 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 76171998042278555039886737408) rfl (by decide +kernel)
  c15_primitives.1 c15_primitives.2 w15_primitives.1 w15_primitives.2
  c15_denominators w15_denominators checked15 ha
def c16 : Inputs p := ⟨⟨79808446907679359597402914816, 79808446907679359597402914816⟩, ⟨10566444697148907618095256104, 10566444697148907618095264297⟩, ⟨9918819055723629594950676028, 9918819055723629594950683333⟩, ⟨0, 0⟩⟩
def c16Exp : ExpWitness p := ⟨10566444697148907618095256104, scale p, 10566444697148907618095264297, scale p, 2,32,2,32,⟨-159616893815358719194805860473, -159616893815358719194805860250⟩,⟨-159616893815358719194805799041, -159616893815358719194805798816⟩⟩
theorem c16_primitives :
 expBoxCheck ((ofInt p (-2)).mul c16.alpha) c16.expNegTwo c16Exp = true ∧
 logBoxCheck ((ofInt p 1).add c16.expNegTwo) c16.logOnePlusExp wl = true := by decide +kernel
theorem c16_denominators : CompactDenominators c16 := by decide +kernel
def w16 : Inputs p := ⟨⟨77990222474978957318644826112, 81626671340379761876161003520⟩, ⟨10092423036609805844145889912, 11062730241578445907568998522⟩, ⟨9499469337197399801640250470, 10355499313875516339587452065⟩, ⟨0, 0⟩⟩
def w16Exp : ExpWitness p := ⟨10092423036609805844145889912, scale p, 11062730241578445907568998522, scale p, 2,32,2,32,⟨-163253342680759523752322039317, -163253342680759523752322039094⟩,⟨-155980444949957914637289623011, -155980444949957914637289622788⟩⟩
theorem w16_primitives :
 expBoxCheck ((ofInt p (-2)).mul w16.alpha) w16.expNegTwo w16Exp = true ∧
 logBoxCheck ((ofInt p 1).add w16.expNegTwo) w16.logOnePlusExp wl = true := by decide +kernel
theorem w16_denominators : CompactDenominators w16 := by decide +kernel
theorem checked16 : centeredTaylorCheck (compactBox c16) (compactBox w16)
 (w16.alpha.sub c16.alpha) = true := by decide +kernel
theorem positive16 : PositiveInterval p 77990222474978957318644826112 81626671340379761876161003520 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 79808446907679359597402914816) rfl (by decide +kernel)
  c16_primitives.1 c16_primitives.2 w16_primitives.1 w16_primitives.2
  c16_denominators w16_denominators checked16 ha
def c17 : Inputs p := ⟨⟨83444895773080164154919092224, 83444895773080164154919092224⟩, ⟨9639666479054764187314417774, 9639666479054764187314425967⟩, ⟨9096848915334135418061925788, 9096848915334135418061933167⟩, ⟨0, 0⟩⟩
def c17Exp : ExpWitness p := ⟨9639666479054764187314417774, scale p, 9639666479054764187314425967, scale p, 3,32,3,32,⟨-166889791546160328309838218300, -166889791546160328309838218004⟩,⟨-166889791546160328309838150962, -166889791546160328309838150664⟩⟩
theorem c17_primitives :
 expBoxCheck ((ofInt p (-2)).mul c17.alpha) c17.expNegTwo c17Exp = true ∧
 logBoxCheck ((ofInt p 1).add c17.expNegTwo) c17.logOnePlusExp wl = true := by decide +kernel
theorem c17_denominators : CompactDenominators c17 := by decide +kernel
def w17 : Inputs p := ⟨⟨81626671340379761876161003520, 85263120205780566433677180928⟩, ⟨9207221049924037016736206195, 10092423036609805844145898105⟩, ⟨8710370586117910843779144274, 9499469337197399801640257807⟩, ⟨0, 0⟩⟩
def w17Exp : ExpWitness p := ⟨9207221049924037016736206195, scale p, 10092423036609805844145898105, scale p, 3,32,2,32,⟨-170526240411561132867354397284, -170526240411561132867354396986⟩,⟨-163253342680759523752321975003, -163253342680759523752321974780⟩⟩
theorem w17_primitives :
 expBoxCheck ((ofInt p (-2)).mul w17.alpha) w17.expNegTwo w17Exp = true ∧
 logBoxCheck ((ofInt p 1).add w17.expNegTwo) w17.logOnePlusExp wl = true := by decide +kernel
theorem w17_denominators : CompactDenominators w17 := by decide +kernel
theorem checked17 : centeredTaylorCheck (compactBox c17) (compactBox w17)
 (w17.alpha.sub c17.alpha) = true := by decide +kernel
theorem positive17 : PositiveInterval p 81626671340379761876161003520 85263120205780566433677180928 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 83444895773080164154919092224) rfl (by decide +kernel)
  c17_primitives.1 c17_primitives.2 w17_primitives.1 w17_primitives.2
  c17_denominators w17_denominators checked17 ha
def c18 : Inputs p := ⟨⟨87081344638480968712435269632, 87081344638480968712435269632⟩, ⟨8794175570945360781367365566, 8794175570945360781367373759⟩, ⟨8339461409722876558471944674, 8339461409722876558471952119⟩, ⟨0, 0⟩⟩
def c18Exp : ExpWitness p := ⟨8794175570945360781367365566, scale p, 8794175570945360781367373759, scale p, 3,32,3,32,⟨-174162689276961937424870576350, -174162689276961937424870576054⟩,⟨-174162689276961937424870502538, -174162689276961937424870502244⟩⟩
theorem c18_primitives :
 expBoxCheck ((ofInt p (-2)).mul c18.alpha) c18.expNegTwo c18Exp = true ∧
 logBoxCheck ((ofInt p 1).add c18.expNegTwo) c18.logOnePlusExp wl = true := by decide +kernel
theorem c18_denominators : CompactDenominators c18 := by decide +kernel
def w18 : Inputs p := ⟨⟨85263120205780566433677180928, 88899569071181370991193358336⟩, ⟨8399659740248142026506220797, 9207221049924037016736214388⟩, ⟨7983562879957401149847756562, 8710370586117910843779151685⟩, ⟨0, 0⟩⟩
def w18Exp : ExpWitness p := ⟨8399659740248142026506220797, scale p, 9207221049924037016736214388, scale p, 3,32,3,32,⟨-177799138142362741982386755488, -177799138142362741982386755194⟩,⟨-170526240411561132867354326784, -170526240411561132867354326488⟩⟩
theorem w18_primitives :
 expBoxCheck ((ofInt p (-2)).mul w18.alpha) w18.expNegTwo w18Exp = true ∧
 logBoxCheck ((ofInt p 1).add w18.expNegTwo) w18.logOnePlusExp wl = true := by decide +kernel
theorem w18_denominators : CompactDenominators w18 := by decide +kernel
theorem checked18 : centeredTaylorCheck (compactBox c18) (compactBox w18)
 (w18.alpha.sub c18.alpha) = true := by decide +kernel
theorem positive18 : PositiveInterval p 85263120205780566433677180928 88899569071181370991193358336 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 87081344638480968712435269632) rfl (by decide +kernel)
  c18_primitives.1 c18_primitives.2 w18_primitives.1 w18_primitives.2
  c18_denominators w18_denominators checked18 ha
def c19 : Inputs p := ⟨⟨90717793503881773269951447040, 90717793503881773269951447040⟩, ⟨8022842298605712771271992916, 8022842298605712771272001109⟩, ⟨7642131041590921267883312410, 7642131041590921267883319919⟩, ⟨0, 0⟩⟩
def c19Exp : ExpWitness p := ⟨8022842298605712771271992916, scale p, 8022842298605712771272001109, scale p, 3,32,3,32,⟨-181435587007763546539902934714, -181435587007763546539902934418⟩,⟨-181435587007763546539902853806, -181435587007763546539902853510⟩⟩
theorem c19_primitives :
 expBoxCheck ((ofInt p (-2)).mul c19.alpha) c19.expNegTwo c19Exp = true ∧
 logBoxCheck ((ofInt p 1).add c19.expNegTwo) c19.logOnePlusExp wl = true := by decide +kernel
theorem c19_denominators : CompactDenominators c19 := by decide +kernel
def w19 : Inputs p := ⟨⟨88899569071181370991193358336, 92536017936582175548709535744⟩, ⟨7662929277941858879150744244, 8399659740248142026506228990⟩, ⟨7314636559213611833704395854, 7983562879957401149847764039⟩, ⟨0, 0⟩⟩
def w19Exp : ExpWitness p := ⟨7662929277941858879150744244, scale p, 8399659740248142026506228990, scale p, 3,32,3,32,⟨-185072035873164351097419114018, -185072035873164351097419113720⟩,⟨-177799138142362741982386678210, -177799138142362741982386677914⟩⟩
theorem w19_primitives :
 expBoxCheck ((ofInt p (-2)).mul w19.alpha) w19.expNegTwo w19Exp = true ∧
 logBoxCheck ((ofInt p 1).add w19.expNegTwo) w19.logOnePlusExp wl = true := by decide +kernel
theorem w19_denominators : CompactDenominators w19 := by decide +kernel
theorem checked19 : centeredTaylorCheck (compactBox c19) (compactBox w19)
 (w19.alpha.sub c19.alpha) = true := by decide +kernel
theorem positive19 : PositiveInterval p 88899569071181370991193358336 92536017936582175548709535744 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 90717793503881773269951447040) rfl (by decide +kernel)
  c19_primitives.1 c19_primitives.2 w19_primitives.1 w19_primitives.2
  c19_denominators w19_denominators checked19 ha
def c20 : Inputs p := ⟨⟨94354242369282577827467624448, 94354242369282577827467624448⟩, ⟨7319162328411160873630933662, 7319162328411160873630941855⟩, ⟨7000564741222576279585568466, 7000564741222576279585576037⟩, ⟨0, 0⟩⟩
def c20Exp : ExpWitness p := ⟨7319162328411160873630933662, scale p, 7319162328411160873630941855, scale p, 3,32,3,32,⟨-188708484738565155654935293416, -188708484738565155654935293116⟩,⟨-188708484738565155654935204728, -188708484738565155654935204430⟩⟩
theorem c20_primitives :
 expBoxCheck ((ofInt p (-2)).mul c20.alpha) c20.expNegTwo c20Exp = true ∧
 logBoxCheck ((ofInt p 1).add c20.expNegTwo) c20.logOnePlusExp wl = true := by decide +kernel
theorem c20_denominators : CompactDenominators c20 := by decide +kernel
def w20 : Inputs p := ⟨⟨92536017936582175548709535744, 96172466801982980106225713152⟩, ⟨6990817120528244536052852304, 7662929277941858879150752437⟩, ⟨6699415522450602347556034588, 7314636559213611833704403395⟩, ⟨0, 0⟩⟩
def w20Exp : ExpWitness p := ⟨6990817120528244536052852304, scale p, 7662929277941858879150752437, scale p, 3,32,3,32,⟨-192344933603965960212451472898, -192344933603965960212451472600⟩,⟨-185072035873164351097419029308, -185072035873164351097419029012⟩⟩
theorem w20_primitives :
 expBoxCheck ((ofInt p (-2)).mul w20.alpha) w20.expNegTwo w20Exp = true ∧
 logBoxCheck ((ofInt p 1).add w20.expNegTwo) w20.logOnePlusExp wl = true := by decide +kernel
theorem w20_denominators : CompactDenominators w20 := by decide +kernel
theorem checked20 : centeredTaylorCheck (compactBox c20) (compactBox w20)
 (w20.alpha.sub c20.alpha) = true := by decide +kernel
theorem positive20 : PositiveInterval p 92536017936582175548709535744 96172466801982980106225713152 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 94354242369282577827467624448) rfl (by decide +kernel)
  c20_primitives.1 c20_primitives.2 w20_primitives.1 w20_primitives.2
  c20_denominators w20_denominators checked20 ha
def c21 : Inputs p := ⟨⟨97990691234683382384983801856, 97990691234683382384983801856⟩, ⟨6677201818979169409582601867, 6677201818979169409582610060⟩, ⟨6410703408857856374214120498, 6410703408857856374214128129⟩, ⟨0, 0⟩⟩
def c21Exp : ExpWitness p := ⟨6677201818979169409582601867, scale p, 6677201818979169409582610060, scale p, 3,32,3,32,⟨-195981382469366764769967652488, -195981382469366764769967652192⟩,⟨-195981382469366764769967555278, -195981382469366764769967554980⟩⟩
theorem c21_primitives :
 expBoxCheck ((ofInt p (-2)).mul c21.alpha) c21.expNegTwo c21Exp = true ∧
 logBoxCheck ((ofInt p 1).add c21.expNegTwo) c21.logOnePlusExp wl = true := by decide +kernel
theorem c21_denominators : CompactDenominators c21 := by decide +kernel
def w21 : Inputs p := ⟨⟨96172466801982980106225713152, 99808915667383784663741890560⟩, ⟨6377655624899220209020271421, 6990817120528244536052860497⟩, ⟨6133957387596217057429361878, 6699415522450602347556042187⟩, ⟨0, 0⟩⟩
def w21Exp : ExpWitness p := ⟨6377655624899220209020271421, scale p, 6990817120528244536052860497, scale p, 3,32,3,32,⟨-199617831334767569327483832178, -199617831334767569327483831880⟩,⟨-192344933603965960212451380046, -192344933603965960212451379748⟩⟩
theorem w21_primitives :
 expBoxCheck ((ofInt p (-2)).mul w21.alpha) w21.expNegTwo w21Exp = true ∧
 logBoxCheck ((ofInt p 1).add w21.expNegTwo) w21.logOnePlusExp wl = true := by decide +kernel
theorem w21_denominators : CompactDenominators w21 := by decide +kernel
theorem checked21 : centeredTaylorCheck (compactBox c21) (compactBox w21)
 (w21.alpha.sub c21.alpha) = true := by decide +kernel
theorem positive21 : PositiveInterval p 96172466801982980106225713152 99808915667383784663741890560 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 97990691234683382384983801856) rfl (by decide +kernel)
  c21_primitives.1 c21_primitives.2 w21_primitives.1 w21_primitives.2
  c21_denominators w21_denominators checked21 ha
def c22 : Inputs p := ⟨⟨101627140100084186942499979264, 101627140100084186942499979264⟩, ⟨6091547383545627341162830929, 6091547383545627341162839122⟩, ⟨5868720805633079216254156830, 5868720805633079216254164513⟩, ⟨0, 0⟩⟩
def c22Exp : ExpWitness p := ⟨6091547383545627341162830929, scale p, 6091547383545627341162839122, scale p, 3,32,3,32,⟨-203254280200168373885000011978, -203254280200168373885000011684⟩,⟨-203254280200168373884999905420, -203254280200168373884999905122⟩⟩
theorem c22_primitives :
 expBoxCheck ((ofInt p (-2)).mul c22.alpha) c22.expNegTwo c22Exp = true ∧
 logBoxCheck ((ofInt p 1).add c22.expNegTwo) c22.logOnePlusExp wl = true := by decide +kernel
theorem c22_denominators : CompactDenominators c22 := by decide +kernel
def w22 : Inputs p := ⟨⟨99808915667383784663741890560, 103445364532784589221258067968⟩, ⟨5818274254431532238279083460, 6377655624899220209020279614⟩, ⟨5614551219988963448386149774, 6133957387596217057429369533⟩, ⟨0, 0⟩⟩
def w22Exp : ExpWitness p := ⟨5818274254431532238279083460, scale p, 6377655624899220209020279614, scale p, 3,32,3,32,⟨-206890729065569178442516191884, -206890729065569178442516191584⟩,⟨-199617831334767569327483730394, -199617831334767569327483730098⟩⟩
theorem w22_primitives :
 expBoxCheck ((ofInt p (-2)).mul w22.alpha) w22.expNegTwo w22Exp = true ∧
 logBoxCheck ((ofInt p 1).add w22.expNegTwo) w22.logOnePlusExp wl = true := by decide +kernel
theorem w22_denominators : CompactDenominators w22 := by decide +kernel
theorem checked22 : centeredTaylorCheck (compactBox c22) (compactBox w22)
 (w22.alpha.sub c22.alpha) = true := by decide +kernel
theorem positive22 : PositiveInterval p 99808915667383784663741890560 103445364532784589221258067968 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 101627140100084186942499979264) rfl (by decide +kernel)
  c22_primitives.1 c22_primitives.2 w22_primitives.1 w22_primitives.2
  c22_denominators w22_denominators checked22 ha
def c23 : Inputs p := ⟨⟨105263588965484991500016156672, 105263588965484991500016156672⟩, ⟨5557260441119121325408129396, 5557260441119121325408137589⟩, ⟨5371020222503493827334455886, 5371020222503493827334463615⟩, ⟨0, 0⟩⟩
def c23Exp : ExpWitness p := ⟨5557260441119121325408129396, scale p, 5557260441119121325408137589, scale p, 3,32,3,32,⟨-210527177930969983000032371914, -210527177930969983000032371618⟩,⟨-210527177930969983000032255110, -210527177930969983000032254814⟩⟩
theorem c23_primitives :
 expBoxCheck ((ofInt p (-2)).mul c23.alpha) c23.expNegTwo c23Exp = true ∧
 logBoxCheck ((ofInt p 1).add c23.expNegTwo) c23.logOnePlusExp wl = true := by decide +kernel
theorem c23_denominators : CompactDenominators c23 := by decide +kernel
def w23 : Inputs p := ⟨⟨103445364532784589221258067968, 107081813398185393778774245376⟩, ⟨5307955977995556483763354966, 5818274254431532238279091653⟩, ⟨5137713241899369481542584834, 5614551219988963448386157479⟩, ⟨0, 0⟩⟩
def w23Exp : ExpWitness p := ⟨5307955977995556483763354966, scale p, 5818274254431532238279091653, scale p, 3,32,3,32,⟨-214163626796370787557548552060, -214163626796370787557548551764⟩,⟨-206890729065569178442516080320, -206890729065569178442516080020⟩⟩
theorem w23_primitives :
 expBoxCheck ((ofInt p (-2)).mul w23.alpha) w23.expNegTwo w23Exp = true ∧
 logBoxCheck ((ofInt p 1).add w23.expNegTwo) w23.logOnePlusExp wl = true := by decide +kernel
theorem w23_denominators : CompactDenominators w23 := by decide +kernel
theorem checked23 : centeredTaylorCheck (compactBox c23) (compactBox w23)
 (w23.alpha.sub c23.alpha) = true := by decide +kernel
theorem positive23 : PositiveInterval p 103445364532784589221258067968 107081813398185393778774245376 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 105263588965484991500016156672) rfl (by decide +kernel)
  c23_primitives.1 c23_primitives.2 w23_primitives.1 w23_primitives.2
  c23_denominators w23_denominators checked23 ha
def c24 : Inputs p := ⟨⟨108900037830885796057532334080, 108900037830885796057532334080⟩, ⟨5069835571475394700505689221, 5069835571475394700505697414⟩, ⟨4914229325765749936737416150, 4914229325765749936737423921⟩, ⟨0, 0⟩⟩
def c24Exp : ExpWitness p := ⟨5069835571475394700505689221, scale p, 5069835571475394700505697414, scale p, 3,32,3,32,⟨-217800075661771592115064732340, -217800075661771592115064732038⟩,⟨-217800075661771592115064604302, -217800075661771592115064604004⟩⟩
theorem c24_primitives :
 expBoxCheck ((ofInt p (-2)).mul c24.alpha) c24.expNegTwo c24Exp = true ∧
 logBoxCheck ((ofInt p 1).add c24.expNegTwo) c24.logOnePlusExp wl = true := by decide +kernel
theorem c24_denominators : CompactDenominators c24 := by decide +kernel
def w24 : Inputs p := ⟨⟨107081813398185393778774245376, 110718262263586198336290422784⟩, ⟨4842397493187868190509047093, 5307955977995556483763363159⟩, ⟨4700180904932675047931570520, 5137713241899369481542592583⟩, ⟨0, 0⟩⟩
def w24Exp : ExpWitness p := ⟨4842397493187868190509047093, scale p, 5307955977995556483763363159, scale p, 4,32,3,32,⟨-221436524527172396672580912819, -221436524527172396672580912448⟩,⟨-214163626796370787557548429768, -214163626796370787557548429468⟩⟩
theorem w24_primitives :
 expBoxCheck ((ofInt p (-2)).mul w24.alpha) w24.expNegTwo w24Exp = true ∧
 logBoxCheck ((ofInt p 1).add w24.expNegTwo) w24.logOnePlusExp wl = true := by decide +kernel
theorem w24_denominators : CompactDenominators w24 := by decide +kernel
theorem checked24 : centeredTaylorCheck (compactBox c24) (compactBox w24)
 (w24.alpha.sub c24.alpha) = true := by decide +kernel
theorem positive24 : PositiveInterval p 107081813398185393778774245376 110718262263586198336290422784 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 108900037830885796057532334080) rfl (by decide +kernel)
  c24_primitives.1 c24_primitives.2 w24_primitives.1 w24_primitives.2
  c24_denominators w24_denominators checked24 ha
def c25 : Inputs p := ⟨⟨112536486696286600615048511488, 112536486696286600615048511488⟩, ⟨4625162522816930270455415118, 4625162522816930270455423311⟩, ⟨4495193542558218096988700674, 4495193542558218096988708489⟩, ⟨0, 0⟩⟩
def c25Exp : ExpWitness p := ⟨4625162522816930270455415118, scale p, 4625162522816930270455423311, scale p, 4,32,4,32,⟨-225072973392573201230097093375, -225072973392573201230097093004⟩,⟨-225072973392573201230096953029, -225072973392573201230096952660⟩⟩
theorem c25_primitives :
 expBoxCheck ((ofInt p (-2)).mul c25.alpha) c25.expNegTwo c25Exp = true ∧
 logBoxCheck ((ofInt p 1).add c25.expNegTwo) c25.logOnePlusExp wl = true := by decide +kernel
theorem c25_denominators : CompactDenominators c25 := by decide +kernel
def w25 : Inputs p := ⟨⟨110718262263586198336290422784, 114354711128987002893806600192⟩, ⟨4417672938366592451783899421, 4842397493187868190509055286⟩, ⟨4298905670101299714408167696, 4700180904932675047931578311⟩, ⟨0, 0⟩⟩
def w25Exp : ExpWitness p := ⟨4417672938366592451783899421, scale p, 4842397493187868190509055286, scale p, 4,32,4,32,⟨-228709422257974005787613274073, -228709422257974005787613273704⟩,⟨-221436524527172396672580778771, -221436524527172396672580778398⟩⟩
theorem w25_primitives :
 expBoxCheck ((ofInt p (-2)).mul w25.alpha) w25.expNegTwo w25Exp = true ∧
 logBoxCheck ((ofInt p 1).add w25.expNegTwo) w25.logOnePlusExp wl = true := by decide +kernel
theorem w25_denominators : CompactDenominators w25 := by decide +kernel
theorem checked25 : centeredTaylorCheck (compactBox c25) (compactBox w25)
 (w25.alpha.sub c25.alpha) = true := by decide +kernel
theorem positive25 : PositiveInterval p 110718262263586198336290422784 114354711128987002893806600192 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 112536486696286600615048511488) rfl (by decide +kernel)
  c25_primitives.1 c25_primitives.2 w25_primitives.1 w25_primitives.2
  c25_denominators w25_denominators checked25 ha
def c26 : Inputs p := ⟨⟨116172935561687405172564688896, 116172935561687405172564688896⟩, ⟨4219491551724005035220633472, 4219491551724005035220641665⟩, ⟨4110968312206562334436098996, 4110968312206562334436106845⟩, ⟨0, 0⟩⟩
def c26Exp : ExpWitness p := ⟨4219491551724005035220633472, scale p, 4219491551724005035220641665, scale p, 4,32,4,32,⟨-232345871123374810345129454933, -232345871123374810345129454564⟩,⟨-232345871123374810345129301097, -232345871123374810345129300726⟩⟩
theorem c26_primitives :
 expBoxCheck ((ofInt p (-2)).mul c26.alpha) c26.expNegTwo c26Exp = true ∧
 logBoxCheck ((ofInt p 1).add c26.expNegTwo) c26.logOnePlusExp wl = true := by decide +kernel
theorem c26_denominators : CompactDenominators c26 := by decide +kernel
def w26 : Inputs p := ⟨⟨114354711128987002893806600192, 117991159994387807451322777600⟩, ⟨4030200787488177485276600344, 4417672938366592451783907614⟩, ⟨3931044802384341879816783380, 4298905670101299714408175525⟩, ⟨0, 0⟩⟩
def w26Exp : ExpWitness p := ⟨4030200787488177485276600344, scale p, 4417672938366592451783907614, scale p, 4,32,4,32,⟨-235982319988775614902645635961, -235982319988775614902645635592⟩,⟨-228709422257974005787613127137, -228709422257974005787613126766⟩⟩
theorem w26_primitives :
 expBoxCheck ((ofInt p (-2)).mul w26.alpha) w26.expNegTwo w26Exp = true ∧
 logBoxCheck ((ofInt p 1).add w26.expNegTwo) w26.logOnePlusExp wl = true := by decide +kernel
theorem w26_denominators : CompactDenominators w26 := by decide +kernel
theorem checked26 : centeredTaylorCheck (compactBox c26) (compactBox w26)
 (w26.alpha.sub c26.alpha) = true := by decide +kernel
theorem positive26 : PositiveInterval p 114354711128987002893806600192 117991159994387807451322777600 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 116172935561687405172564688896) rfl (by decide +kernel)
  c26_primitives.1 c26_primitives.2 w26_primitives.1 w26_primitives.2
  c26_denominators w26_denominators checked26 ha
def c27 : Inputs p := ⟨⟨118416701882892156920819351552, 118416701882892156920819351552⟩, ⟨3987139316252962405544740113, 3987139316252962405544748306⟩, ⟨3890057162513407045368201508, 3890057162513407045368209385⟩, ⟨0, 0⟩⟩
def c27Exp : ExpWitness p := ⟨3987139316252962405544740113, scale p, 3987139316252962405544748306, scale p, 4,32,4,32,⟨-236833403765784313841638784713, -236833403765784313841638784344⟩,⟨-236833403765784313841638621911, -236833403765784313841638621540⟩⟩
theorem c27_primitives :
 expBoxCheck ((ofInt p (-2)).mul c27.alpha) c27.expNegTwo c27Exp = true ∧
 logBoxCheck ((ofInt p 1).add c27.expNegTwo) c27.logOnePlusExp wl = true := by decide +kernel
theorem c27_denominators : CompactDenominators c27 := by decide +kernel
def w27 : Inputs p := ⟨⟨117991159994387807451322777600, 118842243771396506390315925504⟩, ⟨3944537943757913803250135441, 4030200787488177485276608537⟩, ⟨3849486586622132950060792858, 3931044802384341879816791245⟩, ⟨0, 0⟩⟩
def w27Exp : ExpWitness p := ⟨3944537943757913803250135441, scale p, 4030200787488177485276608537, scale p, 4,32,4,32,⟨-237684487542793012780631933519, -237684487542793012780631933138⟩,⟨-235982319988775614902645474897, -235982319988775614902645474528⟩⟩
theorem w27_primitives :
 expBoxCheck ((ofInt p (-2)).mul w27.alpha) w27.expNegTwo w27Exp = true ∧
 logBoxCheck ((ofInt p 1).add w27.expNegTwo) w27.logOnePlusExp wl = true := by decide +kernel
theorem w27_denominators : CompactDenominators w27 := by decide +kernel
theorem checked27 : centeredTaylorCheck (compactBox c27) (compactBox w27)
 (w27.alpha.sub c27.alpha) = true := by decide +kernel
theorem positive27 : PositiveInterval p 117991159994387807451322777600 118842243771396506390315925504 := by
 intro a ha
 exact stableL_pos_of_checked_cell (c := 118416701882892156920819351552) rfl (by decide +kernel)
  c27_primitives.1 c27_primitives.2 w27_primitives.1 w27_primitives.2
  c27_denominators w27_denominators checked27 ha
theorem complete : PositiveInterval p 19807040628566084398385987584 118842243771396506390315925504 :=
 (PositiveInterval.split (PositiveInterval.split (PositiveInterval.split (PositiveInterval.split positive0 (PositiveInterval.split positive1 positive2)) (PositiveInterval.split (PositiveInterval.split positive3 positive4) (PositiveInterval.split positive5 positive6))) (PositiveInterval.split (PositiveInterval.split positive7 (PositiveInterval.split positive8 positive9)) (PositiveInterval.split (PositiveInterval.split positive10 positive11) (PositiveInterval.split positive12 positive13)))) (PositiveInterval.split (PositiveInterval.split (PositiveInterval.split positive14 (PositiveInterval.split positive15 positive16)) (PositiveInterval.split (PositiveInterval.split positive17 positive18) (PositiveInterval.split positive19 positive20))) (PositiveInterval.split (PositiveInterval.split positive21 (PositiveInterval.split positive22 positive23)) (PositiveInterval.split (PositiveInterval.split positive24 positive25) (PositiveInterval.split positive26 positive27)))))
theorem stableL_pos_middle {a : ℝ} (hlo : 1/4 ≤ a) (hhi : a ≤ 3/2) : 0 < stableL a := by
 apply complete a
 norm_num [DyadicInterval.Contains, p, scale]
 constructor <;> linarith
#print axioms stableL_pos_middle
#print axioms complete
end GeneralCK.E8RatioMonotonicity.MiddleCertificate

end


