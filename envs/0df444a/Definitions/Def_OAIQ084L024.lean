-- Prove2me | Definitions.Def_OAIQ084L024
-- name    : OAIQ084L024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:31:38.747473+00:00
-- url     : https://prove2.me/theorems/06c77f64-e495-4af3-9afe-599899cc7892
-- title:
--   Definitions bundle OAIQ084L024 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 9 definitions. The definitions and types are `OAI.LaughlinFock.fourLData_13`, `OAI.LaughlinFock.fourLData_14`, `OAI.LaughlinFock.fourLData_18`, `OAI.LaughlinFock.fourLData_22`, `OAI.LaughlinFock.fourZData_4`, `OAI.LaughlinFock.integerHighestEntry`, `OAI.LaughlinFock.kernelHighestEntry`, `OAI.LaughlinFock.kernelHighestTerm`, `OAI.LaughlinFock.pairWedgeMatrix`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinFock_Certificate04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate04.lean), [`LaughlinFock_Certificate13Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate13Data.lean), [`LaughlinFock_Certificate14Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate14Data.lean), [`LaughlinFock_Certificate18Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate18Data.lean), [`LaughlinFock_Certificate22Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate22Data.lean), [`LaughlinFock_GramCache`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/GramCache.lean), [`LaughlinFock_IntegerFour`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/IntegerFour.lean), [`LaughlinFock_NormalOrdering`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/NormalOrdering.lean).
--
--   **Imports.** It imports the published bundle `Def_LaughlinFock`; the bundles `OAIQ084L012` and `OAIQ084L016` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ084L043`; the statements `OAI.LaughlinFock.fourHighestNumber_20_1`, `OAI.LaughlinFock.fourHighestNumber_20_11`, `OAI.LaughlinFock.fourHighestNumber_20_13`, `OAI.LaughlinFock.fourHighestNumber_20_15`, `OAI.LaughlinFock.fourHighestNumber_20_17`, `OAI.LaughlinFock.fourHighestNumber_20_19`, `OAI.LaughlinFock.fourHighestNumber_20_3`, `OAI.LaughlinFock.fourHighestNumber_20_5`, `OAI.LaughlinFock.fourHighestNumber_20_7`, `OAI.LaughlinFock.fourHighestNumber_20_9`, `OAI.LaughlinFock.fourHighestNumber_21_1`, `OAI.LaughlinFock.fourHighestNumber_21_11`, `OAI.LaughlinFock.fourHighestNumber_21_13`, `OAI.LaughlinFock.fourHighestNumber_21_15`, `OAI.LaughlinFock.fourHighestNumber_21_17`, `OAI.LaughlinFock.fourHighestNumber_21_19`, `OAI.LaughlinFock.fourHighestNumber_21_21`, `OAI.LaughlinFock.fourHighestNumber_21_3`, `OAI.LaughlinFock.fourHighestNumber_21_5`, `OAI.LaughlinFock.fourHighestNumber_21_7`, `OAI.LaughlinFock.fourHighestNumber_21_9`, `OAI.LaughlinFock.fourHighestNumber_22_1`, `OAI.LaughlinFock.fourHighestNumber_22_11`, `OAI.LaughlinFock.fourHighestNumber_22_13`, `OAI.LaughlinFock.fourHighestNumber_22_15`, `OAI.LaughlinFock.fourHighestNumber_22_17`, `OAI.LaughlinFock.fourHighestNumber_22_19`, `OAI.LaughlinFock.fourHighestNumber_22_21`, `OAI.LaughlinFock.fourHighestNumber_22_3`, `OAI.LaughlinFock.fourHighestNumber_22_5`, `OAI.LaughlinFock.fourHighestNumber_22_7`, `OAI.LaughlinFock.fourHighestNumber_22_9`, `OAI.LaughlinFock.fourHighestNumber_23_1`, `OAI.LaughlinFock.fourHighestNumber_23_11`, `OAI.LaughlinFock.fourHighestNumber_23_13`, `OAI.LaughlinFock.fourHighestNumber_23_15`, `OAI.LaughlinFock.fourHighestNumber_23_17`, `OAI.LaughlinFock.fourHighestNumber_23_19`, `OAI.LaughlinFock.fourHighestNumber_23_21`, `OAI.LaughlinFock.fourHighestNumber_23_23`, `OAI.LaughlinFock.fourHighestNumber_23_3`, `OAI.LaughlinFock.fourHighestNumber_23_5`, `OAI.LaughlinFock.fourHighestNumber_23_7` and `OAI.LaughlinFock.fourHighestNumber_23_9`; the proofs of `OAI.LaughlinFock.fourHighestNumber_20_1`, `OAI.LaughlinFock.fourHighestNumber_20_11`, `OAI.LaughlinFock.fourHighestNumber_20_13`, `OAI.LaughlinFock.fourHighestNumber_20_15`, `OAI.LaughlinFock.fourHighestNumber_20_17`, `OAI.LaughlinFock.fourHighestNumber_20_19`, `OAI.LaughlinFock.fourHighestNumber_20_3`, `OAI.LaughlinFock.fourHighestNumber_20_5`, `OAI.LaughlinFock.fourHighestNumber_20_7`, `OAI.LaughlinFock.fourHighestNumber_20_9`, `OAI.LaughlinFock.fourHighestNumber_21_1`, `OAI.LaughlinFock.fourHighestNumber_21_11`, `OAI.LaughlinFock.fourHighestNumber_21_13`, `OAI.LaughlinFock.fourHighestNumber_21_15`, `OAI.LaughlinFock.fourHighestNumber_21_17`, `OAI.LaughlinFock.fourHighestNumber_21_19`, `OAI.LaughlinFock.fourHighestNumber_21_21`, `OAI.LaughlinFock.fourHighestNumber_21_3`, `OAI.LaughlinFock.fourHighestNumber_21_5`, `OAI.LaughlinFock.fourHighestNumber_21_7`, `OAI.LaughlinFock.fourHighestNumber_21_9`, `OAI.LaughlinFock.fourHighestNumber_22_1`, `OAI.LaughlinFock.fourHighestNumber_22_11`, `OAI.LaughlinFock.fourHighestNumber_22_13`, `OAI.LaughlinFock.fourHighestNumber_22_15`, `OAI.LaughlinFock.fourHighestNumber_22_17`, `OAI.LaughlinFock.fourHighestNumber_22_19`, `OAI.LaughlinFock.fourHighestNumber_22_21`, `OAI.LaughlinFock.fourHighestNumber_22_3`, `OAI.LaughlinFock.fourHighestNumber_22_5`, `OAI.LaughlinFock.fourHighestNumber_22_7`, `OAI.LaughlinFock.fourHighestNumber_22_9`, `OAI.LaughlinFock.fourHighestNumber_23_1`, `OAI.LaughlinFock.fourHighestNumber_23_11`, `OAI.LaughlinFock.fourHighestNumber_23_13`, `OAI.LaughlinFock.fourHighestNumber_23_15`, `OAI.LaughlinFock.fourHighestNumber_23_17`, `OAI.LaughlinFock.fourHighestNumber_23_19`, `OAI.LaughlinFock.fourHighestNumber_23_21`, `OAI.LaughlinFock.fourHighestNumber_23_23`, `OAI.LaughlinFock.fourHighestNumber_23_3`, `OAI.LaughlinFock.fourHighestNumber_23_5`, `OAI.LaughlinFock.fourHighestNumber_23_7` and `OAI.LaughlinFock.fourHighestNumber_23_9`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L012
import Definitions.Def_OAIQ084L016

section
-- module Solutions.OAIQ084_LF.LaughlinFock_NormalOrdering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal Ordering. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology
open Filter Topology
open Filter Topology
open scoped Kronecker
open scoped Matrix ComplexOrder Kronecker BigOperators



def pairWedgeMatrix (Q : ℕ) : Matrix (SectorOccupation Q 2) (PairLabel Q) ℂ :=
  fun S p => pairVector Q p.val S

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_IntegerFour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer Four. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def integerHighestEntry (D : ℕ) (r : CopyLabel D) (A : Occupation 24) : ℚ :=
  ∑ j ∈ A, ∑ k ∈ A, ∑ x ∈ A, ∑ y ∈ A, integerHighestTerm D r A x y j k

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_GramCache
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram Cache. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def kernelHighestTerm (D : ℕ) (r : CopyLabel D) (A : Occupation 24)
    (x y j k : Orbital 24) : ℚ :=
  if x<y ∧ j<k ∧ (x.val+y.val-1)+j.val+k.val=D then
    (fastIntegerCopyPolynomial D D r.val.val (x.val+y.val-1) j.val k.val : ℚ) *
      ((x.val:ℚ)-(y.val:ℚ)) * (x.val+y.val-1).factorial * j.val.factorial * k.val.factorial *
      rationalWordVacuum [x,y,j,k] A
  else 0

def kernelHighestEntry (D : ℕ) (r : CopyLabel D) (A : Occupation 24) : ℚ :=
  ∑ j ∈ A, ∑ k ∈ A, ∑ x ∈ A, ∑ y ∈ A, kernelHighestTerm D r A x y j k

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate04. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

def fourZData_4 : Matrix (CopyLabel 4) (CopyLabel 4) ℚ :=
  copyMatrixData 4 [
    [0, 0],
    [0, 0]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate13Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate13 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourLData_13 : Matrix (CopyLabel 13) (CopyLabel 13) ℚ :=
  copyMatrixData 13 [
    [1, 0, 0, 0, 0, 0, 0],
    [(11689849916810741289906063583/9668394871427482199961857042500), 1, 0, 0, 0, 0, 0],
    [(13589354797225438138011294791/23204147691425957279908456902000), (-5722733975085987028604046653929956243704293874849103118195/34281240482376075690109946909475716511496984077694073918916), 1, 0, 0, 0, 0],
    [(-509502443091073156788337649/4640829538285191455981691380400), (-133331179119516533068778683019503316626683544854170179925/45708320643168100920146595879300955348662645436925431891888), (-21706288275812938364385693437825764627858127435592841870260081720101251237530632919/517343355656801378818908150437551439728860213722088824246042411156204427158872474621), 1, 0, 0, 0],
    [(-21141801667723258155053469941/309388635885679430398779425360000), (8164139482202159622549526622922929439160404777133065091103/182833282572672403680586383517203821394650581747701727567552), (-2324798293789167976951373034105741258574109601490474266531011255089316879927249691903/8277493690508822061102530407000823035661763419553421187936678578499270834541959593936), (-27/20), 1, 0, 0],
    [(-10136985870043872385759156641/11250495850388342923591979104000), (-33675001318444951452957104866436564064713894801763875118835/365666565145344807361172767034407642789301163495403455135104), (14207100684267137636925057430646196580175114231330676073245068781101380932888748117185/33109974762035288244410121628003292142647053678213684751746714313997083338167838375744), (33/16), 0, 1, 0],
    [(481284793213666874729611098291/28126239625970857308979947760000), (80172088942951081162996041064320236757429026345000134361817/182833282572672403680586383517203821394650581747701727567552), (9311997670323750558321462484827253025351136669869329162341575057923436780900641522251/33109974762035288244410121628003292142647053678213684751746714313997083338167838375744), (-429/64), 0, 0, 1]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate14Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate14 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourLData_14 : Matrix (CopyLabel 14) (CopyLabel 14) ℚ :=
  copyMatrixData 14 [
    [1, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0],
    [0, (1220225850803980188695600294/4658665020569184332878103901), 1, 0, 0, 0, 0],
    [0, (11717788938700055281155750553/447231841974641695956297974496), (2528507447792559602104460610889800179577158385469111/11527282328038776223543938804720313165114066416035616), 1, 0, 0, 0],
    [0, (-4114421549993682560413450667/74538640329106949326049662416), (-601367064852125876386374050463549407069946629210615/1921213721339796037257323134120052194185677736005936), (-6/7), 1, 0, 0],
    [0, (-110901290240976764798767469/27104960119675254300381695424), (3973368846531165089021295245683971710764106034308603/30739419541436736596117170145920835106970843776094976), (33/56), 0, 1, 0],
    [0, (6718581527267453628143216897/27104960119675254300381695424), (143/256), 0, 0, 0, 1]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate18Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate18 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourLData_18 : Matrix (CopyLabel 18) (CopyLabel 18) ℚ :=
  copyMatrixData 18 [
    [1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, (-19622685426805868627669012/241834110471751660293852243), 1, 0, 0, 0, 0, 0, 0],
    [0, (11907899514743343096973993/3869345767548026564701635888), (-942959943853497737532933439001756109065712828299/2521638922497384864691980677182886104546196483056), 1, 0, 0, 0, 0, 0],
    [0, (-1088215349783697235979995/71654551250889380827808072), (-579204823628016596624476603524201143561035964799/1260819461248692432345990338591443052273098241528), (-322101729697288344392147952249607776977585870663556408186825263663526/896556691289636709022246400557524688955271263723517547157923999074815), 1, 0, 0, 0, 0],
    [0, (65578238647888838567920175/7738691535096053129403271776), (11390305541518521331259601334244984541751526760805/40346222759958157835071690834926177672739143728896), (1764525143126657426552304672749480878308638515903065614115538950149393/8606944236380512406613565445352237013970604131745768452716070391118224), (-746964701974071644619763663296766133499353785736298568429784445370119583960533835042401385/1257803672830877627227527488195898541504022219668692957498233729040566442330578330255827872), 1, 0, 0, 0],
    [0, (5741174184871059350371589/7738691535096053129403271776), (1310160080619562486842653224134698432946302730817/40346222759958157835071690834926177672739143728896), (-330394004973020203955159581918403323443812496648608511748486056799217/1434490706063418734435594240892039502328434021957628075452678398519704), (611650334627304855241497353688554267704941174400765416464543741776492457522000000000000/13102121591988308616953411335373943140666898121548884973939934677505900440943524273498207), (-78/35), 1, 0, 0],
    [0, (-4796259647520084320930065/573236410007115046622464576), (-24275911090440877486016355576015295113520593409485/80692445519916315670143381669852355345478287457792), (821129026386347956739303799931901501603816085711306781981372049648123/2868981412126837468871188481784079004656868043915256150905356797039408), (2506128775452890259623800369079393746679030015173179378992757673094868541242697285183739335/6708286255098014011880146603711458888021451838233029106657246554883021025763084428031081984), (351/80), 0, 1, 0],
    [0, (20045312000000000000000/80611370157250553431284081), (3327001416275461411445027332595808000000000000/157602432656086554043248792323930381534137280191), (4858111925195910439364072755509308781395355553047854473600000000000/537934014773782025413347840334514813373162758234110528294754399444889), (9098298727581159721717273136117244732110999969211385569910088158925325305639750000000000/39306364775964925850860234006121829422000694364646654921819804032517701322830572820494621), (-221/20), 0, 0, 1]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate22Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate22 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourLData_22 : Matrix (CopyLabel 22) (CopyLabel 22) ℚ :=
  copyMatrixData 22 [
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, (-281759001143527504710/1889186882518106776847), 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, (4516345162834156618785/120907960481158833718208), (-163845303147667745278173597/1241300715662491208518027376), 1, 0, 0, 0, 0, 0, 0, 0],
    [0, (-864479036197004558497/60453980240579416859104), (93704257580975353717016787/1551625894578114010647534220), (-107209907723209102697370623360346/902760519093081289878957414547685), 1, 0, 0, 0, 0, 0, 0],
    [0, (71144428250976364305/10991632771014439428928), (-656009087179626239457820719/24826014313249824170360547520), (40888012561406657173603830318939/515863153767475022787975665455820), (-50351149458651936478777592120931795/438763676641540108390949454759117472), 1, 0, 0, 0, 0, 0],
    [0, (-155175095919694458459/60453980240579416859104), (1005262441971194191709101149/99304057252999296681442190080), (-31307006481528102413340575283189/902760519093081289878957414547685), (24605740536733806567629897446205343/603300055382117649037555500293786524), (-99014764382294804145890057625027304458528/291107268883302171114657206843225690858255), 1, 0, 0, 0, 0],
    [0, (175193208941590517615/241815920962317667436416), (-578048670176143455403598799/198608114505998593362884380160), (32725041219376190027990739453963/8253810460279600364607610647293120), (-15168802217910587715934674483744511055/154444814177822118153614208075209350144), (-404387875247230340023283618623839111143595/1863086520853133895133806123796644421492832), (-241594650436252992171996347847338760300930435/150435247616908832584135131604999972144928122), 1, 0, 0, 0],
    [0, (1380000000000000/1889186882518106776847), (-203770575252764288855849127/397216229011997186725768760320), (-176764375836144120789986212342329/14444168305489300638063318632762960), (103616033331847848585777943769681895/38611203544455529538403552018802337536), (325262114945183327776230776455747800344935/1397314890639850421350354592847483316119624), (1468151455180036203053520846993983347811393285/902611485701452995504810789629999832869568732), (-204/49), 1, 0, 0],
    [0, (-72786937500000000/1889186882518106776847), (-52949955015551930470202619/66899575412546894606445264896), (45077441214468065884503493526001537/924426771551315240836052392496829440), (101065376724840752328215248891832154141/308889628355644236307228416150418700288), (8130072555576470941981350029772918139593441/18630865208531338951338061237966444214928320), (-449948144786238924459884042334773513376322589/601740990467635330336540526419999888579712488), (2907/196), 0, 1, 0],
    [0, (1147370000000000000/1889186882518106776847), (65503599217649001326101461669/1337991508250937892128905297920), (22798619955980752149014522559487803/66030483682236802916860885178344960), (8513386380551269323296066713692619085/19305601772227764769201776009401168768), (-62827488129543903360339675724249542131409/1863086520853133895133806123796644421492832), (-23092887666265972052450246932154400504514993995/9627855847482165285384648422719998217275399808), (-969/14), 0, 0, 1]
  ]

end LaughlinFock
end

end OAI
end


