-- Prove2me | Definitions.Def_OAIQ084L023
-- name    : OAIQ084L023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:32:56.532891+00:00
-- url     : https://prove2.me/theorems/476d9739-432d-45ff-851b-32d7a0578b41
-- title:
--   Definitions bundle OAIQ084L023 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 7 definitions. The definitions and types are `OAI.LaughlinFock.fourLData_11`, `OAI.LaughlinFock.fourLData_12`, `OAI.LaughlinFock.fourPivotData_19`, `OAI.LaughlinFock.planarFourGram`, `OAI.LaughlinFock.planarFourWedgeMatrix`, `OAI.LaughlinFock.planarHighestFourAnnihilator`, `OAI.LaughlinFock.rationalHighestEntry`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinFock_Certificate11Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate11Data.lean), [`LaughlinFock_Certificate12Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate12Data.lean), [`LaughlinFock_Certificate19Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate19Data.lean), [`LaughlinFock_RationalWedge`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/RationalWedge.lean), [`LaughlinFock_RelativeTransfer`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/RelativeTransfer.lean).
--
--   **Imports.** It imports the published bundle `Def_LaughlinFock`; the bundles `OAIQ084L007`, `OAIQ084L012`, `OAIQ084L018` and `OAIQ084L020` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ084L043`; the statements `OAI.LaughlinFock.averagedRowsFour_eventual_bound`, `OAI.LaughlinFock.certificate_four` and `OAI.LaughlinFock.fockInequality_eventual_of_certificates`; the proof of `OAI.LaughlinFock.thm_fock`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L007
import Definitions.Def_OAIQ084L012
import Definitions.Def_OAIQ084L018
import Definitions.Def_OAIQ084L020

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RelativeTransfer
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative Transfer. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology



def planarHighestFourAnnihilator (D : ℕ) (r : CopyLabel D) : FockMatrix 24 :=
  ∑ b : FourHighestShell 24 D, planarLocalCopyMatrix D r b •
    (annihilator 24 b.val.2.val.2 * annihilator 24 b.val.2.val.1 * limitPairAnnihilator 24 b.val.1.val)



def planarFourWedgeMatrix (D : ℕ) : Matrix (SectorOccupation 24 4) (CopyLabel D) ℂ :=
  fun A r => annihilatorVector 24 4 (planarHighestFourAnnihilator D r) A

def planarFourGram (D : ℕ) : Matrix (CopyLabel D) (CopyLabel D) ℂ :=
  (planarFourWedgeMatrix D)ᴴ * planarFourWedgeMatrix D

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RationalWedge
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Wedge. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def rationalHighestEntry (D : ℕ) (r : CopyLabel D) (A : Occupation 24) : ℚ :=
  ∑ b : FourHighestShell 24 D, ∑ xy : IncreasingPair 24,
    rationalHighestTerm D r b.val.1.val b.val.2.val.1.val b.val.2.val.2.val
      xy.val.1.val xy.val.2.val *
    rationalWordVacuum [xy.val.1, xy.val.2, b.val.2.val.1, b.val.2.val.2] A

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate11Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate11 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourLData_11 : Matrix (CopyLabel 11) (CopyLabel 11) ℚ :=
  copyMatrixData 11 [
    [1, 0, 0, 0, 0, 0],
    [(31383047013636756733203467204/7051155903302383413526567079169), 1, 0, 0, 0, 0],
    [(-9939372038972515368176183805/25070776545075141025872238503712), (125765185144970030615819379031746558389214906329570600851695/403913072730290964655802469730964386629273989007811824607184), 1, 0, 0, 0],
    [(-296100363493333293793952873/451273977811352538465700293066816), (-226560393294244413444122439360815730073560117487375319268271/807826145460581929311604939461928773258547978015623649214368), (-7/10), 1, 0, 0],
    [(-58943366399805908686060530373/14326158025757223443355564859264), (528213777608874128586441391933335545234702606584196523577119/3231304581842327717246419757847715093034191912062494596857472), (21/40), 0, 1, 0],
    [(27580305897858760803256936653173/601698637081803384620933724089088), (165/256), 0, 0, 0, 1]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate12Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate12 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourLData_12 : Matrix (CopyLabel 12) (CopyLabel 12) ℚ :=
  copyMatrixData 12 [
    [1, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0],
    [0, (163364364513064607528121281645/335222978107285455528947287236), 1, 0, 0, 0],
    [0, (-163364364513064607528121281645/893927941619427881410526099296), (-3/8), 1, 0, 0],
    [0, (-1/16), 0, 0, 1, 0],
    [0, (833361664825525588495918957815/1787855883238855762821052198592), (33/64), 0, 0, 1]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate19Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate19 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourPivotData_19 : CopyLabel 19 → ℚ :=
  copyDiagonalData 19 [(134272890216321057298020353848200719937/5242880000000000000000), (6416213893363475534282471017076289038717677460210985136084893/3152646105238913004684714107734589440000000000000000), (1290449529563955732542701421323712550116316965134583130865730278684193183973793869/65562364105128217643884797578418283244570602552936228959813632000000000000), (4069717415493395784179764413327622017283928267341277224165386816373687138604893891849137144498183/689842690211214441120301740423261708606428425476313810172586734121643629289472000000000000), (10523360835063401957396916150532242395316070491506110656596640614459093767501830240262118396280510200752203/22625940308584729134971537885942573168038792470643950563237378436915214148337352367737597008281600000), (12822518125808256622859078178399541250286886113926611863552748045336341503222635909198372095506361219198331685601/3169822888575045639281917984673524621017939588654288034130143164297734953804118923711198985086367690653696000), (698847760952378595541191690326365080417166967358647868797028146956772497602403809764930020401490316492538821468124921/116134438425514455087531448394422358293518883075178796345145097142223147540463076998393682695526075542725506105344000), 0, 0, 0]

end LaughlinFock
end

end OAI
end


