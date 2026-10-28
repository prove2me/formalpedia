-- Prove2me | Definitions.Def_OAIQ084L035
-- name    : OAIQ084L035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:35:06.412818+00:00
-- url     : https://prove2.me/theorems/8bf1e716-d66d-4439-9673-c76da1486027
-- title:
--   Definitions bundle OAIQ084L035 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 7 definitions. The definitions and types are `OAI.LaughlinFock.fourYData_16`, `OAI.LaughlinFock.fourZData_10`, `OAI.LaughlinFock.fourZData_11`, `OAI.LaughlinFock.fourZData_20`, `OAI.LaughlinFock.rationalFourTrace`, `OAI.LaughlinFock.rowFourPrewedge`, `OAI.LaughlinFock.sourceRowFourKernel`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinFock_Certificate10Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate10Data.lean), [`LaughlinFock_Certificate11Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate11Data.lean), [`LaughlinFock_Certificate16Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate16Data.lean), [`LaughlinFock_Certificate20Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate20Data.lean), [`LaughlinFock_FourTraces`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/FourTraces.lean), [`LaughlinFock_RationalFour`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/RationalFour.lean).
--
--   **Imports.** It imports the published bundle `Def_LaughlinFock`; the bundles `OAIQ084L012`, `OAIQ084L015`, `OAIQ084L018` and `OAIQ084L020` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.LaughlinFock.fourYChecked_16`; the proofs of `OAI.LaughlinFock.averagedRowsFour_eventual_bound`, `OAI.LaughlinFock.certificate_four`, `OAI.LaughlinFock.fourYChecked_16`, `OAI.LaughlinFock.integer_certificate_10`, `OAI.LaughlinFock.integer_certificate_11`, `OAI.LaughlinFock.integer_certificate_16` and `OAI.LaughlinFock.integer_certificate_20`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L012
import Definitions.Def_OAIQ084L015
import Definitions.Def_OAIQ084L018
import Definitions.Def_OAIQ084L020

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RationalFour
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Four. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def rationalFourTrace (D t : ℕ) (a : RowEntry t → ℚ) :
    Matrix (CopyLabel D) (CopyLabel D) ℚ := fun r s =>
  -(∑ b : RowEntry t, ∑ c : RowEntry t, if D ≤ rowFourLevel b c then
    a b*a c*rationalFourFactor D b c *
      rationalCopyPolynomial D (rowFourLevel b c) r.val.val (rowP b) (rowJ b) (rowI c) *
      rationalCopyPolynomial D (rowFourLevel b c) s.val.val (rowP c) (rowJ c) (rowI b)
    else 0)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate10Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate10 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourZData_10 : Matrix (CopyLabel 10) (CopyLabel 10) ℚ :=
  copyMatrixData 10 [
    [0, 0, 0, 0, 0],
    [0, 3780, 0, (-2835/4), (2835/2)],
    [0, 0, 0, 0, 0],
    [0, (-2835/4), 0, (8505/64), (-8505/32)],
    [0, (2835/2), 0, (-8505/32), (8505/16)]
  ]

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



def fourZData_11 : Matrix (CopyLabel 11) (CopyLabel 11) ℚ :=
  copyMatrixData 11 [
    [3628800, 0, 0, 0, -14175, 155925],
    [0, 30240, 0, -1890, 0, (155925/8)],
    [0, 0, (3375/2), (-4725/4), (14175/16), 0],
    [0, -1890, (-4725/4), 945, (-19845/32), (-155925/128)],
    [-14175, 0, (14175/16), (-19845/32), (133245/256), (-155925/256)],
    [155925, (155925/8), 0, (-155925/128), (-155925/256), (39449025/2048)]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate16Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate16 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

def fourYData_16 : Matrix (CopyLabel 16) (CopyLabel 16) ℚ :=
  copyMatrixData 16 [
    [(-3023300183640213893190968391086889/167772160000000000000000), (-1842284299727598695958363192819/4194304000000000000000), (4978857332568431590081678121247/33554432000000000000000), (-495035435219731541754508880991/134217728000000000000000), (-379088797146560907753377563533/83886080000000000000000), (-1950638107811679763870313499579/335544320000000000000000), (830433036679330373158862049057/83886080000000000000000), (-780293120878982200971277577781/134217728000000000000000)],
    [(-1842284299727598695958363192819/4194304000000000000000), (-23811117256265722049574939091203/1677721600000000000000000), (451840005330447003265547996301/167772160000000000000000), (765033524894004427226426290029/1342177280000000000000000), (-299360130730835687934042178557/1677721600000000000000000), (-54641732479826306851381037121/134217728000000000000000), (1596360042122635609616004677469/1677721600000000000000000), (-1867439584107586370782878530553/1342177280000000000000000)],
    [(4978857332568431590081678121247/33554432000000000000000), (451840005330447003265547996301/167772160000000000000000), (-83970211150334552496385437351/67108864000000000000000), (48488780217799936547817299631/335544320000000000000000), (-142712675539696745387515611/10485760000000000000000), (55761689248689962568566349/2097152000000000000000), (-14386490313579701778931067169/335544320000000000000000), (-26878148679024614358884359863/67108864000000000000000)],
    [(-495035435219731541754508880991/134217728000000000000000), (765033524894004427226426290029/1342177280000000000000000), (48488780217799936547817299631/335544320000000000000000), (-3262158077323107028703896377657/26843545600000000000000000), (52643089387008932592230169867/1342177280000000000000000), (53630278770653547050750239809/2684354560000000000000000), (-501723637603154001058680647991/6710886400000000000000000), (1593230986748752248427033240737/5368709120000000000000000)],
    [(-379088797146560907753377563533/83886080000000000000000), (-299360130730835687934042178557/1677721600000000000000000), (-142712675539696745387515611/10485760000000000000000), (52643089387008932592230169867/1342177280000000000000000), (-35077411519799463622935034803/1677721600000000000000000), (1492590838618072536119968653/671088640000000000000000), (40370172661050112192774463001/1677721600000000000000000), (-86392805913427500216351869247/1342177280000000000000000)],
    [(-1950638107811679763870313499579/335544320000000000000000), (-54641732479826306851381037121/134217728000000000000000), (55761689248689962568566349/2097152000000000000000), (53630278770653547050750239809/2684354560000000000000000), (1492590838618072536119968653/671088640000000000000000), (-18951724542978071115384073653/1342177280000000000000000), (3060950838759256839852570543/134217728000000000000000), (-8106039764158833303443597961/536870912000000000000000)],
    [(830433036679330373158862049057/83886080000000000000000), (1596360042122635609616004677469/1677721600000000000000000), (-14386490313579701778931067169/335544320000000000000000), (-501723637603154001058680647991/6710886400000000000000000), (40370172661050112192774463001/1677721600000000000000000), (3060950838759256839852570543/134217728000000000000000), (-184942013999244668370911421/4194304000000000000000), (18946767647015678576766350691/268435456000000000000000)],
    [(-780293120878982200971277577781/134217728000000000000000), (-1867439584107586370782878530553/1342177280000000000000000), (-26878148679024614358884359863/67108864000000000000000), (1593230986748752248427033240737/5368709120000000000000000), (-86392805913427500216351869247/1342177280000000000000000), (-8106039764158833303443597961/536870912000000000000000), (18946767647015678576766350691/268435456000000000000000), (-28303565196748876363274618673/42949672960000000000000)]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate20Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate20 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourZData_20 : Matrix (CopyLabel 20) (CopyLabel 20) ℚ :=
  copyMatrixData 20 [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 266765571072000, 0, 0, 0, 0, 0, 0, -130256626500, (12993098493375/8)],
    [0, 0, 4903778880000, 0, 0, 0, 0, (-67043851875/4), 0, (9280784638125/16)],
    [0, 0, 0, 245188944000, 0, 0, (-17239847625/4), (-335219259375/32), (227949096375/8), (16705412348625/128)],
    [0, 0, 0, 0, 28291032000, -2210236875, -5746615875, 0, (97692469875/8), (1856156927625/128)],
    [0, 0, 0, 0, -2210236875, (40226311125/16), (-63212774625/32), (316063873125/256), 0, (-9280784638125/2048)],
    [0, 0, 0, (-17239847625/4), -5746615875, (-63212774625/32), 3831077250, (-1369610116875/1024), (-423334036125/128), (-16705412348625/4096)],
    [0, 0, (-67043851875/4), (-335219259375/32), 0, (316063873125/256), (-1369610116875/1024), (15697839031875/8192), (-5698727409375/2048), (-64965492466875/32768)],
    [0, -130256626500, 0, (227949096375/8), (97692469875/8), 0, (-423334036125/128), (-5698727409375/2048), (15012076204125/1024), (-12993098493375/16384)],
    [0, (12993098493375/8), (9280784638125/16), (16705412348625/128), (1856156927625/128), (-9280784638125/2048), (-16705412348625/4096), (-64965492466875/32768), (-12993098493375/16384), (121494751697694375/524288)]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourTraces
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Traces. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder



def rowFourPrewedge {β : Type*} [Fintype β] (Q : ℕ)
    (p : β → Fin (2*Q-2+1)) (i j : β → Orbital Q) (a : β → ℝ) :
    Matrix (FourUncoupled Q) (FourUncoupled Q) ℂ :=
  -(∑ b, ∑ c, (a b*a c : ℂ) • Matrix.vecMulVec
    (orderedFourColumn Q (p b) (j b) (i c)) (star (orderedFourColumn Q (p c) (j c) (i b))))



def sourceRowFourKernel {Q t : ℕ} (hQ : 8 ≤ Q) (a : RowEntry t → ℝ) :
    Matrix (FourUncoupled Q) (FourUncoupled Q) ℂ :=
  rowFourPrewedge Q (sourceRowFourP hQ) (sourceRowI hQ) (sourceRowJ hQ) a

end LaughlinFock
end

end OAI
end


