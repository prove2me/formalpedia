-- Prove2me | Definitions.Def_OAIQ084L027
-- name    : OAIQ084L027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:33:23.704198+00:00
-- url     : https://prove2.me/theorems/549f42d0-5589-4fc5-937d-7792727de180
-- title:
--   Definitions bundle OAIQ084L027 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 12 definitions. The definitions and types are `OAI.LaughlinFock.fourPivotData_10`, `OAI.LaughlinFock.fourPivotData_11`, `OAI.LaughlinFock.fourPivotData_12`, `OAI.LaughlinFock.fourPivotData_13`, `OAI.LaughlinFock.fourPivotData_14`, `OAI.LaughlinFock.fourPivotData_20`, `OAI.LaughlinFock.fourPivotData_21`, `OAI.LaughlinFock.fourPivotData_23`, `OAI.LaughlinFock.fourYData_23`, `OAI.LaughlinFock.localBlockError`, `OAI.LaughlinFock.localHamiltonian`, `OAI.LaughlinFock.pairSpinMatrix`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinFock_Certificate10Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate10Data.lean), [`LaughlinFock_Certificate11Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate11Data.lean), [`LaughlinFock_Certificate12Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate12Data.lean), [`LaughlinFock_Certificate13Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate13Data.lean), [`LaughlinFock_Certificate14Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate14Data.lean), [`LaughlinFock_Certificate20Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate20Data.lean), [`LaughlinFock_Certificate21Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate21Data.lean), [`LaughlinFock_Certificate23Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate23Data.lean), [`LaughlinFock_LocalEnergy`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/LocalEnergy.lean), [`LaughlinFock_PairLie`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/PairLie.lean), [`LaughlinFock_RelativePerturbation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/RelativePerturbation.lean).
--
--   **Imports.** It imports the published bundle `Def_LaughlinFock`; the bundles `OAIQ084L007`, `OAIQ084L012`, `OAIQ084L016` and `OAIQ084L017` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.LaughlinFock.fourYChecked_23`; the proofs of `OAI.LaughlinFock.averagedRowsFour_eventual_bound`, `OAI.LaughlinFock.fockInequality_eventual_of_certificates`, `OAI.LaughlinFock.fourYChecked_23`, `OAI.LaughlinFock.integer_certificate_10`, `OAI.LaughlinFock.integer_certificate_11`, `OAI.LaughlinFock.integer_certificate_12`, `OAI.LaughlinFock.integer_certificate_13`, `OAI.LaughlinFock.integer_certificate_14`, `OAI.LaughlinFock.integer_certificate_20`, `OAI.LaughlinFock.integer_certificate_21` and `OAI.LaughlinFock.integer_certificate_23`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L007
import Definitions.Def_OAIQ084L012
import Definitions.Def_OAIQ084L016
import Definitions.Def_OAIQ084L017

section
-- module Solutions.OAIQ084_LF.LaughlinFock_LocalEnergy
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
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


def localHamiltonian (L P Q : ℕ) : FockMatrix L :=
  ∑ p ∈ Finset.range P, (localPairAnnihilator L Q p)ᴴ * localPairAnnihilator L Q p

open Filter Topology

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RelativePerturbation
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
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



def localBlockError {β : Type*} [Fintype β] (L Q : ℕ)
    (M Mstar : Matrix β β ℂ) : Matrix (β × Occupation L) (β × Occupation L) ℂ :=
  M ⊗ₖ ((localDeltaInv L Q)ᴴ * localDeltaInv L Q) - Mstar ⊗ₖ 1

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



def fourPivotData_10 : CopyLabel 10 → ℚ :=
  copyDiagonalData 10 [0, (8105210798198965041984329871639/4294967296000000000000000000), 0, 0, 0]

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



def fourPivotData_11 : CopyLabel 11 → ℚ :=
  copyDiagonalData 11 [(190381209389164352165217311137563/13421772800000000000000000), (75733701136929555872962963074555822492988872938964717113847/26288614586528711076345008361268314112000000000000000000), (31160160353385400741807881710332433700203771124666113757322271747415105611829819889953/948715161298772175963026916321379196390157829147195853630437756764160000000000000000), 0, 0, 0]

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



def fourPivotData_12 : CopyLabel 12 → ℚ :=
  copyDiagonalData 12 [0, (6788265306672530474461182566529/536870912000000000000000000), (13166444846555554646802017772530214918706281995746569/9373513853115332101779238150954024960000000000000000), 0, 0, 0]

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



def fourPivotData_13 : CopyLabel 13 → ℚ :=
  copyDiagonalData 13 [(10337447796530263968199217549841/5368709120000000000000), (694195119768115532724726424916883259357813927573304996858049/5898499968408403534724191540477952000000000000000000000), (13968270602733637228110520061813888872679225770496398254643145101217519533289556814767/599108100334132932380545461509173481945991026270869020893354393600000000000000000), (5883696273719332012203518889149014794794346104783014799260478072665637020854974785901422275094899856437/2169895306004744650385661731012823753860517309855412043890472669282112853650167455792758784000000000000000), 0, 0, 0]

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



def fourPivotData_14 : CopyLabel 14 → ℚ :=
  copyDiagonalData 14 [0, (12452611599981429721783171727373/13421772800000000000000000), (9726144464282717438615198366482764233064993538530051/7401461110012656107624228297113600000000000000000), (756220433458987106260911093151509838908241844881935813830292724684837401603/1611630879254078375650507890146454279656352974168128277708800000000000000000), 0, 0, 0]

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



def fourPivotData_20 : CopyLabel 20 → ℚ :=
  copyDiagonalData 20 [0, (869244263371676065818764349012483/41943040000000000000000), (385172015598864243071868844218861009117255205346517/4240899453874657298689483079680000000000000), (506504886879459989851432926271154150860670244829450849894026924491326389/23676159323074265915334666689859449280488140539166720000000000000), (454294178708108325951467664004177789316244900017142236248749409163960139861/990453034608207371192293162243812802743102559566760777579422220288000), (2442864701541646919176317341151732237970348495765660569758482956637734977606633919/4142986207814888155985228282385465653388685788783795946643212122348912640000), (718567282981337674007366669002548593087012201710765379962596158858384241414384953062941/3238952193537869690068996271307928151869950906519474627711061817423979588364533760000), 0, 0, 0]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate21Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate21 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourPivotData_21 : CopyLabel 21 → ℚ :=
  copyDiagonalData 21 [(204087153776864912607415934305681690743/20971520000000000000), (68686051000951308092485085224845625578784487532876946557/2649183277647207880367275045683200000000000000), (145108231049514310362969863743338229942453332146654340745869/220766470678375750853113283073331280432017089228800), (545921396214739089908393066994960984590653939463756496884072177308629/15927974377500364029115758938990830326904437938405829443584000), (619447964244996785266991661282173764626085685727450857710891938144176089659/47646726228095346508071864492248368510360540499034527535855632384000), (628067262021864256238767162144689872333259282275344863924787846024809203999130291/291544861196246283749438965506187030964581542619414042000757606136361779200), (13719661067550378937930651710372384060889169133346919609631684465615105930952230819273/2785476210447405963060215013242233420577456740160515262628607232634722624208896000), (74340884648338837367812460820456447521614018774423081875531150438350664268838708663613/489065703770381951526275079989036446711996638548250045004638326631256773618439290880), 0, 0, 0]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate23Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate23 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

def fourYData_23 : Matrix (CopyLabel 23) (CopyLabel 23) ℚ :=
  copyMatrixData 23 [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  ]

def fourPivotData_23 : CopyLabel 23 → ℚ :=
  copyDiagonalData 23 [(3596807727106964372495493/800), (2695083358684056754955880339/479349747996800), (41460066632617412037005591462619/516255843783397145600), (1687804688951660387226431508125931/510968990688790738386944), (440474619464572437164875860934388795628693/1578953284015024971845590042624000), (17875786513703508084674654426461795282409857029/427150903847492133676483124235449139200), (161052762702264252299142605764190579764316339459883/60839887585431546652187840550429693824204800), (3104434579359970407545821546788921635658478795883201511/27210227236450195941983139093014766803941221990400), (617253866866789232996626176408903607856598861326229375/107041065082302247237303795868201218521751441375232), 0, 0, 0]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_PairLie
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Lie. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder


def pairSpinMatrix (Q : ℕ) : Matrix (SectorOccupation Q 2) (Fin (2*Q-2+1)) ℂ :=
  fun S p => pairVector Q p.val S



end LaughlinFock
end

end OAI
end


