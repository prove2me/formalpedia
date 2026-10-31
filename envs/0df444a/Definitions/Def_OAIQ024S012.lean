-- Prove2me | Definitions.Def_OAIQ024S012
-- name    : OAIQ024S012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:21:55.915416+00:00
-- url     : https://prove2.me/theorems/03612df7-b5b1-4894-96cb-b88f3c86a74b
-- title:
--   Definitions bundle OAIQ024S012 of the split of OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SKRatio.Certificate.Data.J4K12.blocks`, `OAI.SKRatio.Certificate.Data.J4K3.blocks`, `OAI.SKRatio.Certificate.Data.J4K4.blocks`.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: [`SKRatio_Certificates_ScalarDataJ4K12`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K12.lean), [`SKRatio_Certificates_ScalarDataJ4K3`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K3.lean), [`SKRatio_Certificates_ScalarDataJ4K4`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K4.lean).
--
--   **Imports.** It imports the bundle `OAIQ024S000` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SKRatio.Certificate.Data.J4K12.check_22`, `OAI.SKRatio.Certificate.Data.J4K12.check_23`, `OAI.SKRatio.Certificate.Data.J4K12.check_24`, `OAI.SKRatio.Certificate.Data.J4K12.check_25`, `OAI.SKRatio.Certificate.Data.J4K12.check_26`, `OAI.SKRatio.Certificate.Data.J4K12.check_27`, `OAI.SKRatio.Certificate.Data.J4K12.check_28`, `OAI.SKRatio.Certificate.Data.J4K12.check_29`, `OAI.SKRatio.Certificate.Data.J4K12.check_30`, `OAI.SKRatio.Certificate.Data.J4K12.check_31`, `OAI.SKRatio.Certificate.Data.J4K12.check_32`, `OAI.SKRatio.Certificate.Data.J4K12.check_33`, `OAI.SKRatio.Certificate.Data.J4K12.check_34`, `OAI.SKRatio.Certificate.Data.J4K12.check_35`, `OAI.SKRatio.Certificate.Data.J4K12.check_36`, `OAI.SKRatio.Certificate.Data.J4K12.check_37`, `OAI.SKRatio.Certificate.Data.J4K12.check_38`, `OAI.SKRatio.Certificate.Data.J4K12.check_39`, `OAI.SKRatio.Certificate.Data.J4K12.checks`, `OAI.SKRatio.Certificate.Data.J4K3.check_33`, `OAI.SKRatio.Certificate.Data.J4K3.check_34`, `OAI.SKRatio.Certificate.Data.J4K3.check_35`, `OAI.SKRatio.Certificate.Data.J4K3.check_36`, `OAI.SKRatio.Certificate.Data.J4K3.check_37`, `OAI.SKRatio.Certificate.Data.J4K3.check_38`, `OAI.SKRatio.Certificate.Data.J4K3.check_39`, `OAI.SKRatio.Certificate.Data.J4K3.checks` and `OAI.SKRatio.Certificate.Data.J4K4.checks`; the proofs of `OAI.SKRatio.Certificate.Data.J4K12.check_22`, `OAI.SKRatio.Certificate.Data.J4K12.check_23`, `OAI.SKRatio.Certificate.Data.J4K12.check_24`, `OAI.SKRatio.Certificate.Data.J4K12.check_25`, `OAI.SKRatio.Certificate.Data.J4K12.check_26`, `OAI.SKRatio.Certificate.Data.J4K12.check_27`, `OAI.SKRatio.Certificate.Data.J4K12.check_28`, `OAI.SKRatio.Certificate.Data.J4K12.check_29`, `OAI.SKRatio.Certificate.Data.J4K12.check_30`, `OAI.SKRatio.Certificate.Data.J4K12.check_31`, `OAI.SKRatio.Certificate.Data.J4K12.check_32`, `OAI.SKRatio.Certificate.Data.J4K12.check_33`, `OAI.SKRatio.Certificate.Data.J4K12.check_34`, `OAI.SKRatio.Certificate.Data.J4K12.check_35`, `OAI.SKRatio.Certificate.Data.J4K12.check_36`, `OAI.SKRatio.Certificate.Data.J4K12.check_37`, `OAI.SKRatio.Certificate.Data.J4K12.check_38`, `OAI.SKRatio.Certificate.Data.J4K12.check_39`, `OAI.SKRatio.Certificate.Data.J4K12.checks`, `OAI.SKRatio.Certificate.Data.J4K3.check_33`, `OAI.SKRatio.Certificate.Data.J4K3.check_34`, `OAI.SKRatio.Certificate.Data.J4K3.check_35`, `OAI.SKRatio.Certificate.Data.J4K3.check_36`, `OAI.SKRatio.Certificate.Data.J4K3.check_37`, `OAI.SKRatio.Certificate.Data.J4K3.check_38`, `OAI.SKRatio.Certificate.Data.J4K3.check_39`, `OAI.SKRatio.Certificate.Data.J4K3.checks`, `OAI.SKRatio.Certificate.Data.J4K4.checks`, `OAI.SKRatio.Certificate.diagonal_envelope` and `OAI.SKRatio.Certificate.valid4`.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ024S000

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K12

def blocks : ℕ → Box
  | 0 => ⟨-1/1000000,1/1000000⟩
  | 1 => ⟨-1/1000000,1/1000000⟩
  | 2 => ⟨-1/1000000,1/1000000⟩
  | 3 => ⟨-1/1000000,1/1000000⟩
  | 4 => ⟨-1/1000000,1/1000000⟩
  | 5 => ⟨-1/1000000,1/1000000⟩
  | 6 => ⟨-1/1000000,1/1000000⟩
  | 7 => ⟨-1/1000000,1/1000000⟩
  | 8 => ⟨-1/1000000,1/1000000⟩
  | 9 => ⟨-1/1000000,1/1000000⟩
  | 10 => ⟨-1/1000000,1/1000000⟩
  | 11 => ⟨-1/1000000,1/1000000⟩
  | 12 => ⟨1/1000000,1/500000⟩
  | 13 => ⟨21/1000000,23/1000000⟩
  | 14 => ⟨9/40000,57/250000⟩
  | 15 => ⟨423/250000,1703/1000000⟩
  | 16 => ⟨903/100000,4531/500000⟩
  | 17 => ⟨4147/125000,8307/250000⟩
  | 18 => ⟨20397/250000,5101/62500⟩
  | 19 => ⟨132077/1000000,413/3125⟩
  | 20 => ⟨35257/250000,17641/125000⟩
  | 21 => ⟨50579/500000,50599/500000⟩
  | 22 => ⟨12533/250000,50187/1000000⟩
  | 23 => ⟨1771/100000,111/6250⟩
  | 24 => ⟨917/200000,461/100000⟩
  | 25 => ⟨111/125000,897/1000000⟩
  | 26 => ⟨13/100000,133/1000000⟩
  | 27 => ⟨7/500000,1/62500⟩
  | 28 => ⟨1/1000000,1/500000⟩
  | 29 => ⟨-1/1000000,1/1000000⟩
  | 30 => ⟨-1/1000000,1/1000000⟩
  | 31 => ⟨-1/1000000,1/1000000⟩
  | 32 => ⟨-1/1000000,1/1000000⟩
  | 33 => ⟨-1/1000000,1/1000000⟩
  | 34 => ⟨-1/1000000,1/1000000⟩
  | 35 => ⟨-1/1000000,1/1000000⟩
  | 36 => ⟨-1/1000000,1/1000000⟩
  | 37 => ⟨-1/1000000,1/1000000⟩
  | 38 => ⟨-1/1000000,1/1000000⟩
  | 39 => ⟨-1/1000000,1/1000000⟩
  | _ => Box.rat 0

end SKRatio.Certificate.Data.J4K12

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K3

def blocks : ℕ → Box
  | 0 => ⟨-1/1000000,1/1000000⟩
  | 1 => ⟨-1/1000000,1/1000000⟩
  | 2 => ⟨-1/1000000,1/1000000⟩
  | 3 => ⟨-1/1000000,1/1000000⟩
  | 4 => ⟨-1/1000000,1/1000000⟩
  | 5 => ⟨-1/1000000,1/1000000⟩
  | 6 => ⟨-1/1000000,1/1000000⟩
  | 7 => ⟨-1/1000000,1/1000000⟩
  | 8 => ⟨-1/1000000,1/1000000⟩
  | 9 => ⟨-1/1000000,1/1000000⟩
  | 10 => ⟨-1/1000000,1/1000000⟩
  | 11 => ⟨-1/1000000,1/1000000⟩
  | 12 => ⟨0,1/1000000⟩
  | 13 => ⟨7/1000000,9/1000000⟩
  | 14 => ⟨37/500000,1/12500⟩
  | 15 => ⟨49/100000,257/500000⟩
  | 16 => ⟨1047/500000,2157/1000000⟩
  | 17 => ⟨1297/250000,2651/500000⟩
  | 18 => ⟨303/50000,6239/1000000⟩
  | 19 => ⟨107/62500,981/500000⟩
  | 20 => ⟨103/50000,667/250000⟩
  | 21 => ⟨12339/1000000,13363/1000000⟩
  | 22 => ⟨17301/1000000,9273/500000⟩
  | 23 => ⟨717/62500,12377/1000000⟩
  | 24 => ⟨4419/1000000,4847/1000000⟩
  | 25 => ⟨1089/1000000,311/250000⟩
  | 26 => ⟨9/50000,113/500000⟩
  | 27 => ⟨1/50000,31/1000000⟩
  | 28 => ⟨1/1000000,1/250000⟩
  | 29 => ⟨-1/1000000,1/1000000⟩
  | 30 => ⟨-1/1000000,1/1000000⟩
  | 31 => ⟨-1/1000000,1/1000000⟩
  | 32 => ⟨-1/1000000,1/1000000⟩
  | 33 => ⟨-1/1000000,1/1000000⟩
  | 34 => ⟨-1/1000000,1/1000000⟩
  | 35 => ⟨-1/1000000,1/1000000⟩
  | 36 => ⟨-1/1000000,1/1000000⟩
  | 37 => ⟨-1/1000000,1/1000000⟩
  | 38 => ⟨-1/1000000,1/1000000⟩
  | 39 => ⟨-1/1000000,1/1000000⟩
  | _ => Box.rat 0

end SKRatio.Certificate.Data.J4K3

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K4

def blocks : ℕ → Box
  | 0 => ⟨-1/1000000,1/1000000⟩
  | 1 => ⟨-1/1000000,1/1000000⟩
  | 2 => ⟨-1/1000000,1/1000000⟩
  | 3 => ⟨-1/1000000,1/1000000⟩
  | 4 => ⟨-1/1000000,1/1000000⟩
  | 5 => ⟨-1/1000000,1/1000000⟩
  | 6 => ⟨-1/1000000,1/1000000⟩
  | 7 => ⟨-1/1000000,1/1000000⟩
  | 8 => ⟨-1/1000000,1/1000000⟩
  | 9 => ⟨0,1/1000000⟩
  | 10 => ⟨3/1000000,1/200000⟩
  | 11 => ⟨17/500000,9/250000⟩
  | 12 => ⟨103/500000,53/250000⟩
  | 13 => ⟨863/1000000,219/250000⟩
  | 14 => ⟨2299/1000000,2319/1000000⟩
  | 15 => ⟨397/125000,3229/1000000⟩
  | 16 => ⟨239/200000,1253/1000000⟩
  | 17 => ⟨1921/1000000,1027/500000⟩
  | 18 => ⟨811/62500,3271/250000⟩
  | 19 => ⟨16093/1000000,1017/62500⟩
  | 20 => ⟨889/250000,3781/1000000⟩
  | 21 => ⟨4629/1000000,4919/1000000⟩
  | 22 => ⟨18521/1000000,9469/500000⟩
  | 23 => ⟨10621/500000,2163/100000⟩
  | 24 => ⟨12909/1000000,1639/125000⟩
  | 25 => ⟨1251/250000,641/125000⟩
  | 26 => ⟨677/500000,703/500000⟩
  | 27 => ⟨67/250000,283/1000000⟩
  | 28 => ⟨39/1000000,43/1000000⟩
  | 29 => ⟨1/250000,3/500000⟩
  | 30 => ⟨0,1/1000000⟩
  | 31 => ⟨-1/1000000,1/1000000⟩
  | 32 => ⟨-1/1000000,1/1000000⟩
  | 33 => ⟨-1/1000000,1/1000000⟩
  | 34 => ⟨-1/1000000,1/1000000⟩
  | 35 => ⟨-1/1000000,1/1000000⟩
  | 36 => ⟨-1/1000000,1/1000000⟩
  | 37 => ⟨-1/1000000,1/1000000⟩
  | 38 => ⟨-1/1000000,1/1000000⟩
  | 39 => ⟨-1/1000000,1/1000000⟩
  | _ => Box.rat 0

end SKRatio.Certificate.Data.J4K4

end

end OAI
end


