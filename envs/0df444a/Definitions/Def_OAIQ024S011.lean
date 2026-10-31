-- Prove2me | Definitions.Def_OAIQ024S011
-- name    : OAIQ024S011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:21:10.279995+00:00
-- url     : https://prove2.me/theorems/6bce318f-b912-4832-94d8-ed57c58a3ae3
-- title:
--   Definitions bundle OAIQ024S011 of the split of OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 6 definitions. The definitions and types are `OAI.SKRatio.Certificate.Data.J4K11.blocks`, `OAI.SKRatio.Certificate.Data.J4K2.blocks`, `OAI.SKRatio.Certificate.Data.J4K4.expression`, `OAI.SKRatio.Certificate.Data.J4K5.expression`, `OAI.SKRatio.Certificate.Data.J4K6.expression`, `OAI.SKRatio.Certificate.Data.J4K9.expression`.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: [`SKRatio_Certificates_ScalarDataJ4K11`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K11.lean), [`SKRatio_Certificates_ScalarDataJ4K2`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K2.lean), [`SKRatio_Certificates_ScalarDataJ4K4`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K4.lean), [`SKRatio_Certificates_ScalarDataJ4K5`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K5.lean), [`SKRatio_Certificates_ScalarDataJ4K6`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K6.lean), [`SKRatio_Certificates_ScalarDataJ4K9`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K9.lean).
--
--   **Imports.** It imports the bundle `OAIQ024S000` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SKRatio.Certificate.Data.J4K11.check_14`, `OAI.SKRatio.Certificate.Data.J4K11.check_15`, `OAI.SKRatio.Certificate.Data.J4K11.check_16`, `OAI.SKRatio.Certificate.Data.J4K11.check_17`, `OAI.SKRatio.Certificate.Data.J4K11.check_18`, `OAI.SKRatio.Certificate.Data.J4K11.check_19`, `OAI.SKRatio.Certificate.Data.J4K11.check_20`, `OAI.SKRatio.Certificate.Data.J4K11.check_21`, `OAI.SKRatio.Certificate.Data.J4K11.check_22`, `OAI.SKRatio.Certificate.Data.J4K11.check_23`, `OAI.SKRatio.Certificate.Data.J4K11.check_24`, `OAI.SKRatio.Certificate.Data.J4K11.check_25`, `OAI.SKRatio.Certificate.Data.J4K11.check_26`, `OAI.SKRatio.Certificate.Data.J4K11.check_27`, `OAI.SKRatio.Certificate.Data.J4K11.check_28`, `OAI.SKRatio.Certificate.Data.J4K11.check_29`, `OAI.SKRatio.Certificate.Data.J4K11.check_30`, `OAI.SKRatio.Certificate.Data.J4K11.check_31`, `OAI.SKRatio.Certificate.Data.J4K11.check_32`, `OAI.SKRatio.Certificate.Data.J4K11.check_33`, `OAI.SKRatio.Certificate.Data.J4K11.check_34`, `OAI.SKRatio.Certificate.Data.J4K11.check_35`, `OAI.SKRatio.Certificate.Data.J4K11.check_36`, `OAI.SKRatio.Certificate.Data.J4K11.check_37`, `OAI.SKRatio.Certificate.Data.J4K11.check_38`, `OAI.SKRatio.Certificate.Data.J4K11.check_39`, `OAI.SKRatio.Certificate.Data.J4K11.checks`, `OAI.SKRatio.Certificate.Data.J4K2.checks`, `OAI.SKRatio.Certificate.Data.J4K4.checks`, `OAI.SKRatio.Certificate.Data.J4K5.checks`, `OAI.SKRatio.Certificate.Data.J4K6.checks`, `OAI.SKRatio.Certificate.Data.J4K9.check_12`, `OAI.SKRatio.Certificate.Data.J4K9.check_13`, `OAI.SKRatio.Certificate.Data.J4K9.check_14`, `OAI.SKRatio.Certificate.Data.J4K9.check_15`, `OAI.SKRatio.Certificate.Data.J4K9.check_16`, `OAI.SKRatio.Certificate.Data.J4K9.check_17`, `OAI.SKRatio.Certificate.Data.J4K9.check_18`, `OAI.SKRatio.Certificate.Data.J4K9.check_19`, `OAI.SKRatio.Certificate.Data.J4K9.check_20`, `OAI.SKRatio.Certificate.Data.J4K9.check_21`, `OAI.SKRatio.Certificate.Data.J4K9.check_22`, `OAI.SKRatio.Certificate.Data.J4K9.check_23`, `OAI.SKRatio.Certificate.Data.J4K9.check_24`, `OAI.SKRatio.Certificate.Data.J4K9.check_25`, `OAI.SKRatio.Certificate.Data.J4K9.check_26`, `OAI.SKRatio.Certificate.Data.J4K9.check_27`, `OAI.SKRatio.Certificate.Data.J4K9.check_28`, `OAI.SKRatio.Certificate.Data.J4K9.check_29`, `OAI.SKRatio.Certificate.Data.J4K9.check_30`, `OAI.SKRatio.Certificate.Data.J4K9.check_31`, `OAI.SKRatio.Certificate.Data.J4K9.check_32`, `OAI.SKRatio.Certificate.Data.J4K9.check_33`, `OAI.SKRatio.Certificate.Data.J4K9.check_34`, `OAI.SKRatio.Certificate.Data.J4K9.check_35`, `OAI.SKRatio.Certificate.Data.J4K9.check_36`, `OAI.SKRatio.Certificate.Data.J4K9.check_37`, `OAI.SKRatio.Certificate.Data.J4K9.check_38`, `OAI.SKRatio.Certificate.Data.J4K9.check_39` and `OAI.SKRatio.Certificate.Data.J4K9.checks`; the proofs of `OAI.SKRatio.Certificate.Data.J4K11.check_14`, `OAI.SKRatio.Certificate.Data.J4K11.check_15`, `OAI.SKRatio.Certificate.Data.J4K11.check_16`, `OAI.SKRatio.Certificate.Data.J4K11.check_17`, `OAI.SKRatio.Certificate.Data.J4K11.check_18`, `OAI.SKRatio.Certificate.Data.J4K11.check_19`, `OAI.SKRatio.Certificate.Data.J4K11.check_20`, `OAI.SKRatio.Certificate.Data.J4K11.check_21`, `OAI.SKRatio.Certificate.Data.J4K11.check_22`, `OAI.SKRatio.Certificate.Data.J4K11.check_23`, `OAI.SKRatio.Certificate.Data.J4K11.check_24`, `OAI.SKRatio.Certificate.Data.J4K11.check_25`, `OAI.SKRatio.Certificate.Data.J4K11.check_26`, `OAI.SKRatio.Certificate.Data.J4K11.check_27`, `OAI.SKRatio.Certificate.Data.J4K11.check_28`, `OAI.SKRatio.Certificate.Data.J4K11.check_29`, `OAI.SKRatio.Certificate.Data.J4K11.check_30`, `OAI.SKRatio.Certificate.Data.J4K11.check_31`, `OAI.SKRatio.Certificate.Data.J4K11.check_32`, `OAI.SKRatio.Certificate.Data.J4K11.check_33`, `OAI.SKRatio.Certificate.Data.J4K11.check_34`, `OAI.SKRatio.Certificate.Data.J4K11.check_35`, `OAI.SKRatio.Certificate.Data.J4K11.check_36`, `OAI.SKRatio.Certificate.Data.J4K11.check_37`, `OAI.SKRatio.Certificate.Data.J4K11.check_38`, `OAI.SKRatio.Certificate.Data.J4K11.check_39`, `OAI.SKRatio.Certificate.Data.J4K11.checks`, `OAI.SKRatio.Certificate.Data.J4K2.checks`, `OAI.SKRatio.Certificate.Data.J4K4.checks`, `OAI.SKRatio.Certificate.Data.J4K5.checks`, `OAI.SKRatio.Certificate.Data.J4K6.checks`, `OAI.SKRatio.Certificate.Data.J4K9.check_12`, `OAI.SKRatio.Certificate.Data.J4K9.check_13`, `OAI.SKRatio.Certificate.Data.J4K9.check_14`, `OAI.SKRatio.Certificate.Data.J4K9.check_15`, `OAI.SKRatio.Certificate.Data.J4K9.check_16`, `OAI.SKRatio.Certificate.Data.J4K9.check_17`, `OAI.SKRatio.Certificate.Data.J4K9.check_18`, `OAI.SKRatio.Certificate.Data.J4K9.check_19`, `OAI.SKRatio.Certificate.Data.J4K9.check_20`, `OAI.SKRatio.Certificate.Data.J4K9.check_21`, `OAI.SKRatio.Certificate.Data.J4K9.check_22`, `OAI.SKRatio.Certificate.Data.J4K9.check_23`, `OAI.SKRatio.Certificate.Data.J4K9.check_24`, `OAI.SKRatio.Certificate.Data.J4K9.check_25`, `OAI.SKRatio.Certificate.Data.J4K9.check_26`, `OAI.SKRatio.Certificate.Data.J4K9.check_27`, `OAI.SKRatio.Certificate.Data.J4K9.check_28`, `OAI.SKRatio.Certificate.Data.J4K9.check_29`, `OAI.SKRatio.Certificate.Data.J4K9.check_30`, `OAI.SKRatio.Certificate.Data.J4K9.check_31`, `OAI.SKRatio.Certificate.Data.J4K9.check_32`, `OAI.SKRatio.Certificate.Data.J4K9.check_33`, `OAI.SKRatio.Certificate.Data.J4K9.check_34`, `OAI.SKRatio.Certificate.Data.J4K9.check_35`, `OAI.SKRatio.Certificate.Data.J4K9.check_36`, `OAI.SKRatio.Certificate.Data.J4K9.check_37`, `OAI.SKRatio.Certificate.Data.J4K9.check_38`, `OAI.SKRatio.Certificate.Data.J4K9.check_39`, `OAI.SKRatio.Certificate.Data.J4K9.checks`, `OAI.SKRatio.Certificate.endpointD_prime_lower`, `OAI.SKRatio.Certificate.endpointD_prime_upper`, `OAI.SKRatio.Certificate.endpointK_one_bound` and `OAI.SKRatio.Certificate.valid4`.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ024S000

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K11

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
  | 13 => ⟨1/250000,3/500000⟩
  | 14 => ⟨51/1000000,53/1000000⟩
  | 15 => ⟨79/200000,399/1000000⟩
  | 16 => ⟨2157/1000000,1083/500000⟩
  | 17 => ⟨4059/500000,8133/1000000⟩
  | 18 => ⟨20323/1000000,20333/1000000⟩
  | 19 => ⟨32797/1000000,32823/1000000⟩
  | 20 => ⟨8379/250000,671/20000⟩
  | 21 => ⟨21651/1000000,2709/125000⟩
  | 22 => ⟨897/100000,2249/250000⟩
  | 23 => ⟨2453/1000000,247/100000⟩
  | 24 => ⟨459/1000000,233/500000⟩
  | 25 => ⟨3/50000,63/1000000⟩
  | 26 => ⟨1/200000,7/1000000⟩
  | 27 => ⟨0,1/1000000⟩
  | 28 => ⟨-1/1000000,1/1000000⟩
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

end SKRatio.Certificate.Data.J4K11

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K2

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
  | 10 => ⟨-1/1000000,0⟩
  | 11 => ⟨-1/125000,-3/500000⟩
  | 12 => ⟨-3/40000,-71/1000000⟩
  | 13 => ⟨-301/500000,-583/1000000⟩
  | 14 => ⟨-3573/1000000,-1751/500000⟩
  | 15 => ⟨-7503/500000,-14847/1000000⟩
  | 16 => ⟨-41901/1000000,-8351/200000⟩
  | 17 => ⟨-13837/200000,-68697/1000000⟩
  | 18 => ⟨-21219/500000,-8349/200000⟩
  | 19 => ⟨29251/500000,58877/1000000⟩
  | 20 => ⟨4561/31250,146863/1000000⟩
  | 21 => ⟨28393/200000,142643/1000000⟩
  | 22 => ⟨40929/500000,82303/1000000⟩
  | 23 => ⟨6267/200000,15907/500000⟩
  | 24 => ⟨1059/125000,8733/1000000⟩
  | 25 => ⟨1673/1000000,1771/1000000⟩
  | 26 => ⟨49/200000,273/1000000⟩
  | 27 => ⟨13/500000,33/1000000⟩
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

end SKRatio.Certificate.Data.J4K2

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

def expression : Expr := integrandExpr (1/2) (397973/500000) (524071/1000000) (119553/1000000) (702377/1000000) 4

end SKRatio.Certificate.Data.J4K4

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K5

def expression : Expr := integrandExpr (1/2) (397973/500000) (524071/1000000) (119553/1000000) (702377/1000000) 5

end SKRatio.Certificate.Data.J4K5

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K6

def expression : Expr := integrandExpr (1/2) (397973/500000) (524071/1000000) (119553/1000000) (702377/1000000) 6

end SKRatio.Certificate.Data.J4K6

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K9

def expression : Expr := integrandExpr (1/2) (397973/500000) (524071/1000000) (119553/1000000) (702377/1000000) 9

end SKRatio.Certificate.Data.J4K9

end

end OAI
end


