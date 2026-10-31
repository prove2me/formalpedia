-- Prove2me | Definitions.Def_OAIQ024S013
-- name    : OAIQ024S013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:21:29.637986+00:00
-- url     : https://prove2.me/theorems/8e8e1597-f409-4b02-81a7-497e49fd21c7
-- title:
--   Definitions bundle OAIQ024S013 of the split of OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 definitions. The definitions and types are `OAI.SKRatio.Certificate.Data.J4K5.blocks`, `OAI.SKRatio.Certificate.Data.J4K6.blocks`, `OAI.SKRatio.Certificate.Data.J4K7.blocks`, `OAI.SKRatio.Certificate.Data.J4K7.expression`, `OAI.SKRatio.Certificate.Data.J4K8.expression`.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: [`SKRatio_Certificates_ScalarDataJ4K5`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K5.lean), [`SKRatio_Certificates_ScalarDataJ4K6`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K6.lean), [`SKRatio_Certificates_ScalarDataJ4K7`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K7.lean), [`SKRatio_Certificates_ScalarDataJ4K8`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K8.lean).
--
--   **Imports.** It imports the bundle `OAIQ024S000` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SKRatio.Certificate.Data.J4K5.checks`, `OAI.SKRatio.Certificate.Data.J4K6.checks`, `OAI.SKRatio.Certificate.Data.J4K7.check_26`, `OAI.SKRatio.Certificate.Data.J4K7.check_27`, `OAI.SKRatio.Certificate.Data.J4K7.check_28`, `OAI.SKRatio.Certificate.Data.J4K7.check_29`, `OAI.SKRatio.Certificate.Data.J4K7.check_30`, `OAI.SKRatio.Certificate.Data.J4K7.check_31`, `OAI.SKRatio.Certificate.Data.J4K7.check_32`, `OAI.SKRatio.Certificate.Data.J4K7.check_33`, `OAI.SKRatio.Certificate.Data.J4K7.check_34`, `OAI.SKRatio.Certificate.Data.J4K7.check_35`, `OAI.SKRatio.Certificate.Data.J4K7.check_36`, `OAI.SKRatio.Certificate.Data.J4K7.check_37`, `OAI.SKRatio.Certificate.Data.J4K7.check_38`, `OAI.SKRatio.Certificate.Data.J4K7.check_39`, `OAI.SKRatio.Certificate.Data.J4K7.checks`, `OAI.SKRatio.Certificate.Data.J4K8.check_12`, `OAI.SKRatio.Certificate.Data.J4K8.check_13`, `OAI.SKRatio.Certificate.Data.J4K8.check_14`, `OAI.SKRatio.Certificate.Data.J4K8.check_15`, `OAI.SKRatio.Certificate.Data.J4K8.check_16`, `OAI.SKRatio.Certificate.Data.J4K8.check_17`, `OAI.SKRatio.Certificate.Data.J4K8.check_18`, `OAI.SKRatio.Certificate.Data.J4K8.check_19`, `OAI.SKRatio.Certificate.Data.J4K8.check_20`, `OAI.SKRatio.Certificate.Data.J4K8.check_21`, `OAI.SKRatio.Certificate.Data.J4K8.check_22`, `OAI.SKRatio.Certificate.Data.J4K8.check_23`, `OAI.SKRatio.Certificate.Data.J4K8.check_24`, `OAI.SKRatio.Certificate.Data.J4K8.check_25`, `OAI.SKRatio.Certificate.Data.J4K8.check_26`, `OAI.SKRatio.Certificate.Data.J4K8.check_27`, `OAI.SKRatio.Certificate.Data.J4K8.check_28`, `OAI.SKRatio.Certificate.Data.J4K8.check_29`, `OAI.SKRatio.Certificate.Data.J4K8.check_30`, `OAI.SKRatio.Certificate.Data.J4K8.check_31`, `OAI.SKRatio.Certificate.Data.J4K8.check_32`, `OAI.SKRatio.Certificate.Data.J4K8.check_33`, `OAI.SKRatio.Certificate.Data.J4K8.check_34`, `OAI.SKRatio.Certificate.Data.J4K8.check_35`, `OAI.SKRatio.Certificate.Data.J4K8.check_36`, `OAI.SKRatio.Certificate.Data.J4K8.check_37`, `OAI.SKRatio.Certificate.Data.J4K8.check_38`, `OAI.SKRatio.Certificate.Data.J4K8.check_39` and `OAI.SKRatio.Certificate.Data.J4K8.checks`; the proofs of `OAI.SKRatio.Certificate.Data.J4K5.checks`, `OAI.SKRatio.Certificate.Data.J4K6.checks`, `OAI.SKRatio.Certificate.Data.J4K7.check_26`, `OAI.SKRatio.Certificate.Data.J4K7.check_27`, `OAI.SKRatio.Certificate.Data.J4K7.check_28`, `OAI.SKRatio.Certificate.Data.J4K7.check_29`, `OAI.SKRatio.Certificate.Data.J4K7.check_30`, `OAI.SKRatio.Certificate.Data.J4K7.check_31`, `OAI.SKRatio.Certificate.Data.J4K7.check_32`, `OAI.SKRatio.Certificate.Data.J4K7.check_33`, `OAI.SKRatio.Certificate.Data.J4K7.check_34`, `OAI.SKRatio.Certificate.Data.J4K7.check_35`, `OAI.SKRatio.Certificate.Data.J4K7.check_36`, `OAI.SKRatio.Certificate.Data.J4K7.check_37`, `OAI.SKRatio.Certificate.Data.J4K7.check_38`, `OAI.SKRatio.Certificate.Data.J4K7.check_39`, `OAI.SKRatio.Certificate.Data.J4K7.checks`, `OAI.SKRatio.Certificate.Data.J4K7.integral_bound`, `OAI.SKRatio.Certificate.Data.J4K8.check_12`, `OAI.SKRatio.Certificate.Data.J4K8.check_13`, `OAI.SKRatio.Certificate.Data.J4K8.check_14`, `OAI.SKRatio.Certificate.Data.J4K8.check_15`, `OAI.SKRatio.Certificate.Data.J4K8.check_16`, `OAI.SKRatio.Certificate.Data.J4K8.check_17`, `OAI.SKRatio.Certificate.Data.J4K8.check_18`, `OAI.SKRatio.Certificate.Data.J4K8.check_19`, `OAI.SKRatio.Certificate.Data.J4K8.check_20`, `OAI.SKRatio.Certificate.Data.J4K8.check_21`, `OAI.SKRatio.Certificate.Data.J4K8.check_22`, `OAI.SKRatio.Certificate.Data.J4K8.check_23`, `OAI.SKRatio.Certificate.Data.J4K8.check_24`, `OAI.SKRatio.Certificate.Data.J4K8.check_25`, `OAI.SKRatio.Certificate.Data.J4K8.check_26`, `OAI.SKRatio.Certificate.Data.J4K8.check_27`, `OAI.SKRatio.Certificate.Data.J4K8.check_28`, `OAI.SKRatio.Certificate.Data.J4K8.check_29`, `OAI.SKRatio.Certificate.Data.J4K8.check_30`, `OAI.SKRatio.Certificate.Data.J4K8.check_31`, `OAI.SKRatio.Certificate.Data.J4K8.check_32`, `OAI.SKRatio.Certificate.Data.J4K8.check_33`, `OAI.SKRatio.Certificate.Data.J4K8.check_34`, `OAI.SKRatio.Certificate.Data.J4K8.check_35`, `OAI.SKRatio.Certificate.Data.J4K8.check_36`, `OAI.SKRatio.Certificate.Data.J4K8.check_37`, `OAI.SKRatio.Certificate.Data.J4K8.check_38`, `OAI.SKRatio.Certificate.Data.J4K8.check_39`, `OAI.SKRatio.Certificate.Data.J4K8.checks`, `OAI.SKRatio.Certificate.endpointK_zero_bound` and `OAI.SKRatio.Certificate.valid4`.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ024S000

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
  | 10 => ⟨1/1000000,3/1000000⟩
  | 11 => ⟨1/62500,9/500000⟩
  | 12 => ⟨27/250000,7/62500⟩
  | 13 => ⟨261/500000,531/1000000⟩
  | 14 => ⟨71/40000,1791/1000000⟩
  | 15 => ⟨3989/1000000,1003/250000⟩
  | 16 => ⟨207/40000,523/100000⟩
  | 17 => ⟨2753/1000000,2797/1000000⟩
  | 18 => ⟨19/62500,93/250000⟩
  | 19 => ⟨39/12500,3177/1000000⟩
  | 20 => ⟨117/25000,4797/1000000⟩
  | 21 => ⟨619/500000,723/500000⟩
  | 22 => ⟨51/125000,347/500000⟩
  | 23 => ⟨151/62500,2683/1000000⟩
  | 24 => ⟨41/15625,701/250000⟩
  | 25 => ⟨687/500000,733/500000⟩
  | 26 => ⟨439/1000000,3/6250⟩
  | 27 => ⟨19/200000,27/250000⟩
  | 28 => ⟨7/500000,9/500000⟩
  | 29 => ⟨1/1000000,3/1000000⟩
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
  | 10 => ⟨0,1/1000000⟩
  | 11 => ⟨1/500000,1/250000⟩
  | 12 => ⟨17/500000,37/1000000⟩
  | 13 => ⟨151/500000,313/1000000⟩
  | 14 => ⟨81/40000,1037/500000⟩
  | 15 => ⟨148/15625,1199/125000⟩
  | 16 => ⟨13669/500000,27471/1000000⟩
  | 17 => ⟨40599/1000000,4099/100000⟩
  | 18 => ⟨10913/500000,2207/100000⟩
  | 19 => ⟨2103/1000000,619/250000⟩
  | 20 => ⟨1073/62500,3497/200000⟩
  | 21 => ⟨25081/1000000,25477/1000000⟩
  | 22 => ⟨1283/100000,13143/1000000⟩
  | 23 => ⟨119/40000,1621/500000⟩
  | 24 => ⟨141/500000,391/1000000⟩
  | 25 => ⟨-7/1000000,3/125000⟩
  | 26 => ⟨-1/500000,7/1000000⟩
  | 27 => ⟨0,1/250000⟩
  | 28 => ⟨0,1/1000000⟩
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

end SKRatio.Certificate.Data.J4K6

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K7

def expression : Expr := integrandExpr (1/2) (397973/500000) (524071/1000000) (119553/1000000) (702377/1000000) 7
def blocks : ℕ → Box
  | 0 => ⟨-1/1000000,1/1000000⟩
  | 1 => ⟨-1/1000000,1/1000000⟩
  | 2 => ⟨-1/1000000,1/1000000⟩
  | 3 => ⟨-1/1000000,1/1000000⟩
  | 4 => ⟨-1/1000000,1/1000000⟩
  | 5 => ⟨-1/1000000,1/1000000⟩
  | 6 => ⟨-1/1000000,1/1000000⟩
  | 7 => ⟨-1/1000000,1/1000000⟩
  | 8 => ⟨0,1/1000000⟩
  | 9 => ⟨1/250000,3/500000⟩
  | 10 => ⟨13/250000,7/125000⟩
  | 11 => ⟨433/1000000,7/15625⟩
  | 12 => ⟨557/200000,2857/1000000⟩
  | 13 => ⟨1757/125000,1431/100000⟩
  | 14 => ⟨27361/500000,55353/1000000⟩
  | 15 => ⟨78913/500000,79351/500000⟩
  | 16 => ⟨310803/1000000,312203/1000000⟩
  | 17 => ⟨36263/100000,365337/1000000⟩
  | 18 => ⟨5811/31250,187399/1000000⟩
  | 19 => ⟨16431/1000000,18853/1000000⟩
  | 20 => ⟨49069/500000,19933/200000⟩
  | 21 => ⟨218973/1000000,2771/12500⟩
  | 22 => ⟨196003/1000000,198021/1000000⟩
  | 23 => ⟨107543/1000000,109349/1000000⟩
  | 24 => ⟨43249/1000000,22291/500000⟩
  | 25 => ⟨1389/100000,14549/1000000⟩
  | 26 => ⟨913/250000,779/200000⟩
  | 27 => ⟨39/50000,849/1000000⟩
  | 28 => ⟨133/1000000,37/250000⟩
  | 29 => ⟨17/1000000,21/1000000⟩
  | 30 => ⟨1/1000000,3/1000000⟩
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

end SKRatio.Certificate.Data.J4K7

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K8

def expression : Expr := integrandExpr (1/2) (397973/500000) (524071/1000000) (119553/1000000) (702377/1000000) 8

end SKRatio.Certificate.Data.J4K8

end

end OAI
end


